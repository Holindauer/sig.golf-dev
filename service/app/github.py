"""GitHub: webhook signature, which submission root a pull request touches, statuses and comments."""
from __future__ import annotations

import hashlib
import hmac
import re

import httpx

from . import contract
from .config import settings

API = "https://api.github.com"
SHA_RE = re.compile(r"[0-9a-f]{40}")
REPO_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9-]{0,38}/[A-Za-z0-9_.-]{1,100}")
LOGIN_RE = re.compile(r"^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})(?:\[bot\])?$")
STATUS_CONTEXT = "sig.golf/verifier"


def verify_signature(body: bytes, signature: str | None) -> bool:
    if not settings.github_webhook_secret or not signature:
        return False
    expected = "sha256=" + hmac.new(settings.github_webhook_secret.encode(), body, hashlib.sha256).hexdigest()
    return hmac.compare_digest(expected.encode(), signature.encode("utf-8", "replace"))


def _check(r: httpx.Response, what: str) -> None:
    """A verdict that never reaches the pull request must at least reach the log."""
    if r.status_code >= 300:
        print(f"[github] {what}: HTTP {r.status_code} {r.text[:200]}", flush=True)
        r.raise_for_status()


def _headers() -> dict:
    h = {"Accept": "application/vnd.github+json", "User-Agent": "sig.golf-verifier"}
    if settings.github_token:
        h["Authorization"] = f"Bearer {settings.github_token}"
    return h


def get_pr(owner_repo: str, number: int) -> dict:
    """The pull request as GitHub describes it now: author, state and head come from here, never from
    a webhook payload, so a leaked webhook secret cannot put words in anyone's mouth."""
    with httpx.Client(timeout=30) as client:
        r = client.get(f"{API}/repos/{owner_repo}/pulls/{number}", headers=_headers())
        r.raise_for_status()
        return r.json()


def pr_track(owner_repo: str, number: int, *, expected_files: int | None = None) -> tuple[str | None, list[str]]:
    """The track whose root the PR changes, and the files outside any root (which disqualify it)."""
    roots = {t["submission_root"].rstrip("/") + "/": t["slug"] for t in contract.tracks()}
    touched, outside, count = set(), [], 0
    if expected_files is not None and not 0 <= expected_files <= 3000:
        return None, ["file list exceeds GitHub's 3,000-file limit"]
    with httpx.Client(timeout=30) as client:
        page = 1
        while True:
            r = client.get(f"{API}/repos/{owner_repo}/pulls/{number}/files",
                           params={"per_page": 100, "page": page}, headers=_headers())
            r.raise_for_status()
            files = r.json()
            count += len(files)
            for f in files:
                for name in {f["filename"], f.get("previous_filename", f["filename"])}:
                    slug = next((s for root, s in roots.items() if name.startswith(root)), None)
                    if slug:
                        touched.add(slug)
                    else:
                        outside.append(name)
            if len(files) < 100:
                break
            if page == 30:
                if expected_files != count:
                    return None, ["GitHub returned an incomplete file list"]
                break
            page += 1
    if expected_files is not None and expected_files != count:
        return None, ["GitHub returned an incomplete file list"]
    if len(touched) != 1:
        return None, outside
    return touched.pop(), outside


def post_status(owner_repo: str, sha: str, state: str, description: str, target_url: str) -> None:
    if not settings.github_token:
        return
    with httpx.Client(timeout=30) as client:
        r = client.post(f"{API}/repos/{owner_repo}/statuses/{sha}", headers=_headers(),
                        json={"state": state, "description": description[:140], "target_url": target_url,
                              "context": STATUS_CONTEXT})
    _check(r, f"status on {owner_repo}@{sha[:10]}")


def post_comment(owner_repo: str, number: int, body: str) -> int | None:
    if not settings.github_token:
        return None
    with httpx.Client(timeout=30) as client:
        r = client.post(f"{API}/repos/{owner_repo}/issues/{number}/comments", headers=_headers(), json={"body": body})
    _check(r, f"comment on {owner_repo}#{number}")
    return r.json()["id"]


def update_comment(owner_repo: str, comment_id: int, body: str) -> None:
    with httpx.Client(timeout=30) as client:
        r = client.patch(f"{API}/repos/{owner_repo}/issues/comments/{comment_id}",
                         headers=_headers(), json={"body": body})
    _check(r, f"update comment {comment_id} on {owner_repo}")


FIELD_RE = re.compile(r"^[ \t]*(assisted[ _-]?by|co[ _-]?authors?)[ \t]*:[ \t]*(.*?)[ \t\r]*$", re.I | re.M)
COMMENT_RE = re.compile(r"<!--.*?-->", re.S)


def parse_pr_body(body: str) -> dict:
    """`Assisted by: ...` and `Co-authors: a, b` lines from the pull request body; the rest is the description."""
    assisted, co = None, []
    body = COMMENT_RE.sub("", body or "")
    for m in FIELD_RE.finditer(body):
        key, val = m.group(1).lower().replace("-", "").replace("_", "").replace(" ", ""), m.group(2)
        if key == "assistedby":
            assisted = val or None
        else:
            co = [c.strip().lstrip("@") for c in val.split(",") if c.strip()]
    description = FIELD_RE.sub("", body).strip() or None
    return {"assisted_by": assisted, "co_authors": co, "description": description}
