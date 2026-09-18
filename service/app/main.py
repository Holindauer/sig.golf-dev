"""sig.golf: the site, and the pull-request webhook that queues submissions."""
from __future__ import annotations

import asyncio
import hashlib
import json
import logging
from contextlib import asynccontextmanager, suppress
from pathlib import Path

import httpx
import markdown
import nh3
from fastapi import Depends, FastAPI, HTTPException, Request
from fastapi.concurrency import run_in_threadpool
from fastapi.responses import FileResponse, HTMLResponse, PlainTextResponse
from fastapi.staticfiles import StaticFiles
from fastapi.templating import Jinja2Templates
from sqlalchemy import select
from sqlalchemy.exc import SQLAlchemyError
from sqlalchemy.orm import Session
from starlette.exceptions import HTTPException as StarletteHTTPException

from . import auth, charts, contract, github, records
from .config import settings
from .db import SessionLocal, Submission, User, get_session, init_db, local_lock, schedule_report, utcnow

APP_DIR = Path(__file__).resolve().parent


@asynccontextmanager
async def lifespan(_app):
    if settings.environment == "production" and settings.role != "web":
        raise RuntimeError("the production website must run with SIG_ROLE=web under its separate Unix identity")
    init_db()
    task = None
    if settings.github_token and settings.contract_repo:
        async def report_loop():
            from .worker import retry_reports
            while True:
                try:
                    await run_in_threadpool(retry_reports)
                except Exception:
                    logging.getLogger(__name__).exception("GitHub outbox delivery failed; retrying")
                await asyncio.sleep(3)
        task = asyncio.create_task(report_loop())
    try:
        yield
    finally:
        if task is not None:
            task.cancel()
            with suppress(asyncio.CancelledError):
                await task


app = FastAPI(title="sig.golf", version="0.1.0", docs_url=None, openapi_url=None, redoc_url=None, lifespan=lifespan)
app.mount("/static", StaticFiles(directory=APP_DIR / "static"), name="static")
templates = Jinja2Templates(directory=APP_DIR / "templates")
templates.env.filters["dt"] = lambda d: d.strftime("%Y-%m-%d %H:%M UTC") if d else ""
templates.env.filters["date"] = lambda d: d.strftime("%Y-%m-%d") if d else ""
templates.env.filters["short"] = lambda s: (s or "")[:10]
templates.env.filters["num"] = lambda v: f"{int(v):,}" if v is not None else "–"
MD_TAGS = {"p", "br", "hr", "strong", "em", "del", "code", "pre", "blockquote", "ul", "ol", "li", "a",
           "h1", "h2", "h3", "h4", "h5", "h6", "table", "thead", "tbody", "tr", "th", "td"}


def safe_markdown(text: str | None) -> str:
    """Markdown written by strangers (a pull request body): rendered, then reduced to plain formatting
    tags and http(s)/mailto links."""
    html = markdown.markdown(text or "", extensions=["tables", "fenced_code"])
    return nh3.clean(html, tags=MD_TAGS, attributes={"a": {"href"}}, url_schemes={"http", "https", "mailto"})


templates.env.filters["md"] = safe_markdown


@app.middleware("http")
async def security_headers(request: Request, call_next):
    response = await call_next(request)
    response.headers["X-Content-Type-Options"] = "nosniff"
    response.headers["X-Frame-Options"] = "DENY"
    response.headers["Referrer-Policy"] = "strict-origin-when-cross-origin"
    response.headers["Content-Security-Policy"] = (
        "default-src 'self'; script-src 'self'; style-src 'self' 'unsafe-inline'; "
        "img-src 'self' https: data:; base-uri 'self'; object-src 'none'; frame-ancestors 'none'; form-action 'self'"
    )
    return response


def static_version() -> str:
    assets = sorted(p for p in (APP_DIR / "static").iterdir() if p.suffix in {".css", ".js"})
    return hashlib.sha256(b"".join(p.read_bytes() for p in assets if p.is_file())).hexdigest()[:10]


def render(request: Request, name: str, **ctx) -> HTMLResponse:
    cfg = contract.load()
    ctx.update(request=request, settings=settings, contract_version=cfg["contract"]["version"],
               contract_id=contract.contract_id(), contract_commit=contract.trusted_commit(),
               contract_meter=cfg["contract"]["meter"], static_v=static_version(),
               tracks={t["slug"]: t for t in cfg["tracks"]}, primary=cfg["tracks"][0],
               repo_url=f"https://github.com/{settings.contract_repo}" if settings.contract_repo else None)
    return templates.TemplateResponse(request, name, ctx)


@app.exception_handler(StarletteHTTPException)
async def http_error(request: Request, exc: StarletteHTTPException):
    if request.method in {"GET", "HEAD"} and "text/html" in request.headers.get("accept", ""):
        message = "This page could not be found." if exc.status_code == 404 else "This request could not be completed."
        response = render(request, "error.html", status_code=exc.status_code, message=message)
        response.status_code = exc.status_code
        response.headers.update(exc.headers or {})
        return response
    from fastapi.exception_handlers import http_exception_handler
    return await http_exception_handler(request, exc)


@app.exception_handler(Exception)
async def internal_error(request: Request, _exc: Exception):
    if request.method in {"GET", "HEAD"} and "text/html" in request.headers.get("accept", ""):
        response = render(request, "error.html", status_code=500,
                          message="This page is temporarily unavailable. Please try again shortly.")
        response.status_code = 500
        return response
    from fastapi.responses import JSONResponse
    return JSONResponse({"detail": "internal server error"}, status_code=500)


@app.get("/healthz", include_in_schema=False)
def health(session: Session = Depends(get_session)):
    try:
        session.execute(select(1))
    except SQLAlchemyError:
        raise HTTPException(503, "database unavailable") from None
    return {"status": "ok"}


# --- the one way in: a pull request -----------------------------------------------------------

def queue_submission(session: Session, user: User, track: str, repo: str, commit: str, description: str | None,
                     co_authors: list[str], assisted_by: str | None, pr_number: int | None, pr_url: str | None) -> Submission:
    with local_lock("admission"):
        return _queue_submission(session, user, track, repo, commit, description, co_authors,
                                 assisted_by, pr_number, pr_url)


def _queue_submission(session: Session, user: User, track: str, repo: str, commit: str,
                      description: str | None, co_authors: list[str], assisted_by: str | None,
                      pr_number: int | None, pr_url: str | None) -> Submission:
    track_config = contract.track(track)
    if track_config is None:
        raise HTTPException(400, f"unknown track {track!r}")
    if not contract.admission_open(track_config):
        raise HTTPException(403, "submissions to this track are not open yet; see the rules for the launch gates")
    commit = commit.strip().lower()
    if not github.SHA_RE.fullmatch(commit):
        raise HTTPException(400, "commit must be a full 40-character hex commit hash")
    mine = [s for s in records.in_flight(session) if s.user_id == user.id]
    if len(mine) >= settings.max_inflight_per_user:
        raise HTTPException(429, f"{user.login} already has {len(mine)} submissions in flight")
    if len(records.in_flight(session)) >= settings.queue_cap:
        raise HTTPException(429, "the verification queue is full")
    dup = session.scalars(select(Submission).where(Submission.track == track, Submission.commit == commit,
                                                   Submission.source_repo == repo,
                                                   Submission.status.in_(("pending", "verifying", "verified", "rejected",
                                                                          "timeout")))).first()
    if dup:
        raise HTTPException(409, f"this commit is already submitted: {dup.id}")
    sub = Submission(track=track, user_id=user.id, source_repo=repo, commit=commit,
                     description=(description or "").strip() or None, co_authors=json.dumps(co_authors),
                     assisted_by=(assisted_by or "").strip()[:120] or None, pr_number=pr_number, pr_url=pr_url)
    session.add(sub)
    schedule_report(session, sub)
    session.commit()
    return sub


MAX_WEBHOOK_BYTES = 2 * 1024 * 1024


@app.post("/webhooks/github")
async def webhook(request: Request):
    try:
        declared = int(request.headers.get("content-length") or 0)
    except ValueError:
        raise HTTPException(400, "bad content-length")
    if declared < 0:
        raise HTTPException(400, "bad content-length")
    if declared > MAX_WEBHOOK_BYTES:
        raise HTTPException(413, "payload too large")
    body = b""
    async for chunk in request.stream():
        body += chunk
        if len(body) > MAX_WEBHOOK_BYTES:
            raise HTTPException(413, "payload too large")
    if not github.verify_signature(body, request.headers.get("x-hub-signature-256")):
        raise HTTPException(401, "bad signature")
    if request.headers.get("x-github-event") != "pull_request":
        return {"ignored": True}
    try:
        ev = json.loads(body)
        action, number = ev["action"], ev["pull_request"]["number"]
        owner_repo, head_sha = ev["repository"]["full_name"], ev["pull_request"]["head"]["sha"]
        if (not isinstance(action, str) or type(number) is not int or number <= 0
                or not isinstance(owner_repo, str) or not github.REPO_RE.fullmatch(owner_repo)
                or not isinstance(head_sha, str) or not github.SHA_RE.fullmatch(head_sha)):
            raise ValueError
    except (ValueError, KeyError, TypeError):
        raise HTTPException(400, "malformed event")
    if action not in ("opened", "synchronize", "reopened", "closed"):
        return {"ignored": True}
    if not settings.contract_repo:
        raise HTTPException(503, "GitHub submission admission is not configured")
    if owner_repo.lower() != settings.contract_repo.lower():
        return {"ignored": True, "reason": "not the contract repository"}
    if action == "closed":
        return await run_in_threadpool(handle_merged_pull_request, owner_repo, number, head_sha)
    return await run_in_threadpool(handle_pull_request, owner_repo, number, head_sha)


def handle_pull_request(owner_repo: str, number: int, head_sha: str) -> dict:
    """The event only says where to look. Author, head and changed files are read from GitHub's API,
    and the head must still be the event's commit before and after the files are listed."""
    try:
        pr = github.get_pr(owner_repo, number)
        slug, outside = github.pr_track(owner_repo, number, expected_files=pr.get("changed_files"))
        pr_after = github.get_pr(owner_repo, number)
    except httpx.HTTPError as exc:
        raise HTTPException(502, f"GitHub API: {exc}")
    if (pr.get("state") != "open" or pr_after.get("state") != "open"
            or pr["head"]["sha"] != head_sha or pr_after["head"]["sha"] != head_sha):
        return {"queued": False, "reason": "the pull request moved on; its newer event is the one that counts"}
    if slug is None or outside:
        github.post_comment(owner_repo, number,
                            "**sig.golf verifier:** not queued. A submission must change exactly one "
                            "submission root under submissions/ and no files outside it. "
                            "Check this pull request's Files changed tab.")
        return {"queued": False}
    head_repo = pr["head"].get("repo")
    login = (pr.get("user") or {}).get("login") or ""
    if head_repo is None or not github.LOGIN_RE.fullmatch(login):
        return {"queued": False, "reason": "the head repository is gone or the author is not a GitHub account"}
    fields = github.parse_pr_body(pr.get("body") or "")
    with local_lock("users"), SessionLocal() as session:
        submitter = auth.get_or_create_user(session, login, github_id=pr["user"]["id"],
                                            avatar_url=pr["user"].get("avatar_url"))
        try:
            sub = queue_submission(session, submitter, slug, head_repo["clone_url"], head_sha,
                                   fields["description"], fields["co_authors"], fields["assisted_by"],
                                   number, pr["html_url"])
        except HTTPException as exc:
            github.post_comment(owner_repo, number, f"**sig.golf verifier:** not queued: {exc.detail}")
            return {"queued": False, "reason": exc.detail}
    return {"queued": True, "id": sub.id}


def handle_merged_pull_request(owner_repo: str, number: int, head_sha: str) -> dict:
    """A verified proof becomes a record only after GitHub confirms this exact head was merged."""
    try:
        pr = github.get_pr(owner_repo, number)
    except httpx.HTTPError as exc:
        raise HTTPException(502, f"GitHub API: {exc}") from exc
    if not pr.get("merged") or pr.get("state") != "closed" or pr["head"]["sha"] != head_sha:
        return {"promoted": False, "reason": "this head was not merged"}
    head_repo = pr["head"].get("repo")
    from .worker import promote
    with local_lock("results"), SessionLocal() as session:
        query = select(Submission).where(Submission.pr_number == number, Submission.commit == head_sha)
        if head_repo is not None:
            query = query.where(Submission.source_repo == head_repo["clone_url"])
        submissions = list(session.scalars(query))
        for sub in submissions:
            detail = sub.detail_dict
            detail["merge"] = {"head": head_sha, "repository": owner_repo, "number": number,
                               "merged_at": pr.get("merged_at")}
            sub.detail = json.dumps(detail)
            if sub.status == "verified":
                promote(session, sub)
            schedule_report(session, sub)
        session.commit()
        return {"promoted": any(sub.is_record for sub in submissions)}


# --- pages ------------------------------------------------------------------------------------

@app.get("/", response_class=HTMLResponse)
def home(request: Request, session: Session = Depends(get_session)):
    t = contract.primary_track()
    board = records.board(session, t)
    return render(request, "home.html", board=board, t=t,
                  chart=charts.record_chart(board["curve"], utcnow()),
                  pareto=charts.pareto_chart(board["records"], board["frontier_ids"]))


@app.get("/submissions/{sub_id}", response_class=HTMLResponse)
def submission_page(sub_id: str, request: Request, session: Session = Depends(get_session)):
    sub = session.get(Submission, sub_id)
    if sub is None:
        raise HTTPException(404)
    t = contract.track(sub.track) or contract.primary_track()
    frontier_ids = {s.id for s in records.pareto(records.records(session, sub.track))}
    return render(request, "submission.html", sub=sub, t=t, on_frontier=sub.id in frontier_ids,
                  queue_position=next((i + 1 for i, s in enumerate(records.in_flight(session)) if s.id == sub.id), None))


@app.get("/submissions/{sub_id}/log", response_class=PlainTextResponse)
def submission_log(sub_id: str, session: Session = Depends(get_session)):
    """The verifier's transcript. Public: the submission is a public pull request anyway."""
    sub = session.get(Submission, sub_id)
    if sub is None:
        raise HTTPException(404)
    if sub.log_path and Path(sub.log_path).is_file():
        return FileResponse(sub.log_path, media_type="text/plain; charset=utf-8")
    return "(no log yet)"


@app.get("/solvers/{login}", response_class=HTMLResponse)
def solver_page(login: str, request: Request, session: Session = Depends(get_session)):
    solver = session.scalars(select(User).where(User.login == login)).first()
    if solver is None:
        raise HTTPException(404)
    subs = list(session.scalars(select(Submission).where(Submission.user_id == solver.id)
                                .order_by(Submission.created_at.desc())))
    return render(request, "solver.html", solver=solver, subs=subs)


@app.get("/rules", response_class=HTMLResponse)
def rules():
    """The rules are the draft specification itself, served verbatim from the trusted checkout."""
    path = settings.repo_root / contract.load()["contract"]["rules"]
    if not path.is_file():
        raise HTTPException(404)
    return FileResponse(path, media_type="text/html; charset=utf-8")


@app.get("/llms.txt", response_class=PlainTextResponse)
def llms():
    text = (settings.repo_root / "llms.txt").read_text(encoding="utf-8")
    return text + f"""
## Where the state is

The contract repository is the source of truth: each track's submission root holds the current
record. Open pull requests are the submissions in flight; the verifier's verdict is on each one as
a commit status and a comment linking to {settings.base_url}/submissions/<id>, which shows status,
signature bytes, verification work, the exact spacetime score, attribution and the transcript.
"""
