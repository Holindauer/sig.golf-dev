"""The contract as the service sees it: challenges.json, the protected files, the trusted commit."""
from __future__ import annotations

import hashlib
import json
import subprocess
from functools import lru_cache

from .config import settings


def load() -> dict:
    return json.loads((settings.repo_root / "challenges.json").read_text(encoding="utf-8"))


def tracks() -> list[dict]:
    return load()["tracks"]


def track(slug: str) -> dict | None:
    return next((t for t in tracks() if t["slug"] == slug), None)


def primary_track() -> dict:
    return tracks()[0]


def admission_open(t: dict) -> bool:
    return t.get("admission") == "open"


def contract_id() -> str:
    """A digest over the protected files as they are in the trusted checkout."""
    cfg = load()
    digest = hashlib.sha256()
    for rel in cfg["protected"]:
        path = settings.repo_root / rel
        digest.update(rel.encode())
        digest.update(path.read_bytes() if path.is_file() else b"<missing>")
    return digest.hexdigest()


@lru_cache(maxsize=1)
def trusted_commit() -> str:
    try:
        return subprocess.run(["git", "-C", str(settings.repo_root), "rev-parse", "HEAD"],
                              check=True, capture_output=True, text=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"
