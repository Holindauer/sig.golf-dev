"""The contract as the service sees it: challenges.json, the pin, the trusted commit."""
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


def admission_open(t: dict | None) -> bool:
    """Proof pull requests are queued only while the pinned metadata says the track is open."""
    return bool(t) and t.get("admission") == "open"


def required_files(t: dict) -> set[str]:
    return set(t.get("required_files", ()))


def max_metric() -> int:
    return int(load()["limits"]["max_metric"])


def contract_id() -> str:
    cfg = load()
    pin = settings.repo_root / cfg["contract"]["pin_file"]
    return hashlib.sha256(pin.read_bytes()).hexdigest() if pin.is_file() else "unpinned"


@lru_cache(maxsize=1)
def trusted_commit() -> str:
    try:
        return subprocess.run(["git", "-C", str(settings.repo_root), "rev-parse", "HEAD"],
                              check=True, capture_output=True, text=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"


def score_key(score: int, sigma: int) -> tuple[int, int]:
    """Smaller product wins; the smaller signature breaks ties. Compared in Python: the exact product
    can exceed 64 bits, so it is never compared inside the database."""
    return score, sigma


def leads(score: int, sigma: int, record_score: int | None, record_sigma: int | None) -> bool:
    """Whether (score, sigma) strictly precedes the current best, or there is none."""
    if record_score is None or record_sigma is None:
        return True
    return score_key(score, sigma) < score_key(record_score, record_sigma)


# Audited implications between exact contract fingerprints: a result verified under the key
# (an older pin) counts for the listed tracks under the value's pin. It is empty on purpose:
# no contract revision has been audited yet, so every verified result binds to the exact pin
# it was checked against. Add an entry only with the audit that justifies it, and never
# rewrite an old receipt's contract ID.
RESULT_COMPATIBILITY: dict[str, dict[str, frozenset[str]]] = {}


def compatible_result(slug: str, previous_id: str | None) -> bool:
    """An audited implication between these exact contracts for an already verified result."""
    return slug in RESULT_COMPATIBILITY.get(contract_id(), {}).get(previous_id, ())
