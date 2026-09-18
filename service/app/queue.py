"""Queue a commit for verification the way the webhook would (localhost / baselines).

    .venv/bin/python -m app.queue full [--repo PATH_OR_URL] [--commit HEAD] [--login sig.golf] [--baseline]

Without --repo it queues the contract repository's own submission root, which is how a track's
baseline becomes a real verified entry rather than a configured number.
"""
from __future__ import annotations

import argparse
import subprocess

from . import contract
from .auth import get_or_create_user
from .config import settings
from .db import SessionLocal, Submission, init_db


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("track")
    ap.add_argument("--repo", default=str(settings.repo_root))
    ap.add_argument("--commit", default="HEAD")
    ap.add_argument("--login", default="sig.golf")   # a dot: no GitHub account can claim it
    ap.add_argument("--baseline", action="store_true")
    ap.add_argument("--description", default=None)
    a = ap.parse_args()
    t = contract.track(a.track)
    if t is None:
        print(f"unknown track {a.track}")
        return 1
    sha = a.commit
    if not a.repo.startswith("http"):
        sha = subprocess.run(["git", "-C", a.repo, "rev-parse", a.commit], check=True, capture_output=True,
                             text=True).stdout.strip()
    init_db()
    with SessionLocal() as session:
        user = get_or_create_user(session, a.login, name="sig.golf (baseline)" if a.baseline else None)
        desc = a.description or (f"Baseline of the {t['title'].lower()} track: the organizers' reference scheme "
                                 "as shipped in the contract repository." if a.baseline else None)
        sub = Submission(track=a.track, user_id=user.id, source_repo=a.repo, commit=sha, baseline=a.baseline,
                         description=desc)
        session.add(sub)
        session.commit()
        print(f"queued {sub.id} for {a.track}: {a.repo}@{sha[:10]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
