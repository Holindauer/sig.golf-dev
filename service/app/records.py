"""Leaderboard queries: the ranking, the Pareto frontier, the record history, the queue, the notes journal.

Scores are exact integers sigma * hverify kept as decimal strings; the record set is small, so
ordering and dominance are computed in Python rather than in SQL.
"""
from __future__ import annotations

from sqlalchemy import func, select
from sqlalchemy.orm import Session

from . import contract
from .db import Submission
from .visibility import visible


def eligible(sub: Submission) -> bool:
    """Unversioned and historical results are never evidence for the current contract."""
    return visible(sub) and (sub.current_contract or bool(sub.detail_dict.get("demo")))


def _verified(slug: str):
    return select(Submission).where(Submission.track == slug, Submission.status == "verified")


def records(session: Session, slug: str) -> list[Submission]:
    """Every record of a track, oldest first."""
    rows = session.scalars(_verified(slug).where(Submission.is_record.is_(True), Submission.score.is_not(None))
                           .order_by(Submission.record_at.asc(), Submission.finished_at.asc()))
    return [s for s in rows if s.scored and eligible(s)]


def by_score(subs: list[Submission]) -> list[Submission]:
    """Lowest sigma * hverify first, smaller signature breaks ties, then the earlier record."""
    return sorted(subs, key=lambda s: (s.score_int, s.sigma, s.record_at or s.finished_at or s.created_at))


def dominates(a: Submission, b: Submission) -> bool:
    return a.sigma <= b.sigma and a.hverify <= b.hverify and (a.sigma < b.sigma or a.hverify < b.hverify)


def pareto(subs: list[Submission]) -> list[Submission]:
    """Records no other record beats on both signature bytes and verification work, keeping the
    earliest of exact duplicates, sorted by signature bytes."""
    front = []
    for s in sorted(subs, key=lambda s: (s.sigma, s.hverify, s.record_at or s.created_at)):
        if any(dominates(o, s) or (o.sigma == s.sigma and o.hverify == s.hverify) for o in front):
            continue
        front.append(s)
    return front


def improves(existing: list[Submission], sigma: int, hverify: int) -> bool:
    """A verified head becomes a record if it beats the best score or extends the Pareto frontier.
    An exact duplicate of an existing record improves nothing."""
    if any(o.sigma == sigma and o.hverify == hverify for o in existing):
        return False
    score = sigma * hverify
    if not existing or score < min(o.score_int for o in existing):
        return True
    return not any(o.sigma <= sigma and o.hverify <= hverify for o in existing)


def current_record(session: Session, slug: str) -> Submission | None:
    ranked = by_score(records(session, slug))
    return ranked[0] if ranked else None


def frontier(session: Session, slug: str) -> list[Submission]:
    """The record history, newest first."""
    return records(session, slug)[::-1]


def in_flight(session: Session, slug: str | None = None) -> list[Submission]:
    q = select(Submission).where(Submission.status.in_(("admitting", "pending", "verifying", "publishing")))
    if slug:
        q = q.where(Submission.track == slug)
    return [s for s in session.scalars(q.order_by(Submission.created_at.asc())) if visible(s)]


def solver_count(session: Session, slug: str) -> int:
    return len({s.user_id for s in session.scalars(_verified(slug)) if eligible(s)})


def track_state(session: Session, t: dict) -> dict:
    rec = current_record(session, t["slug"])
    return {
        "slug": t["slug"], "title": t["title"], "direction": t["direction"], "admission": t.get("admission", "closed"),
        "record": rec,
        "record_score": rec.score_int if rec else None,
        "record_sigma": rec.sigma if rec else None,
        "record_hverify": rec.hverify if rec else None,
        "record_verified": bool(rec and not rec.detail_dict.get("demo")),
        "record_demo": bool(rec and rec.detail_dict.get("demo")),
        "record_submission_id": rec.id if rec else None,
        "record_setter": rec.user.login if rec else None,
        "record_at": rec.record_at.isoformat() + "Z" if rec and rec.record_at else None,
        "solvers": solver_count(session, t["slug"]),
        "in_flight": len(in_flight(session, t["slug"])),
    }


def curve(session: Session, slug: str) -> list[dict]:
    """The best score over time: a step curve through the records that lowered it."""
    best, points = None, []
    for s in records(session, slug):
        if s.record_at is None:
            continue
        if best is None or s.score_int < best:
            best = s.score_int
            points.append({"t": s.record_at, "value": s.score_int, "id": s.id, "login": s.user.login,
                           "sigma": s.sigma, "hverify": s.hverify, "demo": bool(s.detail_dict.get("demo"))})
    return points


def gains(recs: list[Submission]) -> dict[str, float | None]:
    """Relative improvement of each record over the best score before it, in percent; None when it
    entered through the Pareto frontier rather than by lowering the best score."""
    best, out = None, {}
    for s in recs:                                   # chronological
        if best is None or s.score_int >= best:
            out[s.id] = None
        else:
            out[s.id] = round(100 * (best - s.score_int) / best, 2)
        best = s.score_int if best is None else min(best, s.score_int)
    return out


def track_label(t: dict) -> tuple[str, str]:
    """The one-line name of a track and the leaderboard section it links to."""
    return t["title"], "/#board-title"


def journal(session: Session, track: str | None = None, limit: int = 300, per_author: int = 20) -> list[dict]:
    """Notes of checked submissions, newest first: records, non-records and proofs the checker
    rejected, so ideas and dead ends stay readable. Only the latest checked head of each pull
    request counts, submissions refused before any proof check (format, infrastructure) are left
    out, and each author has at most `per_author` entries, so no one can flood the journal."""
    q = select(Submission).where(Submission.status.in_(("verified", "rejected", "timeout")))
    items, seen_prs, by_author = [], set(), {}
    for s in session.scalars(q.order_by(func.coalesce(Submission.finished_at, Submission.created_at).desc())):
        if not visible(s):
            continue
        if s.pr_url:
            if s.pr_url in seen_prs:
                continue
            seen_prs.add(s.pr_url)
        if not s.notes or not contract.track(s.track) or (track and s.track != track):
            continue
        if by_author.get(s.user_id, 0) >= per_author:
            continue
        by_author[s.user_id] = by_author.get(s.user_id, 0) + 1
        t = contract.track(s.track)
        label, href = track_label(t)
        items.append({"sub": s, "cfg": t, "label": label, "href": href})
        if len(items) >= limit:
            break
    return items


def board(session: Session, t: dict) -> dict:
    recs = records(session, t["slug"])
    ranking = by_score(recs)
    front = pareto(recs)
    return {"cfg": t, "state": track_state(session, t), "records": recs, "ranking": ranking,
            "history": recs[::-1], "frontier": front, "frontier_ids": {s.id for s in front},
            "gains": gains(recs), "in_flight": in_flight(session, t["slug"]),
            "curve": curve(session, t["slug"])}
