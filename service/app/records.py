"""Leaderboard queries: the Spacetime ranking, the Pareto frontier, the record history, the queue.

Scores are exact integers sigma * hverify kept as decimal strings; the record set is small, so
ordering and dominance are computed in Python rather than in SQL."""
from __future__ import annotations

from sqlalchemy import func, select
from sqlalchemy.orm import Session

from . import contract
from .db import Submission


def _verified(slug: str):
    return select(Submission).where(Submission.track == slug, Submission.status == "verified")


def records(session: Session, slug: str) -> list[Submission]:
    """Every merged, verified record of a track, oldest first."""
    rows = session.scalars(_verified(slug).where(Submission.is_record.is_(True), Submission.score.is_not(None))
                           .order_by(Submission.record_at.asc(), Submission.finished_at.asc()))
    return [s for s in rows if s.scored]


def by_score(subs: list[Submission]) -> list[Submission]:
    """Spacetime tab: lowest sigma * hverify first, smaller signature breaks ties, then earlier record."""
    return sorted(subs, key=lambda s: (s.score_int, s.sigma, s.record_at or s.finished_at or s.created_at))


def dominates(a: Submission, b: Submission) -> bool:
    return a.sigma <= b.sigma and a.hverify <= b.hverify and (a.sigma < b.sigma or a.hverify < b.hverify)


def pareto(subs: list[Submission]) -> list[Submission]:
    """Pareto tab: records no other record beats on both signature bytes and verification work,
    keeping the earliest of exact duplicates, sorted by signature bytes."""
    front = []
    for s in sorted(subs, key=lambda s: (s.sigma, s.hverify, s.record_at or s.created_at)):
        if any(dominates(o, s) or (o.sigma == s.sigma and o.hverify == s.hverify) for o in front):
            continue
        front.append(s)
    return front


def improves(existing: list[Submission], sigma: int, hverify: int) -> bool:
    """A verified head becomes a record if it beats the best score or extends the Pareto frontier
    (spec section 6). An exact duplicate of an existing record improves nothing."""
    if any(o.sigma == sigma and o.hverify == hverify for o in existing):
        return False
    score = sigma * hverify
    if not existing or score < min(o.score_int for o in existing):
        return True
    return not any(o.sigma <= sigma and o.hverify <= hverify for o in existing)


def current_record(session: Session, slug: str) -> Submission | None:
    ranked = by_score(records(session, slug))
    return ranked[0] if ranked else None


def in_flight(session: Session, slug: str | None = None) -> list[Submission]:
    q = select(Submission).where(Submission.status.in_(("pending", "verifying")))
    if slug:
        q = q.where(Submission.track == slug)
    return list(session.scalars(q.order_by(Submission.created_at.asc())))


def verified_unmerged(session: Session, slug: str) -> list[Submission]:
    """Verified heads whose pull request is not merged yet: shown, never ranked."""
    rows = session.scalars(_verified(slug).where(Submission.is_record.is_(False)).order_by(Submission.finished_at.desc()))
    return [s for s in rows if s.scored]


def solver_count(session: Session, slug: str) -> int:
    return session.scalar(select(func.count(func.distinct(Submission.user_id)))
                          .where(Submission.track == slug, Submission.status == "verified")) or 0


def track_state(session: Session, t: dict) -> dict:
    rec = current_record(session, t["slug"])
    return {
        "slug": t["slug"], "title": t["title"], "direction": t["direction"], "admission": t.get("admission", "closed"),
        "record": rec,
        "record_score": rec.score_int if rec else None,
        "record_sigma": rec.sigma if rec else None,
        "record_hverify": rec.hverify if rec else None,
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
        if best is None:
            out[s.id] = None
        elif s.score_int < best:
            out[s.id] = round(100 * (best - s.score_int) / best, 2)
        else:
            out[s.id] = None
        best = s.score_int if best is None else min(best, s.score_int)
    return out


def board(session: Session, t: dict) -> dict:
    recs = records(session, t["slug"])
    ranking = by_score(recs)
    front = pareto(recs)
    front_ids = {s.id for s in front}
    return {"cfg": t, "state": track_state(session, t), "records": recs, "ranking": ranking,
            "frontier": front, "frontier_ids": front_ids, "gains": gains(recs),
            "unmerged": verified_unmerged(session, t["slug"]), "in_flight": in_flight(session, t["slug"]),
            "curve": curve(session, t["slug"])}
