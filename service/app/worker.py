"""One-host verifier worker with a durable GitHub result outbox.

Verification checks a proof. A trusted merged-PR event promotes its verified head to a record.
Run with ``.venv/bin/python -m app.worker``; a file lock prevents concurrent workers.
"""
from __future__ import annotations

import json
import os
import shutil
import signal
import subprocess
import sys
import time
import traceback
from datetime import timedelta

from sqlalchemy import select

from . import contract, github, records
from .config import settings
from .db import GithubReport, SessionLocal, Submission, init_db, local_lock, schedule_report, utcnow

POLL_SECONDS = 3
FINAL = ("verified", "rejected", "timeout")


def _log(msg: str) -> None:
    print(f"[worker {utcnow().isoformat(timespec='seconds')}] {msg}", flush=True)


def _stop_pipeline(proc) -> tuple[str, str]:
    """Let verify_pr.py stop the isolated verifier, then kill remaining children if necessary."""
    try:
        os.killpg(proc.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        return proc.communicate(timeout=40)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        return proc.communicate(timeout=10)


def valid_verified(result: dict, sub: Submission, limits: dict) -> bool:
    sigma, hverify, score = result.get("sigma"), result.get("hverify"), result.get("score")
    return (result.get("track") == sub.track and result.get("commit") == sub.commit
            and type(sigma) is int and type(hverify) is int
            and 0 < sigma <= limits["max_metric"] and 0 < hverify <= limits["max_metric"]
            and isinstance(score, str) and score == str(sigma * hverify))


def run_pipeline(sub: Submission) -> tuple[dict, str | None]:
    """Run the trusted verifier and accept only a matching, consistent result."""
    cfg = contract.load()
    limit = cfg["limits"]["wall_clock_seconds"]
    work = settings.work_dir / sub.id
    shutil.rmtree(work, ignore_errors=True)
    cmd = [sys.executable, str(settings.repo_root / "scripts" / "verify_pr.py"), sub.track,
           "--source", sub.source_repo, "--commit", sub.commit, "--json", "--keep", "--work", str(work)]
    if settings.insecure_local and settings.environment != "production":
        cmd.append("--insecure-local")
    timed_out = False
    proc = subprocess.Popen(cmd, cwd=settings.repo_root, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            text=True, start_new_session=True)
    try:
        stdout, stderr = proc.communicate(timeout=limit + 600)
    except subprocess.TimeoutExpired:
        timed_out = True
        stdout, stderr = _stop_pipeline(proc)
    except BaseException:
        _stop_pipeline(proc)
        raise
    log_dst = settings.data_dir / "logs" / f"{sub.id}.log"
    src_log = work / "verify.log"
    if src_log.is_file():
        shutil.copyfile(src_log, log_dst)
    else:
        log_dst.write_text(stdout + "\n" + stderr, encoding="utf-8")
    shutil.rmtree(work, ignore_errors=True)
    if timed_out:
        with log_dst.open("a", encoding="utf-8") as log:
            log.write("\n[pipeline exceeded its outer time limit]\n")
        return {"status": "timeout", "reason": "pipeline exceeded its outer time limit"}, str(log_dst)
    try:
        result = json.loads(stdout)
        if not isinstance(result, dict) or not isinstance(result.get("status"), str):
            raise ValueError("missing status")
        if result["status"] == "verified" and (proc.returncode != 0 or not valid_verified(result, sub, cfg["limits"])):
            raise ValueError("verified result does not match the queued head or the metric limits")
    except (ValueError, TypeError):
        result = {"status": "failed", "reason": f"verify_pr.py exited {proc.returncode} without a valid matching result"}
    return result, str(log_dst)


def promote(session, sub: Submission) -> None:
    """Only merged, verified heads (or an explicit local certificate) can become records, and only
    when they beat the best score or extend the Pareto frontier."""
    if sub.status != "verified" or not sub.scored or sub.is_record:
        return
    merge = sub.detail_dict.get("merge") or {}
    if not sub.baseline and not (
        merge.get("head") == sub.commit and merge.get("number") == sub.pr_number
        and settings.contract_repo and merge.get("repository", "").lower() == settings.contract_repo.lower()
    ):
        return
    existing = [s for s in records.records(session, sub.track) if s.id != sub.id]
    if records.improves(existing, sub.sigma, sub.hverify):
        sub.is_record = True
        sub.record_at = utcnow()


def report(sub: Submission) -> int | None:
    """Publish a verdict; retain the comment ID so later updates edit the same comment."""
    url = f"{settings.base_url}/submissions/{sub.id}"
    if sub.status in {"pending", "verifying"}:
        state, what = "pending", "queued for verification" if sub.status == "pending" else "verification in progress"
        body = f"**sig.golf verifier:** {what}. Details: {url}"
    elif sub.status == "verified":
        what = (f"verified: spacetime {sub.score} = {sub.sigma} B × {sub.hverify}"
                + (" — new record" if sub.is_record else " (not a merged record)"))
        state, body = "success", f"**sig.golf verifier:** {what}. Details: {url}"
    else:
        failure = (sub.detail_dict.get("failure") or {}).get("message", "")
        what = f"{sub.status}: {failure}"[:140] if failure else sub.status
        state = "error" if sub.status == "failed" else "failure"
        quoted = failure[:600].replace("```", "'''")
        body = f"**sig.golf verifier:** `{sub.status}`.\n\n```\n{quoted}\n```\n\nDetails: {url}"
    github.post_status(settings.contract_repo, sub.commit, state, what, url)
    comment_id = sub.detail_dict.get("github_comment_id")
    if type(comment_id) is int:
        try:
            github.update_comment(settings.contract_repo, comment_id, body)
            return comment_id
        except github.httpx.HTTPStatusError as exc:
            if exc.response.status_code != 404:
                raise
    return github.post_comment(settings.contract_repo, sub.pr_number, body)


def deliver_report(sub_id: str) -> None:
    if not settings.contract_repo or not settings.github_token:
        return
    with SessionLocal() as session:
        pending = session.get(GithubReport, sub_id)
        sub = session.get(Submission, sub_id)
        if pending is None or sub is None or pending.next_attempt > utcnow():
            return
        version = pending.version
    error, comment_id = None, None
    try:
        comment_id = report(sub)
    except Exception as exc:
        error = exc
        _log(f"GitHub report for {sub_id} failed: {type(exc).__name__}; queued for retry")
    with local_lock("results"), SessionLocal() as session:
        pending = session.get(GithubReport, sub_id)
        current = session.get(Submission, sub_id)
        if pending is None or current is None:
            return
        if comment_id is not None:
            detail = current.detail_dict
            detail["github_comment_id"] = comment_id
            current.detail = json.dumps(detail)
        if pending.version == version:
            if error is None:
                session.delete(pending)
            else:
                pending.attempts += 1
                pending.next_attempt = utcnow() + timedelta(seconds=min(3600, 30 * 2 ** min(pending.attempts, 7)))
        session.commit()


def retry_reports() -> None:
    if not settings.contract_repo or not settings.github_token:
        return
    try:
        with local_lock("reports", blocking=False):
            with SessionLocal() as session:
                ids = list(session.scalars(select(GithubReport.submission_id).where(
                    GithubReport.next_attempt <= utcnow()).order_by(GithubReport.next_attempt).limit(20)))
            for sub_id in ids:
                deliver_report(sub_id)
    except BlockingIOError:
        return


def process(sub_id: str) -> None:
    with SessionLocal() as session:
        sub = session.get(Submission, sub_id)
        if sub is None or sub.status != "pending":
            return
        sub.status, sub.started_at = "verifying", utcnow()
        session.commit()
    _log(f"verifying {sub.id} ({sub.track}, {sub.source_repo}@{sub.commit[:10]})")
    try:
        result, log_path = run_pipeline(sub)
    except Exception:
        _log(traceback.format_exc())
        result, log_path = {"status": "failed", "reason": "internal error in the verifier; the operator has the trace"}, None
    with local_lock("results"), SessionLocal() as session:
        sub = session.get(Submission, sub_id)
        if sub is None:
            return
        sub.status = result["status"] if result["status"] in FINAL else "failed"
        if sub.status == "verified":
            sub.sigma, sub.hverify, sub.score = result["sigma"], result["hverify"], result["score"]
        sub.finished_at, sub.duration_s, sub.log_path = utcnow(), result.get("duration_s"), log_path
        failure = None
        if sub.status != "verified":
            msg = result.get("reason") or "; ".join(result.get("errors", [])) or ""
            failure = {"code": sub.status, "message": msg[-2000:]}
        detail = sub.detail_dict
        detail.update(failure=failure, commit=result.get("commit"), comparator_exit=result.get("comparator_exit"),
                      compilation_exit=result.get("compilation_exit"), receipt=result.get("receipt"),
                      claim_version=result.get("claim_version"), hash_meter=result.get("hash_meter"))
        sub.detail = json.dumps(detail)
        promote(session, sub)
        schedule_report(session, sub)
        session.commit()
        _log(f"{sub.id}: {sub.status}" + (f" score {sub.score}" + (" RECORD" if sub.is_record else "")
                                           if sub.status == "verified" else ""))


def work_loop() -> None:
    with SessionLocal() as session:
        for sub in session.scalars(select(Submission).where(Submission.status == "verifying")):
            sub.status = "pending"
        session.commit()
    while True:
        with SessionLocal() as session:
            sub_id = session.scalar(select(Submission.id).where(Submission.status == "pending")
                                    .order_by(Submission.created_at.asc()).limit(1))
        if sub_id:
            process(sub_id)
        else:
            time.sleep(POLL_SECONDS)


def main() -> None:
    if settings.environment == "production" and settings.role != "worker":
        raise SystemExit("the production verifier must run with SIG_ROLE=worker and no GitHub secrets")

    def shutdown(signum, _frame):
        raise SystemExit(128 + signum)

    signal.signal(signal.SIGTERM, shutdown)
    init_db()
    _log(f"repo {settings.repo_root}, state {settings.data_dir}")
    try:
        with local_lock("worker", blocking=False):
            work_loop()
    except BlockingIOError:
        raise SystemExit("another verifier worker already holds this data directory") from None


if __name__ == "__main__":
    main()
