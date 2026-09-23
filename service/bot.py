#!/usr/bin/env python3
"""Poll beta PRs, verify frozen heads, then publish before reporting success.

GitHub holds the queue and all verified source snapshots. This process needs no database.
"""
from __future__ import annotations

import argparse
import fcntl
from contextlib import contextmanager
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import time
import uuid
from pathlib import Path

from github import BRANCH, REPO, SHA, Github, GithubError, publish_verified, registry_from_branch, write_local_registry

ROOT = Path(__file__).resolve().parent.parent
POLL_SECONDS = 60


@contextmanager
def shared_verify_slot():
    path = os.environ.get('SIG_SHARED_VERIFY_LOCK')
    if not path:
        yield
        return
    with Path(path).open('a') as handle:
        fcntl.flock(handle, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(handle, fcntl.LOCK_UN)


def open_prs(api: Github) -> list[dict]:
    results = []
    for page in range(1, 11):
        batch = api.get(f'/repos/{REPO}/pulls?state=open&base={BRANCH}&per_page=100&page={page}')
        if not isinstance(batch, list):
            raise GithubError('invalid PR listing')
        results.extend(pr for pr in batch if isinstance(pr, dict) and pr.get('base', {}).get('ref') == BRANCH)
        if len(batch) < 100:
            break
    else:
        raise GithubError('too many open beta PRs for one scan')
    return sorted(results, key=lambda pr: pr.get('created_at', ''))


def checked_status(api: Github, commit: str, context: str, bot_login: str) -> str | None:
    statuses = api.get(f'/repos/{REPO}/commits/{commit}/statuses?per_page=100')
    if not isinstance(statuses, list):
        raise GithubError('invalid commit statuses')
    for status in statuses:
        if (isinstance(status, dict) and status.get('context') == context and
                status.get('creator', {}).get('login', '').lower() == bot_login.lower()):
            return status.get('state')
    return None


def run_verifier(pr: dict, contract: str, work_root: Path, secret_dir: Path) -> dict:
    number = pr['number']
    commit = pr['head']['sha']
    work = work_root / f'{number}-{commit[:12]}-{uuid.uuid4().hex[:8]}'
    cmd = [sys.executable, str(ROOT / 'verifier' / 'verify.py'), '--repository', REPO,
           '--pr', str(number), '--commit', commit, '--trusted', str(ROOT), '--work', str(work),
           '--hide', str(secret_dir), '--cleanup']
    verifier_user = os.environ.get('SIG_VERIFIER_USER')
    if verifier_user:
        if not re.fullmatch(r'[a-z_][a-z0-9_-]*', verifier_user):
            raise ValueError('invalid verifier user')
        cmd = ['sudo', '-n', '-H', '-u', verifier_user, '--', *cmd]
    clean = {key: os.environ[key] for key in ('PATH', 'HOME', 'LANG', 'XDG_RUNTIME_DIR',
              'DBUS_SESSION_BUS_ADDRESS') if key in os.environ}
    proc = subprocess.Popen(cmd, cwd=ROOT, env=clean, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            text=True, start_new_session=True)
    try:
        output, error = proc.communicate(timeout=4 * 3600 + 900)
        if len(output) > 256 * 1024 or len(error) > 256 * 1024:
            raise ValueError('verifier output exceeded its limit')
        value = json.loads(output)
        if not isinstance(value, dict) or value.get('commit') != commit or value.get('contract_commit') != contract:
            raise ValueError('verifier returned the wrong source or contract')
        if value.get('status') == 'verified' and proc.returncode != 0:
            raise ValueError('verifier success had a nonzero exit code')
        return value
    except (subprocess.TimeoutExpired, ValueError, json.JSONDecodeError) as exc:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        proc.communicate()
        return {'status': 'failed', 'reason': f'verifier did not return a valid result: {exc}',
                'commit': commit, 'contract_commit': contract}
    finally:
        shutil.rmtree(work, ignore_errors=True)


def once(api: Github, work_root: Path, local_records: Path, state_file: Path, secret_dir: Path) -> int:
    contract = subprocess.run(['git', '-C', str(ROOT), 'rev-parse', 'HEAD'],
                              check=True, text=True, capture_output=True, timeout=10).stdout.strip()
    if not SHA.fullmatch(contract):
        raise GithubError('invalid contract commit')
    state_file.parent.mkdir(parents=True, exist_ok=True)
    pending = state_file.with_suffix('.tmp')
    pending.write_text(json.dumps({'contract_commit': contract}) + '\n')
    pending.replace(state_file)
    context = 'sig.golf/beta/' + contract[:12]
    me = api.get('/user')
    login = me.get('login') if isinstance(me, dict) else None
    if not isinstance(login, str):
        raise GithubError('cannot identify bot account')
    write_local_registry(local_records, registry_from_branch(api))
    processed = 0
    for pr in open_prs(api):
        commit = pr.get('head', {}).get('sha')
        if not isinstance(commit, str) or not SHA.fullmatch(commit):
            continue
        if checked_status(api, commit, context, login) in {'success', 'failure'}:
            continue
        api.status(commit, 'pending', 'Checking the beta submission', context)
        with shared_verify_slot():
            result = run_verifier(pr, contract, work_root, secret_dir)
        status = result.get('status')
        if status == 'verified':
            try:
                entry, _ = publish_verified(api, pr, result, contract, local_records)
            except GithubError as exc:
                api.status(commit, 'error', 'Verification passed; publication will retry', context)
                print(f'PR #{pr["number"]}: publication pending: {exc}', flush=True)
                continue
            label = 'New record' if entry.get('record') else 'Verified'
            api.status(commit, 'success', f'{label}: score {entry["score"]}', context)
            print(f'PR #{pr["number"]}: {label.lower()} {entry["score"]}', flush=True)
        elif status in {'rejected', 'policy_rejected'}:
            reason = (result.get('errors') or [result.get('reason') or status])[0]
            api.status(commit, 'failure', str(reason).replace('\n', ' ')[:140], context)
            print(f'PR #{pr["number"]}: {status}', flush=True)
        else:
            api.status(commit, 'error', 'Verifier failed; bot will retry', context)
            print(f'PR #{pr["number"]}: infrastructure failure: {str(result.get("reason"))[:200]}', flush=True)
        processed += 1
    return processed


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--token-file', type=Path, required=True)
    parser.add_argument('--work-root', type=Path, required=True)
    parser.add_argument('--records-file', type=Path, required=True)
    parser.add_argument('--state-file', type=Path, required=True)
    parser.add_argument('--once', action='store_true')
    args = parser.parse_args()
    args.work_root.mkdir(parents=True, exist_ok=True)
    lock = args.work_root / 'bot.lock'
    with lock.open('w') as handle:
        try:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise SystemExit('another sig.golf bot owns the queue')
        while True:
            try:
                token = args.token_file.read_text().strip()
                count = once(Github(token), args.work_root, args.records_file, args.state_file, args.token_file.parent)
                print(f'Queue scan complete: {count} checked', flush=True)
            except (GithubError, OSError, subprocess.SubprocessError) as exc:
                print(f'Queue scan failed: {exc}', file=sys.stderr, flush=True)
                if args.once:
                    return 1
            if args.once:
                return 0
            time.sleep(POLL_SECONDS)


if __name__ == '__main__':
    raise SystemExit(main())
