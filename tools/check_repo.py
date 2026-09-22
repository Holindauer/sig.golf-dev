#!/usr/bin/env python3
"""Run local regression checks without network access or changing the running site.

    python3 tools/check_repo.py --formal
    python3 tools/check_repo.py --official --submissions ../sig.golf-submissions

--formal builds the Lean statement and its tests and audits the axiom closures; --official runs
the official pipeline for the track whose root exists in the --submissions checkout. Service tests
run when service/.venv exists (see service/README.md). The Linux sandbox acceptance probes are a
separate command: verifier/check-sandbox.py on the deployment host.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
SKIP_DIRS = {'.git', '.lake', '.tools', '.venv', 'benchmark-results', 'node_modules', '__pycache__'}


def shell_scripts() -> list[Path]:
    found = []
    for path in ROOT.rglob('*.sh'):
        if not SKIP_DIRS & set(path.relative_to(ROOT).parts):
            found.append(path)
    return sorted(found)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--service-python', default=str(ROOT / 'service/.venv/bin/python'),
                        help='Python of the service environment; its tests are skipped when it is absent')
    parser.add_argument('--node', help='Node.js executable for JavaScript syntax checks (otherwise found on PATH)')
    parser.add_argument('--formal', action='store_true', help='build Lean and audit the protected statement')
    parser.add_argument('--official', action='store_true',
                        help='also verify the submission root present in the --submissions checkout')
    parser.add_argument('--submissions', type=Path, help='submissions checkout verified by --official')
    args = parser.parse_args()
    if args.official and not args.submissions:
        parser.error('--official needs --submissions PATH, a checkout of the submissions repository')
    service_python = shutil.which(args.service_python)
    node = shutil.which(args.node or 'node')

    def check(label: str, command: list[str], cwd: Path = ROOT) -> None:
        print(f'\nChecking {label}', flush=True)
        subprocess.run(command, cwd=cwd, check=True)

    skipped = []
    try:
        check('contract pin', [sys.executable, 'verifier/pin_contract.py', 'check'])
        check('verifier regression tests', [sys.executable, '-m', 'unittest', 'discover', '-s', 'verifier/tests', '-v'])
        check('tools and rules-page tests', [sys.executable, '-m', 'unittest', 'discover', '-s', 'tools/tests', '-v'])
        if service_python:
            check('service regression tests', [service_python, '-m', 'unittest', 'discover', '-s', 'tests', '-v'],
                  ROOT / 'service')
        else:
            skipped.append('service tests (no service/.venv; run `cd service && uv sync --frozen`)')
        static = sorted((ROOT / 'service/app/static').glob('*.js')) if (ROOT / 'service/app/static').is_dir() else []
        if node:
            for script in static:
                check(script.name, [node, '--check', str(script)])
        elif static:
            skipped.append('JavaScript syntax (Node.js not found; pass --node)')
        for script in shell_scripts():
            check(str(script.relative_to(ROOT)), ['bash', '-n', str(script)])
        if args.formal or args.official:
            check('Lean statement and tests', ['lake', 'build', 'LeanSphincs', 'LeanSphincsTest'], ROOT / 'formal')
            for audit in ('check-axioms.lean', 'check-ots-axioms.lean', 'check-availability-axioms.lean'):
                check(f'axiom audit {audit}', ['lake', 'env', 'lean', f'scripts/{audit}'], ROOT / 'formal')
        if args.official:
            cfg = json.loads((ROOT / 'challenges.json').read_text())
            source = args.submissions.resolve()
            present = [t for t in cfg['tracks'] if (source / t['submission_root'] / 'Solution.lean').is_file()]
            if not present:
                print(f'No submission roots found in {source}', file=sys.stderr)
                return 1
            for track in present:
                check(f"official pipeline {track['slug']}",
                      [sys.executable, 'verifier/verify.py', track['slug'], '--source', str(source)])
    except (subprocess.CalledProcessError, OSError) as error:
        print(f'Check failed: {error}', file=sys.stderr)
        return 1
    for item in skipped:
        print(f'Skipped: {item}')
    print('\nRequested local checks passed. Browser and Linux deployment acceptance are separate checks.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
