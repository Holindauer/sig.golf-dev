#!/usr/bin/env bash
# Start the site and the worker for local development, unsandboxed (organizer diagnostics only).
set -euo pipefail
cd "$(dirname "$0")"
export SIG_INSECURE_LOCAL="${SIG_INSECURE_LOCAL:-1}"
env -u GITHUB_TOKEN -u GITHUB_WEBHOOK_SECRET SIG_ROLE=worker .venv/bin/python -m app.worker &
worker=$!
trap 'kill "$worker" 2>/dev/null || true; wait "$worker" 2>/dev/null || true' EXIT
.venv/bin/uvicorn app.main:app --port "${PORT:-8000}" --reload
