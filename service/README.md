# sig.golf: website, webhook and verification worker

The FastAPI website shows the leaderboard (Spacetime ranking and Pareto frontier), serves the
draft specification as the rules, and accepts pull requests through an authenticated GitHub
webhook. A separate worker verifies each pull request's head commit with
`scripts/verify_pr.py`, which exports only the submission root and runs the isolated verifier
`scripts/verify_submission.py`. The repository defines the contract; the website displays it.

## Local development

```sh
cd service
uv sync --frozen
./run-local.sh          # worker + site on http://localhost:8000, verifier unsandboxed (SIG_INSECURE_LOCAL=1)
```

Queue the checkout's own submission root as a local baseline with
`.venv/bin/python -m app.queue full --baseline`. Tests: `.venv/bin/python -m unittest discover -s tests`.

## How a submission flows

1. A pull request against the contract repository changes exactly one submission root
   (`submissions/full/`). The webhook checks the event signature, then reads author, head and changed
   files from GitHub's API, never from the payload.
2. The web process queues the head commit (admission must be `open` in `challenges.json`; duplicate
   heads, per-user and global queue caps are enforced under a lock).
3. The worker runs `scripts/verify_pr.py full --source <fork> --commit <sha> --json`, accepts only a
   result whose track, commit and metrics are consistent (`score == sigma * hverify`), and stores the
   verdict with the transcript.
4. Verdicts reach the pull request as a commit status and a comment from a durable outbox that
   retries without repeating the proof.
5. A verified head becomes a record only when GitHub confirms that exact head was merged, and only if
   it beats the best spacetime score or extends the Pareto frontier. The service never merges.

## Configuration

| Variable | Default | Purpose |
|---|---|---|
| `SIG_ENV` | `development` | `development` or `production` |
| `SIG_ROLE` | `web` | `web` or `worker` |
| `SIG_REPO_ROOT` | checkout root | trusted contract checkout |
| `SIG_DATA_DIR` | `service/data` | SQLite database, logs and process locks |
| `SIG_WORK_DIR` | `<data>/work` | per-job work directories (a bounded volume in production) |
| `SIG_BASE_URL` | `http://localhost:8000` | public origin used in links and statuses |
| `SIG_CONTRACT_REPO` | empty | `owner/repository` of the public contract repository |
| `SIG_QUEUE_CAP`, `SIG_MAX_INFLIGHT_PER_USER` | 20, 2 | admission limits |
| `SIG_INSECURE_LOCAL` | `0` | development only: run the verifier without its sandbox |
| `GITHUB_WEBHOOK_SECRET`, `GITHUB_TOKEN` | empty | web process only; production refuses them on the worker |

Deployment: [deploy/README.md](deploy/README.md).
