# Website and hosted verifier

A FastAPI website that receives proof pull requests from
[sig.golf-submissions](https://github.com/leanEthereum/sig.golf-submissions) and reports their
results, plus a separate worker that checks each proof against the trusted core checkout with
`verifier/verify.py`. The competition rules are on [sig.golf/rules](https://sig.golf/rules) and,
precisely, in [AGENTS.md](../AGENTS.md); maintainer instructions for the site are in
[AGENTS.md](AGENTS.md).

## Live maintenance

The active workflow is commit, push, then update the production host; no localhost preview or
refresh is required. Follow [deployment and recovery](deploy/README.md) for host checks,
exact-commit updates and rebuilding a disposable server from GitHub. Production web and worker use
`SIG_PHONY=0`.

## Optional local development

```sh
cd service
uv sync --frozen
./run-local.sh
```

Open `http://localhost:8000`. The default `SIG_PHONY=0` shows only real submissions; the board
shows "No record yet" without a verified record. For a requested demo preview, run
`SIG_PHONY=1 ./run-local.sh`. Startup then refreshes the fictional [demo fixtures](demo/README.md),
preserving their IDs and dates; each row carries a demo label, and real submissions are left alone.
`run-local.sh` sets `SIG_INSECURE_LOCAL=1`, so the local worker runs the verifier without its Linux
sandbox; production refuses that flag.

For a deliberately running demo preview, `SIG_PHONY=1 bash refresh-local.sh` updates the fixtures.
The worker does not hot-reload: restart `run-local.sh` after changing worker code. The startup
script removes GitHub credentials from the worker's environment.

**Demo rows.** `seed_demo.py --refresh` updates them, plain `seed_demo.py` reconciles them and
`--remove` deletes them. The script refuses production mode and non-loopback site URLs, even with
`--force`, and normally accepts only the default local database. Never use fictional data in
production.

**Local proof jobs.** After `verifier/setup_tools.sh` and a warm `formal/` build, queue a commit of
a submissions checkout the way the webhook would:

```sh
.venv/bin/python -m app.queue full --repo ../../sig.golf-submissions
```

Local jobs never become records. Only one worker may use a data directory; lock files enforce this
across processes on the same host.

## How it works

- **Pages.** The homepage has one board: the current best score, the score ranking, the Pareto
  frontier of signature bytes against verification work, and the record history. `#score` and
  `#pareto` select the view. `/rules` serves the rules page from the trusted checkout, `/rules.md`
  the submission specification (the root `AGENTS.md` before its maintainer section), `/llms.txt`
  the agent guide and `/notes.md` the journal of checked submissions' `NOTES.md`.
- **Admission.** While `admission` is `closed` in `challenges.json`, proof PRs receive a "not
  queued" comment and nothing is retained. When open, a pull request must change exactly one
  submission root. The service checks the repository, files and full head SHA, creates
  `refs/tags/sig-source/<submission-id>` in the base submissions repository, and publishes a pending
  receipt with frozen attribution and contract identity. The worker cannot start until GitHub
  confirms that receipt. Its serialized metadata is capped at 48 KiB; longer prose belongs in
  `NOTES.md`. Draft PRs are not queued; `ready_for_review` admits the current head.
- **Verification.** The worker runs `verifier/verify.py full --source <repo> --commit <sha> --json`
  with the data directory hidden and the source archive store as the retention target, and accepts
  only a result whose track and commit match the queued head and whose metrics are consistent
  (`score == sigma * hverify`, both positive and within `limits.max_metric`).
- **Records.** A verified head becomes a record when it beats the best score or extends the Pareto
  frontier, decided in verification-finish order under the results lock once its verdict comment is
  durable. Demo rows cannot affect records. After the verdict is durable, the bot commits the best
  score's checked root and its `records.json` entry to submissions `main`, preserving other
  repository files, with `Co-authored-by` trailers for every Git author of the admitted PR
  revision. The bot never merges or closes PRs.
- **Reporting.** The local outbox retries GitHub delivery without repeating a finished proof. A
  result awaiting its comment stays `publishing`; later jobs wait. Record-snapshot commits also
  retry through the outbox.
- **Code.** Submission pages link directly to the submitted GitHub folder at the original checked
  SHA. Exact source ZIPs remain optional artifacts, independently reconstructible from the retained
  commit.
- **Recovery.** GitHub source tags and bot comments are durable state; submissions `main` and
  `records.json` provide the current-record snapshot. SQLite and deterministic source ZIPs are
  rebuildable caches; original logs are disposable. `python -m app.rebuild` restores metadata and
  queued receipts; `--sources` also fetches exact commits. See
  [rebuilding the server](deploy/README.md#rebuilding-the-server-from-nothing).

Whenever the contract or the admission status changes, update the metadata, charts, leaderboard,
rules and documentation together, then check the rendered live pages after deployment.

## Configuration

| Variable | Default | Purpose |
|---|---|---|
| `SIG_ENV` | `development` | `development` or `production` |
| `SIG_ROLE` | `web` | `web` or `worker` |
| `SIG_REPO_ROOT` | checkout root | trusted contract checkout |
| `SIG_DATA_DIR` | `service/data` | SQLite and source ZIP caches, disposable logs and process locks |
| `SIG_WORK_DIR` | `<data>/work` | disposable verification jobs; dedicated bounded mount on Linux |
| `SIG_DATABASE_URL` | `sqlite:///<data>/sig.db` | database connection; deployment uses SQLite |
| `SIG_BASE_URL` | `http://localhost:8000` | site origin, without a path |
| `SIG_CONTRACT_REPO` | `leanEthereum/sig.golf-dev` | core repository; source and specification links |
| `SIG_SUBMISSIONS_REPO` | empty | proof PR repository; set to `leanEthereum/sig.golf-submissions` to configure intake |
| `GITHUB_WEBHOOK_SECRET` | empty | webhook authentication; web process only |
| `GITHUB_TOKEN` | empty | GitHub API access and reporting; web process only |
| `SIG_PHONY` | `0` | show real submissions only; `1` opts into labeled demo rows for local development |
| `SIG_RESYNC_ON_START` | `1` | rebuild missing submissions from GitHub when the website starts |
| `SIG_BOT_LOGIN` | token's login | account whose PR comments carry verdicts |
| `SIG_MAX_INFLIGHT_PER_USER` | `2` | admitting, pending, verifying and publishing jobs per user |
| `SIG_QUEUE_CAP` | `20` | in-flight jobs overall |
| `SIG_INSECURE_LOCAL` | `0` | development only: run the verifier without its sandbox; refused in production |

Production web startup requires HTTPS, two distinct repositories, a token and a webhook secret of
at least 32 characters. Production workers refuse GitHub credentials. Run the web process and the
worker under different Unix identities, sharing only the state group. See
[deployment](deploy/README.md) for storage, isolation, GitHub recovery and launch checks, and
[repository setup](../docs/repositories.md) for the submissions workspace.

## Checks

```sh
uv sync --frozen
.venv/bin/python -m unittest discover -s tests -v
```

Service tests use isolated databases and mock GitHub. They import `verifier/source_archive.py` from
the trusted checkout for the archive format; the verifier's own host tests live in `verifier/tests`.
