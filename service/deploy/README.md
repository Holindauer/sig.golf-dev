# Deploying the verifier and website

The operational guide for a production host: installation, the Linux acceptance checks, the gates
before public launch, and day-to-day operations. For local development see the
[service README](../README.md). The verifier's trust boundary and the remaining launch work are in
[docs/HARNESS_SECURITY.md](../../docs/HARNESS_SECURITY.md).

## Requirements

- **Host.** One x86_64 Linux host running Ubuntu 26.04, with at least 8 cores and 32 GB RAM, space
  for the trusted warm Lean build, and **systemd 257 or newer**. The verifier's pinned Linux
  profile requires **Landlock ABI 8 or newer**, a user systemd manager with cgroup limits and seccomp
  filtering (kept alive with `loginctl enable-linger`), and Go to build the pinned landrun. Ubuntu
  24.04's standard kernel and systemd do not meet these requirements. The worker and all web
  processes share one data directory; workers on separate hosts are not supported. Use the locked
  Python dependencies.
- **GitHub.** The public submissions repository retains source commits and the bot's receipt and
  verdict comments. The server is disposable; database and source ZIPs are rebuildable caches, and
  original verification logs are disposable. Source fetching uses public HTTPS without a token.
- **Bounded job storage.** Untrusted work needs a **dedicated filesystem of at most 64 GiB**,
  separate from the operating system, trusted checkout, warm Lean cache, account homes and
  persistent website data. Memory and time limits do not prevent a submission from filling a disk.
- **Linux acceptance.** A proof check on a development machine is not a production sandbox test.
  Complete the [acceptance checks](#linux-acceptance-checks) on the actual host before connecting
  the public webhook. The installer deliberately leaves the services stopped.

## Install and configure

1. As root, run:

   ```sh
   SIG_REPO_URL=https://github.com/leanEthereum/sig.golf-dev \
     SIG_SUBMISSIONS_REPO=leanEthereum/sig.golf-submissions \
     SIG_DOMAIN=sig.golf bash service/deploy/setup-server.sh
   ```

   The script installs the tools, warms the trusted Lean project, and installs Caddy and the two
   systemd units. Review the downloaded elan, uv, Go and Caddy installers as part of host
   provisioning; this bootstrap is not a hermetic operating-system image. The repository pins the
   proof tool commits and the Python dependency lockfile.

2. Add a fine-grained token for a dedicated bot account to `/etc/sig/secrets.env`, scoped to
   `leanEthereum/sig.golf-submissions` only. Grant commit statuses read/write, pull requests
   read/write for the receipt/verdict comments, and **Contents read/write** to create source
   retention tags and commit current record snapshots to submissions `main`. Metadata read-only is
   implied. The bot never merges or closes PRs and never updates a source tag; it creates
   `refs/tags/sig-source/<submission-id>` pointing at the exact admitted commit before verification
   can start. No core-repository write access is needed.

   Configure repository rulesets for `sig-source/**`: allow tag creation by the bot, and prohibit
   tag updates and deletion. Use separate creation and update/deletion rules so the bot's creation
   bypass does not also permit mutation or deletion. Protect `main` from unauthorized updates,
   force pushes and deletion, but explicitly authorize the publishing bot through the
   branch-update ruleset bypass needed for record commits. Scope that bypass to `main`; it must not
   apply to source tags. The bot publishes a fast-forward commit containing only the checked record
   root and its `records.json` update, preserving every unrelated path. Retain the bot's PR comments
   as the durable result history.

   Keep `/etc/sig/secrets.env` `root:root 0600`; the installer generates its webhook secret. Do not
   put credentials in `/etc/sig/public.env`, the checkout, Git configuration, the `sig` account's
   home or the verifier environment. A replacement server gets a reissued token for the same bot
   account and a freshly configured webhook secret; no server backup is required.

   `sig-web` owns the website and GitHub reporting; only that service receives `secrets.env`. The
   verifier runs as the different Unix user `sig`, with public settings only. Both use the
   `sig-state` group for the SQLite database, logs and lock files. The data directory is setgid and
   the services use `UMask=0007`. Production worker startup refuses GitHub credentials and the
   `SIG_INSECURE_LOCAL` flag. Do not run both services as the same user.

   Ubuntu restricts unprivileged user namespaces, which the per-user systemd manager needs for each
   job's private namespaces. The installer loads `/etc/apparmor.d/sig-systemd-executor`, an
   **unconfined** profile granting `userns` to `systemd-executor` and inherited by its children. It
   is not the candidate sandbox: the boundary is Landlock plus the verifier's checked systemd
   restrictions (`verifier/sandbox_profile.py`). Run the probe on the deployed host.

3. Job storage at `/srv/sig-work`, at most 64 GiB. The installer creates it: a fully allocated
   48 GiB image, `/var/lib/sig-work.img`, mounted through `/etc/fstab` at every boot, root owned by
   `sig:sig-state` with mode `2770`, with `nodiscard,X-fstrim.notrim` so scheduled `fstrim` never
   punches holes into the backing image. A dedicated block volume also works. Do not put the
   database, logs, trusted checkout or warm cache on it. `SIG_WORK_DIR=/srv/sig-work` and
   `TMPDIR=/srv/sig-work` in `public.env` put job directories and temporary Git clones on the
   bounded volume. Confirm that a full work volume fails a job while the website and database
   continue to work.

4. Inspect the installed units and validate Caddy:

   ```sh
   systemd-analyze verify /etc/systemd/system/sig-web.service /etc/systemd/system/sig-worker.service
   caddy validate --config /etc/caddy/Caddyfile
   ```

   The units set `SIG_ENV=production` and their respective `SIG_ROLE=web|worker`. Production web
   startup requires an HTTPS origin, two distinct repositories, a token and a webhook secret of at
   least 32 characters. The data/work paths, SQLite URL, domain, `SIG_CONTRACT_REPO` and
   `SIG_SUBMISSIONS_REPO` are in `/etc/sig/public.env`. New installations set `SIG_PHONY=0` for both
   services; existing environment files are preserved.

## Linux acceptance checks

Run these with the public webhook disconnected and the production configuration in place:

1. As the verifier user, run the sandbox probes and the harness tests, then verify a reference root
   from a submissions checkout: `/srv/sig/submissions-check` is a separate checkout of a submissions
   repository holding the track's reference root (before launch, the maintainer's fork), never the
   trusted checkout.

   ```sh
   sudo -u sig -H bash -c 'set -a; . /etc/sig/public.env; set +a
     export PATH="$HOME/.elan/bin:/usr/local/go/bin:/usr/local/bin:/usr/bin:/bin"
     cd /srv/sig/repo
     python3 verifier/check-sandbox.py &&
     python3 verifier/test-sandbox-lifecycle.py &&
     python3 verifier/test-sandbox-comparator.py &&
     python3 verifier/test-verifier.py &&
     python3 verifier/verify.py full --source /srv/sig/submissions-check'
   ```

   The probes must pass the filesystem, network, process and signal denial checks of the pinned
   profile: Landlock ABI 8 or newer, denied TCP, UDP, IPv6 and Unix sockets, protected and
   dependency writes refused, and complete cgroup cleanup after a stop. Never remove a check to make
   a host pass. Also exercise the contract's memory limit and a timed-out test submission, and
   confirm the entire transient service and process group terminate.

2. Start the services, still without a public webhook:

   ```sh
   systemctl start sig-web sig-worker caddy
   curl --fail https://sig.golf/healthz
   ```

   Check the journal and confirm different process owners. From `sig`, a read of
   `/proc/<sig-web-pid>/environ` must fail. Inspect the worker environment as root without printing
   secret values and confirm that neither GitHub credential variable is set. Test the site on narrow
   and desktop screens, keyboard navigation and both light and dark schemes.

3. Confirm `SIG_PHONY=0` for both services. The board shows "No record yet" until a real verified
   record exists; there are no invented production records or reference baselines. Existing demo
   rows remain stored but hidden and cannot participate in record decisions.

4. In a staging repository, exercise a signed PR webhook, duplicate delivery, a rejected proof, a
   verified improvement, a second PR with the same metrics (verified, not a record), a Pareto
   frontier extension, and a GitHub API outage followed by recovery. Confirm that the bot never
   merges or closes a PR. Stop and restart the worker during a job; it must requeue the interrupted
   job and refuse a concurrent worker. Confirm a retained source tag and frozen pending receipt exist
   before compilation, and that a result remains `publishing` until GitHub confirms its verdict
   comment. Confirm the best score reaches `main` as the exact checked root with a matching
   `records.json` entry, preserving other repository files. Test snapshot publication retry after an
   API failure. Also force-push or close the staging PR, reconstruct its old pending receipt and
   exact source with `app.rebuild --sources`, and compare the recovered archive digest.

5. On `leanEthereum/sig.golf-submissions`, connect GitHub's **Pull requests** webhook to
   `https://<domain>/webhooks/github`, with JSON content and the configured secret. Only `opened`,
   `synchronize`, `reopened` and `ready_for_review` events are used; closing or merging a PR changes
   nothing. The service ignores other repositories and refuses admission when
   `SIG_SUBMISSIONS_REPO` is missing. Core-repository PRs are not proof submissions.

6. Flip `admission` to `open` in `challenges.json` only when the launch gates in
   `docs/SCHEMECLAIM_PLAN.md` are met. While it is `closed`, the webhook answers proof PRs with a
   "not queued" comment and nothing enters the queue.

## Gates before public launch

A successful local proof check establishes none of the following; each must pass on the intended host:

1. The isolation probes and the reference proof from a submissions checkout, run under the deployed
   identities, including memory exhaustion, timeout and a full work volume, with complete process
   cleanup, the website and database still available, and refusal when isolation is unavailable.
2. Web credentials unreadable to the verifier identity, effective systemd restrictions, HTTPS/proxy
   configuration, protected source tags and a successful fresh-directory rebuild from GitHub
   receipts/verdicts and exact commits, with matching source ZIP digests.
3. The staging GitHub flow of acceptance check 4. The local tests mock GitHub and cannot replace it.
4. The remaining verifier launch work in `docs/HARNESS_SECURITY.md` and the gates in
   `docs/SCHEMECLAIM_PLAN.md`.

The host bootstrap downloads system tooling and is not a reproducible operating-system image. This
is a single-host deployment; the process locks are not a distributed queue protocol.

## Operations, upgrades and recovery

### Monitoring

`/healthz` checks the web process and database connection; it is not a certificate or worker-health
signal. Monitor `journalctl -u sig-web -u sig-worker`, queue age, free disk space, verification
failures and the `github_reports` outbox. Admission stays `admitting` until its pending receipt
comment is durable. A completed check stays `publishing`, outside public verified results and record
promotion, until its verdict comment is durable; later jobs wait behind that publication. Failed
reports retry with backoff up to an hour. A confirmed comment suffices even if its supplementary
commit-status update must retry. Record-snapshot publication uses the outbox too: after the verdict
is durable, the bot copies the best score's checked root into submissions `main` and updates
`records.json`. A GitHub failure retries publication without rerunning the proof. Retained source
tags and verdict comments remain authoritative while a current-record snapshot is delayed.

### Worker

The worker holds a process lock for the shared data directory. At startup it requeues interrupted
`verifying` jobs, then processes one job at a time. Outer pipeline timeouts retain their logs and
terminate the verifier process group; the verifier also stops its transient systemd service and
confirms the cgroup is empty. SIGTERM unwinds worker cleanup and exits 143, which the worker unit
treats as a successful stop. Keep one trusted checkout per worker and update it only while that
worker is stopped.

### Rebuilding the server from nothing

GitHub is the durable competition store; no server backups are required. For each hosted
submission, a creation-only `refs/tags/sig-source/<submission-id>` tag retains its exact commit in
the submissions repository. A bot comment freezes its author ID/login/avatar, admission time,
description, co-authors, assistance, submission root and trusted contract commit. The serialized
receipt is capped at 48 KiB; long prose belongs in the submitted `NOTES.md`. The terminal comment
adds the verdict, metrics, finish time, record flag, archive descriptor and bounded failure summary.
Do not delete the retention tags or bot comments. `refs/pull/<N>/head` moves and is never used to
reconstruct an old revision. The record root and `records.json` on submissions `main` are a
published snapshot of the best score, not the source of historical verdicts.

The verifier retains a deterministic, uncompressed source ZIP under `SIG_DATA_DIR/sources/` before
running candidate code. ZIPs and their sidecars are local caches. The primary **Code** link opens
the submitted folder on GitHub at its exact original checked SHA, so browsing checked code does not
depend on the ZIP cache. Recovery fetches the full exact commit from the base submissions repository
with a credential-free bounded exporter, recreates the historical manifest and requires the original
digest when recorded. It never compiles a historical proof to recover its source. Missing original
logs remain unavailable; they are not recreated by rechecking a completed proof.

On a new host, install the trusted core and dependencies, recreate `/etc/sig/public.env`, provision
a token for the existing bot account and a new webhook secret, and repeat the Linux acceptance
checks. Keep web and worker stopped while rebuilding. Run this as root so systemd reads the protected
secret file and starts the command as `sig-web`; the verifier user never receives those credentials:

```sh
systemctl stop sig-web sig-worker
systemd-run --quiet --wait --pipe --collect --unit=sig-rebuild \
  --uid=sig-web --gid=sig-state \
  --property=WorkingDirectory=/srv/sig/repo/service --property=UMask=0007 \
  --property=EnvironmentFile=/etc/sig/public.env \
  --property=EnvironmentFile=/etc/sig/secrets.env \
  --setenv=SIG_ENV=production --setenv=SIG_ROLE=web --setenv=SIG_REPO_ROOT=/srv/sig/repo \
  /srv/sig/repo/service/.venv/bin/python -m app.rebuild --sources
```

Inspect the JSON counts and errors; a partial failure exits nonzero. Once metadata recovery and host
checks pass, run `systemctl start sig-web sig-worker`. Missing optional source caches stay
unavailable and can be retried separately.

A failed or interrupted metadata restore leaves `SIG_DATA_DIR/recovery.incomplete`. While it exists,
new verification and result publication remain paused, including after a restart. Resolve the API
or receipt error and rerun `app.rebuild` or `app.resync`; only successful metadata recovery clears
this marker. Never delete it to bypass incomplete record history.

For metadata only, omit `--sources`. `--sources --limit N` bounds attempts to recover missing caches.
`--queue-open-heads` additionally admits current open PR heads that have no durable receipt. Default
rebuild already restores durable pending receipts even if their PR was closed or force-pushed. It
initializes a missing database and does not wipe an existing one. Records are reconstructed in
verification-finish order within the current contract; frozen attribution takes precedence over
subsequently edited PR text.

Ordinary startup runs metadata resync; `SIG_RESYNC_ON_START=0` disables it. Startup and page
requests do not fetch source ZIPs. Missing caches are fetched only by the explicit `--sources`
command. GitHub API pagination is bounded; a reported listing limit or API error must be resolved
before calling a rebuild complete.

### Updating the live deployment

The maintainer workflow is **commit, push, then update the host**. Stop the worker before changing
`/srv/sig/repo`, fetch the published core commit, check out that exact commit, synchronize the
locked dependencies, rebuild the trusted Lean project when the contract changed (`lake build
LeanSphincs` in `formal/`), run `python3 verifier/pin_contract.py check`, install changed units and
run `systemctl daemon-reload` when needed. Keep `/etc/sig/public.env` at `SIG_PHONY=0`. Restart web
and worker after the update, confirm `/healthz` responds, check `/rules` and `/rules.md` for the
deployed commit, inspect the board and the service journal, and repeat the actual-host isolation and
reference checks whenever the verifier or sandbox changes. A moved `main` is a new trusted commit and
a new contract fingerprint when a protected file changed; queued jobs from the previous fingerprint
fail closed and must be resubmitted.

### Webhook delivery

Webhook events can be duplicated or missed. GitHub does not automatically retry failed deliveries:
use its delivery history to redeliver a lost push event, or restart the website, whose resync queues
open heads without a verdict. Records are decided when verification finishes, never by webhook
events, and the service never updates the trusted checkout.
