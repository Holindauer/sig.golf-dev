# Deploying the sig.golf verifier and website

One x86_64 Linux host running Ubuntu 24.04 with at least 8 cores and 32 GB RAM. The layout, the
two Unix identities and the bounded job volume follow the ots.golf deployment: the web process
holds the GitHub credentials and never compiles anything; the worker compiles untrusted code and
never sees a credential.

## Install and configure

1. As root:

   ```sh
   SIG_REPO_URL=https://github.com/leanEthereum/leanSphincs SIG_DOMAIN=sig.golf bash service/deploy/setup-server.sh
   ```

   It installs the tools, clones the contract repository, builds the comparator at its pinned
   revision (`setup.sh`), warms the trusted Lean build, and installs Caddy and the two systemd
   units, left stopped.

2. Put a fine-grained repository token in `/etc/sig/secrets.env` (commit statuses and pull
   requests: read and write; no contents write). The file already holds a generated webhook secret.
   Keep it `root:root 0600`. Only `sig-web` receives this file.

3. Provision a dedicated ext4 or xfs volume at `/srv/sig-work` (at most 64 GiB), persist it in
   `/etc/fstab`, and give its root to `sig:sig-state` with mode `2770`. Job copies and temporary
   clones live there and nowhere else, so a submission that fills the disk cannot touch the
   database, the logs or the trusted checkout.

4. Register the webhook on the contract repository: payload URL `https://<domain>/webhooks/github`,
   content type `application/json`, the secret from `secrets.env`, event `Pull requests` only.

5. Validate and start:

   ```sh
   systemd-analyze verify /etc/systemd/system/sig-web.service /etc/systemd/system/sig-worker.service
   caddy validate --config /etc/caddy/Caddyfile
   systemctl start caddy sig-web sig-worker
   ```

## Acceptance checks before opening admission

- `sudo -u sig bash -c 'cd /srv/sig/repo && python3 scripts/test-sandbox-lifecycle.py && python3 scripts/test-sandbox-comparator.py'`
  passes on the host: Landlock, systemd transient services and the memory and time caps hold.
- Queue the organizer baseline with `.venv/bin/python -m app.queue full --baseline` and confirm the
  worker reaches a verdict, writes a receipt under `benchmark-results/runs/` and the site shows it.
- A pull request touching a file outside `submissions/full/` receives the "not queued" comment.
- A full work volume fails a job while the website and database keep working.
- Flip `admission` to `open` in `challenges.json` only after the launch gates in
  `SCHEMECLAIM_PLAN.md` are met; the webhook refuses submissions until then.

## Operations

- Logs: `journalctl -u sig-web -u sig-worker`; verifier transcripts under `/srv/sig/data/logs/`.
- Update the contract: pull `main` in `/srv/sig/repo`, rebuild `lake build LeanSphincs`, restart both units.
  The worker verifies against the checkout it runs from; a moved `main` is a new trusted commit.
- Never run the worker as `sig-web`, never give `sig` the secrets file, never run either as root.
