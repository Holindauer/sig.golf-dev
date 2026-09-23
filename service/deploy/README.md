# h2 beta deployment

`sig.golf-dev` and `sig.golf-submissions` run from their `beta` branches. The beta site is static at `/srv/sig-golf/public/site`; the bot polls GitHub PRs and publishes verified snapshots to `sig.golf-submissions/beta`. No server-local submission record is authoritative.

Use separate `sigbot` and `sigverify` accounts. Give `sigbot` read access to a file containing only the GitHub token, and narrowly permit it to run `verifier/verify.py` as `sigverify` through sudo. Both users share `/srv/sig-golf/work`; only `sigbot` writes the public `records.json` and `state.json`. The trusted Lean build cache and dependencies belong to `sigverify`. Run `verifier/setup_tools.sh` or use the exact compatible pinned tools already present on the host. Install `sig-bot.service` as a systemd service.

Import `/srv/sig-golf/app/service/deploy/beta.Caddyfile` from the host Caddyfile. It serves `beta.sig.golf`, routes `/llms.txt`, and permits fetching presentation metadata from GitHub. Keep the `ots.golf` route unchanged. The optional `OTS_SHARED_VERIFY_LOCK` and `SIG_SHARED_VERIFY_LOCK` must name the same lock file to prevent the two verifiers running together on this host.

For a fresh host, clone both beta branches, build the trusted Lean project and verifier tools, copy `site/` to the public root, configure the two service accounts and token, enable the bot service, then enable the Caddy route. The bot rebuilds its local registry from `sig.golf-submissions/beta` on every scan.

Keep two checkouts: `/srv/sig-golf/app` runs the current beta website and bot; `/srv/sig-golf/repo` holds the trusted verifier and Lean build at the revision in `service/deploy/contract-revision`. Set `SIG_TRUSTED_ROOT` as in the unit file. Website and bot releases must not advance the trusted checkout: its commit identifies the rules and filters the leaderboard. On a fresh host, restore that pinned revision from GitHub, then let the bot recover records from the submissions branch.

## Reset submissions

A reset changes the trusted rules revision. Old proofs, attribution, and scores remain in GitHub; only records matching the active revision appear on the site. The bot skips unchanged heads already published under older rules. Authors resubmit with a new commit, which is verified normally.

1. Update the rules, Lean statements, and reference proof on `beta`; build them and push.
2. Set `service/deploy/contract-revision` to that full commit SHA, commit it, and push `beta` again. The application revision and contract revision are deliberately separate.
3. Stop `sig-bot` after its current verification finishes. Fetch `beta` into `/srv/sig-golf/app` and `/srv/sig-golf/repo`; fast-forward the application checkout, and check out the pinned contract in the trusted checkout. Build `SigGolf` as `sigverify` with the existing 24 GiB ceiling. Do not change the OTS checkout or services.
4. Copy the application’s `site/` to the public directory, excluding `records.json` and `state.json`, using `rsync -a --no-owner --no-group --exclude=records.json --exclude=state.json site/ /srv/sig-golf/public/site/`. Keep the public `site` directory owned by `sigbot:sigwork` so it can atomically replace these caches. Restart the bot: it restores all records from GitHub and publishes the active contract in `state.json`, hiding previous submissions.
5. Open a new proof PR from the personal fork to `leanEthereum/sig.golf-submissions:beta`. The bot verifies and publishes it automatically.

No submission database or local archive needs preserving. A replacement host needs the GitHub repositories, the pinned contract, rebuilt Lean/tool caches, and freshly installed service credentials. `records.json` is restored from the submissions branch; source and presentation files are in `verified/<PR-head-SHA>/`; PRs and commit statuses retain the queue and verdict history. The credentials are provisioning secrets, not submission data.
