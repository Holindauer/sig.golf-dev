# h2 beta deployment

`sig.golf-dev` and `sig.golf-submissions` run from their `beta` branches. The beta site is static at `/srv/sig-golf/public/site`; the bot polls GitHub PRs and publishes verified snapshots to `sig.golf-submissions/beta`. No server-local submission record is authoritative.

Use separate `sigbot` and `sigverify` accounts. Give `sigbot` read access to a file containing only the GitHub token, and narrowly permit it to run `verifier/verify.py` as `sigverify` through sudo. Both users share `/srv/sig-golf/work`; only `sigbot` writes the public `records.json` and `state.json`. The trusted Lean build cache and dependencies belong to `sigverify`. Run `verifier/setup_tools.sh` or use the exact compatible pinned tools already present on the host. Install `sig-bot.service` as a systemd service.

The site route is `beta.sig.golf` with document root `/srv/sig-golf/public`, `/` redirected to `/site/`, and `file_server`. Keep the `ots.golf` route unchanged. The optional `OTS_SHARED_VERIFY_LOCK` and `SIG_SHARED_VERIFY_LOCK` must name the same lock file to prevent the two verifiers running together on this host.

For a fresh host, clone both beta branches, build the trusted Lean project and verifier tools, copy `site/` to the public root, configure the two service accounts and token, enable the bot service, then enable the Caddy route. The bot rebuilds its local registry from `sig.golf-submissions/beta` on every scan.

Keep two checkouts: `/srv/sig-golf/app` runs the current beta website and bot; `/srv/sig-golf/repo` holds the trusted verifier and Lean build at the revision in `service/deploy/contract-revision`. Set `SIG_TRUSTED_ROOT` as in the unit file. Website and bot releases must not advance the trusted checkout: its commit identifies the rules and filters the leaderboard. On a fresh host, restore that pinned revision from GitHub, then let the bot recover records from the submissions branch.
