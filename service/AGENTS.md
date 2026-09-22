# Live maintenance and optional local development

The maintainer workflow is commit, push, then update the live deployment. No localhost preview or
post-commit refresh is required. Do not start local web or worker processes unless the user requests
local development. Run isolated tests before publishing changes, stop the live worker before
replacing its trusted checkout, and verify the deployed pages after an update. The deployment guide
owns host prerequisites, acceptance checks and recovery.

`SIG_PHONY=0` is the default for both web and worker: show real submissions only. Existing demo rows
keep their IDs and dates but remain hidden and cannot affect records. The board starts without a
record when there is no real verified submission. Reference schemes reach the site as ordinary pull
requests; no baseline score belongs to the contract.

For explicitly requested local development, `./run-local.sh` starts the worker and web process. Set
`SIG_PHONY=1` to opt into the labeled demo fixtures. Preserve fixture IDs and dates when refreshing.
`seed_demo.py` refuses production mode and non-loopback site URLs, even with `--force`; never force
it against production. `demo/README.md` owns the fixture policy. Keep fixtures, metadata, admission
status, charts, leaderboard and rules aligned.

GitHub holds durable source tags `refs/tags/sig-source/<submission-id>` and the bot's frozen
receipt/verdict comments. After a new best score's verdict is durable, the bot commits only its
checked root and the corresponding `records.json` entry to submissions `main`. Preserve other
repository files. This is a current-record snapshot, never a PR merge; source tags and comments
remain the historical authority. Record commits include `Co-authored-by` trailers for every Git
author and co-author of the admitted PR commits. Freeze the deduplicated identities in the GitHub
admission receipt and preserve them during recovery; never substitute the authors of a newer head
when publishing an older checked revision. Keep snapshot publication retryable through the outbox
without rerunning verification. Older-base PRs remain eligible when they change only their own
admitted root. The server needs no backups: the database and exact source ZIPs are rebuildable
caches; original logs are disposable. Preserve the admission and verdict publication gates,
reporting retries, immutable source identity and digest checks. `python -m app.rebuild` restores
metadata; `--sources` also reconstructs ZIPs, without compiling historical submissions. The primary
Code link opens the submitted folder on GitHub at its original checked SHA. Do not replace it with a
moving `main` link. Never create replacement logs by rerunning an already published verdict. See
`deploy/README.md`.

One track, `full`, is admitted through `challenges.json`. Derive everything from that metadata:
the submission root, the required files, the limits and the admission status. While `admission`
is `closed`, proof PRs receive a "not queued" comment and nothing is retained or queued; never flip
it without the organizers. The record rule is the specification's: a verified head becomes a
record when it beats the best score (`sigma * hverify`, exact integer, smaller signature breaks
ties) or extends the Pareto frontier of signature bytes against verification work. Only the best
score is copied to submissions `main`; frontier records stay on the board and in the chart. Scores
can exceed 64 bits: compare them in Python, never in SQL.

Keep `llms.txt`, `rules.md` and the GitHub links in the footer. The rules and the exact proof PR
destination remain at the top of `/llms.txt` and in the homepage's submission steps. `/rules` serves
the repository-root `index.html` unchanged; `/rules.md` serves the submission specification from the
root `AGENTS.md`, ending before its "Maintaining the website" section. Keep that boundary and its
regression check aligned; do not duplicate the specification in a second hand-maintained file.

Keep the rules concise and independent of current scores, candidate results and proof history.
Keep the homepage concise: the objective, the admission status, the current record and the two
board views; detailed requirements belong in the rules. Demo rows are clearly marked and never
receive verified badges or fabricated commit links. Style: no em dashes in prose; do not name
vendors or platforms behind sibling competitions (naming the competitions themselves is fine).

After deploying worker code, restart the live worker as well as the web service. Keep one worker per
data directory. Production web and worker run as different Unix users; only the web process receives
GitHub credentials. The bot creates retention tags, writes receipt/verdict comments and commit
statuses, and commits new record snapshots to submissions `main`. It never merges or closes pull
requests or changes an existing source tag. The bot's authorized `main` ruleset bypass must not
grant bypass of source-tag update/deletion protection. Draft PRs are not admitted, including during
startup resync. The `ready_for_review` webhook admits the current head through the same checks as a
new PR. A verified improvement becomes public only after the verdict comment is durable, with record
ordering determined by verification-finish time under the results lock. Never bypass Linux isolation
or bounded-storage checks to make a host pass. See `deploy/README.md` for the launch gates.

Ask the user before making substantial visible website changes. Permission to improve documentation
or agent discovery does not authorize changing navigation or the visible page layout. Explicitly
requested feature previews stay local and uncommitted until the user validates them.
