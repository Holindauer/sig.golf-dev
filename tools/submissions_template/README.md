# sig.golf submissions

Before preparing a scheme, read [the rules](https://leanethereum.github.io/sig.golf-dev/), also
available as [plain text](https://sig.golf/rules.md). Open proof PRs from your fork's branch into
[leanEthereum/sig.golf-submissions](https://github.com/leanEthereum/sig.golf-submissions),
base branch **main**. With GitHub CLI, set the destination explicitly:
`gh pr create --repo leanEthereum/sig.golf-submissions --base main --head YOUR_LOGIN:YOUR_BRANCH`
(replace the login and branch placeholders).

Proof submissions for [sig.golf](https://sig.golf). A submission is a pull request to this
repository that creates or changes the submission root below. Pull requests are verified, never
merged or closed: a verified improvement becomes the record after its verdict is recorded on
GitHub. The bot then commits only that checked root and its `records.json` entry to `main`,
preserving the other repository files. `main` contains the current record root; the registry links
it to its original checked commit, PR and trusted core. Admission is closed until the core's
`challenges.json` says `open`.

The hosted service retains the admitted commit under `refs/tags/sig-source/<submission-id>` and
freezes attribution in a pending receipt before verification starts. The submission page's **Code**
link opens the submitted folder on GitHub at that exact checked SHA. The statement, verifier and
website are developed in [leanEthereum/sig.golf-dev](https://github.com/leanEthereum/sig.golf-dev).

**Rules:** read them on the [rules page](https://leanethereum.github.io/sig.golf-dev/). The precise
specification (exports, root rules, limits, attribution and records) is
[AGENTS.md](https://github.com/leanEthereum/sig.golf-dev/blob/{{CONTRACT_COMMIT}}/AGENTS.md) in the
pinned core, also available locally as `.contract/AGENTS.md`.

| Track | Folder | Check it with |
|---|---|---|
| Stateless scheme | `formal/Submissions/Full/` | `.contract/verifier/verify.py full --source .` |

Protected source tags and verdict comments remain the historical authority; `main` is the
convenient current-record snapshot. Its publication retries without rerunning the proof. Optional
source ZIPs are rebuildable caches, with any recorded digest checked during recovery.
`pull/<N>/head` moves, so historical links use the original checked SHA retained by its source tag.
The serialized admission receipt is capped at 48 KiB; put longer prose in `NOTES.md`.
Original verification logs are disposable. Before starting, read the
[notes journal](https://sig.golf/notes.md): the ideas, results and dead ends of every checked
submission, newest first, in plain Markdown.

## Check your scheme

Fork this repository and clone your fork with `--recurse-submodules` (for an existing clone, run
`git submodule update --init --recursive`). Install elan, then, from the root of the checkout:

```sh
.contract/verifier/setup_tools.sh
(cd .contract/formal && lake exe cache get && lake build LeanSphincs)
python3 .contract/verifier/verify.py full --source .
```

Change only the submission root; do not edit `records.json` or `.contract` in a proof PR. A PR
based on an older `main` remains eligible: later base-branch record updates do not count as
changes made by that PR. The root must remain self-contained under the import rules: `Scheme.lean`,
`Solution.lean`, `sigma.txt`, `hverify.txt`, `bound.txt`, optional helper modules, optional
`NOTES.md` and `README.md`. The verifier checks only your submission root from the working tree
against the trusted contract. A real check requires Linux with Landlock ABI 8 or newer and a user
systemd manager, as described in the core's
[harness profile](https://github.com/leanEthereum/sig.golf-dev/blob/{{CONTRACT_COMMIT}}/docs/HARNESS_SECURITY.md);
`--insecure-local` is an organizer-only diagnostic.

## Contract pin

`.contract` is a Git submodule of the core repository, pinned to commit `{{CONTRACT_COMMIT}}`
(contract ID `{{CONTRACT_ID}}`). Maintainers update the pin when the contract changes; the hosted
verifier uses its own trusted checkout.

## Local website

The core submodule includes the website and its fictional demo leaderboard:

```sh
cd .contract/service
uv sync --frozen
SIG_PHONY=1 ./run-local.sh        # http://localhost:8000
```

The default `SIG_PHONY=0` shows only real submissions; `1` opts into the demo entries.

## Credits

The competition follows [ots.golf](https://ots.golf) and draws on [better.codes](https://better.codes)
and [zk.golf](https://zk.golf). License: Apache 2.0.
