# Proof submissions

Before preparing a scheme, read [the rules](https://leanethereum.github.io/sig.golf-dev/), also
available as [plain text](https://sig.golf/rules.md). Open proof PRs from your fork's branch into
[leanEthereum/sig.golf-submissions](https://github.com/leanEthereum/sig.golf-submissions),
base branch **main**. With GitHub CLI, set the destination explicitly:
`gh pr create --repo leanEthereum/sig.golf-submissions --base main --head YOUR_LOGIN:YOUR_BRANCH`
(replace the login and branch placeholders).

Follow `.contract/AGENTS.md`: it is the precise specification of the track, exports, root rules
and submission workflow. If `.contract` is empty, run `git submodule update --init --recursive`.

| Track | Folder | Check it with |
|---|---|---|
| Stateless scheme | `formal/Submissions/Full/` | `.contract/verifier/verify.py full --source .` |

Run the check from the root of this checkout. Keep proof PR changes inside the admitted root; do
not edit root `records.json` or `.contract`. The root must satisfy the import policy on its own:
`Scheme.lean` imports only `LeanSphincs.Benchmark.Target` and sibling modules as
`LeanSphincs.Submission.<File>`, and `Solution.lean` exports exactly `LeanSphincs.Benchmark.candidate`.
PRs from an older `main` remain eligible; subsequent base-branch record updates are not their changes.
Admission is closed until the core's `challenges.json` says `open`; a PR opened before then is
answered but not queued.

After a new record's verdict is durable, the bot copies only its checked root and registry entry
to `main` in a separate commit. It never merges or closes the proof PR. Protected source tags and
bot receipt/verdict comments remain the authority for the original checked source and result.
The submission page's Code link opens the exact checked folder at its original GitHub SHA.
