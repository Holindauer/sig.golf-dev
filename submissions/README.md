# Submission roots

Each track in `challenges.json` names a directory under `submissions/`. The directory holds the
current record for that track; a pull request that changes exactly that directory, and nothing
else, is a submission. The hosted verifier fetches the pull request's head commit, keeps only that
directory, and answers on the pull request as a commit status and a comment.

| Track | Root | Contents |
|---|---|---|
| `full` | `submissions/full/` | `Scheme.lean`, `Solution.lean`, `sigma.txt`, `hverify.txt`, `bound.txt`, optional flat `Helper.lean` modules |

There is no accepted baseline yet, so `submissions/full/` does not exist on `main`: the first
merged submission creates it. See [SUBMISSION.md](../SUBMISSION.md) for the exact contract.
