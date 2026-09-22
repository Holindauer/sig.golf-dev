# Tools

Research scripts, the repository regression runner, the submissions-repository preparation script
and the rules-page test. Numerical results are exploration only: every claim requires a Lean proof.

| Script | Purpose |
|---|---|
| `check_repo.py` | repository regression checks |
| `prepare_submissions_repo.py` | create a new, empty submissions repository pinned to this core |
| `ots_experiments.py` | exact integer cost and count experiments for the one-time-signature library |
| `polynomial_annex.py` | arithmetic checks for the polynomial-coding annex ([review](../docs/POLYNOMIAL_CODING_REVIEW.md)) |
| `write-score.py` | legacy declared-metrics calculator; never verification evidence |
| `check-pr19.sh`, `check-pr19.lean` | reproduce the [PR 19 review](../docs/PR19_REVIEW.md)'s 126-bit endpoint and axiom check |
| `tests/` | the research-script regressions and `test_rules_page.py`, which asserts the version marker and load-bearing sentences of `index.html` |

The research scripts import the verifier's meter and scoring modules from `../verifier/`; they
need only the standard library.

```sh
python3 tools/ots_experiments.py --profile rom32-input64 --selection product
python3 tools/polynomial_annex.py
python3 -m unittest discover -s tools/tests -v
```

## Repository checks

```sh
python3 tools/check_repo.py --formal
```

The runner checks the contract pin, the verifier and tools unit tests, the service tests when
`service/.venv` exists, `bash -n` on every shell script and `node --check` on the site's static
JavaScript. `--formal` builds `LeanSphincs` and `LeanSphincsTest` in `formal/` and runs the three
axiom audits in `formal/scripts/`. `--official --submissions PATH` runs the official pipeline for
the root present in that submissions checkout. The runner uses the existing warm Lean and tool
caches; it never installs packages, refreshes demos, pushes or deploys. Linux sandbox acceptance
runs on the deployment host with `verifier/check-sandbox.py`; a pass elsewhere cannot replace it.

## Submissions repository

```sh
python3 tools/prepare_submissions_repo.py .build/sig.golf-submissions
```

Creates a new local repository with no submission roots: the README, agent instructions and PR
template from [`submissions_template/`](submissions_template/), an empty `records.json` and a
`.contract` submodule pinned to this commit. It requires a clean, committed core checkout and a new
destination, and never pushes. See [repository setup](../docs/repositories.md).
