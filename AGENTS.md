# sig.golf: submission rules

sig.golf is a Lean-kernel-verified competition on stateless hash-based signatures for Ethereum
accounts: the smallest product of signature bytes and worst-case verification work for a scheme
proved strongly unforgeable in the classical, pure random-oracle model. The protected statement
is `formal/LeanSphincs/Benchmark/Claim.lean` (`SchemeClaim`); `challenges.json` lists the
track, limits and protected files; `verifier/` runs the hosted verifier's checks. This file is
the precise specification. [The rules](https://leanethereum.github.io/sig.golf-dev/) present the
design, the eligibility rules R1 to R9 and the cost meters for reading; the live site serves the
same page at [sig.golf/rules](https://sig.golf/rules).

## Before preparing a submission

Read the rules, or fetch this submission specification as
[plain text](https://sig.golf/rules.md). Open proof PRs from your fork's branch into
[leanEthereum/sig.golf-submissions](https://github.com/leanEthereum/sig.golf-submissions),
base branch **main**. The core repository, `leanEthereum/sig.golf-dev`, maintains the statement,
verifier and website. The [agent guide](https://sig.golf/llms.txt) gives the setup and submission
steps. Admission is closed until the track's `admission` field in `challenges.json` says `open`;
the launch gates are in `docs/SCHEMECLAIM_PLAN.md`. Do not flip admission without the organizers.

## Layout

```
formal/                              the Lean project (lake root)
  LeanSphincs/Benchmark/Target.lean  the only protected module a submission imports
  LeanSphincs/Benchmark/Claim.lean   SchemeClaim: the statement a submission proves
  LeanSphincs/Benchmark/             Oracle, SchemeInterface, Game, Bound, Availability
  LeanSphincs/OTS/                   experimental one-time-signature library; not a target
  Submissions/Full/                  the submission root; lives in the submissions repository, never here
verifier/                            verify.py, verify_submission.py, policy checks, contract pin, configs
challenges.json                      the track, limits, protected files
```

Protected files (listed in `challenges.json`, pinned in `verifier/protected.sha256`) come from
the trusted contract. A submission consists of one submission root's contents. The core holds no
accepted scheme; the baseline will be an ordinary submission.

## The track

One track is open for preparation, **Stateless scheme** (`full`, Stage 2): a complete stateless
account-signature scheme against the protected byte-level interface.

- **Scheme syntax.** `keygen` returns `(pk, sk)`, `sign` returns `Option Bytes` and `verify`
  consumes bytes. Messages are 32-byte digests. Immutable precomputation may live in `sk`; there
  is no auxiliary cache or presign interface, and no mutable state.
- **Public key at most 32 bytes**, on every key-generation path.
- **Exact signature size.** Every successful signature has exactly the declared length.
- **Worst-case weighted verification bound**, covering malformed inputs.
- **Strong unforgeability.** A pure-ROM SUF-CMA bound `Adv <= B(qH + qS, qS)` for every
  admissible adversary with up to `2^32` signing requests, with no additional cryptographic
  assumption. `qH` counts raw hash queries across the whole experiment: challenger key
  generation, honest signing, adversarial hashing and final forgery verification. `qS` counts
  every signing request, including failed and repeated ones. Only an exact successful
  message/signature pair is a replay.
- **Two endpoints on the same scheme and bound.** 124 bits at up to `2^20` requests
  (`B(Q, 2^20) <= Q / 2^124` for `1 <= Q <= 2^124`) and 100 bits at up to `2^32`
  (`B(Q, 2^32) <= Q / 2^100`). No reparameterization and no constants dropping.
- **Correctness on success**, and separately a fresh-key, fixed-message signing failure
  probability of at most `2^-128` for every 32-byte message. A `2^-256` certificate also
  qualifies.
- **Adaptive availability.** At every permitted request position, in a shared-ROM interaction
  with adaptive messages, the unconditional probability that the request occurs and returns
  `none` is at most `2^-128`, both for up to `2^20` requests with `Q <= 2^124` and for up to
  `2^32` requests with `Q <= 2^100`. Absent positions are not failures; the lifetime union bound
  over `2^32` positions is `2^-96`.
- **Structural query caps on every response path**, including responses the oracle never
  returns: key generation at most `2^28` raw hash calls and `2^28` uniform samples; each signing
  request at most `2^20` raw hash calls and `2^20` uniform samples, for every secret key and
  message; verification at most `2^16` raw hash calls, including empty ones, and no sampling.
  These values are uncalibrated placeholders mirrored by `verifier/resources.json`.

Signing and key-generation latency (rule R9: 1.5 s and 60 s normal targets with overrun
probability at most `2^-40` per operation, absolute limits of 120 s and 360 s, 64 KiB of working
RAM) are eligibility gates that the current statement does not bind. Until the executable
resource contract exists, every receipt says `ranked: false` and deployment eligibility stays
false; scores are diagnostic.

## Oracle model and cost meter

All parties share one random oracle on byte strings, returning 32 bytes. Equal inputs receive
the same answer across all uses; a scheme may put a domain tag in its input and pays for those
bytes. The security experiment counts raw queries. The scoring meter `rom256-input64-ceil-v1`
charges `ceil(inputBytes / 64)` hash-work units per call, summed over calls; the empty input costs
zero weighted units but one raw query. An abstract unit is neither a compression block nor an
instruction; full-program arithmetic and memory costs belong to a separate execution profile.

## What a submission exports

`Scheme.lean` imports `LeanSphincs.Benchmark.Target` and defines the scheme:

```lean
def LeanSphincs.Submission.scheme : LeanSphincs.Benchmark.SigScheme := ...
```

`Solution.lean` exports exactly one theorem, whose type the verifier renders from your three
metric files and compares against your declaration:

```lean
theorem LeanSphincs.Benchmark.candidate :
    LeanSphincs.Benchmark.SchemeClaim LeanSphincs.Submission.scheme sigmaBytes hVerify coeffs := ...
```

`scheme` is the only comparator hole: any term of the stated type is admissible, and `candidate`
pins it down. The oracle, game, claim fields, budgets, metric arguments and bound semantics must
match the protected statement exactly. Straight-line algorithms discharge the structural caps with
`isQueryBoundP_pure` and the bind lemmas; data-dependent loops need a fixed iteration cap.

The three metric files fix the arguments:

- `sigma.txt`: the exact successful-signature byte length.
- `hverify.txt`: the worst-case verification bound in hash-work units, malformed inputs included.
- `bound.txt`: the coefficients of `B`, a JSON array of 1 to 128 terms
  `[numerator, denominator, a, b, k]`, each denoting `(numerator / denominator) * Q^a * qS^b / 2^k`.
  Fractions are positive and reduced; `a <= 32`, `b <= 64`, `k <= 1024`; terms are unique and
  sorted by `(a, b, k)`. In Lean the denominator uses predecessor encoding, so `[[4,1,1,0,128]]`
  renders as `[⟨4, 0, 1, 0, 128⟩]`. Declaring a bound is not a proof that the scheme satisfies it.

The fixed-cap certificate checks the whole interval from `Q = 1`, including infeasible points
with `Q` below the signing cap; it is conservative and monotone in `qS`. The security theorem
itself must cover the extended request range.

**Score** (smaller is better): the exact integer `sigma * hverify`, in bytes times hash-work
units, with the smaller signature as tie-break. The rule comes only from `verifier/scoring.json`;
no bandwidth coefficient or entrant price file is admitted. Keep both coordinates: the site also
retains the size/verification Pareto frontier.

## Rules for the submission root

1. **Flat.** A single directory containing `Scheme.lean`, `Solution.lean`, `sigma.txt`,
   `hverify.txt`, `bound.txt`, optional additional `.lean` helper modules, and optional
   `NOTES.md` and `README.md`. Lean filenames match `[A-Za-z_][A-Za-z0-9_]*\.lean`; sources are
   UTF-8 without NUL. No build files, compiled artifacts, symlinks, subdirectories or executable
   tools.
2. **Source-header imports.** One ordinary `import Module.Name` per line in the initial import
   block of every submitted `.lean` file. Header imports may name `LeanSphincs.Benchmark.Target`,
   pinned `Mathlib`, `VCVio` and `HashSig` modules, and sibling files of the same root as
   `LeanSphincs.Submission.<File>`. No other `LeanSphincs` module is admitted. Custom elaborators
   and macros, `eval%`, build-time execution and kernel-bypass features are rejected by source
   scanning as defense in depth; compilation runs in the sandbox regardless.
3. **Metrics.** `sigma.txt` and `hverify.txt` each hold one positive ASCII decimal integer at
   most `2^63 - 1`, without leading zeros or whitespace other than an optional final LF.
   `bound.txt` holds the JSON array above. The list length, coefficients and exponents are fixed
   independently of `Q` and `qS`.
4. **Axioms.** The theorem and every algorithm may depend only on `propext`, `Quot.sound` and
   `Classical.choice`. `native_decide` adds `Lean.ofReduceBool` and is refused; so is `sorry`.
5. **Limits.** 1,000 files, 4 MiB per file, 10 MiB per root. Verification: 90 minutes of wall
   clock, 24 GiB of memory, and 4 MiB (4,194,304 bytes) of combined standard output and standard
   error, including compiler and verifier messages. Output beyond this limit is truncated and can
   cause rejection even if the proof is correct. No network; Mathlib and VCVio are prebuilt.
6. **Toolchain.** Exactly `formal/lean-toolchain` and `formal/lake-manifest.json`. Both are
   protected.

## Check locally before submitting

From the root of a submissions checkout, whose `.contract` submodule is this core:

```sh
.contract/verifier/setup_tools.sh                                        # once
(cd .contract/formal && lake exe cache get && lake build LeanSphincs)    # once
python3 .contract/verifier/verify.py full --source .                     # the full pipeline
```

From the core, pass the submissions checkout as `--source`. `setup_tools.sh` requires elan and
installs the pinned comparator, lean4export and landrun; the `lake build` line fetches Mathlib and
builds VCVio and the statement. `verify.py` exports only the track's root from `--source` (or from
an exact `--commit`), captures its bytes once, applies the source policy, and hands that private
copy to `verify_submission.py`. The isolated verifier builds a fresh project holding only the
protected statement and your root, renders the theorem from your metric files, compiles your
modules in a separate constrained systemd service, confirms the whole service has stopped,
snapshots the declared artifacts, and runs the pinned comparator on those read-only bytes with
`--verify-prebuilt`: statement comparison, axiom audit and kernel replay. Filenames, sizes and
hashes are rechecked before the receipt is written.

Linux with Landlock ABI 8 or newer and a user systemd manager is required; passing active
boundary probes (`verifier/check-sandbox.py`) are part of setup. Unsupported hosts fail closed.
`--insecure-local` is an organizer-only diagnostic that runs without the sandbox; its result never
certifies isolation or resource enforcement and is not a substitute for the competition verifier.
Only one verification is admitted per checkout: a `worker_busy` result is retryable and does not
read your candidate. Do not delete `.worker.lock` to bypass admission.

## Submitting

The core repository is `leanEthereum/sig.golf-dev`: statement, verifier and website. Competition
PRs go to `leanEthereum/sig.golf-submissions`. Its `main` holds the current record root under
`formal/Submissions/Full/`, a root `records.json` registry linking the record to its checked
source commit, PR and trusted core, and a `.contract` submodule for local checking. From that
repository, run `python3 .contract/verifier/verify.py full --source .` after following its setup
instructions.

There is one way in: a pull request against the submissions repository that creates or changes
only the admitted submission root. The verifier fetches the head commit, keeps only that root,
verifies it on the trusted core checkout, and answers on the pull request with a commit status and
a comment linking to the submission page. Pushing to the pull request re-queues its new head.
Draft PRs are not queued; marking a PR ready for review submits its current head. A PR opened
from an older `main` remains eligible: later bot updates to `main` do not count as changes made by
that PR. Your PR must still change only the admitted root; do not edit `records.json` or
`.contract` as part of a proof submission.

Attribution comes from the pull request: its author, plus two optional lines in the body (the
template has them):

```
Assisted by: <model or tool>
Co-authors: alice, bob
```

The rest of the body is the public description. Admission freezes that description, author,
co-authors and assistance in a GitHub receipt. The complete serialized receipt is limited to
48 KiB; put longer explanations in the submitted `NOTES.md`.

Write a `NOTES.md` in the root for the next solver, human or agent: the idea, the result, what did
not work and why, and what you would try next. The verifier reads it from the checked head whatever
the verdict, and https://sig.golf/notes.md collects the notes, newest first, as plain Markdown for
agents: the latest checked head of each pull request, at most 20 entries per author, each quoted
as untrusted text. Submissions refused before the proof check (format or infrastructure) are not
listed. Read the journal before starting. Non-record submissions and failed attempts are welcome
for their notes.

Before verification starts, the service retains the exact head in the submissions repository
under `refs/tags/sig-source/<submission-id>` and publishes its pending receipt. Those creation-only
tags and the bot's receipt/verdict comments are the durable record. The submission page's **Code**
link opens the submitted folder on GitHub at its exact original checked SHA. Before compiling, the
verifier also caches the exact root as a deterministic, SHA-256-addressed ZIP; that optional
artifact can be rebuilt from the retained commit and must match any recorded digest. `pull/<N>/head`
moves and is never a historical source reference. Original verifier logs are disposable and are
never recreated by replaying a historical verdict.

A verified improvement becomes the record: a verified head is the track's new record if, when its
verification finishes, its score strictly improves the current record, or the track has none.
Records are decided in the order verifications finish, so a later identical or copied score never
takes a record. A result becomes public as verified only after its verdict comment is durable on
GitHub; later jobs wait while publication retries. Pull requests are never merged or closed by the
verifier; a record identifies its exact retained source commit and checked root. After the verdict
is durable, the bot commits that checked root and its registry entry to submissions `main`,
preserving other repository files; it does not merge the submitter's branch. Each record commit
credits every Git author and `Co-authored-by` trailer from the PR's admitted commits, deduplicated
by email; these identities are frozen in the admission receipt. GitHub publication failures retry
through the outbox without rerunning the proof. Retained source tags and bot comments remain the
authority for historical results; `main` is the convenient current-record snapshot. Submissions
never update the trusted core checkout. See `docs/repositories.md` for workspace preparation and
configuration.

Receipts remain explicitly unranked while the resource certificates of rule R9 are unimplemented:
a verified result is a diagnostic score on the current statement, not deployment eligibility.
Historical receipts under an earlier claim identifier must be rerun, never relabeled.

## Maintaining the website

Humans read the published rules; this section is for the agents and scripts that edit them.

**Publication.** GitHub is canonical (organizer decision, 2026-09-10): `index.html` on `main`
is the single source of the competition rules, published unchanged to GitHub Pages at
https://leanethereum.github.io/sig.golf-dev/ and served by the site at `/rules`. The repository
moved from `nconsigny/leansphincs` to `leanEthereum/leansphincs` on 2026-09-15, was renamed
`leanSphincs` the same day, became `sig.golf` on 2026-09-18 when the website and pull-request
intake landed, and became the core `sig.golf-dev` on 2026-09-22 when proof submissions moved to
`sig.golf-submissions`. GitHub redirects the old repository URLs; the old Pages addresses
`nconsigny.github.io/leansphincs` and `leanethereum.github.io/sig.golf` are not redirected and must
not be cited. The earlier Claude artifact
(https://claude.ai/code/artifact/44cc19cb-44bb-475b-a1c0-e4aad483010a) is a frozen legacy copy at
draft v0.13. Never republish it, never treat it as the current rules, and never wait for it before
pushing to `main`. Do not describe any of this inside `index.html`.

**Editing the rules.**

1. Read the verbatim HTML before replacing text. Plain-text extraction hides inline markup such
   as `<strong>`, `<sub>` and `<span class="tbd">`, and an edit that matches the wrong string
   silently changes nothing.
2. Bump the version marker in the status line and the footer together, and set the status-line
   date.
3. Update `tools/tests/test_rules_page.py` in the same change: it asserts the version and the
   load-bearing sentences of the current rules, and `tools/check_repo.py` runs it.
4. Keep the companion documents consistent: `README.md`, `llms.txt`, `docs/SCHEMECLAIM_PLAN.md`,
   `docs/IMPLEMENTATION.md`, `docs/OTS_STAGE1.md`, `docs/POLYNOMIAL_CODING_REVIEW.md` and
   `tools/submissions_template/`. Record superseded decisions as history rather than deleting
   them.
5. Style: define objects by their structure, permitted operations and exact requirements; keep
   prose direct, precise and concise; no em dashes; no vendor or platform names for the
   infrastructure behind sibling competitions (naming the competitions themselves is fine);
   friendly framing toward leanSig, which is a parallel track on the consensus layer, not a rival.
6. Amber `<span class="tbd">` marks a value or decision still open. Remove the span when the
   decision closes.

Whenever the contract or the admission status changes, update `challenges.json`, the website,
the rules and the documentation in the same change, and regenerate the pin with
`python3 verifier/pin_contract.py pin`. Rules describe requirements without current scores.
READMEs describe their directory and link to this file instead of restating it.

**Checking a change.**

```sh
python3 tools/check_repo.py --formal
```

The runner checks the pin, the verifier, tools and service unit tests, shell and static
JavaScript syntax, and with `--formal` builds `LeanSphincs` and `LeanSphincsTest` and audits the
axiom closures. `lake build` output piped through `tail` hides the exit code; read `PIPESTATUS`.
The maintainer workflow is commit, push and update the live deployment, without starting
localhost; `service/README.md` documents an explicitly requested seeded local preview. Production
launch requires the acceptance checks and launch gates in `service/deploy/README.md` and
`docs/HARNESS_SECURITY.md`.
