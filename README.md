# sig.golf

Which stateless hash-based signature should a quantum-resistant Ethereum account use?

[sig.golf](https://sig.golf) is a competition in which every claim is a Lean proof about a pinned
contract: a complete stateless signature scheme, proved strongly unforgeable in the classical pure
random-oracle model, scored by signature bytes times worst-case verification work. This repository,
**sig.golf-dev**, is the core: the protected Lean statement, the isolated verifier and the website.
It holds no accepted scheme; schemes are submitted as pull requests to
[sig.golf-submissions](https://github.com/leanEthereum/sig.golf-submissions).

**Rules:** read them at [leanethereum.github.io/sig.golf-dev](https://leanethereum.github.io/sig.golf-dev/),
the draft rules page (`index.html`) that the live site serves at `/rules`. [AGENTS.md](AGENTS.md)
is the precise specification: exact exports, submission-root rules, limits and the submission
workflow. **Submissions are not open**: admission stays `closed` in [`challenges.json`](challenges.json)
until the launch gates in [docs/SCHEMECLAIM_PLAN.md](docs/SCHEMECLAIM_PLAN.md) are met. The
`sig.golf` domain is pending; until the service is deployed, GitHub Pages serves the rules.

## Tracks

| Track | Folder | Check it with |
|---|---|---|
| Stateless scheme (`full`) | `formal/Submissions/Full/` | `verify.py full` |

The root lives at `formal/Submissions/Full/` in the submissions repository. The current record is
on [sig.golf](https://sig.golf). The submissions repository's `main` carries the current record
root and `records.json`, which links the record to its original checked commit, PR and trusted
core. After publishing a new record's verdict, the bot copies its checked root into `main` with a
separate commit; proof PRs are never merged or closed. Each submission's **Code** link opens its
folder on GitHub at the original checked SHA, independent of later `main` updates.

## Quick start

Build the statement and check a submission root from a submissions checkout next to this one:

```sh
verifier/setup_tools.sh
(cd formal && lake exe cache get && lake build LeanSphincs && lake env lean scripts/check-axioms.lean)
python3 verifier/verify.py full --source ../sig.golf-submissions
```

`verify.py` takes only the track's root from `--source`; the contract and tooling come from this
checkout. A real check needs Linux with Landlock ABI 8 or newer, a user systemd manager and passing
boundary probes; `--insecure-local` is an organizer-only diagnostic and never a fallback. The
verifier's trust boundary and launch gates are in [docs/HARNESS_SECURITY.md](docs/HARNESS_SECURITY.md).

Development checks:

```sh
python3 tools/check_repo.py --formal
(cd formal && lake env lean scripts/check-ots-axioms.lean)
python3 verifier/test-comparator.py
```

For optional local website development, see [service/README.md](service/README.md); the demo
fixtures are opt-in with `SIG_PHONY=1`.

## What the statement pins

- A scheme-parametric, classical **pure-ROM SUF-CMA** claim with no additional cryptographic
  assumptions: `SchemeClaim` in `formal/LeanSphincs/Benchmark/Claim.lean`, claim identifier
  `suf-cma-total-work-pk32-adaptive-availability-v2`.
- Byte-level algorithms: `keygen` returns `(pk, sk)`, `sign` returns `Option Bytes`, `verify`
  consumes bytes. Immutable precomputation may live in `sk`; there is no auxiliary cache or presign
  interface.
- **32-byte public keys**, exact successful signature size, and a worst-case weighted verification
  bound including malformed inputs.
- **Total query work `Q = qH + qS`**: raw hash queries across the whole experiment plus every
  signing request. A fixed explicit exact-rational bound with proved endpoint certificates,
  **124 bits at up to 2^20 requests and 100 bits at up to 2^32**, for the same scheme, parameters
  and bound; no constants-dropping gate.
- Correctness on success, fresh-key fixed-message signing failure at most 2^-128, adaptive
  per-position availability in both budget regimes (lifetime union bound 2^-96 over 2^32
  requests), and structural raw-query and sampling caps on every response path.
- The oracle accepts arbitrary bytes and returns 32 bytes. Meter `rom256-input64-ceil-v1` charges
  `ceil(inputBytes / 64)` per call, including domain tags; the empty input costs zero weighted
  work but one raw security query.

## Remaining gates

Rule R9's latency guarantees (1.5 s signing and 60 s keygen with overrun probability at most 2^-40
per operation, absolute limits of 120 s and 360 s, 64 KiB working RAM) and the executable
resource, storage and side-channel certificates are not bound by the current statement. Receipts
say `ranked: false`; scores are diagnostic; deployment eligibility stays false. Baseline #0 is
intended to be an eligible SPHINCS⁻ variant; its pinned 126-bit proof at 2^24 requests still needs
an extended-lifetime argument at 2^32, serialization, game/cost transport and signing-failure
proofs. Positive comparator fixtures prove metric matching only. The workstream plan and decision
history are in [docs/SCHEMECLAIM_PLAN.md](docs/SCHEMECLAIM_PLAN.md).

## Live service and recovery

Maintainer updates follow commit, push, then deployment; no localhost preview is required.
Production shows real submissions only (`SIG_PHONY=0`). GitHub retains each admitted commit under
`refs/tags/sig-source/<submission-id>` and stores frozen receipt/verdict comments. The server is
disposable: `python -m app.rebuild` restores metadata; retained tags and verdict comments remain the
history authority; the current-record snapshot on submissions `main` can be republished from
checked sources. GitHub retries do not rerun a finished proof. Original logs are disposable. See the
[deployment guide](service/deploy/README.md) for the host requirements, the credentialed rebuild,
source-tag protection and launch checks.

## Repository map

| Path | Contents |
|---|---|
| [`AGENTS.md`](AGENTS.md) | submission specification, served as `/rules.md` |
| [`index.html`](index.html) | the draft rules page, served as `/rules` and published to GitHub Pages |
| [`llms.txt`](llms.txt) | agent guide, served as `/llms.txt` |
| [`challenges.json`](challenges.json) | track metadata, limits, protected files, admission |
| [`formal/LeanSphincs/Benchmark/`](formal/LeanSphincs/Benchmark/) | the contract: [`Oracle.lean`](formal/LeanSphincs/Benchmark/Oracle.lean), [`SchemeInterface.lean`](formal/LeanSphincs/Benchmark/SchemeInterface.lean), [`Game.lean`](formal/LeanSphincs/Benchmark/Game.lean), [`Bound.lean`](formal/LeanSphincs/Benchmark/Bound.lean), [`Availability.lean`](formal/LeanSphincs/Benchmark/Availability.lean), [`Claim.lean`](formal/LeanSphincs/Benchmark/Claim.lean), [`Target.lean`](formal/LeanSphincs/Benchmark/Target.lean) |
| [`formal/LeanSphincs/OTS/`](formal/LeanSphincs/OTS/) | experimental one-time-signature library ([docs/OTS_STAGE1.md](docs/OTS_STAGE1.md)); not a track |
| [`formal/LeanSphincsTest/`](formal/LeanSphincsTest/) | statement regressions and comparator canary fixtures |
| [`verifier/`](verifier/) | [`verify.py`](verifier/verify.py), [`verify_submission.py`](verifier/verify_submission.py), policy checks, contract pin, comparator and profile configs, host tests |
| [`service/`](service/README.md) | website and hosted verifier; [deployment](service/deploy/README.md) |
| [`docs/`](docs/README.md) | implementation contract, harness security profile, plans and reviews, repository setup |
| [`tools/`](tools/README.md) | research scripts, repository checks, submissions-repo preparation |

See [repository setup](docs/repositories.md) for how the core and submissions repositories fit
together.

## Credits

The competition follows [ots.golf](https://ots.golf), which shares its intake, record and
publication model, and draws on [better.codes](https://better.codes)' protected-target harness
and [zk.golf](https://zk.golf)'s specification discussion. It complements
[leanSig](https://eprint.iacr.org/2025/1332) on the consensus layer. Third-party source notices are
in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md). License: Apache 2.0.
