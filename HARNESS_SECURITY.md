# Verifier trust boundary and launch gates

Status: staged engineering profile, 2026-09-07. Not an external security audit,
registered verifier, open leaderboard or accepted baseline.

## Submission path

`bash benchmark.sh /path/to/submission` captures a flat folder, validates the
captured bytes, prepares a private Lake project, compiles its protected challenge,
audits the protected axioms, then runs the real comparator in the Linux profile.
The runner compiles candidate modules in a separate service and freezes their artifacts.
The prebuilt comparator rechecks them with `leanchecker`, exports
their statements, compares against the rendered claim and checks axiom closure.

Each run retains `source/`, `project/`, `verification/`, logs and `result.json` in a distinct
mode-0700 directory under `benchmark-results/runs/`. The receipt binds filenames,
source bytes, all three metrics, harness sources, dependency Git pins, tool-binary
hashes and log hashes. A score is emitted only when the organizer profile has
a calibrated price, after successful comparison and post-run source/harness,
dependency-pin/cleanliness and tool-binary integrity checks. Lake is included alongside Lean, leanchecker, exporter, comparator and
(in the strict profile) Landrun in the recorded/rechecked tool hashes.
Every receipt says `ranked: false`.

Historical draft v0.17 used claim identifier `suf-cma-total-work-pk32-decay-v1`,
which cannot certify the current adaptive claim.
Organizer-owned `benchmark/scoring.json` belongs to the protected harness
manifest. Its current null price issues no scalar score, including on a local
accepted result; a configured exact rational price would give c*sigma+hverify.
No entrant-supplied price is admitted. Price calibration and complete-program
resource gates are still launch work. Recheck old receipts under the revised
total-work, 32-byte-key, same-scheme decay claim rather than relabeling them.

Receipts are written to a private temporary file, flushed and atomically renamed
to `result.json`. A failed write does not publish a partial JSON receipt. A hard
kill may leave a temporary file or no receipt; consumers must require a complete
`result.json`. This is not a power-loss durability guarantee or authentication.
The integrity checks detect persistent drift between checks, not changes restored
in between; authenticated dependency build artifacts remain a launch requirement.

The statuses are `worker_busy`, `source_rejected`, `infrastructure_error`, `verification_failed`,
`interrupted` and `accepted`. `verification_failed` can include a compiler/tool error, not just
a false theorem; consult its log. Rejections never emit a score. Receipts are local
evidence, not signed attestations or authority to award/promote a submission.

## Admission and operator responsibilities

The `verify()` entry point (including `benchmark.sh` and insecure diagnostics)
holds a nonblocking kernel file lock at `benchmark-results/runs/.worker.lock`
before capture and through receipt publication. A concurrent invocation returns
a `worker_busy` receipt with `retryable: true`, no captured submission and no
score. It exits nonzero; a trusted caller may retry with backoff. This is not
a theorem rejection and does not require changing the candidate.

The lock is per checkout and cooperative, not a host-wide resource quota or a
durable queue. Organizer-only comparator canaries do not use this entry point.
Do not delete or replace the lock file: its persistent inode is intentional;
the kernel releases ownership when the owning process closes it or dies. Its
descriptor is not inherited by executed children. A hard-killed owner may still
leave a detached systemd service running until its runtime cap. Operators must
stop/verify orphaned services before reusing a worker after such a failure.

Use one disposable worker checkout per provisioned resource allocation, with an
external scheduler preventing overlapping jobs. Put results on a quota-limited
volume and bound queue ingress/retention before accepting public submissions.
Busy receipts themselves use disk, so admission locking is not a disk-exhaustion
defense. No automatic artifact deletion is implemented. A signed receipt service,
aggregate disk quota and crash-surviving worker lifecycle remain launch gates.

## Filesystem and cache isolation

- Directory-relative `O_NOFOLLOW` opens capture inputs once. FIFOs, symlinks,
  nested directories, non-UTF-8/NUL source and ambiguous Lean filenames are rejected.
  The accepted bytes need not describe a simultaneous state of a changing live
  directory: those captured bytes themselves define the submitted artifact.
- Each run has independent generated source and candidate build outputs. No prior
  candidate `.olean` is copied. There is no shared generated `Challenge.lean`.
- Pinned dependency caches are read-only to candidate processes. Protected source,
  configuration and compiled modules are also read-only. Only the two candidate
  output directories under `.lake/build/{lib/lean,ir}/LeanSphincs/Submission` are
  writable, plus `/dev/null`. Candidate-generated files cannot be executed.
- The inherited comparator's filesystem-wide reads and `.lake` write grant are
  replaced by `strict-landrun.py`; incoming permission flags are not forwarded.
  User home, Git credentials and arbitrary project siblings are not read grants.
- Trusted challenge preparation runs before candidate compilation and imports only
  protected modules. It can use organizer dependency caches. The source parser is
  a defense-in-depth policy, not the operating-system security boundary.

## Linux profile: mandatory, actively checked

The profile requires Linux x86-64 or AArch64, Landlock ABI **at least 8**, a user
systemd manager with cgroup limits and seccomp filtering, and the setup-pinned
Landrun/comparator/toolchain. It never falls back automatically to no sandbox.

Pinned [Landrun source](https://github.com/Zouuup/landrun/tree/811cfff51ceaf3d9843708aa6d22e9b84ccac8b4)
targets ABI 9. We explicitly allow ABI 8 compatibility with its `--best-effort`
option only after enforcing the ABI floor. The missing pathname Unix-socket
restriction is covered by systemd's mandatory denial of the entire `@network-io`
system-call group. TCP, UDP and Unix sockets are all probed for denial. This is
an explicit composite profile, not a claim that ABI 8 supplies ABI 9 features.

Limits: 24 GiB memory, no swap, 256 tasks, 80 minutes, 2 GiB per output file,
no core dumps, no new privileges. Network I/O, mount, reboot, swap, raw-I/O and
debug syscall groups are denied. The service receives a clean environment and a
private HOME and closed stdin. Each service has a unique unit name; timeout or
cancellation requests a stop of its whole cgroup, not just the waiting client.
The CLI maps SIGTERM to the same cleanup/interrupted-receipt path as Ctrl-C,
ignoring repeated SIGTERM while unwinding. Library callers retain control of
their own signal policy. SIGKILL, host failure, or interruption outside the
receipt-producing portion of verification can still leave no receipt.

`python3 scripts/check-sandbox.py` runs synthetic positive/negative probes using the
same resource/permission constructors as verification. It checks outside-file
reads; protected, dependency and source writes; TCP, UDP, IPv6 and Unix sockets;
and allowed candidate-output writes. A probe failure is an infrastructure error.
`BENCHMARK_INSECURE_LOCAL=1` is only an explicit organizer diagnostic mode.

Local validation on 2026-09-07 passed all eleven boundary checks, all five
sandboxed metric canaries, all four actual-claim rejection cases, 22 host tests
and the Lean library/test builds. This is evidence for this checkout/host, not
an independent audit or a remote CI/deployment result.

Receipt hardening on 2026-09-08 adds host tests for post-run source, harness,
dependency and tool drift; failed receipt publication; and orchestration failures
and interruption before scoring. The host suite now has 33 tests. Its simulated
success path mocks compilation/comparison and is not an accepted signature scheme.
The same checkout also passed all eleven live sandbox probes, all five sandboxed
metric canaries and all four actual-claim rejection cases on 2026-09-08. Each
actual-claim rejection retained an unranked receipt without a score.

On 2026-09-09 the host suite grew to 37 tests, including real subprocess SIGTERM
cleanup, signal-handler restoration, repeated-termination behavior and mocked
systemd stop ordering (including a stop timeout). These do not establish cgroup
cleanup after a failed systemd stop; the service runtime limit remains a backstop.

Admission follow-up on 2026-09-09 brings the host suite to 45 tests. Tests cover
same-process and cross-process contention, recovery after owner death, exception
release, no lock inheritance across exec, symlink/FIFO rejection, receipt timing
and retry without reading a candidate while busy.
The admission-enabled runner also passed all four actual-claim rejection cases
in the strict Linux profile, each with the intended diagnostic and no score.
A concurrent CLI probe returned `worker_busy` before accessing its nonexistent
input. The protected library/test build and standard-axiom audit passed again.

## Tests and remaining launch work

```sh
bash setup.sh
python3 -m unittest discover -s tests -v
lake build LeanSphincs LeanSphincsTest
python3 scripts/test-comparator.py       # organizer metric canaries, unsandboxed
python3 scripts/test-sandbox-comparator.py # same metric cases in the real sandbox
python3 scripts/test-verifier.py         # actual SchemeClaim negative path, sandboxed
```

The five comparator canaries prove only metric statements. The production-path
negatives use the real rendered `SchemeClaim`: forged axiom, `sorry`, weakened
statement and a computation reaching outside the oracle type. They must fail for
the intended reason, not merely because compilation or sandbox setup is broken.

Ordinary GitHub-hosted CI runs the host/Lean tests and explicitly unsandboxed
organizer fixtures. The manual `sandbox.yml` workflow is restricted to `main`
and requires a separately provisioned disposable, credential-free Linux worker
labelled `leansphincs-verifier`. It has not been registered or run remotely by
this implementation. The workflow retains test logs and receipts for 14 days.

Before opening submissions:

1. Land baseline #0 with the actual security-game/serialization transport,
   verification-cost proof, signing-failure certificate and same-scheme 2^32-request decay proof. Mutate that accepted
   baseline to complete the full production-profile negative matrix.
2. Review and freeze the revised protected modules, calibrated pricing/resource profiles and governance. The 64-byte input-unit convention is already pinned.
3. Build a reproducible, independently controlled verifier image. Source Git pins
   and recorded binary hashes alone do not authenticate precompiled dependency
   artifacts. Organizer caches/tool installation remain trusted inputs here.
4. Run the external harness audit; pin the operating-system/systemd/tool versions
   and validate the profile on its dedicated worker. Do not run an untrusted PR
   on a credential-bearing persistent self-hosted runner.
5. Extend the cooperative per-checkout admission lock with an external durable
   queue, crash-surviving worker lifecycle, aggregate disk quotas, log-retention
   policy and signed verifier receipts. Per-file/process limits are not an
   aggregate disk quota. Local runs retain artifacts; an operator must manage retention.
6. Add reviewed frontier promotion/credit and website ingestion of authenticated
   results. Do not let a submitted JSON receipt promote itself. Wallet/cycle gates
   and full-track rules remain separate unfinished work.

The threat model excludes an attacker who already controls the verifier's Unix
account, trusted dependencies, tool binaries or kernel. Run directories protect
against candidate subprocesses, not an independent same-user process editing
organizer files. No cryptographic eligibility or launch readiness follows merely
from passing the harness tests.

## v0.21 implemented contract and blocked deployment gates

`Availability.lean` reuses the signing oracle in a shared-ROM interaction with
adaptive messages and an ordered response log. `SchemeClaim` now requires
`adaptive_failure` and `adaptive_decay_failure` as well as the fresh-key,
fixed-message certificate. Failure at zero-based position i means that request i
occurs and returns `none`; absent positions are not failures. Its unconditional
probability includes keygen, ROM and participant randomness, and is at most
2^-128 for every permitted position: up to 2^20 requests / Q <= 2^124, and up to
2^32 requests / Q <= 2^100. Q counts all interaction raw hashes (including keygen
and honest signing) plus requests; it excludes final forgery verification.
Structural query bounds quantify over every response path. Stronger thresholds
transport, and the union bound gives at most 2^-96 over 2^32 positions, not 2^-128.
The SUF-CMA experiment and its final-verification accounting are unchanged.

Protected claim ID: `suf-cma-total-work-pk32-adaptive-availability-v2`. Historical
receipts must be rerun, never relabeled as certificates for this claim.

The runner compiles in a separate constrained systemd service, confirms the
whole service has stopped, then captures declared regular Lean artifacts into
`verification/`. Kernel checking, export, comparison and axiom auditing use
`--verify-prebuilt`, which invokes no build. The verification child has no
candidate write grants. Artifact filenames, sizes and hashes are recorded and
rechecked before receipt publication. Source scanning rejects `eval%` and unsafe
helpers as defense in depth; compilation can execute code even if scanning passes.
Source pins do not authenticate precompiled dependency caches.

`benchmark/resources.json` is organizer-owned. Reference execution calibration,
verification limits, raw keygen/sign/verify caps, persistent secret and
precomputation storage, executable size and evidence validators remain unset.
Missing values fail closed. Execution evidence must bind algorithms, executable
and profile, including malformed-input rejection, parsing, arithmetic, randomness,
retries and setup. Structural raw-query certificates must include impossible-ROM
response branches; ROM-consistent measurements alone cannot certify them.
Storage evidence counts serialized secret/precomputation bytes and documents key
restoration. RAM is no substitute. Independent side-channel implementation review
must state a timing/memory-access leakage model and bind executable and profile;
this is not a formal noninterference theorem.

Executable resource validation is unimplemented: deployment eligibility remains
false even with supplied evidence. Receipts separate mathematical verification,
resource certification, side-channel review and deployment eligibility and keep
`ranked: false`. Any calibrated diagnostic score is explicitly non-eligible.
The additive organizer profile is the only scoring authority; its bandwidth
coefficient remains null, so no scalar score is issued. Existing latency targets,
2^-40 overrun allowances, absolute deadlines and 64 KiB RAM cap are unchanged.
Positive metric/availability fixtures are not cryptographic baselines. Emile's
upstream pin, OTS construction work and baseline parameters are unchanged.
