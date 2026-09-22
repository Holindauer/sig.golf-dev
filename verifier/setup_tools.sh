#!/usr/bin/env bash
# Install the pinned proof tools into verifier/.tools, warm the trusted Lean project in formal/
# and run the host acceptance checks. Idempotent; run from anywhere.
set -euo pipefail
cd "$(dirname "$0")/.."

readonly comparator_rev=777e7f56119efc0fac34003db4efe831e0b53723
readonly landrun_rev=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
readonly tools_dir=verifier/.tools
readonly comparator_dir=$tools_dir/comparator

clone_at() {
  local url="$1" revision="$2" destination="$3"
  if [[ ! -d "$destination" ]]; then
    git clone --no-checkout "$url" "$destination"
    git -C "$destination" checkout --detach "$revision"
  fi
  [[ "$(git -C "$destination" rev-parse HEAD)" == "$revision" ]] || {
    echo "tool checkout at unexpected revision: $destination" >&2
    exit 1
  }
  if [[ "$destination" == "$comparator_dir" ]]; then
    for patch in comparator-leanchecker.patch comparator-leanchecker-v1.patch; do
      if [[ "$(git -C "$destination" diff -- Main.lean)" == "$(<"verifier/$patch")" ]] &&
          [[ -z "$(git -C "$destination" status --porcelain -- . ':!Main.lean')" ]] &&
          [[ -z "$(git -C "$destination" diff --cached)" ]]; then
        if [[ "$patch" == comparator-leanchecker-v1.patch ]]; then
          git -C "$destination" apply --reverse "$PWD/verifier/$patch"
        fi
        return
      fi
    done
  fi
  [[ -z "$(git -C "$destination" status --porcelain)" ]] || {
    echo "tool checkout contains local changes: $destination" >&2
    exit 1
  }
}

# git clone creates the leading verifier/.tools directory.
clone_at https://github.com/leanprover/comparator.git "$comparator_rev" "$comparator_dir"
if git -C "$comparator_dir" apply --check "$PWD/verifier/comparator-leanchecker.patch" 2>/dev/null; then
  git -C "$comparator_dir" apply "$PWD/verifier/comparator-leanchecker.patch"
fi
toolchain="$(<formal/lean-toolchain)"
lake "+$toolchain" -d "$comparator_dir" build comparator lean4export

if [[ "${BENCHMARK_INSECURE_LOCAL:-0}" != 1 ]]; then
  clone_at https://github.com/Zouuup/landrun.git "$landrun_rev" "$tools_dir/landrun"
  (cd "$tools_dir/landrun" && go build -trimpath -o landrun ./cmd/landrun)
fi

(
  cd formal
  lake exe cache get
  lake build LeanSphincs
  lake env lean scripts/check-axioms.lean
)
python3 verifier/pin_contract.py check
if [[ "${BENCHMARK_INSECURE_LOCAL:-0}" != 1 ]]; then
  python3 verifier/check-sandbox.py
fi
