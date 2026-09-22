#!/usr/bin/env bash
# Reproduce the source review's 126-bit endpoint and axiom check. Organizer tool.
set -euo pipefail
cd "$(dirname "$0")/.."

readonly revision=a1daec3b929d8963b4eee4f1e05985065a96de9d
readonly reference="$PWD/.benchmark-tools/sphincs-reference"
readonly audit="$PWD/scripts/check-pr19.lean"

if [[ ! -d "$reference" ]]; then
  git clone --filter=blob:none --no-checkout https://github.com/leanEthereum/leanVM-b.git "$reference"
  git -C "$reference" checkout --detach "$revision"
fi
[[ "$(git -C "$reference" rev-parse HEAD)" == "$revision" ]] || {
  echo "PR reference is not at the reviewed revision" >&2; exit 1;
}
[[ -z "$(git -C "$reference" status --porcelain --untracked-files=no)" ]] || {
  echo "PR reference has tracked changes" >&2; exit 1;
}

package="$reference/formal/sphincs"
mkdir -p "$package/.lake"
if [[ ! -e "$package/.lake/packages" && -d "$PWD/.lake/packages" ]]; then
  # Both projects pin the same dependency revisions; retain artifacts in the
  # workspace across interrupted sessions instead of rebuilding under /tmp.
  ln -s "$PWD/.lake/packages" "$package/.lake/packages"
fi
lake -d "$package" build SphincsSecurity.Proof.Security126Completion
lake -d "$package" env lean "$audit"
