#!/usr/bin/env bash
# One-shot setup of the verifier + site on Ubuntu 26.04 with systemd 257+ (run as root once).
#
#   SIG_DOMAIN=sig.golf bash deploy/setup-server.sh
#
# What it does: creates the unprivileged users `sig` (verifier) and `sig-web` (site), installs elan,
# Go (for landrun), uv and Caddy, clones the core repository, builds the verification tools and the
# warm Lean build, installs the two systemd units (web, worker) and the Caddy site. Secrets go in
# /etc/sig/secrets.env.
set -euo pipefail

: "${SIG_REPO_URL:=https://github.com/leanEthereum/sig.golf-dev}"
: "${SIG_SUBMISSIONS_REPO:=leanEthereum/sig.golf-submissions}"
: "${SIG_DOMAIN:=localhost}"
SIG_HOME=/srv/sig
[[ "${EUID}" == 0 ]] || { echo 'run this installer as root' >&2; exit 1; }
[[ "${SIG_REPO_URL}" =~ ^https://github\.com/[A-Za-z0-9-]+/[A-Za-z0-9_.-]+/?$ ]] || {
  echo 'SIG_REPO_URL must be a GitHub HTTPS repository URL' >&2; exit 1;
}
[[ "${SIG_SUBMISSIONS_REPO}" =~ ^[A-Za-z0-9][A-Za-z0-9-]{0,38}/[A-Za-z0-9_.-]{1,100}$ ]] || {
  echo 'SIG_SUBMISSIONS_REPO must be owner/repository' >&2; exit 1;
}
core_repo="${SIG_REPO_URL#https://github.com/}"
core_repo="${core_repo%/}"
core_repo="${core_repo%.git}"
[[ "${core_repo,,}" != "${SIG_SUBMISSIONS_REPO,,}" ]] || {
  echo 'the core and submissions repositories must be different' >&2; exit 1;
}
[[ "${SIG_DOMAIN}" =~ ^[A-Za-z0-9]([A-Za-z0-9.-]*[A-Za-z0-9])?$ ]] || {
  echo 'SIG_DOMAIN must be a hostname' >&2; exit 1;
}
mem_gb=$(( $(awk '/MemTotal/ {print $2}' /proc/meminfo) / 1024 / 1024 ))
(( mem_gb >= 30 )) || { echo 'at least 32 GB of installed RAM is required' >&2; exit 1; }
[[ "$(uname -m)" == x86_64 ]] || { echo 'this installer currently supports x86_64 Linux only' >&2; exit 1; }

systemd_version="$(systemd --version | awk 'NR == 1 {print $2}')"
[[ "${systemd_version}" =~ ^[0-9]+$ ]] && (( systemd_version >= 257 )) || {
  echo 'systemd 257 or newer is required; use Ubuntu 26.04 or an equivalent supported host' >&2; exit 1;
}

apt-get update
apt-get install -y git curl build-essential python3 gnupg sudo openssl sqlite3 apparmor e2fsprogs util-linux debian-keyring debian-archive-keyring apt-transport-https
# Go from go.dev (landrun requires 1.24 or newer)
if ! /usr/local/go/bin/go version >/dev/null 2>&1; then
  go_ver="$(curl -fsSL 'https://go.dev/VERSION?m=text' | head -1)"
  curl -fsSL "https://go.dev/dl/${go_ver}.linux-amd64.tar.gz" -o /tmp/go.tgz
  rm -rf /usr/local/go && tar -C /usr/local -xzf /tmp/go.tgz && rm /tmp/go.tgz
fi
# Caddy (TLS + reverse proxy)
curl -1sLf 'https://dl.cloudsmith.io/public/caddy/stable/gpg.key' | gpg --dearmor --batch --yes -o /usr/share/keyrings/caddy-stable-archive-keyring.gpg
curl -1sLf 'https://dl.cloudsmith.io/public/caddy/stable/debian.deb.txt' > /etc/apt/sources.list.d/caddy-stable.list
apt-get update && apt-get install -y caddy

id -u sig >/dev/null 2>&1 || useradd --system --create-home --home-dir "${SIG_HOME}" --shell /bin/bash sig
getent group sig-state >/dev/null || groupadd --system sig-state
usermod -aG sig-state sig
id -u sig-web >/dev/null 2>&1 || useradd --system --create-home --home-dir /var/lib/sig-web --gid sig-state --shell /usr/sbin/nologin sig-web
install -d -o sig -g sig-state -m 2770 "${SIG_HOME}/data" "${SIG_HOME}/data/logs" /srv/sig-work
chmod o+x "${SIG_HOME}"
# Bounded job storage: a fully allocated (not sparse) 48 GiB image on the system disk, mounted at
# /srv/sig-work at every boot. A runaway proof can fill only this volume.
work_image=/var/lib/sig-work.img
# Scheduled fstrim must not punch holes in this fully reserved loop image. Update
# existing installations too; the exclusion is read from fstab without a remount.
python3 - "${work_image}" <<'PY'
from pathlib import Path
import sys
image = sys.argv[1]
fstab = Path('/etc/fstab')
lines, found = [], False
for line in fstab.read_text().splitlines():
    fields = line.split()
    if len(fields) >= 4 and fields[:2] == [image, '/srv/sig-work']:
        options = [o for o in fields[3].split(',') if o != 'discard']
        for option in ('nodiscard', 'X-fstrim.notrim'):
            if option not in options:
                options.append(option)
        fields[3] = ','.join(options)
        line, found = ' '.join(fields), True
    lines.append(line)
if not found:
    lines.append(f'{image} /srv/sig-work ext4 loop,nosuid,nodev,nodiscard,X-fstrim.notrim 0 2')
fstab.write_text('\n'.join(lines) + '\n')
PY
if ! mountpoint -q /srv/sig-work; then
  if [[ ! -f "${work_image}" ]]; then
    fallocate -l 48G "${work_image}"
    chmod 600 "${work_image}"
    # Initialize everything now: discard, or a lazy background zeroing through the loop device,
    # would punch holes into the image. The second fallocate fills any hole left by mkfs.
    mkfs.ext4 -q -m 0 -E nodiscard,lazy_itable_init=0,lazy_journal_init=0 "${work_image}"
    fallocate -l 48G "${work_image}"
  fi
  mount /srv/sig-work
fi
# Restore the reservation if an older installation was trimmed. fallocate fills
# holes without overwriting existing filesystem contents.
fallocate -l "$(stat -c %s "${work_image}")" "${work_image}"
chown sig:sig-state /srv/sig-work
chmod 2770 /srv/sig-work
loginctl enable-linger sig   # systemd --user for the transient sandbox services of the worker
# Ubuntu restricts unprivileged user namespaces. This unconfined AppArmor profile permits
# systemd-executor to create the job namespaces and is inherited by its child processes.
# It is not a restriction to the executor alone; Landlock and the checked systemd restrictions
# enforce the candidate boundary. Run the actual-host isolation probe before admission.
cat > /etc/apparmor.d/sig-systemd-executor <<'APPARMOR'
abi <abi/4.0>,
include <tunables/global>

profile sig-systemd-executor /usr/lib/systemd/systemd-executor flags=(unconfined) {
  userns,
  include if exists <local/sig-systemd-executor>
}
APPARMOR
apparmor_parser -r /etc/apparmor.d/sig-systemd-executor
# Only sig-web receives secrets. The verifier's different Unix identity must never receive them,
# including through /proc/<pid>/environ. The shared group grants database/log access, not credentials.
mkdir -p /etc/sig
[[ -f /etc/sig/public.env ]] || cat > /etc/sig/public.env <<ENV
SIG_BASE_URL=https://${SIG_DOMAIN}
SIG_CONTRACT_REPO=${core_repo}
SIG_SUBMISSIONS_REPO=${SIG_SUBMISSIONS_REPO}
SIG_DATABASE_URL=sqlite:///${SIG_HOME}/data/sig.db
SIG_DATA_DIR=${SIG_HOME}/data
SIG_WORK_DIR=/srv/sig-work
TMPDIR=/srv/sig-work
SIG_PHONY=0
ENV
[[ -f /etc/sig/secrets.env ]] || ( umask 077; cat > /etc/sig/secrets.env <<ENV
GITHUB_WEBHOOK_SECRET=$(openssl rand -hex 32)
GITHUB_TOKEN=
ENV
)
chown root:root /etc/sig/public.env /etc/sig/secrets.env
chmod 644 /etc/sig/public.env && chmod 600 /etc/sig/secrets.env

sudo -u sig -H bash -euo pipefail <<USER
cd "${SIG_HOME}"
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
curl -LsSf https://astral.sh/uv/install.sh | sh
export PATH="\$HOME/.elan/bin:\$HOME/.local/bin:/usr/local/go/bin:\$PATH"
[[ -d repo/.git ]] || git clone "${SIG_REPO_URL}" repo
cd repo
verifier/setup_tools.sh                          # comparator, lean4export, landrun at their pinned revisions
( cd formal && lake exe cache get && lake build LeanSphincs )   # the protected statement only; submissions compile in the sandbox
python3 verifier/pin_contract.py check
( cd service && uv sync --locked )
USER

install -m 644 "${SIG_HOME}/repo/service/deploy/sig-web.service" /etc/systemd/system/
install -m 644 "${SIG_HOME}/repo/service/deploy/sig-worker.service" /etc/systemd/system/
# the worker's memory backstop: 6 GB below the machine, at most the unit's 28G (the sandboxed run
# itself is capped at the contract's 24 GiB by the verifier's transient service)
cap=$(( mem_gb - 6 )); (( cap > 28 )) && cap=28
sed -i "s/^MemoryMax=.*/MemoryMax=${cap}G/" /etc/systemd/system/sig-worker.service
sed "s/{{DOMAIN}}/${SIG_DOMAIN}/" "${SIG_HOME}/repo/service/deploy/Caddyfile" > /etc/caddy/Caddyfile
systemctl daemon-reload
systemctl enable sig-web sig-worker caddy
echo "installed, not started. Configure /etc/sig/secrets.env and complete deploy/README.md's Linux acceptance checks before public admission."
