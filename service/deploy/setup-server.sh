#!/usr/bin/env bash
# One-shot setup of the sig.golf verifier + site on a fresh Ubuntu 24.04 host (run as root once).
#
#   SIG_REPO_URL=https://github.com/leanEthereum/leanSphincs SIG_DOMAIN=sig.golf bash service/deploy/setup-server.sh
#
# Creates the unprivileged users `sig` (verifier) and `sig-web` (site), installs elan, Go (for
# landrun), uv and Caddy, clones the contract repository, builds the comparator tools and the warm
# Lean build, installs the two systemd units and the Caddy site. Secrets go in /etc/sig/secrets.env.
set -euo pipefail

: "${SIG_REPO_URL:?set SIG_REPO_URL}"
: "${SIG_DOMAIN:=localhost}"
SIG_HOME=/srv/sig
[[ "${EUID}" == 0 ]] || { echo 'run this installer as root' >&2; exit 1; }
[[ "${SIG_REPO_URL}" =~ ^https://github\.com/[A-Za-z0-9-]+/[A-Za-z0-9_.-]+/?$ ]] || {
  echo 'SIG_REPO_URL must be a GitHub HTTPS repository URL' >&2; exit 1;
}
[[ "${SIG_DOMAIN}" =~ ^[A-Za-z0-9]([A-Za-z0-9.-]*[A-Za-z0-9])?$ ]] || { echo 'SIG_DOMAIN must be a hostname' >&2; exit 1; }
mem_gb=$(( $(awk '/MemTotal/ {print $2}' /proc/meminfo) / 1024 / 1024 ))
(( mem_gb >= 30 )) || { echo 'at least 32 GB of installed RAM is required' >&2; exit 1; }
[[ "$(uname -m)" == x86_64 ]] || { echo 'this installer currently supports x86_64 Linux only' >&2; exit 1; }

apt-get update
apt-get install -y git curl build-essential python3 gnupg sudo openssl sqlite3 debian-keyring debian-archive-keyring apt-transport-https
if ! /usr/local/go/bin/go version >/dev/null 2>&1; then
  go_ver="$(curl -fsSL 'https://go.dev/VERSION?m=text' | head -1)"
  curl -fsSL "https://go.dev/dl/${go_ver}.linux-amd64.tar.gz" -o /tmp/go.tgz
  rm -rf /usr/local/go && tar -C /usr/local -xzf /tmp/go.tgz && rm /tmp/go.tgz
fi
curl -1sLf 'https://dl.cloudsmith.io/public/caddy/stable/gpg.key' | gpg --dearmor --batch --yes -o /usr/share/keyrings/caddy-stable-archive-keyring.gpg
curl -1sLf 'https://dl.cloudsmith.io/public/caddy/stable/debian.deb.txt' > /etc/apt/sources.list.d/caddy-stable.list
apt-get update && apt-get install -y caddy

id -u sig >/dev/null 2>&1 || useradd --system --create-home --home-dir "${SIG_HOME}" --shell /bin/bash sig
getent group sig-state >/dev/null || groupadd --system sig-state
usermod -aG sig-state sig
id -u sig-web >/dev/null 2>&1 || useradd --system --create-home --home-dir /var/lib/sig-web --gid sig-state --shell /usr/sbin/nologin sig-web
install -d -o sig -g sig-state -m 2770 "${SIG_HOME}/data" "${SIG_HOME}/data/logs" /srv/sig-work
chmod o+x "${SIG_HOME}"
loginctl enable-linger sig   # systemd --user for the transient sandbox services of the worker
mkdir -p /etc/sig
[[ -f /etc/sig/public.env ]] || cat > /etc/sig/public.env <<ENV
SIG_BASE_URL=https://${SIG_DOMAIN}
SIG_CONTRACT_REPO=$(echo "${SIG_REPO_URL}" | sed -E 's#^https://github.com/##; s#/$##; s#\.git$##')
SIG_DATABASE_URL=sqlite:///${SIG_HOME}/data/sig.db
SIG_DATA_DIR=${SIG_HOME}/data
SIG_WORK_DIR=/srv/sig-work
TMPDIR=/srv/sig-work
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
bash setup.sh                                   # comparator, lean4export, landrun at their pinned revisions
lake exe cache get || true                      # Mathlib cache through VCVio, when available
lake build LeanSphincs                          # the protected statement only; submissions compile in the sandbox
lake env lean scripts/check-axioms.lean
( cd service && uv sync --frozen )
USER

install -m 644 "${SIG_HOME}/repo/service/deploy/sig-web.service" /etc/systemd/system/
install -m 644 "${SIG_HOME}/repo/service/deploy/sig-worker.service" /etc/systemd/system/
cap=$(( mem_gb - 6 )); (( cap > 28 )) && cap=28
sed -i "s/^MemoryMax=.*/MemoryMax=${cap}G/" /etc/systemd/system/sig-worker.service
sed "s/{{DOMAIN}}/${SIG_DOMAIN}/" "${SIG_HOME}/repo/service/deploy/Caddyfile" > /etc/caddy/Caddyfile
systemctl daemon-reload
systemctl enable sig-web sig-worker caddy
echo "installed, not started. Mount bounded job storage at /srv/sig-work, configure /etc/sig/secrets.env, register the GitHub webhook, and complete deploy/README.md's Linux acceptance checks before opening admission."
