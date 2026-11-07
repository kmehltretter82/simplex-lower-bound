#!/usr/bin/env bash
set -euo pipefail
exec > >(tee -a /var/log/oliver-lean-bootstrap.log) 2>&1
export DEBIAN_FRONTEND=noninteractive
apt-get update
apt-get install -y ca-certificates curl git unzip zstd build-essential libgmp-dev python3
id lean >/dev/null 2>&1 || useradd --create-home --shell /bin/bash lean
install -d -o lean -g lean /opt/oliver-lean
cat > /opt/oliver-lean/setup-worker.sh <<'WORKER'
#!/usr/bin/env bash
set -euo pipefail
export ELAN_HOME="$HOME/.elan"
export PATH="$ELAN_HOME/bin:$PATH"
if ! command -v elan >/dev/null; then
  curl --fail --location --silent --show-error https://elan.lean-lang.org/elan-init.sh -o /tmp/oliver-elan-init.sh
  bash /tmp/oliver-elan-init.sh -y --default-toolchain leanprover/lean4:v4.33.1
fi
elan toolchain install leanprover/lean4:v4.33.1
cd /opt/oliver-lean
if [ ! -d mathlib/.git ]; then
  git clone https://github.com/leanprover-community/mathlib4.git mathlib
fi
cd mathlib
git fetch origin 0df444a360eaa60ab8c11dca51a86af692955474
git checkout --detach 0df444a360eaa60ab8c11dca51a86af692955474
lake exe cache get
lake env lean --version
printf '%s\n' 'leanprover/lean4:v4.33.1' 'mathlib 0df444a360eaa60ab8c11dca51a86af692955474' > /opt/oliver-lean/READY
WORKER
chown lean:lean /opt/oliver-lean/setup-worker.sh
chmod 755 /opt/oliver-lean/setup-worker.sh
runuser -u lean -- /opt/oliver-lean/setup-worker.sh
