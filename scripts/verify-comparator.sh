#!/usr/bin/env bash
set -euo pipefail

# Compare the independent advertised statements with the actual proofs and
# replay their exported dependencies through the toolchain's three kernels.
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

for command_name in lake lean bwrap python3; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "Required command is missing: $command_name" >&2
    exit 1
  fi
done

lean_prefix=$(lean --print-prefix)
for checker_name in leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -x "$lean_prefix/bin/$checker_name" ]; then
    echo "The pinned Lean toolchain does not supply $checker_name" >&2
    exit 1
  fi
done

# Palomar injects these checker paths itself. Keep them out of the submitted
# comparator.json and use this temporary configuration only for local/CI checks.
comparator_config=$(mktemp)
trap 'rm -f "$comparator_config"' EXIT
python3 - "$lean_prefix" "$comparator_config" <<'PY'
import json
from pathlib import Path
import sys

prefix, output = sys.argv[1:]
config = json.loads(Path('comparator.json').read_text())
if 'external_kernels' in config:
    raise SystemExit('Submitted comparator.json must not supply external_kernels')
config.pop('enable_nanoda', None)
config['external_kernels'] = {
    'nanoda': [str(Path(prefix) / 'bin/nanoda_bin')],
    'con-ron': [str(Path(prefix) / 'bin/con-ron')],
}
Path(output).write_text(json.dumps(config, indent=2) + '\n')
PY

lake comparator --config "$comparator_config"
