#!/usr/bin/env python3
"""Check replacement modules/certificates in an isolated tree with the pinned toolchain.

Usage: python3 reviews/2026-11-02-lambda-missions/check_lean.py [FILE.lean ...]
No arguments compiles all 5 replacement modules, definitions before theorem targets.
Open targets intentionally contain sorry; audit certificates must not.
"""
import json
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
TREE = HERE / 'lean'
BUILD = TREE / 'build'
BUILD.mkdir(exist_ok=True)
toolchain = (ROOT / 'lean-toolchain').read_text().strip()
binary = Path.home() / '.elan/toolchains' / toolchain.replace('/', '--').replace(':', '---') / 'bin/lean'
paths = [BUILD, TREE]
paths.extend(p / '.lake/build/lib/lean' for p in sorted((ROOT / '.lake/packages').iterdir()) if p.is_dir())
env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, paths)), ELAN_TOOLCHAIN=toolchain)
if len(sys.argv) > 1:
    files = [Path(s).resolve() for s in sys.argv[1:]]
else:
    modules = json.loads((TREE / 'module-index.json').read_text())
    files = [TREE / m['path'] for kind in ['definition', 'theorem'] for m in modules if m['kind'] == kind]
failed = []
for source in files:
    try:
        module = source.relative_to(TREE)
    except ValueError:
        module = source.relative_to(HERE)
    output = BUILD / module.with_suffix('.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    print('CHECK', source.relative_to(HERE), flush=True)
    result = subprocess.run([str(binary), '-DautoImplicit=false', '-R', str(HERE), '-o', str(output), str(source)], env=env, cwd=HERE)
    if result.returncode:
        failed.append(str(source))
print(f'Checked {len(files)} files; failed {len(failed)}.', flush=True)
sys.exit(bool(failed))
