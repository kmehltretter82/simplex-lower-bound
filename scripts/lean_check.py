#!/usr/bin/env python3
"""Check one module using cached dependencies, without rebuilding shared Mathlib."""

import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent

if len(sys.argv) < 2:
    raise SystemExit("usage: python3 scripts/lean_check.py PATH.lean [LEAN_OPTIONS...]")
source = Path(sys.argv[1]).resolve()
try:
    relative = source.relative_to(ROOT)
except ValueError:
    raise SystemExit("source must be inside this package")
if source.suffix != ".lean":
    raise SystemExit("source must be a Lean module")
output = ROOT / ".lake/build/lib/lean" / relative.with_suffix(".olean")
output.parent.mkdir(parents=True, exist_ok=True)
library_paths = [ROOT / ".lake/build/lib/lean", ROOT]
packages = ROOT / ".lake/packages"
if not packages.exists():
    raise SystemExit("missing dependency cache: run lake update and lake exe cache get in this package first")
library_paths.extend(p / ".lake/build/lib/lean" for p in sorted(packages.iterdir()) if p.is_dir())
environment = os.environ.copy()
environment["LEAN_PATH"] = os.pathsep.join(str(p) for p in library_paths)
toolchain = (ROOT / "lean-toolchain").read_text().strip()
environment["ELAN_TOOLCHAIN"] = toolchain
os.chdir(ROOT)
toolchain_directory = toolchain.replace("/", "--").replace(":", "---")
elan_root = Path(environment.get("ELAN_HOME", str(Path.home() / ".elan")))
installed_lean = elan_root / "toolchains" / toolchain_directory / "bin/lean"
binary = str(installed_lean) if installed_lean.is_file() else "lean"
command = [binary, "-DautoImplicit=false", "-o", str(output), str(relative), *sys.argv[2:]]
raise SystemExit(subprocess.call(command, env=environment))
