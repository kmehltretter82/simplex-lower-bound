#!/usr/bin/env python3
"""Snapshot portable mission files and create a credential-free ZIP archive."""

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parent.parent
PIN = "0df444a360eaa60ab8c11dca51a86af692955474"
directories = ["Definitions", "Theorems", "Solutions", "scripts", "mission-data", "notes", "audits", "checks", "upload", "build-logs"]
selected = []
for name in ["README.md", "lean-toolchain", "lakefile.lean", "lake-manifest.json", ".gitignore", "sources.json", "references.bib"]:
    path = ROOT / name
    if path.is_file():
        selected.append(path)
for name in ["README.md", "setup_vms.py", "bootstrap-lean.sh", "status.json", "mock-checks.json"]:
    path = ROOT / "cloud" / name
    if path.is_file():
        selected.append(path)
for name in directories:
    directory = ROOT / name
    if not directory.exists():
        continue
    for path in directory.rglob("*"):
        if not path.is_file() or path.is_symlink() or "__pycache__" in path.parts:
            continue
        if path.suffix in {".olean", ".ilean", ".pyc"}:
            continue
        if "credential" in path.name.lower() or path.name.endswith((".state.json", ".pending.json")) or path.name == "state.json":
            continue
        selected.append(path)
files = []
for path in sorted(set(selected)):
    content = path.read_bytes()
    files.append({"path": str(path.relative_to(ROOT)), "bytes": len(content),
                  "sha256": hashlib.sha256(content).hexdigest()})
report_path = ROOT / "build-logs/verification.json"
verification = json.loads(report_path.read_text()) if report_path.is_file() else None
receipts = [json.loads(p.read_text()) for p in sorted((ROOT / "upload").glob("*.receipt.json"))]
manifest = {"created_at_utc": datetime.now(timezone.utc).isoformat(),
            "toolchain": "leanprover/lean4:v4.33.1", "mathlib_rev": PIN,
            "verification": verification,
            "platform_upload": receipts if receipts else "No draft upload recorded.",
            "note": "Theorem targets are open statements. Compilation is not a proof.",
            "files": files}
manifest_path = ROOT / "packet-manifest.json"
manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
archive_path = ROOT / "friedmann-missions.zip"
with zipfile.ZipFile(archive_path, "w", compression=zipfile.ZIP_DEFLATED) as archive:
    for entry in files:
        archive.write(ROOT / entry["path"], "friedmann-missions/" + entry["path"])
    archive.write(manifest_path, "friedmann-missions/packet-manifest.json")
print(f"Archived {len(files)} source, metadata and log files to {archive_path}")
