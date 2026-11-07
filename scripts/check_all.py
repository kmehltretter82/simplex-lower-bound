#!/usr/bin/env python3
"""Elaborate definitions, then independent targets grouped by identical preambles.

Grouping only applies to files containing one open theorem and no helper
commands. It reuses exactly the same imported environment while avoiding an
expensive identical Mathlib reload for each statement. No proof is claimed.
"""
from collections import defaultdict
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
logs = ROOT / 'build-logs'
logs.mkdir(exist_ok=True)
previous = {}
if '--resume' in sys.argv and (logs / 'verification.json').is_file():
    old = json.loads((logs / 'verification.json').read_text())
    if old.get('toolchain') == (ROOT / 'lean-toolchain').read_text().strip() and old.get('mathlib_rev') == '0df444a360eaa60ab8c11dca51a86af692955474':
        previous = {record['module']: record for record in old.get('modules', []) if record.get('exit_code') == 0}
generated = ROOT / 'checks/generated'
generated.mkdir(parents=True, exist_ok=True)
files = sorted(path for folder in ('Definitions', 'Theorems') for path in (ROOT / folder).glob('*.lean'))
modules = {'.'.join(p.relative_to(ROOT).with_suffix('').parts): p for p in files}
ordered, visiting, visited = [], set(), set()

def visit(name):
    if name in visited: return
    if name in visiting: raise SystemExit('cyclic local imports: ' + name)
    visiting.add(name)
    for dependency in re.findall(r'^\s*import\s+([A-Za-z0-9_.]+)', modules[name].read_text(), flags=re.M):
        if dependency in modules: visit(dependency)
    visiting.remove(name)
    visited.add(name)
    ordered.append(name)

for name in modules: visit(name)

def strip_comments(code):
    # These modules use ordinary comments without nested delimiters.
    return re.sub(r'/\-.*?\-/|--[^\n]*', '', code, flags=re.S)

def compile_file(path, label):
    started = time.monotonic()
    result = subprocess.run([sys.executable, str(ROOT / 'scripts/lean_check.py'), str(path)],
                            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = logs / (label + '.log')
    log.write_bytes(result.stdout)
    if result.returncode: print(result.stdout.decode(errors='replace'), flush=True)
    return result.returncode, round(time.monotonic() - started, 3), str(log.relative_to(ROOT))

records = []
success = True
for name in ordered:
    path = modules[name]
    if path.parent.name != 'Definitions': continue
    raw = path.read_bytes()
    if re.search(r'\b(sorry|axiom|unsafe)\b', strip_comments(raw.decode())):
        raise SystemExit('definition has an unproved or unsupported declaration: ' + name)
    cached = previous.get(name)
    olean = ROOT / '.lake/build/lib/lean' / path.relative_to(ROOT).with_suffix('.olean')
    if cached and cached.get('sha256') == hashlib.sha256(raw).hexdigest() and olean.is_file():
        records.append({**cached, 'reused_unchanged_success': True})
        print('REUSE ' + name, flush=True)
        continue
    status, elapsed, log = compile_file(path, name)
    records.append({'module': name, 'path': str(path.relative_to(ROOT)),
        'sha256': hashlib.sha256(raw).hexdigest(), 'exit_code': status,
        'elapsed_seconds': elapsed, 'log': log, 'method': 'standalone'})
    print(('PASS ' if status == 0 else 'FAIL ') + name, flush=True)
    if status:
        success = False
        break

if success:
    groups = defaultdict(list)
    for name in ordered:
        path = modules[name]
        if path.parent.name != 'Theorems': continue
        raw = path.read_text()
        marker = re.search(r'^namespace\s', raw, flags=re.M)
        if marker is None: raise SystemExit('target has no explicit namespace: ' + name)
        preamble, body = raw[:marker.start()], raw[marker.start():]
        clean = strip_comments(body)
        if len(re.findall(r'^theorem\s', clean, flags=re.M)) != 1:
            raise SystemExit('grouped target must contain exactly one theorem: ' + name)
        declarations = re.sub(r'^\s*open scoped [^\n]+', '', clean, flags=re.M)
        if re.search(r'^\s*(?:noncomputable\s+)?(?:def|abbrev|structure|inductive|instance|axiom|example|variable|open|set_option)\s', declarations, flags=re.M):
            raise SystemExit('grouped target contains extra commands: ' + name)
        if re.search(r'^\s*import\s+Theorems\.', preamble, flags=re.M):
            raise SystemExit('grouped target imports a sibling theorem: ' + name)
        if len(re.findall(r'\bsorry\b', clean)) != 1:
            raise SystemExit('target must have one open body: ' + name)
        groups[preamble].append((name, path, body))
    for index, (preamble, members) in enumerate(groups.items(), 1):
        path = generated / f'TargetGroup{index}.lean'
        path.write_text(preamble + '\n\n'.join(body for _, _, body in members))
        status, elapsed, log = compile_file(path, f'TargetGroup{index}')
        for name, original, _ in members:
            records.append({'module': name, 'path': str(original.relative_to(ROOT)),
                'sha256': hashlib.sha256(original.read_bytes()).hexdigest(), 'exit_code': status,
                'elapsed_seconds': elapsed, 'log': log, 'method': 'identical-preamble aggregate',
                'aggregate': str(path.relative_to(ROOT)),
                'aggregate_sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
        print(('PASS ' if status == 0 else 'FAIL ') + f'TargetGroup{index} ({len(members)} independent targets)', flush=True)
        if status:
            success = False
            break

report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(),
    'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
    'mathlib_rev': '0df444a360eaa60ab8c11dca51a86af692955474',
    'all_modules_checked': len(records) == len(ordered),
    'success': success and len(records) == len(ordered) and all(r['exit_code'] == 0 for r in records),
    'note': 'Definitions compile independently. Each theorem is elaborated with its exact preamble; independent one-theorem files share a compilation group. Open target bodies are not proofs.',
    'modules': records}
(logs / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
raise SystemExit(0 if report['success'] else 1)
