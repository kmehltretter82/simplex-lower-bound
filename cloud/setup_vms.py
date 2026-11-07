#!/usr/bin/env python3
"""Provision the two requested Lean workers. Default prints a plan only."""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import shlex
import subprocess

ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--apply', action='store_true')
parser.add_argument('--project', default='project-6ac635c9-6153-4290-a99')
parser.add_argument('--zone', default='europe-west3-a')
parser.add_argument('--machine-type', default='e2-standard-4')
parser.add_argument('--max-run-duration', default='24h')
parser.add_argument('--cloudsdk-config', type=Path)
args = parser.parse_args()
names = ['oliver-lean-20261102-a', 'oliver-lean-20261102-b']
common = ['--project='+args.project, '--zone='+args.zone, '--quiet']
command = ['gcloud', 'compute', 'instances', 'create', *names, *common,
    '--machine-type='+args.machine_type, '--image-family=ubuntu-2404-lts-amd64',
    '--image-project=ubuntu-os-cloud', '--boot-disk-size=60GB', '--boot-disk-type=pd-balanced',
    '--no-service-account', '--no-scopes', '--no-restart-on-failure',
    '--max-run-duration='+args.max_run_duration, '--instance-termination-action=STOP',
    '--labels=workload=lean,task=oliver-friedmann,managed-by=codex',
    '--metadata-from-file=startup-script='+str(ROOT/'bootstrap-lean.sh'), '--format=json']
print(shlex.join(command), flush=True)
if not args.apply:
    print('Plan only. No credentials read, API calls or VM creation.')
    raise SystemExit(0)
env = os.environ.copy()
env['CLOUDSDK_CORE_DISABLE_FILE_LOGGING'] = 'true'
env['CLOUDSDK_COMPONENT_MANAGER_DISABLE_UPDATE_CHECK'] = 'true'
if args.cloudsdk_config:
    env['CLOUDSDK_CONFIG'] = str(args.cloudsdk_config)

def invoke(argv):
    return subprocess.run(argv, env=env, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, timeout=600)

# Reconcile existing names before every attempt, including a prior partial create.
listed = invoke(['gcloud','compute','instances','list','--project='+args.project,
                 '--filter=name:oliver-lean-20261102-','--format=json','--quiet'])
if listed.returncode:
    print(listed.stderr)
    raise SystemExit('Instance preflight failed; no create request was sent.')
existing = {vm['name']:vm for vm in json.loads(listed.stdout) if vm['name'] in names}
for name, vm in existing.items():
    if vm.get('labels',{}).get('task') != 'oliver-friedmann':
        raise SystemExit('Existing name belongs to another workload: '+name)
    if vm.get('zone','').split('/')[-1] != args.zone:
        raise SystemExit('Existing instance is in another zone: '+name)
    if vm.get('machineType','').split('/')[-1] != args.machine_type:
        raise SystemExit('Existing instance has another machine type: '+name)
missing = [name for name in names if name not in existing]
if missing:
    create = ['gcloud','compute','instances','create',*missing,*command[6:]]
    # command[6:] begins with common flags after the two fixed instance names.
    result = invoke(create)
    if result.returncode:
        print(result.stderr)
        raise SystemExit('Creation did not complete cleanly. Rerun to reconcile instances before any retry.')
readback = invoke(['gcloud','compute','instances','list','--project='+args.project,
                  '--filter=name:oliver-lean-20261102-','--format=json','--quiet'])
if readback.returncode:
    raise SystemExit('Could not read back final state; do not assume provisioning completed.')
records = [vm for vm in json.loads(readback.stdout) if vm['name'] in names]
(ROOT/'instances.json').write_text(json.dumps({'observed_at_utc':datetime.now(timezone.utc).isoformat(),
    'project':args.project,'instances':records},indent=2)+'\n')
if len(records) != 2 or any(vm.get('status') != 'RUNNING' for vm in records):
    raise SystemExit('Two RUNNING instances have not been observed; inspect cloud/instances.json.')
print('Two VM instances are RUNNING. Bootstrap readiness still requires /opt/oliver-lean/READY on each guest.')
for name in names:
    print(shlex.join(['gcloud','compute','ssh',name,*common,'--command=cat /opt/oliver-lean/READY']))
