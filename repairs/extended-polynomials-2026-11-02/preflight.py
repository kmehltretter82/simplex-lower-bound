#!/usr/bin/env python3
"""Read-only platform preflight. Credentials stay in private temporary curl configs."""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(ROOT / 'scripts'))
from stage_drafts import API

proposal_id = '059a0f02-b778-44fd-9e95-ec7cbdba9cbc'
api = API(Path.home() / 'prove2me_workspace/credentials.json', transport='manual-curl')
requests = [
    ('proposal-before-repair.json', '/mission-proposals/' + proposal_id),
    ('milestones-before-repair.json', '/mission-proposals/' + proposal_id + '/milestones'),
    ('definitions-before-repair.json', '/definitions?q=Schwichtenberg1976&include_deprecated=true&limit=100'),
    ('theorems-before-repair.json', '/theorems?q=Schwichtenberg1976&include_deprecated=true&limit=100'),
]
for filename, path in requests:
    result = api.request('GET', path)
    (HERE / filename).write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    if filename.startswith('proposal'):
        if result['status'] != 'Draft':
            raise SystemExit('Proposal is not Draft; no writes authorized by this preflight.')
        if result['env'] != '0df444a360eaa60ab8c11dca51a86af692955474':
            raise SystemExit('Unexpected proposal environment.')
        print(json.dumps({'status': result['status'], 'name': result['name'],
                          'items': len(result['items']), 'env': result['env']}), flush=True)
    else:
        print('Saved ' + filename, flush=True)
print('READ_ONLY_PREFLIGHT_COMPLETE', flush=True)
