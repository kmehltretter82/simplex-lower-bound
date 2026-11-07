#!/usr/bin/env python3
"""Assemble canonical editable-draft packets from audited Lean source files."""
import hashlib
import json
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parent.parent
PIN='0df444a360eaa60ab8c11dca51a86af692955474'
FIELD='105f8c80-f763-4beb-822c-d9265917c2b1'
META={
'friedmann_parity':('Finite parity games and deterministic strategy improvement',
 'Finite positional parity games, ultimately periodic plays, three-component valuations, minima over legal counterstrategies, local and global improvement, completed executions, and constrained lower-bound propositions. No witness family or long execution is assumed.',
 'Friedmann, LMCS2011, §§2–8; https://arxiv.org/abs/1106.0778'),
'friedmann_payoff':('Rational payoff and stopping stochastic game models',
 'Rational discounted Bellman values, the specified parity-to-payoff reduction, stopping stochastic absorption equations, and the corresponding local and global update rules. Validity predicates require total arenas, a discount in (0,1), or almost-sure absorption as appropriate.',
 'Friedmann, LMCS2011, §9; https://arxiv.org/abs/1106.0778'),
'friedmann_simplex':('Rational primal simplex and cyclic entering-variable selection',
 'Standard-form rational linear programs, actual basic solutions at nonsingular feasible bases, reduced costs, minimum-ratio pivots, and cyclic entering-variable selection. No lower bound is a field or hypothesis.',
 'Avis and Friedmann, Mathematical Programming2017, §4.1; https://arxiv.org/abs/1305.3944'),
'friedmann_multiplicity':('Parity-game valuations with repeated priorities',
 'Priority-occurrence-count comparison, minimum valuations over legal opponents, and improving edges for repeated-priority parity games.',
 'Avis and Friedmann, Mathematical Programming2017, §2.2; https://arxiv.org/abs/1305.3944'),
'friedmann_cunningham':('Explicit Cunningham lower-bound constructions',
 'The finite source graph, its repeated-priority valuation, an absorbing MDP, a graph-derived rational LP, prescribed cyclic ordering and initial state, and a polytope/cube realization.',
 'Avis and Friedmann, Mathematical Programming2017, §§2–4; https://arxiv.org/abs/1305.3944'),
'friedmann_zadeh':('Explicit least-entered counters and the source tie rule',
 'The finite counter, actual policy and simplex evaluations, zero initial occurrence counts, exact least-entered choices, a fixed completion of the source tie rule, and the induced occupancy LP. Parameter restrictions, complete executions and all boundary conventions are explicit.',
 'Disser, Friedmann and Hopp, Mathematical Programming2023, §§2–6; https://arxiv.org/abs/1911.01074v2')
}

out=ROOT/'upload';out.mkdir(exist_ok=True)
summary=[]
for slug in ('parity','cunningham','zadeh'):
    metadata=json.loads((ROOT/'mission-data'/f'{slug}.json').read_text())
    readbacks=json.loads((ROOT/'audits'/f'{slug}-readbacks.json').read_text())
    items=[];milestones=[]
    def readback(relative):
        entry=readbacks.get(relative)
        actual=hashlib.sha256((ROOT/relative).read_bytes()).hexdigest()
        if not entry or entry.get('source_sha256')!=actual:
            raise SystemExit('Missing or stale independent readback: '+relative+' in '+slug)
        return {'readback':entry['readback'],'readback_model':entry['readback_model']}
    for relative in metadata['definition_files']:
        name=Path(relative).stem.removeprefix('Def_')
        title,natural,source=META[name]
        natural=metadata.get('definition_descriptions',{}).get(name,natural)
        items.append({'key':'def:'+name,'kind':'definition','definition_name':name,
            'definition_title':title,'definition':(ROOT/relative).read_text(),
            'natural_language_statement':natural,'source':source,
            'tags':['theoretical-computer-science','algorithm-analysis','oliver-friedmann'],
            **readback(relative)})
    for theorem in metadata['theorems']:
        relative=theorem['file'];code=(ROOT/relative).read_text()
        start=re.search(r'^namespace\s',code,flags=re.M)
        if not start:raise SystemExit('Missing namespace: '+relative)
        preamble=code[:start.start()].strip()+'\n'
        statement=re.sub(r':=\s*by\s+sorry',':= by sorry',code[start.start():]).strip()
        item={'key':theorem['key'],'kind':'theorem',
            **{key:theorem[key] for key in ('theorem_name','theorem_title','natural_language_statement','source')},
            'preamble':preamble,'formal_statement':statement,
            'tags':['theoretical-computer-science','algorithm-analysis','oliver-friedmann'],
            **readback(relative)}
        items.append(item)
        if theorem['key']!=metadata['main_key']:
            title=theorem.get('milestone_title')
            description=theorem.get('milestone_description')
            if not title or not description:raise SystemExit('Missing milestone metadata: '+relative)
            milestones.append({'key':theorem['key'],'milestone_title':title,'milestone_description':description})
    packet={'proposal':{'name':metadata['name'],'description':metadata['description'],
        'mission_type':'ResearchPaper','env':PIN,'field_ids':[FIELD],'visibility':'public'},
        'items':items,'main_key':metadata['main_key'],'milestones':milestones}
    destination=out/f'{slug}.json'
    destination.write_text(json.dumps(packet,ensure_ascii=False,indent=2)+'\n')
    summary.append({'paper':slug,'packet':str(destination.relative_to(ROOT)),
        'definitions':len(metadata['definition_files']),'theorems':len(metadata['theorems']),
        'milestones':len(milestones),'sha256':hashlib.sha256(destination.read_bytes()).hexdigest()})
    print(slug+': '+str(len(items))+' audited draft items, '+str(len(milestones))+' milestones')
receipts=[json.loads(p.read_text()) for p in sorted(out.glob('*.receipt.json'))]
(out/'index.json').write_text(json.dumps({'environment':PIN,'packets':summary,'server_uploads':receipts},indent=2)+'\n')
