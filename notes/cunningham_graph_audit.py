"""Compare actual Lean data with independent Figure 2/7/8 graph expansion.

Run the Lean exporter first:
 python3 scripts/lean_check.py checks/CunninghamExport.lean > build-logs/CunninghamExport.log
Then run this script. No coefficient or reward routine is imported from the
implementation or the earlier numeric check. Exact finite checks complement
the general algebraic argument; they do not prove a lower bound.
"""
from fractions import Fraction as Q
from functools import lru_cache
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def source_graph(n):
    decision = [(k, i) for k, lo, hi in
                [('a', 2, n), ('b', 2, n-1), ('c', 2, n),
                 ('d', 2, n), ('e', 1, n)] for i in range(lo, hi+1)]
    vertices = decision + [(k, i) for k in ['F', 'g', 'h']
                           for i in range(1, n+1)] + [('s', 0), ('t', 0)]
    N = 2*n+1
    eps = Q(1, N**(2*n+2))

    def alias(v):
        k, i = v
        if k in ['b', 'c'] and i == 1:
            return ('g', 1)
        if k == 'a' and i == n+1:
            return ('t', 0)
        return v

    def action(k, i, bit):
        if bit:
            return ('g' if k in 'abc' else 'F', i)
        return alias({'a': ('a', i+1), 'b': ('b', i-1),
                      'c': ('c', i-1), 'd': ('b', i-1), 'e': ('s', 0)}[k])

    def random_edges(v):
        k, i = v
        if k == 'g': return [(Q(1), ('F', i))], Q((-N)**(2*i-1))
        if k == 'h': return [(Q(1), alias(('a', i+1)))], Q(N**(2*i))
        if k == 's': return [(Q(1), ('c', n))], Q(1)
        if k == 't': return [(Q(1), ('t', 0))], Q(0)
        assert k == 'F'
        return ([(eps, ('h', i)), (1-eps, ('e', i))] if i == 1 else
                [(eps, ('h', i)), ((1-eps)/2, ('d', i)),
                 ((1-eps)/2, ('e', i))]), Q(0)

    @lru_cache(None)
    def collapse(v):
        # Stop at the NEXT decision vertex: rewards belong only to eliminated
        # outgoing edges. Terminal sink has no further reward or flow.
        if v in decision: return Q(0), {v: Q(1)}
        if v == ('t', 0): return Q(0), {}
        edges, reward = random_edges(v)
        distribution = {}
        for probability, w in edges:
            r, targets = collapse(w)
            reward += probability*r
            for q, p in targets.items():
                distribution[q] = distribution.get(q, Q(0)) + probability*p
        return reward, distribution

    def priority(v):
        k, i = v
        if k in 'abc': return 3
        if k in 'de': return 5
        if k == 'F': return 6
        if k == 'g': return 2*i+7
        if k == 'h': return 2*i+8
        return 8 if k == 's' else 1

    # Source equation (1), independent list concatenation rather than Lean's
    # integer division/modulo enumeration and inverse-rank formulas.
    order = [('e', 1, 1)]
    for i in range(2, n+1):
        order += [('d', i, 0), ('e', i, 1)]
        if i < n: order += [('b', i, 1), ('b', i, 0)]
    order += [('c', i, b) for i in range(2, n+1) for b in [0, 1]]
    order += [('e', i, 0) for i in range(1, n+1)]
    order += [('d', i, 1) for i in range(2, n+1)]
    order += [('a', i, b) for i in range(n, 1, -1) for b in [1, 0]]
    return decision, vertices, action, random_edges, collapse, priority, order


def main():
    raw = (ROOT/'build-logs/CunninghamExport.log').read_text()
    by_n = {}
    for line in raw.splitlines():
        if line[:2] not in ['N|', 'R|', 'C|', 'G|']: continue
        tag, ns, *rest = line.split('|')
        by_n.setdefault(int(ns), {}).setdefault(tag, []).append(rest)
    assert sorted(by_n) == list(range(3, 11)), 'missing or failed Lean export'
    report = []
    for n, records in sorted(by_n.items()):
        rows, nodes, action, random_edges, collapse, priority, order = source_graph(n)
        assert records['N'] == [[str(len(rows)), str(len(order))]]
        assert len(records['R']) == len(rows)
        assert len(records['C']) == len(order)
        assert len(records['G']) == len(nodes)
        assert len(set(order)) == 2*len(rows)
        for i, label, bit in records['R']:
            k, level = label.split(',')
            assert rows[int(i)] == (k, int(level))
            assert int(bit) == int(k == 'd' or (k == 'e' and int(level) == 1))
        for j, label, reward_text, matrix_text, src, tgt, rank in records['C']:
            k, level, bit = label.split(',')
            name = (k, int(level), int(bit))
            assert order[int(j)] == name
            assert rank == j
            target = action(*name)
            reward, transitions = collapse(target)
            assert reward == Q(reward_text), (n, name, 'reward')
            expected_column = [Q(q == name[:2])-transitions.get(q, Q(0)) for q in rows]
            assert expected_column == [Q(x) for x in matrix_text.split(',')], (n, name, 'flow')
            assert nodes[int(src)] == name[:2]
            assert nodes[int(tgt)] == target
            assert all(p >= 0 for p in transitions.values())
            assert sum(transitions.values()) <= 1
        for v, p, successors in records['G']:
            node = nodes[int(v)]
            expected = ({action(*node, b) for b in [0, 1]} if node in rows else
                        {w for _, w in random_edges(node)[0]})
            assert {nodes[int(w)] for w in successors.split(',')} == expected
            assert int(p) == priority(node)
        report.append({'n': n, 'rows': len(rows), 'columns': len(order),
                       'matrix_entries': len(rows)*len(order), 'graph_vertices': len(nodes),
                       'all_exact_checks_passed': True})
    files = ['Definitions/Def_friedmann_cunningham.lean', 'checks/CunninghamExport.lean',
             'notes/cunningham_graph_audit.py', 'build-logs/CunninghamExport.log']
    result = {'method': 'Independent source-graph elimination compared with actual Lean #eval output',
              'universal_proof': False, 'cases': report,
              'sha256': {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in files}}
    (ROOT/'audits/cunningham-graph-comparison.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'all_passed': True, 'n': list(by_n),
                      'matrix_entries': sum(r['matrix_entries'] for r in report)}, indent=2))


if __name__ == '__main__':
    main()
