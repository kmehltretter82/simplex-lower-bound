"""Exact certificates for two issues in the source audit.

This file uses the n=3 conservation equations directly, not the existing LP
generator or pivot simulator. It checks finite rational witnesses only.
"""

from fractions import Fraction as Q
import json

N = 7
EPS = Q(1, N**8)
DEN = 2882401
ROWS = [('a', 2), ('a', 3), ('b', 2), ('c', 2), ('c', 3),
        ('d', 2), ('d', 3), ('e', 1), ('e', 2), ('e', 3)]
COLS = [(k, i, b) for k, i in ROWS for b in (0, 1)]


def lhs(x):
    def v(k, i, b):
        return x.get((k, i, b), Q(0))
    def own(k, i):
        return v(k, i, 0) + v(k, i, 1)
    def act(i):
        return sum(v(k, i, 1) for k in 'abcde')
    bottom = v('b', 2, 0) + v('c', 2, 0) + v('d', 2, 0) + v('e', 1, 1)
    return [
        own('a', 2) - EPS * bottom,
        own('a', 3) - v('a', 2, 0) - EPS * act(2),
        own('b', 2) - v('d', 3, 0),
        own('c', 2) - v('c', 3, 0),
        own('c', 3) - sum(v('e', i, 0) for i in (1, 2, 3)),
        own('d', 2) - (1 - EPS) / 2 * act(2),
        own('d', 3) - (1 - EPS) / 2 * act(3),
        own('e', 1) - (1 - EPS) * bottom,
        own('e', 2) - (1 - EPS) / 2 * act(2),
        own('e', 3) - (1 - EPS) / 2 * act(3),
    ]


def determinant(matrix):
    a = [list(row) for row in matrix]
    result = Q(1)
    for i in range(len(a)):
        pivot = next((j for j in range(i, len(a)) if a[j][i]), None)
        if pivot is None:
            return Q(0)
        if pivot != i:
            a[i], a[pivot] = a[pivot], a[i]
            result = -result
        d = a[i][i]
        result *= d
        for j in range(i + 1, len(a)):
            factor = a[j][i] / d
            for k in range(i, len(a)):
                a[j][k] -= factor * a[i][k]
    return result


def certificate(bits, numerators):
    basis = [(k, i, b) for (k, i), b in zip(ROWS, bits)]
    x = {col: Q(num, DEN) for col, num in zip(basis, numerators)}
    assert all(value > 0 for value in x.values())
    assert lhs(x) == [Q(1)] * len(ROWS)
    columns = [lhs({col: Q(1)}) for col in basis]
    det = determinant(list(map(list, zip(*columns))))
    assert det != 0
    alias_flow = sum(x.get((k, 2, 0), Q(0)) for k in 'bcd')
    return {
        'basis': ['%s%d^%d' % col for col in basis],
        'positive_basic_values': [str(x[col]) for col in basis],
        'basis_determinant': str(det),
        'alias_flow': str(alias_flow),
        'alias_objective_contribution': str((-N + EPS * N**2) * alias_flow),
    }


initial = certificate(
    [0, 0, 0, 0, 0, 1, 1, 1, 0, 0],
    [25941607, 28824009, DEN, 17294404, 14412003,
     5764801, 5764801, 132931713631201, 5764801, 5764801])
b2_one = certificate(
    [0, 0, 1, 0, 0, 1, 1, 1, 0, 0],
    [25941606, 28824009, DEN, 20176804, 17294403,
     8647201, 5764801, 132931707866401, 8647201, 5764801])
all_e_zero = certificate(
    [0, 0, 0, 0, 0, 1, 1, 0, 0, 0],
    [25941607, 28824009, DEN, 132931730925605, 132931728043204,
     5764801, 5764801, 132931713631201, 5764801, 5764801])
assert initial['alias_objective_contribution'] != b2_one['alias_objective_contribution']
print(json.dumps({
    'n': 3, 'N': N, 'epsilon': str(EPS),
    'method': 'direct rational substitution into all ten source conservation equations',
    'initial': initial, 'b2_one': b2_one, 'all_e_zero': all_e_zero,
    'conclusions': {
        'alias_contribution_not_constant_on_feasible_set': True,
        'all_e_zero_start_is_nonsingular_and_strictly_positive': True,
    },
}, indent=2))
