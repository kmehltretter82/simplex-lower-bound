"""Exact rational sanity checks of the §4.4 transcription; no theorem proof."""
from fractions import Fraction as Q
import sys


def solve(matrix, rhs):
    a = [list(row) + [v] for row, v in zip(matrix, rhs)]
    n = len(rhs)
    for i in range(n):
        p = next(k for k in range(i, n) if a[k][i])
        a[i], a[p] = a[p], a[i]
        z = a[i][i]
        a[i] = [x / z for x in a[i]]
        for k in range(n):
            if k != i:
                z = a[k][i]
                if z:
                    a[k] = [x - z * y for x, y in zip(a[k], a[i])]
    return [row[-1] for row in a]


def data(n, mode):
    N = 2 * n + 1
    ep = Q(1, N ** (2 * n + 2))
    rows = [(k, i) for k, indices in [
        ('a', range(2, n + 1)), ('b', range(2, n)),
        ('c', range(2, n + 1)), ('d', range(2, n + 1)),
        ('e', range(1, n + 1))] for i in indices]
    cols = [('e', 1, 1)] + [
        (k, i, b) for i in range(2, n + 1)
        for k, b in [('d', 0), ('e', 1)] +
        ([('b', 1), ('b', 0)] if i < n else [])
    ] + [('c', i, b) for i in range(2, n + 1) for b in [0, 1]] + [
        ('e', i, 0) for i in range(1, n + 1)
    ] + [('d', i, 1) for i in range(2, n + 1)] + [
        ('a', i, b) for i in range(n, 1, -1) for b in [1, 0]
    ]

    def coefficient(row, v):
        k, i = row
        x = lambda k, i, b: Q(v == (k, i, b))
        own = x(k, i, 0) + x(k, i, 1)
        active = sum(x(j, i, 1) for j in 'abcde')
        if k == 'a':
            if i == 2:
                return own - ep * (x('b', 2, 0) + x('c', 2, 0) +
                                   x('d', 2, 0) + x('e', 1, 1))
            return own - x('a', i - 1, 0) - ep * sum(x(j, i - 1, 1) for j in 'abcde')
        if k == 'b':
            return own - x('b', i + 1, 0) - x('d', i + 1, 0)
        if k == 'c':
            if i == n:
                return own - sum(x('e', j, 0) for j in range(1, n + 1))
            return own - x('c', i + 1, 0)
        if k == 'd':
            return own - (1 - ep) / 2 * active
        if k == 'e':
            if i == 1:
                return own - (1 - ep) * (x('b', 2, 0) + x('c', 2, 0) +
                                        x('d', 2, 0) + x('e', 1, 1))
            return own - (1 - ep) / 2 * active

    def cost(v):
        k, i, bit = v
        if mode in {'reward', 'display_reward'}:
            g, h, s = (-N) ** (2 * i - 1), N ** (2 * i), 1
        elif mode == 'priority':
            g, h, s = 2 * i - 1, 2 * i, 0
        elif mode == 'positive':
            g, h, s = N ** (2 * i - 1), N ** (2 * i), 1
        else:
            raise ValueError(mode)
        if mode == 'reward' and i == 2 and not bit and k in 'bcd':
            return Q(-N) + ep * N ** 2
        if k in 'abc' and bit:
            return g + ep * h
        if k in 'de' and bit:
            return ep * h
        return Q(s) if k == 'e' else Q(0)

    A = [[coefficient(row, v) for v in cols] for row in rows]
    c = [cost(v) for v in cols]
    initial = [cols.index((k, i, int(k == 'd' or k == 'e' and i == 1))) for k, i in rows]
    return rows, cols, A, c, initial


def check(n, mode='reward', verbose=False):
    rows, cols, A, c, basis = data(n, mode)
    last = 0
    t = 0
    seen = set()
    previous = None
    while True:
        matrix = [[r[j] for j in basis] for r in A]
        xb = solve(matrix, [Q(1)] * len(rows))
        assert min(xb) > 0
        val = sum(c[j] * x for j, x in zip(basis, xb))
        assert previous is None or previous < val
        previous = val
        dual = solve(list(map(list, zip(*matrix))), [c[j] for j in basis])
        rc = [c[j] - sum(y * r[j] for y, r in zip(dual, A)) for j in range(len(cols))]
        improving = [j for j in range(len(cols)) if j not in basis and rc[j] > 0]
        if not improving:
            break
        j = min(improving, key=lambda j: (j + len(cols) - last) % len(cols))
        direction = solve(matrix, [r[j] for r in A])
        leaving = min((i for i in range(len(rows)) if direction[i] > 0),
                      key=lambda i: xb[i] / direction[i])
        if verbose:
            print(t, cols[j], 'out', cols[basis[leaving]])
        basis[leaving] = j
        last = j
        t += 1
        signature = tuple(basis)
        assert signature not in seen
        seen.add(signature)
        if t > 100000:
            raise RuntimeError('run exceeded sanity-check cap')
    result = {'n': n, 'mode': mode, 'rows': len(rows), 'cols': len(cols),
              'pivots': t, 'bound': 2 ** n, 'strict': True}
    print(result)
    return result


if __name__ == '__main__':
    for n in [3, 4, 5, 6]:
        check(n, sys.argv[1] if len(sys.argv) > 1 else 'reward')
