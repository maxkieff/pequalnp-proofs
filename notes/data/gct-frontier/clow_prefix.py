"""Exact checks for the closed-walk prefix obstruction. Uses the standard library."""

from collections import Counter, defaultdict
from fractions import Fraction
from functools import cache
from itertools import combinations
from math import comb, isqrt

from clow_moments import cover, walk_groups


def permanent(rows):
    """Expand on the sparsest row, including forced rows in the large examples."""
    if not rows:
        return 1
    pivot = min(range(len(rows)), key=lambda i: sum(bool(a) for a in rows[i]))
    return sum(
        a * permanent([r[:j] + r[j + 1:] for i, r in enumerate(rows) if i != pivot])
        for j, a in enumerate(rows[pivot]) if a
    )


def embed(n, addresses, columns, root, entries, forced):
    """The remaining singleton rows force row zero to take the column 'forced'."""
    assert forced in addresses and forced not in columns
    rows = [[0] * n for _ in range(n)]
    for i, a in enumerate(addresses):
        rows[0][a] = root[i]
        for j, b in enumerate(columns):
            rows[a][b] = entries[i][j]
    free_rows = sorted(set(range(1, n)) - set(addresses))
    free_cols = sorted(set(range(n)) - set(columns) - {forced})
    for i, j in zip(free_rows, free_cols, strict=True):
        rows[i][j] = 1
    return rows


def six_row_tests():
    addresses = (1, 2, 3, 4)
    cols = (2, 3, 4, 5)
    z = (-1, 3, -3, 1)
    rows = embed(6, addresses, cols, (1,) * 4, [[a] * 4 for a in z], 1)
    for b in cols:
        for k in range(3):
            assert sum(rows[0][i] * rows[i][b] * i**k for i in addresses) == 0
    assert permanent(rows) == 216

    grid = []
    for a in addresses:
        values = []
        for t in addresses:
            x = [[0] * 6 for _ in range(6)]
            x[0][a] = x[5][0] = 1
            for i in addresses:
                for b in range(1, 6):
                    x[i][b] = int(t != b)
            values.append(permanent(x))
        grid.append(values)
    assert grid == [[24 * int(a == t) for t in addresses] for a in addresses]
    print("six rows: quadratic encoding gives 0, permanent 216; shared-vector grid is 24 I_4")


def balance(exponents):
    """Maximum-weight assignment with row quotas 1,3,..., and its dual potentials."""
    s, n = len(exponents), len(exponents[0])
    quota = tuple(2 * i + 1 for i in range(s))
    assert n == sum(quota)

    @cache
    def optimum(remaining):
        j = n - sum(remaining)
        if j == n:
            return 0, ()
        options = []
        for i, left in enumerate(remaining):
            if left:
                next_counts = remaining[:i] + (left - 1,) + remaining[i + 1:]
                value, owners = optimum(next_counts)
                options.append((exponents[i][j] + value, (i,) + owners))
        return max(options)

    _, owners = optimum(quota)
    potential = [0] * s
    for _ in range(s - 1):
        previous = potential[:]
        for j, k in enumerate(owners):
            for i in range(s):
                potential[i] = max(potential[i], previous[k] + exponents[i][j] - exponents[k][j])
    tight = [
        [exponents[i][j] - potential[i] - exponents[k][j] + potential[k]
         for j, k in enumerate(owners)]
        for i in range(s)
    ]
    assert all(e <= 0 for row in tight for e in row)
    assert all(tight[k][j] == 0 for j, k in enumerate(owners))
    return potential, tight


def scaled_example():
    s, width, n = 4, 3, 21
    cols = tuple(range(5, n))
    addresses = tuple(range(1, 5))
    exponent = [[(11 * i + 5 * j + 3 * i * j + i * j * j) % 19 - 9
                 for j in range(len(cols))] for i in range(s)]
    signs = [[(-1) ** ((i + 2) * (j + 1) % 5) for j in range(len(cols))] for i in range(s)]
    potential, tight = balance(exponent)
    limit = [[signs[i][j] * (e == 0) for j, e in enumerate(row)] for i, row in enumerate(tight)]
    subset, target = next(
        (subset, value) for subset in combinations(range(len(cols)), s)
        if (value := permanent([[row[j] for j in subset] for row in limit]))
    )
    anchor = potential.index(max(potential))
    for base in (Fraction(2), Fraction(7)):
        raw = [[signs[i][j] * base ** exponent[i][j] for j in subset] for i in range(s)]
        x = [[signs[i][j] * base ** tight[i][j] for j in subset] for i in range(s)]
        root = [base ** (v - max(potential)) for v in potential]
        assert root[anchor] == 1 and all(abs(a) <= 1 for row in x for a in row)
        for j in range(s):
            for k in range(width):
                # These three coordinates make raw[:,j] an exact kernel vector.
                p = [raw[-1][j] * (i == k) if i < width else -raw[k][j] for i in range(s)]
                assert sum(p[i] * raw[i][j] for i in range(s)) == 0
                assert sum(p[i] * root[i] * x[i][j] for i in range(s)) == 0
        full = embed(n, addresses, [cols[j] for j in subset], root, x, addresses[anchor])
        assert permanent(full) == permanent(x)
    print("21-row bounded witness: column labels", tuple(cols[j] for j in subset),
          "forced root label", addresses[anchor], "limiting permanent", target)


def rank_mod(equations, modulus):
    """Row rank by sparse Gaussian elimination over a prime field."""
    pivots = {}
    for equation in equations:
        row = {i: a % modulus for i, a in equation.items() if a % modulus}
        while row:
            i = min(row)
            if i not in pivots:
                inverse = pow(row[i], -1, modulus)
                pivots[i] = {j: a * inverse % modulus for j, a in row.items()}
                break
            multiple = row[i]
            for j, a in pivots[i].items():
                value = (row.get(j, 0) - multiple * a) % modulus
                if value:
                    row[j] = value
                else:
                    row.pop(j, None)
    return len(pivots)


def single_cut_six():
    """Recover the entire cut matrix when all other cuts use the exact history program."""
    n = 6
    groups = walk_groups(n)
    covers = [paths[0] for key, paths in groups.items() if cover(key, n)]
    assert len(covers) == 720 and all(len(groups[tuple(sorted((i, j) for _, i, j, _ in p))]) == 1
                                      for p in covers)
    for k, expected in ((2, (4, 72)), (3, (6, 210)), (4, (4, 110))):
        starts = {p[:k] for p in covers}
        ends = {p[k:] for p in covers}
        histories = defaultdict(set)
        equations = []
        off_diagonal = set()
        diagonal = set()
        for key, paths in groups.items():
            eq = Counter()
            for p in paths:
                if p[:k] not in starts or p[k:] not in ends:
                    continue
                h, _, v, g = p[k - 1]
                state = (g, g) if v == h else (h, v)
                a = frozenset(i for _, i, _, _ in p[:k])
                b = frozenset(range(n)) - frozenset(i for _, i, _, _ in p[k:])
                slot = (state, tuple(sorted(a)), tuple(sorted(b)))
                if cover(key, n):
                    assert a == b
                    diagonal.add(slot)
                    histories[state].add(slot[1])
                else:
                    assert a != b
                    eq[slot] += 1
                    off_diagonal.add(slot)
            if eq:
                equations.append(eq)
        assert all((state, a, b) in diagonal | off_diagonal for state, hs in histories.items()
                   for a in hs for b in hs)
        peak = max(map(len, histories.values()))
        rank = rank_mod(equations, 101)
        assert (peak, rank) == expected and rank == len(off_diagonal)
        print("six-row cut", k, "peak history width", peak, "off-diagonal rank", rank)


def spectator_projection():
    """Check equality of path sets, including all nonmatching paths, after extraction."""
    n = 6
    walks = [p for paths in walk_groups(n).values() for p in paths]
    tests = 0
    for t in range(1, 4):
        small = [p for paths in walk_groups(n - t).values() for p in paths]
        for h in range(1, t + 1):
            for extra in combinations(range(h + 1, n), t - h):
                cycle = tuple(range(h)) + extra
                active = tuple(sorted(set(range(n)) - set(cycle)))
                arcs = list(zip(cycle, cycle[1:] + cycle[:1]))
                prefix = tuple((0, i, j, h if j == 0 else 0) for i, j in arcs)
                expected = {
                    prefix + tuple((active[a], active[i], active[j], active[g] if g >= 0 else -1)
                                   for a, i, j, g in p)
                    for p in small
                }
                actual = set()
                for p in walks:
                    edges = [(i, j) for _, i, j, _ in p]
                    if sum(i == h for i, _ in edges) != 1:
                        continue
                    if sorted((i, j) for i, j in edges if i not in active or j not in active) == sorted(arcs):
                        actual.add(p)
                assert expected == actual
                tests += 1
    print("six-row spectator projections checked on all paths:", tests)


def state_bound(m):
    direct = 0
    closed = 0
    for s in range(1, (isqrt(4 * m - 3) - 1) // 2 + 1):
        tmax = m - s * s - s - 1
        direct += m - s * s
        direct += sum(m - h - s * s for t in range(1, tmax + 1) for h in range(1, t + 1))
        closed += (m - s * s) * (1 + comb(tmax + 1, 2)) - comb(tmax + 2, 3)
    assert direct == closed
    return closed


if __name__ == "__main__":
    six_row_tests()
    scaled_example()
    single_cut_six()
    spectator_projection()
    for m, expected in ((21, 3871), (69, 325715), (70, 343257), (71, 361464), (100, 1252371)):
        result = state_bound(m)
        assert result == expected, (m, result)
        print("rows", m, "internal-coordinate lower bound", result, "cubic budget", m**3)
