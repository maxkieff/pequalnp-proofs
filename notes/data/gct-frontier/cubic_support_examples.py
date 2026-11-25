"""Exact experiments for the c=3 case of L-gct-011. Uses the Python standard library."""

from collections import Counter
from fractions import Fraction
from itertools import combinations, combinations_with_replacement
from math import comb, factorial, prod


def live_layers(rows):
    """Column subsets on at least one complete matching path in this row order."""
    full = (1 << len(rows)) - 1

    def reachable(order):
        levels = [{0}]
        for allowed in order:
            following = set()
            for used in levels[-1]:
                available = allowed & ~used
                while available:
                    bit = available & -available
                    following.add(used | bit)
                    available ^= bit
            levels.append(following)
        return levels

    prefix = reachable(rows)
    suffix = reachable(reversed(rows))
    return [left & {full ^ unused for unused in right}
            for left, right in zip(prefix, reversed(suffix))]


def determinant_size(layers):
    return sum(map(len, layers)) - 1


def subset_minor(weights, layers):
    """Signed source-to-sink cofactor of I minus the weighted adjacency matrix."""
    vertices = [v for layer in layers for v in sorted(layer)]
    size = len(vertices) - 1
    columns = {v: j for j, v in enumerate(vertices[1:])}
    matrix = [[0] * size for _ in range(size)]
    for i, state in enumerate(vertices[:-1]):
        if state in columns:
            matrix[i][columns[state]] = 1
        for j, weight in enumerate(weights[state.bit_count()]):
            bit = 1 << j
            destination = state | bit
            if not state & bit and destination in columns:
                matrix[i][columns[destination]] -= weight
    if size % 2:
        matrix[0] = [-x for x in matrix[0]]
    return matrix


def determinant(matrix):
    """Bareiss elimination over the integers, with row pivoting."""
    matrix = [row[:] for row in matrix]
    n = len(matrix)
    sign = previous = 1
    for k in range(n - 1):
        pivot_row = next((i for i in range(k, n) if matrix[i][k]), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            matrix[k], matrix[pivot_row] = matrix[pivot_row], matrix[k]
            sign = -sign
        pivot = matrix[k][k]
        for i in range(k + 1, n):
            multiplier = matrix[i][k]
            for j in range(k + 1, n):
                value = pivot * matrix[i][j] - multiplier * matrix[k][j]
                matrix[i][j], remainder = divmod(value, previous)
                assert remainder == 0
            matrix[i][k] = 0
        previous = pivot
    return sign * matrix[-1][-1]


def permanent(matrix):
    """Expand row by row, keeping the total for each set of used columns."""
    partial = {0: 1}
    for row in matrix:
        following = {}
        for j, weight in enumerate(row):
            if weight:
                bit = 1 << j
                for used, total in partial.items():
                    if not used & bit:
                        key = used | bit
                        following[key] = following.get(key, 0) + weight * total
        partial = following
    return partial.get((1 << len(matrix)) - 1, 0)


def band_rows(m, width):
    return [sum(1 << j for j in range(m) if abs(i - j) <= width) for i in range(m)]


def masked_rows(m, deleted, order=None):
    rows = [(1 << m) - 1] * m
    for i, j in deleted:
        rows[i] &= ~(1 << j)
    return rows if order is None else [rows[i] for i in order]


def schur_moments(weights, layers):
    """c T^j b for the internal states of the subset graph, j = 0,...,m-1."""
    m = len(weights)
    full = (1 << m) - 1
    internal = set().union(*layers[1:-1])
    row = {1 << j: weights[0][j] for j in range(m) if 1 << j in internal}
    moments = []
    for _ in range(m):
        tail = 0
        following = {}
        for state, coefficient in row.items():
            for j, weight in enumerate(weights[state.bit_count()]):
                bit = 1 << j
                if state & bit:
                    continue
                destination = state | bit
                if destination == full:
                    tail += coefficient * weight
                elif destination in internal:
                    following[destination] = following.get(destination, 0) + coefficient * weight
        moments.append(tail)
        row = following
    return moments


def verify_minor(rows):
    m = len(rows)
    weights = [[((5 * i + 3 * j + 4) % 11 - 5) if rows[i] >> j & 1 else 0
                for j in range(m)] for i in range(m)]
    layers = live_layers(rows)
    minor = subset_minor(weights, layers)
    value = determinant(minor)
    assert value == permanent(weights)
    moments = schur_moments(weights, layers)
    assert moments == [0] * (m - 2) + [value, 0]
    return len(minor), value, moments


def simplex_examples(m):
    count = matches = failures_at_two = repaired_failures = 0
    denom = 2**m
    for mass in range(m + 1):
        for entries in combinations_with_replacement(range(m*m), mass):
            matrix = [[0] * m for _ in range(m)]
            for e in entries:
                matrix[e // m][e % m] += 1
            target = permanent(matrix)
            row_sums = list(map(sum, matrix))
            diagonal = prod(row_sums) * prod(map(sum, zip(*matrix)))
            assert target == diagonal
            count += 1
            matches += target != 0
            failures_at_two += denom * target != denom**2 * diagonal
            # Linear interpolant for t^(-m) at 1 and 2, evaluated on the first row sum.
            for t in (1, 2):
                factor = 2*denom - 1 + (1 - denom)*t*row_sums[0]
                repaired_failures += t**(2*m)*diagonal*factor != denom*t**m*target
    assert (count, matches) == (comb(m*m + m, m), factorial(m))
    assert failures_at_two == matches and repaired_failures == 0
    return count, matches, failures_at_two, repaired_failures


def cut_ranks(m, triples):
    """Verify identity submatrices on row-basis inputs at every row cut."""
    masks = [sum(1 << (m*i+j) for i, j in triple) for triple in triples]
    ranks = []
    total = 0
    for k in range(m + 1):
        subsets = list(combinations(range(m), k))
        prefixes = [sum(1 << (m*i+j) for i, j in enumerate(s)) for s in subsets]
        tails = [tuple(j for j in range(m) if j not in s) for s in subsets]
        suffixes = [sum(1 << (m*i+j) for i, j in enumerate(t, k)) for t in tails]
        for s, prefix in zip(subsets, prefixes):
            for t, tail, suffix in zip(subsets, tails, suffixes):
                assert (len(set(s + tail)) == m) == (s == t)
                assert any((prefix | suffix) & deleted == 0 for deleted in masks)
                total += 1
        ranks.append(len(subsets))
    assert total == comb(2*m, m)
    return ranks, total


def three_zero_sizes(m):
    """Compare all placements of three zeros in a column with the two end runs."""
    sizes = Counter()
    for rows in combinations(range(m), 3):
        front = next(i for i in range(m) if i not in rows)
        back = next(i for i in range(m) if m-1-i not in rows)
        predicted = 2**m - 1 - sum(comb(m-1, k) for end in (front, back) for k in range(end))
        actual = determinant_size(live_layers(masked_rows(m, {(i, 0) for i in rows})))
        assert actual == predicted
        sizes[actual] += 1
    minimum = min(sizes)
    assert minimum == 2**m - 1 - sum(comb(m-1, k) for k in range(3))
    assert sizes[minimum] == 2
    return sizes


def ten_by_ten():
    m = 10
    triples = [{((j + d) % m, j) for d in range(3)} for j in range(m)]
    triples.append({(i, 0) for i in (3, 4, 5)})
    assert len(set.union(*triples)) == 33
    for deleted in triples:
        first = sorted(i for i, _ in deleted)
        order = first + [i for i in range(m) if i not in first]
        layers = live_layers(masked_rows(m, deleted, order))
        assert list(map(len, layers)) == [1, 9, 36, 84, 210, 252, 210, 120, 45, 10, 1]
    # A permutation monomial missed by the first ten must use a deleted entry
    # in each of their ten different columns.
    forbidden = set.union(*triples[:m])
    invisible = permanent([[int((i, j) in forbidden) for j in range(m)] for i in range(m)])
    assert invisible == 125
    print("11 disjoint triples; size on each =", determinant_size(layers))
    print("Matching monomials unseen after 10, then 11 triples:", invisible, 0)
    counts = three_zero_sizes(m)
    assert sum(n for size, n in counts.items() if size <= 1001) == 2
    print("Sizes for all 120 three-row choices in one column, fixed row order:", sorted(counts.items()))
    # Each order can put two distinct triples at its ends. Five orders realize
    # all ten distinct cyclic row triples, including the extra use of rows 3,4,5.
    covered = set()
    for j in range(5):
        front = sorted(i for i, _ in triples[j])
        back = sorted(i for i, _ in triples[j+5])
        middle = [i for i in range(m) if i not in front and i not in back]
        order = front + middle + back
        assert len(set(order)) == len(order) == m
        for index, deleted in enumerate(triples):
            if determinant_size(live_layers(masked_rows(m, deleted, order))) <= 1001:
                covered.add(index)
    assert covered == set(range(11))
    ranks, pairs = cut_ranks(m, triples)
    print("Row-cut ranks, total required vertices, tested pairs:", ranks, sum(ranks), pairs)


def main():
    print("Full support: m, cofactor size, cubic target")
    for m in range(1, 13):
        n = determinant_size(live_layers([(1 << m) - 1] * m))
        assert n == 2**m - 1
        print(m, n, m**3 + 1)
    print("Bandwidth two: m, layer sizes, cofactor size")
    for m in (6, 8, 10, 12):
        layers = live_layers(band_rows(m, 2))
        print(m, list(map(len, layers)), determinant_size(layers))
        assert determinant_size(layers) == 6*m - 11
    print("Three zeros in one column: m, optimal row-ordered cofactor, cubic target")
    for m in (4, 8, 9, 11, 12):
        print(m, min(three_zero_sizes(m)), m**3 + 1)
    print("Independent integer checks: determinant size, common value, Schur moments")
    for rows in ([7]*3, [15]*4, [31]*5, band_rows(10, 2)):
        print(*verify_minor(rows))
    ten_by_ten()
    print("Simplex: m, points, nonzero permanents, errors at 2, repaired errors at 1 and 2")
    for m in range(2, 6):
        print(m, *simplex_examples(m))
    print("At t I_4: t, permanent, product of row/column sums, two-scale interpolant")
    for t in range(1, 4):
        print(t, t**4, t**8, Fraction(t**8*(31 - 15*t), 16))


if __name__ == "__main__":
    main()
