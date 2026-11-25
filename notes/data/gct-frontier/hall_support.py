"""Exact bordered Hessians of the four-by-four permanent at J + I.

PeaBrane proposed the bordered Hessian support test in project discussion 9114.
The program checks every choice of four missing cells and the three-cell boundary.
"""

from collections import Counter
from itertools import combinations, permutations, product
from math import prod

cells = list(product(range(4), repeat=2))


def minor(omitted_rows, omitted_columns):
    rows = [i for i in range(4) if i not in omitted_rows]
    columns = [j for j in range(4) if j not in omitted_columns]
    return sum(
        prod(1 + (i == j) for i, j in zip(rows, matching))
        for matching in permutations(columns)
    )


def bordered():
    gradient = [minor({i}, {j}) for i, j in cells]
    hessian = [
        [minor({i, k}, {j, l}) if i != k and j != l else 0 for k, l in cells]
        for i, j in cells
    ]
    return [row + [v] for row, v in zip(hessian, gradient)] + [gradient + [0]]


def det(matrix):
    """Fraction-free elimination with exact pivoting."""
    a = [row[:] for row in matrix]
    previous_pivot, sign = 1, 1
    for k in range(len(a) - 1):
        if not a[k][k]:
            swap_row = next((i for i in range(k + 1, len(a)) if a[i][k]), None)
            if swap_row is None:
                return 0
            a[k], a[swap_row] = a[swap_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, len(a)):
            for j in range(k + 1, len(a)):
                value, remainder = divmod(a[i][j] * pivot - a[i][k] * a[k][j], previous_pivot)
                assert remainder == 0
                a[i][j] = value
        previous_pivot = pivot
    return sign * a[-1][-1]


def restricted(matrix, holes):
    keep = [i for i in range(len(matrix)) if i not in holes]
    return [[matrix[i][j] for j in keep] for i in keep]


if __name__ == "__main__":
    b = bordered()
    determinants = Counter(det(restricted(b, holes)) for holes in combinations(range(16), 4))
    assert sum(determinants.values()) == 1820 and 0 not in determinants
    print("four-cell holes:", sum(determinants.values()))
    print("distinct exact determinants:", len(determinants))
    print("minimum absolute determinant:", min(map(abs, determinants)))
    print("maximum absolute determinant:", max(map(abs, determinants)))
    print("singular restrictions:", determinants[0])
    triples = Counter(det(restricted(b, holes)) for holes in combinations(range(16), 3))
    assert sum(triples.values()) == 560 and 0 not in triples
    print("three-cell holes:", sum(triples.values()))
    print("distinct exact determinants:", len(triples))
    print("singular restrictions:", triples[0])
