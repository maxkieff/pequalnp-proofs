"""Check the four-row cube-root family and certify its inclusion-maximality.

All evaluations for containment take place in Z[w], w^2+w+1=0.
For the extension obstruction we certify a unit minor and a nonzero
quadratic coefficient after the specialization w -> 3 modulo 13.
Run with Python 3, without third-party packages.
"""

from itertools import combinations, permutations
from math import perm


def simplex(n, degree):
    if not n:
        yield ()
        return
    for i in range(degree + 1):
        for tail in simplex(n - 1, degree - i):
            yield (i, *tail)


def family_point(q, params):
    """J plus the perturbation, with entries in the basis (1, w)."""
    top = [*params[:q - 1], -sum(params[:q - 1])]
    rows = [[(1 + x, 0) for x in top]] + [[(1, 0)] * q for _ in range(3)]
    one, w, w2 = (1, 0), (0, 1), (-1, -1)
    for block, weights in enumerate(((one, w, w2), (one, w2, w))):
        for row, (a, b) in enumerate(weights, 1):
            x = params[q - 1 + block]
            rows[row][2 * block] = (1 + a*x, b*x)
            rows[row][2 * block + 1] = (1 - a*x, -b*x)
    return rows


def permanent(rows, injections):
    real = omega = 0
    for cols in injections:
        a, b = rows[0][cols[0]]
        for i in (1, 2, 3):
            c, d = rows[i][cols[i]]
            a, b = a*c - b*d, a*d + b*c - b*d
        real += a
        omega += b
    return real, omega


def gradient(rows, injections):
    q = len(rows[0])
    result = [0] * (4*q)
    for cols in injections:
        a, b, c, d = (rows[i][cols[i]] for i in range(4))
        for i, term in enumerate((b*c*d, a*c*d, a*b*d, a*b*c)):
            result[i*q + cols[i]] += term
    return [x % 13 for x in result]


def insert(basis, equation):
    """Echelon reduction modulo 13, including the last (right-hand-side) entry."""
    row = equation.copy()
    for i in range(len(row) - 1):
        if row[i] == 0:
            continue
        if i not in basis:
            scale = pow(row[i], -1, 13)
            basis[i] = [x * scale % 13 for x in row]
            return
        scale = row[i]
        row = [(x - scale*y) % 13 for x, y in zip(row, basis[i])]
    assert row[-1] == 0


def verify(q):
    injections = list(permutations(range(q), 4))
    for params in simplex(q + 1, 4):
        assert permanent(family_point(q, params), injections) == (perm(q, 4), 0)

    size = 4*q
    basis = {}
    for params in simplex(q + 1, 3):
        point = [[(a + 3*b) % 13 for a, b in row] for row in family_point(q, params)]
        insert(basis, gradient(point, injections) + [0])
    tangent_rank = len(basis)
    # Subtract a family member to zero its q+1 free coordinates.
    # The final coordinate is untouched by this subtraction.
    for i in [*range(q - 1), q, q + 2, size - 1]:
        equation = [0] * (size + 1)
        equation[i] = 1
        equation[-1] = int(i == size - 1)
        insert(basis, equation)
    assert len(basis) == size
    solution = [0] * size
    for i in reversed(range(size)):
        row = basis[i]
        solution[i] = (row[-1] - sum(x*y for x, y in zip(row[i+1:-1], solution[i+1:]))) % 13
    quadratic = sum(solution[i*q + j] * solution[k*q + l]
                    for i, k in combinations(range(4), 2)
                    for j, l in permutations(range(q), 2)) % 13
    assert (tangent_rank, quadratic) == {6: (16, 2), 7: (19, 8)}[q]
    print(f"4 x {q}: level family dimension {q+1}, gradient rank mod 13 {tangent_rank}, "
          f"quadratic obstruction {quadratic} mod 13")


if __name__ == "__main__":
    verify(6)
    verify(7)
