"""Exact coefficient elimination for a root of order at least ten in three binomial cubes.

Translate the smallest input exponent to zero, rescale the positive root to one,
and permute the three inputs. Only exponent patterns are enumerated. All
coefficient calculations, including the real-root test, use integer arithmetic.
"""

from argparse import ArgumentParser
from collections import Counter
from itertools import combinations
from math import comb, gcd, lcm, prod


def multiply_linear(f, g):
    """Coefficients of the product in the basis A^2, A*B, B^2."""
    a, b = f
    c, d = g
    return a*c, a*d + b*c, b*d


def cross(v, w):
    a, b, c = v
    x, y, z = w
    return b*z - c*y, c*x - a*z, a*y - b*x


def cubic_equations(forms):
    """Three quadratic equations characterize four nonzero coefficients of a cube."""
    for start in range(0, 12, 4):
        v = forms[start:start + 4]
        for i, j, k, m, factor in ((1, 1, 0, 2, 3), (2, 2, 1, 3, 3), (1, 2, 0, 3, 9)):
            lhs = multiply_linear(v[i], v[j])
            rhs = multiply_linear(v[k], v[m])
            yield tuple(x - factor*y for x, y in zip(lhs, rhs))


def possible_line(q, forbidden):
    """Can a nonzero real projective pair satisfy one quadratic and avoid the lines?"""
    a, b, c = q
    if not any(q):
        return True
    if c == 0 and all(y != 0 for x, y in forbidden):
        return True  # The projective point A = 0.
    if c == 0:
        return b != 0 and all(b*x - a*y != 0 for x, y in forbidden)
    discriminant = b*b - 4*a*c
    if discriminant < 0:
        return False
    forbidden_roots = set()
    for x, y in forbidden:
        if y and a*y*y - b*x*y + c*x*x == 0:
            d = gcd(x, y)
            sign = 1 if y > 0 else -1
            forbidden_roots.add((sign*x//d, sign*y//d))
    return len(forbidden_roots) < (1 if discriminant == 0 else 2)


def has_admissible_zero(forms, one_collision):
    """Intersect the quadratic equations in [A:B] and exclude zero input coefficients."""
    forbidden = list(forms)
    if one_collision:
        forbidden.append((1, 0))  # At A=0 all aggregate coefficients vanish.
    if (0, 0) in forbidden:
        return False
    first = None
    null = None
    for row in cubic_equations(forms):
        if not any(row):
            continue
        if first is None:
            first = row
        elif null is None:
            candidate = cross(first, row)
            if any(candidate):
                # Two independent equations fix [A^2 : A*B : B^2].
                u, v, w = candidate
                if v*v != u*w:
                    return False
                null = candidate
        elif sum(x*y for x, y in zip(null, row)) != 0:
            return False
    if null is None:
        return possible_line(first or (0, 0, 0), forbidden)
    u, v, w = null
    A, B = (u, v) if u != 0 else (0, 1)
    return all(x*A + y*B != 0 for x, y in forbidden)


def check_pattern(slots):
    """Find the nullspace of the ten Euler derivatives at one by interpolation.

    With N distinct exponents and D_e = product(f != e) (e-f), the vector
    (e^j / D_e) has its first N-1-j moments zero. The Vandermonde matrix
    has row rank ten when N >= 10. For twelve exponents the nullspace
    consists of (A+B*e)/D_e. For eleven it consists of A/D_e on the
    aggregate coefficients. One additional parameter splits the collision.
    """
    exponents = set(slots)
    if len(exponents) < 11:
        return "at most ten distinct powers"
    denominators = {e: prod(e-f for f in exponents if f != e) for e in exponents}
    common = lcm(*denominators.values())
    weights = {e: common//d for e, d in denominators.items()}
    collision = len(exponents) == 11
    if collision:
        shared = next(e for e in exponents if slots.count(e) == 2)
        i, j = slots.index(shared), len(slots)-1-slots[::-1].index(shared)
        forms = [(weights[e], 0) for e in slots]
        forms[i], forms[j] = (weights[shared], 1), (0, -1)
    else:
        forms = [(weights[e], e*weights[e]) for e in slots]
    if has_admissible_zero(forms, collision):
        return "admissible coefficient solution"
    return "one collision excluded" if collision else "disjoint supports excluded"


def scan(limit):
    """Enumerate unordered triples of distinct binomial supports with minimum exponent zero."""
    pairs = list(combinations(range(limit+1), 2))
    blocks = {(a, b): (3*a, 2*a+b, a+2*b, 3*b) for a, b in pairs}
    totals = Counter()
    for p, q, r in combinations(pairs, 3):
        if p[0] != 0:
            break
        result = check_pattern(blocks[p]+blocks[q]+blocks[r])
        totals[result] += 1
        if result == "admissible coefficient solution":
            print("candidate", p, q, r, flush=True)
    expected = comb(len(pairs), 3) - comb(len(pairs) - limit, 3)
    assert sum(totals.values()) == expected
    return totals


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("limit", type=int, help="maximum input exponent after common translation")
    args = parser.parse_args()
    if args.limit < 1:
        parser.error("limit must be positive")
    counts = scan(args.limit)
    for outcome, count in sorted(counts.items()):
        print(f"{outcome}: {count}")
    print("Total normalized support triples:", sum(counts.values()))
