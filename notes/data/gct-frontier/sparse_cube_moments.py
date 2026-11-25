"""Compute the sparse cube examples from equal moments of integer exponent sets."""

from collections import defaultdict
from fractions import Fraction
from functools import reduce
from itertools import combinations, product
from math import comb, gcd, lcm, prod


def equal_moment_triple(size, largest_allowed):
    groups = defaultdict(list)
    for top in range(size - 1, largest_allowed + 1):
        for initial in combinations(range(top), size - 1):
            exponents = initial + (top,)
            moments = tuple(sum(e**j for e in exponents) for j in range(1, size))
            group = groups[moments]
            group.append(exponents)
            if len(group) == 3:
                return group
    raise ValueError("No triple within the exponent bound")


def integer_carrier(exponents):
    weights = [Fraction(1, prod(e - f for f in exponents if f != e)) for e in exponents]
    denominator = lcm(*(weight.denominator for weight in weights))
    return dict(zip(exponents, (int(weight * denominator) for weight in weights)))


def cube(poly):
    result = defaultdict(int)
    for i, j, k in product(poly, repeat=3):
        result[i + j + k] += poly[i] * poly[j] * poly[k]
    return result


def taylor_at_one(poly, order):
    return sum(value * comb(e, order) for e, value in poly.items() if e >= order)


def example(size, exponent_bound):
    exponents = equal_moment_triple(size, exponent_bound)
    carriers = [integer_carrier(row) for row in exponents]
    cubes = [cube(poly) for poly in carriers]
    base_order = 3 * (size - 1)
    first = [taylor_at_one(poly, base_order) for poly in cubes]
    later = [taylor_at_one(poly, base_order + size) for poly in cubes]
    weights = [
        first[(i+1) % 3] * later[(i+2) % 3] - first[(i+2) % 3] * later[(i+1) % 3]
        for i in range(3)
    ]
    divisor = reduce(gcd, weights)
    weights = [weight // divisor for weight in weights]
    for order in range(3 * exponent_bound + 1):
        coefficient = sum(weight * taylor_at_one(poly, order) for weight, poly in zip(weights, cubes))
        if coefficient:
            return exponents, weights, order, coefficient
    raise ArithmeticError("The weighted cube sum was zero")


if __name__ == "__main__":
    for size, bound in ((2, 5), (3, 16), (4, 25)):
        knots, weights, order, coefficient = example(size, bound)
        assert order == 5 * size - 3
        print(f"{size} terms: exponents {knots}, cube weights {weights}")
        print(f"  order {order} at 1, first nonzero Taylor coefficient {coefficient}")
