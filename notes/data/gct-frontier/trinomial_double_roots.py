"""Exact search for high multiplicities of three trinomial cubes at a common double root.

Scale the root to one and subtract the least input exponent from every exponent.
A nonzero trinomial with a double root then has coefficients fixed up to scale.
Three distinct exponent sums fix the three effective cube weights up to scale as
soon as moments six and seven vanish. Equal sums are covered by the Lean theorem.
"""

from argparse import ArgumentParser
from collections import Counter
from itertools import combinations, product
from math import comb, gcd, lcm


def cube_moments(support, highest=14):
    """Euler derivatives, with the second input derivative normalized to one."""
    a, b, c = support
    s, p, t = a+b+c, a*b+b*c+c*a, a*b*c
    moments = [0, 0, 1]
    while len(moments) <= highest:
        moments.append(s*moments[-1] - p*moments[-2] + t*moments[-3])

    def convolve(left, right):
        return [sum(comb(n, i)*left[i]*right[n-i] for i in range(n+1)) for n in range(highest+1)]

    return convolve(convolve(moments, moments), moments)


def verify_order(supports):
    """Expand the polynomial itself and check its Taylor coefficients independently."""
    centers = list(map(sum, supports))
    mass = [centers[(i+1) % 3] - centers[(i+2) % 3] for i in range(3)]
    rows = [(c-b, a-c, b-a) for a,b,c in supports]
    scales = [sum(x*e*e for x,e in zip(row,support))**3 for row,support in zip(rows,supports)]
    common = lcm(*scales)
    polynomial = Counter()
    for s, row, weight, scale in zip(supports, rows, mass, scales):
        for i,j,k in product(range(3), repeat=3):
            polynomial[s[i]+s[j]+s[k]] += weight*(common//scale)*row[i]*row[j]*row[k]
    for n in range(max(polynomial)+1):
        value = sum(c*comb(e,n) for e,c in polynomial.items() if e>=n)
        if value:
            return n
    return None


def count_distinct_means(supports):
    one = two = three = 0
    for size in Counter(map(sum, supports)).values():
        three += two*size
        two += one*size
        one += size
    return three


def scan(limit):
    supports = list(combinations(range(limit+1), 3))
    nodes = list(map(sum, supports))
    moments = [cube_moments(s) for s in supports]
    hits = Counter()
    best_order, best_example = 9, None
    for base, support in enumerate(supports):
        if support[0]:
            break
        x0, v0 = nodes[base], moments[base]
        groups = {}
        for j in range(base+1, len(supports)):
            dx = nodes[j]-x0
            if dx == 0:
                continue
            v = moments[j]
            y, z = v[8]-v0[8], v[9]-v0[9]
            divisor = gcd(dx,y,z) if dx>0 else -gcd(dx,y,z)
            key = dx//divisor, y//divisor, z//divisor
            group = groups.setdefault(key, [])
            for i in group:
                if nodes[i]==nodes[j]:
                    continue
                di, vi = nodes[i]-x0, moments[i]
                order = next((n for n in range(10,15) if di*(v[n]-v0[n]) != dx*(vi[n]-v0[n])), None)
                triple = (support, supports[i], supports[j])
                if order is None:
                    order = verify_order(triple)
                    if order is None:
                        hits["identically zero"] += 1
                        continue
                hits[order] += 1
                if order > best_order:
                    assert verify_order(triple) == order
                    best_order, best_example = order, triple
            group.append(j)
    positive_min = [s for s in supports if s[0]]
    total = comb(len(supports),3) - comb(len(positive_min),3)
    distinct = count_distinct_means(supports) - count_distinct_means(positive_min)
    return total, distinct, hits, best_order, best_example


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("span", type=int, help="maximum exponent after subtracting the least exponent")
    args = parser.parse_args()
    if args.span < 2:
        parser.error("span must be at least two")
    total, distinct, hits, best, example = scan(args.span)
    print("Normalized triples of distinct supports:", total)
    print("Triples with three distinct exponent sums:", distinct)
    print("Distinct-sum triples attaining order at least ten under their unique weights:", dict(hits))
    if example:
        print("Maximum order with distinct exponent sums:", best, "at", example)
    else:
        print("Distinct exponent sums give order at most nine in this range.")
