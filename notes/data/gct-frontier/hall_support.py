from itertools import permutations, product, combinations
from math import prod
from collections import Counter

cells = list(product(range(4), repeat=2))
def minor(rows, cols):
    r = [i for i in range(4) if i not in rows]
    c = [j for j in range(4) if j not in cols]
    return sum(prod(1 + (i == j) for i, j in zip(r, p)) for p in permutations(c))
def bordered():
    g = [minor({i}, {j}) for i,j in cells]
    h = [[minor({i,k}, {j,l}) if i != k and j != l else 0 for k,l in cells] for i,j in cells]
    return [row + [v] for row,v in zip(h,g)] + [g + [0]]
def det(a):
    """Fraction-free elimination with exact pivoting."""
    a = [r[:] for r in a]
    last, sign = 1, 1
    for k in range(len(a)-1):
        if not a[k][k]:
            r = next((r for r in range(k+1,len(a)) if a[r][k]),None)
            if r is None:
                return 0
            a[k], a[r] = a[r], a[k]
            sign = -sign
        piv = a[k][k]
        for i in range(k+1,len(a)):
            for j in range(k+1,len(a)):
                value, rem = divmod(a[i][j]*piv - a[i][k]*a[k][j], last)
                assert rem == 0
                a[i][j] = value
        last = piv
    return sign*a[-1][-1]
def restricted(b, holes):
    keep = [i for i in range(17) if i not in holes]
    return [[b[i][j] for j in keep] for i in keep]
if __name__ == "__main__":
    b = bordered()
    determinants = Counter(det(restricted(b, holes)) for holes in combinations(range(16),4))
    assert sum(determinants.values()) == 1820 and 0 not in determinants
    print("four-cell holes:", sum(determinants.values()))
    print("distinct exact determinants:", len(determinants))
    print("minimum absolute determinant:", min(map(abs, determinants)))
    print("maximum absolute determinant:", max(map(abs, determinants)))
    print("singular restrictions:", determinants[0])
