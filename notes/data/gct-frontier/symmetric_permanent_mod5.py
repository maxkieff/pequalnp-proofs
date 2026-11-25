"""Exhaust the symmetric four-by-four permanent level space over F_5.

Run with Python 3. The three output counts concern vector dimensions
one, two, and three. Only the Python standard library is required.
"""

from itertools import permutations, product


SIZE = 4
FIELD = range(5)
POSITIONS = [(i, i) for i in range(SIZE)] + [
    (i, j) for i in range(SIZE) for j in range(i + 1, SIZE)
]
PERM_TERMS = [
    [POSITIONS.index(tuple(sorted((i, j)))) for i, j in enumerate(perm)]
    for perm in permutations(range(SIZE))
]


def permanent(entries):
    return sum(entries[a] * entries[b] * entries[c] * entries[d]
               for a, b, c, d in PERM_TERMS) % 5


def level_directions():
    """Normalize the first nonzero one of nine independent coordinates."""
    for first in range(9):
        for tail in product(FIELD, repeat=8-first):
            x = (0,) * first + (1,) + tail
            a, b, c, e, f, g, h, i, j = x
            # The linear coefficient fixes the remaining diagonal entry.
            d = -(a + b + c + 2*(e + f + g + h + i + j)) % 5
            entries = (a, b, c, d, e, f, g, h, i, j)
            row_sums = (a+e+f+g, b+e+h+i, c+f+h+j, d+g+i+j)
            quad = (sum(z*z for z in entries[:4])
                    + 2*sum(z*z for z in entries[4:])
                    - 2*sum(z*z for z in row_sums))
            if quad % 5:
                continue
            # The two remaining coefficients have opposite/same parity.
            if all(permanent([1 + t*z for z in entries]) == 24 % 5
                   for t in (1, -1)):
                yield x


# One four-bit digit per independent coordinate. A sum of two base-field
# digits is at most 8. Adding 3 sets bit 3 exactly when that sum is >= 5.
ONES = sum(1 << (4*i) for i in range(9))


def pack(x):
    return sum(z << (4*i) for i, z in enumerate(x))


def add(x, y):
    total = x+y
    carries = ((total + 3*ONES) & (8*ONES)) >> 3
    return total - 5*carries


def enumerate_subspaces():
    for a, b in product(FIELD, repeat=2):
        assert add(a*ONES, b*ONES) == ((a+b) % 5)*ONES

    points = list(level_directions())
    multiples = [[pack([(a*z) % 5 for z in point]) for a in range(1, 5)]
                 for point in points]
    index = {v: rank for rank, orbit in enumerate(multiples) for v in orbit}
    assert len(index) == 4*len(points)

    lines = []
    adjacent = [set() for _ in points]
    for i, orbit in enumerate(multiples):
        x = orbit[0]
        for j in range(i+1, len(points)):
            line = [i, j]
            for multiple in multiples[j]:
                k = index.get(add(x, multiple))
                # Record each line once, from its two least points.
                if k is None or k < j:
                    break
                line.append(k)
            else:
                assert len(set(line)) == 6
                lines.append(line)
                for p in line:
                    adjacent[p].update(line)

    planes = set()
    for line in lines:
        for p in set.intersection(*(adjacent[q] for q in line)).difference(line):
            # Every line joining p to the base line lies in the level set.
            plane = set(line) | {p}
            for q in line:
                plane.update(index[add(multiples[p][0], m)] for m in multiples[q])
            assert len(plane) == 31
            planes.add(frozenset(plane))
    return len(points), len(lines), len(planes)


if __name__ == "__main__":
    result = enumerate_subspaces()
    print(f"one-dimensional {result[0]}, two-dimensional {result[1]}, "
          f"three-dimensional {result[2]}")
    assert result == (3918, 156, 0)
