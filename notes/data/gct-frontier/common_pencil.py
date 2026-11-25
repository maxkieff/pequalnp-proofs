"""Exact checks for common pencils on pairs of the ten-row coordinate restrictions."""

from collections import Counter, defaultdict
from functools import cache
from itertools import combinations
from math import comb

from cubic_support_examples import determinant, permanent


def subsets(n, k):
    return [sum(1 << j for j in s) for s in combinations(range(n), k)]


def masks():
    return [(sum(1 << ((j + h) % 10) for h in range(3)), j) for j in range(10)] + [(56, 0)]


@cache
def classes(k, enabled, same_column):
    """Count boundary states by which of the two masks kill their path polynomials."""
    counts = [0] * 4
    for s in subsets(10, k):
        present = int(bool(s & 1)) + 2 * int(bool(s & (1 if same_column else 2)))
        counts[present & enabled] += 1
    return counts


@cache
def max_matching(k, h, left_enabled, right_enabled, same_column):
    left = classes(k, left_enabled, same_column)
    right = classes(h, right_enabled, same_column)
    # Minimum vertex cover. Types on either side have identical neighbours internally.
    def cover_cost(leave):
        active = [u for u in range(4) if left[u] and leave >> u & 1]
        return sum(left[u] for u in range(4) if not (leave >> u & 1)) + sum(
            right[v] for v in range(4) if any(u | v == 3 for u in active)
        )
    return min(cover_cost(leave) for leave in range(16))


@cache
def maximum_fold(overlap, same_column):
    # Only row-set intersection and column equality matter up to permutation.
    a = 7
    b = (1 << overlap) - 1 | (((1 << (3 - overlap)) - 1) << 3)
    flags = [int(s & ~a == 0) + 2 * int(s & ~b == 0) for s in range(1024)]
    best = 0
    for front in range(1, 1023):
        free = 1023 ^ front
        back = (free - 1) & free
        while back:
            best = max(best, max_matching(front.bit_count(), back.bit_count(), flags[front],
                                           flags[back], same_column))
            back = (back - 1) & free
    return best


def classify():
    counts = Counter()
    for (a, i), (b, j) in combinations(masks(), 2):
        shared = (a & b).bit_count()
        rank = maximum_fold(shared, i == j)
        counts[shared, i == j, rank] += 1
    for (overlap, same, rank), number in sorted(counts.items()):
        print(f"overlap={overlap}, same column={same}, pairs={number}, maximum fold={rank}")
    assert sum(counts.values()) == 55
    assert sum(n for (_, _, r), n in counts.items() if 1023 - r <= 1001) == 30


def block_data(x, c, d, k):
    """Cut after the first k rows and before the last k; use complementary labels at the late cut."""
    m = len(x)
    full = (1 << m) - 1
    states = subsets(m, k)
    front = [s for s in states if s >> c & 1]
    def swap(s):
        return s ^ ((1 << c) | (1 << d)) if (s >> c ^ s >> d) & 1 else s
    back = list(map(swap, front))

    def minor(rows, s):
        return permanent([[row[j] for j in range(m) if s >> j & 1] for row in rows])

    left = {s: minor(x[:k], s) for s in states}
    right = {s: minor(x[m-k:], s) for s in states}
    def middle(s, q):
        return 0 if s & q else minor(x[k:m-k], full ^ (s | q))
    l, r = [left[s] for s in front], [right[q] for q in back]
    others_l = [s for s in states if s not in front]
    others_r = [q for q in states if q not in back]
    K = [[middle(s, q) for q in back] for s in front]
    u = [sum(left[s] * middle(s, q) for s in others_l) for q in back]
    v = [sum(middle(s, q) * right[q] for q in others_r) for s in front]
    direct = sum(left[s] * middle(s, q) * right[q] for s in others_l for q in others_r)
    return l, r, u, v, K, direct


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def reduced_numerator(data, z):
    """Bordered determinant equals z times the scaled cofactor, even away from the masks."""
    l, r, u, v, K, direct = data
    n = len(l)
    block = [[int(i == j) - z * K[i][j] for j in range(n)] + [r[i] + z * v[i]]
             for i in range(n)]
    block.append([-l[i] - z * u[i] for i in range(n)] + [z * direct])
    return determinant(block)


def folded_minor(x, c, d, k, z, prime):
    """Build the signed affine cofactor at a nonzero parameter in the prime field."""
    m = len(x)
    full = (1 << m) - 1
    inverse_z = pow(z, -1, prime)
    def label(s):
        if s.bit_count() == m - k and not (s >> d & 1):
            q = full ^ s
            if (q >> c ^ q >> d) & 1:
                q ^= (1 << c) | (1 << d)
            return q
        return s
    states = list(dict.fromkeys(label(s) for s in sorted(range(full+1), key=int.bit_count)))
    ix = {s: i for i, s in enumerate(states)}
    minor = [defaultdict(int) for _ in states[:-1]]
    for s in states[1:-1]:
        minor[ix[s]][ix[s]-1] = 1
    for s in range(full):
        for j in range(m):
            if not (s >> j & 1):
                t = s | 1 << j
                scale = 1
                if label(t) != t:
                    scale = z
                elif label(s) != s:
                    scale = inverse_z
                minor[ix[label(s)]][ix[label(t)]-1] -= scale * x[s.bit_count()][j]
    if len(minor) % 2:
        minor[0] = {j: -v for j, v in minor[0].items()}
    return minor


def modular_determinant(rows, prime):
    """Independent sparse Gaussian elimination of the full affine pencil."""
    rows = [{j: v % prime for j, v in row.items() if v % prime} for row in rows]
    result = 1
    for i in range(len(rows)):
        pivot = next((a for a in range(i, len(rows)) if rows[a].get(i)), None)
        if pivot is None:
            return 0
        if pivot != i:
            rows[i], rows[pivot] = rows[pivot], rows[i]
            result = -result
        row = rows[i]
        value = row[i]
        result = result * value % prime
        inverse = pow(value, -1, prime)
        for other in rows[i+1:]:
            if i not in other:
                continue
            scale = other[i] * inverse % prime
            for j, a in row.items():
                b = (other.get(j, 0) - scale * a) % prime
                if b:
                    other[j] = b
                else:
                    other.pop(j, None)
    return result % prime


def example(m, c, d, k, mode):
    x = [[(7*i + 11*j + 3*i*j + i*i + j*j) % 13 - 6 for j in range(m)] for i in range(m)]
    if mode == 'front':
        for i in range(k):
            x[i][c] = 0
    elif mode == 'back':
        for i in range(m-k, m):
            x[i][d] = 0
    data = block_data(x, c, d, k)
    l, r, u, v, K, direct = data
    pole = dot(l, r)
    target = permanent(x)
    assert target == direct + dot(l, v) + dot(u, r) + dot(l, [dot(row, r) for row in K])
    if mode != 'full':
        assert pole == 0
    p = 1009
    size = 2**m - 1 - comb(m-1, k-1)
    for z in (1, 2):
        minor = folded_minor(x, c, d, k, z, p)
        assert len(minor) == size
        assert z * modular_determinant(minor, p) % p == reduced_numerator(data, z) % p
    # For integral data the first two coefficients can be read modulo p and p² at z=p.
    assert reduced_numerator(data, 0) == pole
    first = target - sum(row[i] for i, row in enumerate(K)) * pole
    assert (reduced_numerator(data, p) - pole - p*first) % (p*p) == 0
    print(f"m={m}, columns={c},{d}, {mode}: size {size}, pole {pole}, "
          f"constant term {first}, permanent {target}, cofactor at z=1 mod {p} {reduced_numerator(data, 1) % p}")


def rank_cut_example(m, rank):
    """Realize a nondiagonal central transfer UV by an explicit affine cofactor."""
    cut = m // 2
    full = (1 << m) - 1
    central = subsets(m, cut)
    assert 2 <= rank < len(central)
    x = [[(7*i + 11*j + 3*i*j + i*i + j*j) % 13 - 6 for j in range(m)] for i in range(m)]
    left = {}
    right = {}
    for i, s in enumerate(central):
        if i < rank:
            left[s] = right[s] = [(i, 1)]
        else:
            left[s] = [(i % rank, 2), ((i + 1) % rank, -1)]
            right[s] = [((i + 1) % rank, 3), (i % rank, -2)]

    def minor(rows, columns):
        return permanent([[row[j] for j in range(m) if columns >> j & 1] for row in rows])

    lhs, rhs = [0] * rank, [0] * rank
    unchanged = 0
    for s in central:
        first, last = minor(x[:cut], s), minor(x[cut:], full ^ s)
        unchanged += first * last
        for a, w in left[s]:
            lhs[a] += first * w
        for a, w in right[s]:
            rhs[a] += w * last
    assert unchanged == permanent(x)

    ordinary = sorted(range(full + 1), key=int.bit_count)
    nodes = ([s for s in ordinary if s.bit_count() < cut] + [-1-a for a in range(rank)]
             + [s for s in ordinary if s.bit_count() > cut])
    index = {s: i for i, s in enumerate(nodes)}
    cofactor = [defaultdict(int) for _ in nodes[:-1]]
    for s in nodes[1:-1]:
        cofactor[index[s]][index[s]-1] = 1

    def edge(s, t, weight):
        cofactor[index[s]][index[t]-1] -= weight

    for s in range(full):
        k = s.bit_count()
        for j, weight in enumerate(x[k]):
            if s >> j & 1:
                continue
            t = s | 1 << j
            if k + 1 == cut:
                for a, w in left[t]:
                    edge(s, -1-a, weight * w)
            elif k == cut:
                for a, w in right[s]:
                    edge(-1-a, t, w * weight)
            else:
                edge(s, t, weight)
    if len(cofactor) % 2:
        cofactor[0] = {j: -v for j, v in cofactor[0].items()}
    assert len(cofactor) == full - len(central) + rank
    expected = dot(lhs, rhs) % 1009
    assert modular_determinant(cofactor, 1009) == expected
    print(f"central transfer rank {rank}: size {len(cofactor)}, determinant mod 1009 {expected}")


def error_hessian(long):
    """An integer smooth zero and an exact modular Hessian minor for each error polynomial."""
    n, prime = 10, 1009
    full = (1 << n) - 1
    triples = [s for s in subsets(n, 3) if s & 1]
    cols = [full ^ s for s in triples] if long else triples
    left, right = (127, 1016) if long else (7, 896)
    pivot = 1 if long else 0
    x = [[(17*i + 7*j + i*j + i*i + 2*j*j) % 13 - 6 for j in range(n)] for i in range(n)]
    x[0][pivot] = 0

    @cache
    def per(rows, columns):
        if not rows:
            return 1
        i = (rows & -rows).bit_length() - 1
        return sum(x[i][j] * per(rows ^ (1 << i), columns ^ (1 << j))
                   for j in range(n) if columns >> j & 1)

    value = sum(per(left, s) * per(right, s) for s in cols)
    slope = sum(per(left ^ 1, s ^ (1 << pivot)) * per(right, s) for s in cols if s >> pivot & 1)
    assert slope % prime
    x[0] = [a * slope for a in x[0]]
    x[0][pivot] = -value
    per.cache_clear()
    assert sum(per(left, s) * per(right, s) for s in cols) == 0
    variables = [(i, j) for i in range(n) for j in range(n)
                 if (left | right) >> i & 1 and any(s >> j & 1 for s in cols)]
    H = [[0] * len(variables) for _ in variables]

    def add_factor(rows, s, other_value):
        grad = []
        for a, (i, j) in enumerate(variables):
            if not (rows >> i & 1 and s >> j & 1):
                continue
            rr, cc = rows ^ (1 << i), s ^ (1 << j)
            grad.append((a, per(rr, cc) % prime))
            for b, (h, k) in enumerate(variables):
                if rr >> h & 1 and cc >> k & 1:
                    H[a][b] += other_value * (per(rr ^ (1 << h), cc ^ (1 << k)) % prime)
        return grad

    for s in cols:
        dl = add_factor(left, s, per(right, s) % prime)
        dr = add_factor(right, s, per(left, s) % prime)
        for a, va in dl:
            for b, vb in dr:
                H[a][b] += va * vb
                H[b][a] += va * vb
    H = [[v % prime for v in row] for row in H]
    assert H == list(map(list, zip(*H)))
    # Re-evaluate on a line and interpolate its quadratic coefficient independently.
    direction = [(17*a*a + 13*a + 1) % prime for a in range(len(variables))]
    degree = 14 if long else 6
    saved = [row[:] for row in x]
    coeff2 = 0
    for t in range(degree + 1):
        for a, (i, j) in enumerate(variables):
            x[i][j] = (saved[i][j] + t * direction[a]) % prime
        per.cache_clear()
        value_at_t = sum(per(left, s) * per(right, s) for s in cols) % prime
        coeff = [1, 0, 0]
        denom = 1
        for h in range(degree + 1):
            if h != t:
                coeff = [-h*coeff[0], coeff[0]-h*coeff[1], coeff[1]-h*coeff[2]]
                denom = denom * (t-h) % prime
        coeff2 += value_at_t * coeff[2] * pow(denom, -1, prime)
    assert (2*coeff2 - dot(direction, [dot(row, direction) for row in H])) % prime == 0
    # Retain the original row and column positions of a nonsingular minor.
    reduced = [row[:] for row in H]
    order = list(range(len(H)))
    pivots = []
    for j in range(len(H)):
        k = len(pivots)
        a = next((i for i in range(k, len(H)) if reduced[i][j]), None)
        if a is None:
            continue
        reduced[k], reduced[a] = reduced[a], reduced[k]
        order[k], order[a] = order[a], order[k]
        inv = pow(reduced[k][j], -1, prime)
        for row in reduced[k+1:]:
            factor = row[j] * inv % prime
            if factor:
                row[j:] = [(v - factor * w) % prime for v, w in zip(row[j:], reduced[k][j:])]
        pivots.append(j)
    minor = [[H[i][j] for j in pivots] for i in order[:len(pivots)]]
    residue = determinant(minor) % prime
    assert residue
    print("degree", 14 if long else 6, "variables", len(H), "smooth slope", slope,
          "Hessian minor order", len(pivots), "det mod 1009", residue)
    return len(pivots), residue


if __name__ == "__main__":
    classify()
    for mode in ('full', 'front', 'back'):
        example(6, 0, 1, 2, mode)
        example(10, 0, 0, 3, mode)
        example(10, 0, 5, 3, mode)
    ones = [[1] * 10 for _ in range(10)]
    left, right, u, v, K, direct = block_data(ones, 0, 0, 3)
    assert all(not any(row) for row in K)
    assert (dot(left, right), direct + dot(left, v) + dot(u, right), dot(u, v)) == (
        1296, 3628800, 914457600)
    assert comb(232, 2) == 26796
    rank_cut_example(6, 3)
    rank_cut_example(10, 230)
    assert error_hessian(False) == (60, 897)
    assert error_hessian(True) == (90, 975)
