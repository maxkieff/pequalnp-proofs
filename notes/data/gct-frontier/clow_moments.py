"""Exact experiments with row-mixing permanent pencils on ordered closed walks."""

from collections import Counter, defaultdict
from itertools import permutations
from math import comb
from random import Random


def walk_groups(n):
    """Group length-n walks by commutative monomial. The first head is vertex 0."""
    groups = defaultdict(list)

    def extend(head, current, path):
        last = len(path) + 1 == n
        closing = (head, current, head)
        if last:
            finished = path + (closing + (-1,),)
            key = tuple(sorted((i, j) for _, i, j, _ in finished))
            groups[key].append(finished)
            return
        for destination in range(head + 1, n):
            extend(head, destination, path + ((head, current, destination, head),))
        for next_head in range(head + 1, n):
            extend(next_head, next_head, path + (closing + (next_head,),))

    extend(0, 0, ())
    return groups


def cover(key, n):
    return {i for i, _ in key} == set(range(n)) and {j for _, j in key} == set(range(n))


def coefficient(paths, weight):
    total = 0
    for path in paths:
        value = 1
        for t, (h, i, j, g) in enumerate(path):
            value *= weight(t, h, i, j, g)
        total += value
    return total


def perm_key(p):
    return tuple(enumerate(p))


def nine_coefficients(n, i, j, other, coefficients):
    outside = [(v, v) for v in range(n) if v not in (0, i, j, other)]

    def read(*pairs):
        return coefficients[tuple(sorted(list(pairs) + outside))]

    a = read((0, other), (other, i), (i, 0), (j, j))
    b = read((0, other), (other, 0), (i, i), (j, j))
    c = read((0, other), (other, j), (j, i), (i, 0))
    d = read((0, other), (other, 0), (i, j), (j, i))
    e = read((0, other), (other, i), (i, j), (j, 0))
    f = read((0, other), (other, j), (j, 0), (i, i))
    k1 = read((0, i), (i, i), (i, 0), (j, j))
    k2 = read((0, i), (i, j), (j, i), (i, 0))
    k3 = read((0, i), (i, i), (i, j), (j, 0))
    return a, b, c, d, e, f, k1, k2, k3


def minors(values):
    a, b, c, d, e, f, k1, k2, k3 = values
    return a*d*f + b*c*e, a*d*k3 - d*e*k1 + b*e*k2


def sextic(n, coefficients, i=1, j=2, other=3):
    d1, n1 = minors(nine_coefficients(n, i, j, other, coefficients))
    d3, n3 = minors(nine_coefficients(n, other, j, i, coefficients))
    return n1*n3 - d1*d3


def feature(t, arc, model):
    h, i, j, g = arc
    if model == 'stationary':
        return h, i, j
    if model == 'layer':
        return t, h, i, j
    if model == 'transition':
        return t, h, i, j, g
    raise ValueError(model)


def signing(groups, n, model):
    """Solve the forced one- and two-path sign equations over F2 by elimination."""
    variables = {}
    pivots = {}

    def path_mask(path):
        mask = 0
        for t, arc in enumerate(path):
            v = feature(t, arc, model)
            mask ^= 1 << variables.setdefault(v, len(variables))
        return mask

    for key, paths in groups.items():
        if cover(key, n):
            assert len(paths) == 1
            mask, rhs = path_mask(paths[0]), 0
        elif len(paths) == 2:
            mask, rhs = path_mask(paths[0]) ^ path_mask(paths[1]), 1
        else:
            continue
        while mask:
            index = mask.bit_length() - 1
            if index not in pivots:
                pivots[index] = mask, rhs
                break
            other, other_rhs = pivots[index]
            mask ^= other
            rhs ^= other_rhs
        if not mask and rhs:
            return 'inconsistent', None

    solution = 0
    for index, (mask, rhs) in sorted(pivots.items()):
        if (solution & mask).bit_count() % 2 != rhs:
            solution |= 1 << index
    negative = {v for v, i in variables.items() if solution >> i & 1}
    weight = lambda t, h, i, j, g: -1 if feature(t, (h, i, j, g), model) in negative else 1
    bad = sum(coefficient(paths, weight) != int(cover(key, n)) for key, paths in groups.items())
    return ('exact' if not bad else f'{bad} remaining coefficients'), negative


def determinant_sign(p):
    return (-1) ** sum(i < j and p[i] > p[j] for i in range(len(p)) for j in range(len(p)))


def history_widths(groups, n):
    """Split each live state by the row origins used on a permutation prefix."""
    layers = [defaultdict(set) for _ in range(n-1)]
    for key, paths in groups.items():
        if not cover(key, n):
            continue
        path, = paths
        seen = 0
        for level, (h, i, j, g) in enumerate(path[:-1]):
            seen |= 1 << i
            state = (g, g) if j == h else (h, j)
            layers[level][state].add(seen)
    return [max(map(len, layer.values())) for layer in layers], layers


def verify_history_program(n, groups, layers):
    """Multiply 0/1 matrices that update the stored history on each arc."""
    def final_weight(path):
        histories = {0: 1}
        for t, (h, i, j, g) in enumerate(path):
            next_histories = defaultdict(int)
            for mask, ways in histories.items():
                if mask >> i & 1:
                    continue
                following = mask | 1 << i
                if t+1 == n:
                    assert following == (1 << n)-1
                else:
                    state = (g, g) if j == h else (h, j)
                    if following not in layers[t].get(state, ()):
                        continue
                next_histories[following] += ways
            histories = next_histories
        return sum(histories.values())
    assert all(sum(map(final_weight, paths)) == int(cover(key, n)) for key, paths in groups.items())


def history_layers(n):
    """Reachable prefixes of genuine cycle covers. Each can finish with singleton cycles."""
    states = {(0, 0): {0}}
    layers = []
    for _ in range(n-1):
        following = defaultdict(set)
        for (h, u), masks in states.items():
            for mask in masks:
                seen = mask | 1 << u
                for v in range(h+1, n):
                    if not seen >> v & 1:
                        following[h, v].add(seen)
                next_head = next(i for i in range(n) if not seen >> i & 1)
                following[next_head, next_head].add(seen)
        layers.append(following)
        states = following
    return layers


def residue_layers(n, layers, q):
    colors = [sum(i for i in range(n) if mask >> i & 1) % q for mask in range(1 << n)]
    return [{state: {colors[mask] for mask in masks} for state, masks in layer.items()}
            for layer in layers]


def residue_transitions(n, layers, q, t, state):
    h, u, tag = state
    tag = (tag + u) % q
    if t+1 == n:
        if tag == sum(range(n)) % q:
            yield None, (u, h), 1
        return
    for v in range(h+1, n):
        if tag in layers[t].get((h, v), ()):
            yield (h, v, tag), (u, v), -1 if u == v else 1
    for g in range(h+1, n):
        if tag in layers[t].get((g, g), ()):
            yield (g, g, tag), (u, h), 1


def residue_evaluate(matrix, layers, q):
    n = len(matrix)
    previous = {(0, 0, 0): 1}
    for t in range(n):
        following = defaultdict(int)
        for state, value in previous.items():
            for dest, (i, j), sign in residue_transitions(n, layers, q, t, state):
                following[dest] += value * matrix[i][j] * sign
        previous = following
    return previous.get(None, 0)


def residue_coefficient(n, layers, q, edges):
    remaining = Counter(edges)

    def follow(t, state):
        if t == n:
            return 1
        total = 0
        for dest, edge, sign in residue_transitions(n, layers, q, t, state):
            if remaining[edge]:
                remaining[edge] -= 1
                total += sign * follow(t+1, dest)
                remaining[edge] += 1
        return total
    assert len(edges) == n
    return follow(0, (0, 0, 0))


def repeated_cycle_key(n, i, j, missing):
    return [(0,i),(i,0),(i,j),(j,i)] + [(v,v) for v in range(n) if v not in (0,i,j,missing)]


def ten_rows():
    from cubic_support_examples import determinant, permanent
    n, q = 10, 4
    history = history_layers(n)
    assert [len(layer) for layer in history] == [10,19,27,34,40,45,49,52,54]
    assert [max(map(len, layer.values())) for layer in history] == [comb(n-2,k) for k in range(n-1)]
    total_histories = sum(sum(map(len, layer.values())) for layer in history)
    assert total_histories == (n-1)*2**(n-1)
    budget = sum(sum(min(q, len(masks)) for masks in layer.values()) for layer in history)
    tags = residue_layers(n, history, q)
    actual = sum(sum(map(len, layer.values())) for layer in tags)
    matrix = [[(7*i + 11*j + 3*i*j + 2) % 9 - 4 for j in range(n)] for i in range(n)]
    got, want = residue_evaluate(matrix, tags, q), permanent(matrix)
    assert got != want
    print('Ten rows: scalar states, full history states, four-channel capped states, residue states:',
          sum(map(len, history)), total_histories, budget, actual)
    print('Four-channel residue pencil on signed dense input, pencil and permanent:', got, want)
    support = {(i, i) for i in range(n)} | {(0,1), (1,0), (1,2), (2,1)}
    block = [[int((i,j) in support) for j in range(n)] for i in range(n)]
    block_values = residue_evaluate(block, tags, q), permanent(block), determinant(block)
    assert block_values == (19, 3, -1)
    print('Three-row block plus identity: pencil, permanent, determinant:', block_values)
    for i, missing in ((1,5), (1,6)):
        j = 2
        edges = repeated_cycle_key(n, i, j, missing)
        value = residue_coefficient(n, tags, q, edges)
        assert value == (2 if i % q == missing % q else 0)
        print('Repeated row, missing row, pencil coefficient, permanent coefficient:', i, missing, value, 0)
    masks = [{((j+d)%n, j) for d in range(3)} for j in range(n)] + [{(i, 0) for i in (3,4,5)}]
    visible = [0] * len(masks)
    count = 0
    for i, j, missing in permutations(range(1,n), 3):
        if i % q != missing % q:
            continue
        edges = repeated_cycle_key(n, i, j, missing)
        assert residue_coefficient(n, tags, q, edges) == 2
        count += 1
        for k, mask in enumerate(masks):
            visible[k] += mask.isdisjoint(edges)
    assert count == 84 and all(visible)
    print('Errors in this family surviving each of the eleven earlier restrictions:', visible)

def run():
    for n in (2, 3, 4, 5, 6):
        groups = walk_groups(n)
        expected = {perm_key(p): determinant_sign(p) for p in permutations(range(n))}
        signed = {key: (-1)**n * coefficient(paths, lambda t,h,i,j,g: -1 if j == h else 1)
                  for key, paths in groups.items()}
        assert {k:v for k,v in signed.items() if v} == expected
        target = {key: int(cover(key, n)) for key in groups}
        change_loops = lambda t,h,i,j,g: -1 if i == j and h < i else 1
        wrong = {key: coefficient(paths, change_loops) for key, paths in groups.items()
                 if coefficient(paths, change_loops) != target[key]}
        assert bool(wrong) == (n >= 4)
        print(f'{n} rows: {sum(map(len, groups.values()))} walks, '
              f'{len(groups)} monomials, {len(wrong)} errors with interior loops negated')
        if n >= 4:
            assert nine_coefficients(n, 1, 2, 3, {**target, **wrong})[7] == 2
            assert sextic(n, target) == -4
            assert sextic(n, signed) == 0
            rng = Random(n)
            for trial in range(10):
                weights = defaultdict(lambda: rng.choice((-3,-2,-1,1,2,3)) if trial else rng.randint(-2,2))
                coeffs = {key: coefficient(paths, lambda t,h,i,j,g: weights[t,h,i,j,g])
                          for key, paths in groups.items()}
                for i, j, other in permutations(range(1,n), 3):
                    assert sextic(n, coeffs, i, j, other) == 0
        for model in ('stationary', 'layer', 'transition'):
            status, _ = signing(groups, n, model)
            print(' ', model, status)
        widths, layers = history_widths(groups, n)
        verify_history_program(n, groups, layers)
        assert history_layers(n) == layers
        assert [len(layer) for layer in layers] == [k*n - comb(k, 2) for k in range(1,n)]
        assert 3 * sum(map(len, layers)) == n**3-n
        if n == 6:
            tags = residue_layers(n, layers, 3)
            assert residue_coefficient(n, tags, 3, repeated_cycle_key(n, 1, 2, 4)) == 2
            print('  three-channel residue pencil: size',
                  1 + sum(sum(map(len, layer.values())) for layer in tags), 'and unwanted coefficient 2')
        print('  exact history widths:', widths, 'internal states:',
              sum(sum(map(len, layer.values())) for layer in layers))
    ten_rows()


if __name__ == '__main__':
    run()
