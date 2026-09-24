#!/usr/bin/env python3
"""Exact, independent small-instance audits for the full-grid polymer argument.

This is a diagnostic, not a substitute for the general proof or Lean verification.
Only the Python standard library is used. All comparisons use integers/Fractions.
"""

from argparse import ArgumentParser
from fractions import Fraction as Q
from itertools import combinations
from random import Random
from time import perf_counter


def submasks(mask):
    sub = mask
    while sub:
        yield sub
        sub = (sub - 1) & mask


def components(n, edges, selected):
    groups = [1 << v for v in range(n)]
    for i, (u, v) in enumerate(edges):
        if not selected >> i & 1:
            continue
        left = next(g for g in groups if g >> u & 1)
        right = next(g for g in groups if g >> v & 1)
        if left != right:
            groups.remove(left)
            groups.remove(right)
            groups.append(left | right)
    return groups


def prepare(n, edges):
    size = 1 << n
    coeff = [0] * size
    trees = []
    whitney = []
    for v in range(n):
        coeff[1 << v] = 1
    for selected in range(1 << len(edges)):
        comps = components(n, edges, selected)
        sign = (-1) ** selected.bit_count()
        whitney.append((sign, comps))
        nontrivial = [s for s in comps if s.bit_count() > 1]
        if len(nontrivial) == 1:
            s = nontrivial[0]
            coeff[s] += sign
            if selected.bit_count() == s.bit_count() - 1:
                trees.append((s, selected))
    for s in range(1, size):
        if s.bit_count() >= 2:
            assert abs(coeff[s]) <= sum(t == s for t, _ in trees)
            assert coeff[s] * (-1) ** (s.bit_count() - 1) >= 0
    return coeff, trees, whitney


def intersections(n, lists, k):
    inter = [0] * (1 << n)
    for s in range(1, 1 << n):
        v = (s & -s).bit_length() - 1
        rest = s & (s - 1)
        inter[s] = lists[v] if not rest else inter[rest] & lists[v]
    sizes = [x.bit_count() for x in inter]
    defects = [0] + [k - x for x in sizes[1:]]
    assert all(sizes[1 << v] == k for v in range(n))
    return sizes, defects


def recurrence(n, coeff, defects, k, t):
    z, dz = [Q(0)] * (1 << n), [Q(0)] * (1 << n)
    z[0] = Q(1)
    for u in range(1, 1 << n):
        root = u & -u
        for s in submasks(u):
            if not s & root or not coeff[s]:
                continue
            rest = u ^ s
            w = coeff[s] * (k - t * defects[s])
            z[u] += w * z[rest]
            dz[u] += -coeff[s] * defects[s] * z[rest] + w * dz[rest]
        # Independent all-block derivative identity, not a differentiation rule for the code.
        direct = sum(-coeff[s] * defects[s] * z[u ^ s] for s in submasks(u))
        assert dz[u] == direct
    return z, dz


def audit_graph(n, edges, rng, k=25):
    assert max((sum(v in e for e in edges) for v in range(n)), default=0) <= 4
    coeff, trees, whitney = prepare(n, edges)
    if rng.randrange(5) == 0:
        lists = [(1 << k) - 1] * n
    else:
        lists = [sum(1 << c for c in rng.sample(range(k + 2), k)) for _ in range(n)]
    sizes, defects = intersections(n, lists, k)
    de = [defects[(1 << u) | (1 << v)] for u, v in edges]
    q, b = Q(8 * k, 13), Q(32, 25)
    # Deficiency domination is tested for every individual embedded spanning tree.
    for s, selected in trees:
        assert defects[s] <= sum(d for i, d in enumerate(de) if selected >> i & 1)
    # Rooted and edge-rooted tree envelopes. No polynomial coefficients are used here.
    for v in range(n):
        rooted = sum(q ** (1 - s.bit_count()) for s, _ in trees if s >> v & 1)
        assert rooted <= Q(5, 13)
    for i in range(len(edges)):
        anchored = sum(q ** (2 - s.bit_count()) for s, selected in trees
                       if s.bit_count() >= 3 and selected >> i & 1)
        assert anchored <= b * b - 1
    for t in (Q(0), Q(1, 3), Q(2, 3), Q(1)):
        z, dz = recurrence(n, coeff, defects, k, t)
        for u in range(1, 1 << n):
            assert z[u] > 0
            for v in range(n):
                if u >> v & 1:
                    assert z[u] >= q * z[u ^ (1 << v)]
            edge_term = sum(de[i] * z[u ^ ((1 << a) | (1 << b))]
                            for i, (a, b) in enumerate(edges)
                            if u >> a & 1 and u >> b & 1)
            assert dz[u] >= Q(226, 625) * edge_term
        if t in (0, 1):
            count = 0
            for sign, comps in whitney:
                term = sign
                for s in comps:
                    term *= k if t == 0 else sizes[s]
                count += term
            assert z[-1] == count


def grid(rows, cols):
    edges = []
    for i in range(rows):
        for j in range(cols):
            v = i * cols + j
            if i + 1 < rows:
                edges.append((v, v + cols))
            if j + 1 < cols:
                edges.append((v, v + 1))
    return rows * cols, edges


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=4)
    parser.add_argument('--grids', action='store_true')
    args = parser.parse_args()
    rng, checked, started = Random(20260906), 0, perf_counter()
    # The rational constants used in the proposed degree-four theorem.
    x, b = Q(13, 200), Q(32, 25)
    assert (1 + x * b) ** 3 <= b
    assert (1 + x * b) ** 4 <= Q(18, 13)
    assert b * b - 1 == Q(399, 625)
    for n in range(args.max_n + 1):
        possible = list(combinations(range(n), 2))
        for mask in range(1 << len(possible)):
            edges = [e for i, e in enumerate(possible) if mask >> i & 1]
            if max((sum(v in e for e in edges) for v in range(n)), default=0) > 4:
                continue
            audit_graph(n, edges, rng)
            checked += 1
        print(f'n={n}: {checked} cumulative graph audits passed', flush=True)
    if args.grids:
        for rows, cols in ((2, 4), (2, 5), (3, 3)):
            n, edges = grid(rows, cols)
            for k in (25, 32):
                audit_graph(n, edges, rng, k)
                checked += 1
                print(f'{rows}x{cols}, k={k}: passed', flush=True)
    print(f'{checked} exact audits passed in {perf_counter() - started:.3f}s')


if __name__ == '__main__':
    main()
