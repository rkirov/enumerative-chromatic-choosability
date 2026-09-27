#!/usr/bin/env python3
"""Generate the kernel-checked certificates that K_{2,25} is ECC at four.

    python3 TwoDegenerate/K2n/gen_k2n.py            # regenerate TwoDegenerate/K2n/R0..R4.lean
    python3 TwoDegenerate/K2n/gen_k2n.py --check    # regenerate in memory and compare

Setting (see Reduction.lean). Hub lists A = {0,1,2,3} and B, sharing r colours; every right list
is a four-subset ("type") of A u B, identified by its membership bits along
A n B, A \\ B, B \\ A.  For multiplicities m (summing to N = 25) the colouring count is

    F(m) = sum over the 16 pairs p = (i, j) of prod over types t of W[t][p] ** m[t],

W[t][p] = |t \\ {a_i, b_j}|, and the claim is F(m) >= 4*3**N + 12*2**N for every m.

Certificates are binary branch-and-bound trees over the types in a fixed order (Checker.lean):
  leaf        last type; its multiplicity is forced, evaluate exactly
  split a b   a: this type has multiplicity 0;  b: at least 1 (absorb one copy, recurse)
  bound k     weighted AM-GM with integer weights k (sum D):
                D**D * prod_p c_p**k_p * g**rem >= prod_p k_p**k_p * CONST**D,
              g = least prod_p W[t][p]**k_p over the remaining types.
The weights come from the continuous dual (mirror descent on the convex relaxation), rounded to
integers; every certificate is re-checked in exact integer arithmetic before it is written, and
the Lean kernel checks it again.  Requires numpy.
"""

import itertools
import math
import os
import sys

import numpy as np

N = 25
CONST = 4 * 3**N + 12 * 2**N
LC = math.log(CONST)
HERE = os.path.dirname(os.path.abspath(__file__))
sys.setrecursionlimit(100000)


def setup(r):
    """Types (four-subsets of the 8 - r colours) and their 16 pair values."""
    U = 8 - r
    A = [0, 1, 2, 3]
    B = list(range(r)) + list(range(4, 8 - r))
    types = [frozenset(c) for c in itertools.combinations(range(U), 4)]
    pairs = [(x, y) for x in A for y in B]
    W = np.array([[4 - len(T & {x, y}) for (x, y) in pairs] for T in types])
    return types, W


def order_for(r, types):
    key = lambda t: ''.join(map(str, sorted(t)))
    if r == 2:  # the four types carrying the continuous optimum, then its fifth support type
        main = ['0124', '0134', '0125', '0135', '2345']
        return ([i for m in main for i, t in enumerate(types) if key(t) == m]
                + [i for i, t in enumerate(types) if key(t) not in main])
    if r == 3:
        return sorted(range(len(types)), key=lambda i: key(types[i]) not in ('0123', '0124'))
    return list(range(len(types)))


def dual_bound(logc, L, rem, iters=500):
    """Best AM-GM (Lagrange dual) lower bound on log F over the remaining types, and its weights."""
    nt = L.shape[0]
    mu = np.ones(nt) / nt
    best, bestlam = -1e300, None
    for _ in range(iters):
        z = logc + rem * (mu @ L)
        w = np.exp(z - z.max())
        lam = w / w.sum()
        g = L @ lam
        pos = lam > 0
        d = -(lam[pos] * np.log(lam[pos])).sum() + (lam * logc).sum() + rem * g.min()
        if d > best:
            best, bestlam = d, lam
        mu = mu * np.exp(-(g - g.min()))
        mu /= mu.sum()
    return best, bestlam


def integerize(lam, D):
    raw = lam * D
    k = [int(math.floor(x)) for x in raw]
    for p in sorted(range(16), key=lambda p: raw[p] - k[p], reverse=True)[:D - sum(k)]:
        k[p] += 1
    return k


def bound_ok(W, d, c, rem, k):
    D = sum(k)
    lhs = D**D * math.prod(c[p]**k[p] for p in range(16))
    lhs *= min(math.prod(int(W[i][p])**k[p] for p in range(16)) for i in range(d, len(W)))**rem
    return lhs >= math.prod(kp**kp for kp in k) * CONST**D


def build(W, Ds=(8, 16, 24, 32, 48, 64, 96, 128, 192, 256, 384, 512)):
    nt = len(W)
    L = np.log(W.astype(float))

    def node(d, c, rem):
        if d == nt - 1:
            return 'leaf'
        val, lam = dual_bound(np.array([math.log(x) for x in c]), L[d:], rem)
        if val > LC + 1e-9:
            for D in Ds:
                k = integerize(lam, D)
                if bound_ok(W, d, c, rem, k):
                    return ('bound', k)
        a = node(d + 1, c, rem)
        b = 'leaf' if rem == 0 else node(d, [c[p] * int(W[d][p]) for p in range(16)], rem - 1)
        return ('split', a, b)

    return node(0, [1] * 16, N)


def check(W, d, c, rem, t):
    """Exact re-check with the semantics of `K2n.check`."""
    nt = len(W)
    if t == 'leaf':
        return d == nt - 1 and sum(c[p] * int(W[d][p])**rem for p in range(16)) >= CONST
    if t[0] == 'bound':
        return sum(t[1]) > 0 and bound_ok(W, d, c, rem, t[1])
    if d >= nt - 1 or not check(W, d + 1, c, rem, t[1]):
        return False
    return rem == 0 or check(W, d, [c[p] * int(W[d][p]) for p in range(16)], rem - 1, t[2])


def count(t, kind):
    if t == 'leaf':
        return int(kind in ('nodes', 'leaf'))
    if t[0] == 'bound':
        return int(kind in ('nodes', 'bound'))
    return int(kind == 'nodes') + count(t[1], kind) + count(t[2], kind)


def lean_cert(t):
    if t == 'leaf':
        return '.leaf'
    if t[0] == 'bound':
        return '(.bound [%s])' % ', '.join(map(str, t[1]))
    return '(.split %s %s)' % (lean_cert(t[1]), lean_cert(t[2]))


def lean_file(r, keys, W, t):
    rows = '[' + ',\n    '.join('[' + ', '.join(map(str, row)) + ']' for row in W.tolist()) + ']'
    ks = '[' + ',\n    '.join('[' + ', '.join('true' if b else 'false' for b in k) + ']'
                            for k in keys) + ']'
    plural = '' if r == 1 else 's'
    return f"""/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import TwoDegenerate.K2n.Reduction

/-!
# `K₂,₂₅` at four: the certificate for hub lists sharing {r} colour{plural}

Generated by `TwoDegenerate/K2n/gen_k2n.py`; checked here by the kernel. The keys are the
four-subsets of `A ∪ B` in branching order, the rows their sixteen pair values, and the
certificate a `Cert` tree ({count(t, 'nodes')} nodes, {count(t, 'bound')} closed by AM–GM).
-/

namespace SimpleGraph.TwoDegenerate.K2n.K2_25

/-- The four-subsets of `A ∪ B`, as membership bits, in branching order. -/
def keys{r} : List (List Bool) :=
  {ks}

/-- Their rows, `rowOf {r}`. -/
def rows{r} : List (List ℕ) :=
  {rows}

/-- The certificate. -/
def cert{r} : Cert := {lean_cert(t)}

set_option maxRecDepth 100000 in
theorem rows{r}_eq : rows{r} = keys{r}.map (rowOf {r}) := by decide +kernel

set_option maxRecDepth 100000 in
theorem nodup{r} : keys{r}.Nodup := by decide +kernel

set_option maxRecDepth 100000 in
theorem complete{r} : ∀ κ ∈ allBool (8 - {r}), κ.count true = 4 → κ ∈ keys{r} := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem check{r} : check (4 * 3 ^ 25 + 12 * 2 ^ 25) cert{r} rows{r} ones16 25 = true := by
  decide +kernel

theorem keyGoal{r} : KeyGoal (4 * 3 ^ 25 + 12 * 2 ^ 25) 25 {r} keys{r} := by
  refine ⟨nodup{r}, complete{r}, ?_⟩
  rw [← rows{r}_eq]
  exact check_sound _ _ _ _ _ check{r}

end SimpleGraph.TwoDegenerate.K2n.K2_25
"""


def main():
    compare = '--check' in sys.argv
    ok = True
    for r in range(5):
        types, W = setup(r)
        order = order_for(r, types)
        Wo = W[order]
        t = build(Wo)
        assert check(Wo, 0, [1] * 16, N, t), f'certificate for r = {r} fails the exact re-check'
        keys = [[x in types[i] for x in range(8 - r)] for i in order]
        src = lean_file(r, keys, Wo, t)
        path = os.path.join(HERE, f'R{r}.lean')
        print(f'r = {r}: {count(t, "nodes")} nodes, {count(t, "bound")} AM-GM bounds')
        if compare:
            same = open(path).read() == src
            ok &= same
            print('   ', path, 'matches' if same else 'DIFFERS')
        else:
            open(path, 'w').write(src)
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
