#!/usr/bin/env python3
"""Generate the kernel-checked certificates that K_{2,n} is ECC at k for n <= N_k.

    python3 TwoDegenerate/K2n/gen_k2n.py            # write TwoDegenerate/K2n/{Keys,Cert}/*.lean
    python3 TwoDegenerate/K2n/gen_k2n.py --check    # regenerate in memory and compare

List sizes and thresholds: (k, N_k) = (3, 11), (4, 25), (5, 43).

Setting (see Reduction.lean). Hub lists A = {0..k-1} and B, sharing r colours; after the
reduction every right list is a k-subset ("type") of A u B, identified by its membership bits
along A n B, A \\ B, B \\ A.  For multiplicities m (summing to n) the colouring count is

    F(m) = sum over the k*k pairs p = (i, j) of prod over types t of W[t][p] ** m[t],

W[t][p] = |t \\ {a_i, b_j}|, and the claim is F(m) >= k (k-1)^n + k (k-1) (k-2)^n.

Certificates are binary branch-and-bound trees over the types in a fixed order (Checker.lean):
  leaf        last type; its multiplicity is forced, evaluate exactly
  split a b   a: this type has multiplicity 0;  b: at least 1 (absorb one copy, recurse)
  bound w     weighted AM-GM with integer weights w (sum D):
                D**D * prod_p c_p**w_p * g**rem >= prod_p w_p**w_p * T**D,
              g = least prod_p W[t][p]**w_p over the remaining types.
The weights come from the continuous dual (mirror descent on the convex relaxation), rounded to
integers; every certificate is re-checked in exact integer arithmetic before it is written, and
the Lean kernel checks it again.  Deterministic.  Requires numpy.
"""

import itertools
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
THRESHOLDS = {3: 11, 4: 25, 5: 43}
sys.setrecursionlimit(100000)


def target(k, n):
    return k * (k - 1)**n + k * (k - 1) * (k - 2)**n


def setup(k, r):
    """Types (k-subsets of the 2k - r colours) and their k*k pair values."""
    A = list(range(k))
    B = list(range(r)) + list(range(k, 2 * k - r))
    types = [frozenset(c) for c in itertools.combinations(range(2 * k - r), k)]
    pairs = [(x, y) for x in A for y in B]
    W = np.array([[k - len(T & {x, y}) for (x, y) in pairs] for T in types])
    return types, W


def dual_bound(logc, L, rem, iters=500):
    """Best AM-GM (Lagrange dual) lower bound on log F over the remaining types, and weights."""
    mu = np.ones(L.shape[0]) / L.shape[0]
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


def branch_order(k, r):
    """Types by decreasing weight in the continuous optimum at the threshold."""
    types, W = setup(k, r)
    L = np.log(W.astype(float))
    n = THRESHOLDS[k]
    mu = np.ones(len(types)) / len(types)
    for _ in range(3000):
        z = n * (mu @ L)
        w = np.exp(z - z.max())
        g = L @ (w / w.sum())
        mu = mu * np.exp(-(g - g.min()))
        mu /= mu.sum()
    return sorted(range(len(types)), key=lambda i: (-round(mu[i], 6), i))


def integerize(lam, D):
    raw = lam * D
    w = [int(math.floor(x)) for x in raw]
    for p in sorted(range(len(w)), key=lambda p: raw[p] - w[p], reverse=True)[:D - sum(w)]:
        w[p] += 1
    return w


def bound_ok(W, d, c, rem, w, T):
    P, D = len(w), sum(w)
    if D == 0:
        return False
    lhs = D**D * math.prod(c[p]**w[p] for p in range(P))
    lhs *= min(math.prod(int(W[i][p])**w[p] for p in range(P)) for i in range(d, len(W)))**rem
    return lhs >= math.prod(x**x for x in w) * T**D


def build(W, n, T, Ds=(8, 16, 24, 32, 48, 64, 96, 128, 192, 256, 384, 512, 768, 1024)):
    nt, P = W.shape
    L = np.log(W.astype(float))
    LT = math.log(T)

    def node(d, c, rem):
        if d == nt - 1:
            return 'leaf'
        val, lam = dual_bound(np.array([math.log(x) for x in c]), L[d:], rem)
        if val > LT + 1e-9:
            for D in Ds:
                w = integerize(lam, D)
                if bound_ok(W, d, c, rem, w, T):
                    return ('bound', w)
        a = node(d + 1, c, rem)
        b = 'leaf' if rem == 0 else node(d, [c[p] * int(W[d][p]) for p in range(P)], rem - 1)
        return ('split', a, b)

    return node(0, [1] * P, n)


def check(W, d, c, rem, t, T):
    """Exact re-check with the semantics of `K2n.check`."""
    nt, P = W.shape
    if t == 'leaf':
        return d == nt - 1 and sum(c[p] * int(W[d][p])**rem for p in range(P)) >= T
    if t[0] == 'bound':
        return bound_ok(W, d, c, rem, t[1], T)
    if d >= nt - 1 or not check(W, d + 1, c, rem, t[1], T):
        return False
    return rem == 0 or check(W, d, [c[p] * int(W[d][p]) for p in range(P)], rem - 1, t[2], T)


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


HEADER = """/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
"""


def keys_file(k, r, keys, W):
    rows = '[' + ',\n    '.join('[' + ', '.join(map(str, row)) + ']' for row in W.tolist()) + ']'
    ks = '[' + ',\n    '.join('[' + ', '.join('true' if b else 'false' for b in key) + ']'
                            for key in keys) + ']'
    return HEADER + f"""import TwoDegenerate.K2n.Reduction

/-!
# Types for list size {k}, hub lists sharing {r} colour{'' if r == 1 else 's'}

Generated by `TwoDegenerate/K2n/gen_k2n.py`. The {len(keys)} `{k}`-subsets of `A ∪ B` as membership
bits along `A ∩ B`, `A \\ B`, `B \\ A`, in branching order, and their rows of `{k * k}` pair values.
-/

namespace SimpleGraph.TwoDegenerate.K2n.Data

/-- The keys. -/
def keys_{k}_{r} : List (List Bool) :=
  {ks}

/-- Their rows, `rowOf {k} {r}`. -/
def rows_{k}_{r} : List (List ℕ) :=
  {rows}

set_option maxRecDepth 100000 in
theorem rows_{k}_{r}_eq : rows_{k}_{r} = keys_{k}_{r}.map (rowOf {k} {r}) := by decide +kernel

set_option maxRecDepth 100000 in
theorem nodup_{k}_{r} : keys_{k}_{r}.Nodup := by decide +kernel

set_option maxRecDepth 100000 in
theorem complete_{k}_{r} :
    ∀ κ ∈ allBool (2 * {k} - {r}), κ.count true = {k} → κ ∈ keys_{k}_{r} := by
  decide +kernel

end SimpleGraph.TwoDegenerate.K2n.Data
"""


def cert_file(k, n, certs):
    T = f'{k} * ({k} - 1) ^ {n} + {k} * ({k} - 1) * ({k} - 2) ^ {n}'
    imports = 'import TwoDegenerate.K2n.Count\n' + '\n'.join(
        f'import TwoDegenerate.K2n.Keys.K{k}R{r}' for r in range(k + 1))
    parts = []
    for r, t in enumerate(certs):
        parts.append(f"""/-- Overlap {r}: {count(t, 'nodes')} nodes, {count(t, 'bound')} AM–GM bounds. -/
def cert_{k}_{n}_{r} : Cert := {lean_cert(t)}

set_option maxRecDepth 100000 in
theorem check_{k}_{n}_{r} :
    check ({T}) cert_{k}_{n}_{r} rows_{k}_{r} (onesK {k}) {n} = true := by
  decide +kernel

theorem keyGoal_{k}_{n}_{r} : KeyGoal {k} ({T}) {n} {r} keys_{k}_{r} := by
  refine ⟨nodup_{k}_{r}, complete_{k}_{r}, ?_⟩
  rw [← rows_{k}_{r}_eq]
  exact check_sound _ _ _ _ _ check_{k}_{n}_{r}
""")
    cases = '\n'.join(f'  | {r}, _ => exact ⟨_, keyGoal_{k}_{n}_{r}⟩' for r in range(k + 1))
    return HEADER + imports + f"""

/-!
# `K₂,{n}` is enumeratively chromatic-choosable at {k}

Generated by `TwoDegenerate/K2n/gen_k2n.py`: one certificate per overlap of the hub lists.
-/

namespace SimpleGraph.TwoDegenerate.K2n.Data

""" + '\n'.join(parts) + f"""
theorem eccAt_{k}_{n} : (completeBipartiteGraph (Fin 2) (Fin {n})).ECCAt {k} := by
  intro L hL
  rw [colConst_K2n]
  refine le_col_of_keyGoals (fun r hr => ?_) L hL
  match r, hr with
{cases}

end SimpleGraph.TwoDegenerate.K2n.Data
"""


def positive_file(k):
    N = THRESHOLDS[k]
    imports = '\n'.join(f'import TwoDegenerate.K2n.Cert.K{k}N{n}' for n in range(N + 1))
    cases = '\n'.join(f'  | {n}, _ => Data.eccAt_{k}_{n}' for n in range(N + 1))
    cases += f'\n  | _ + {N + 1}, h => absurd h (by omega)'
    return HEADER + imports + f"""

/-!
# `K₂,ₙ` is ECC at {k} for every `n ≤ {N}`

One generated certificate file per `n` (`TwoDegenerate/K2n/Cert/K{k}N*.lean`).
-/

namespace SimpleGraph.TwoDegenerate.K2n

theorem eccAt_{k}_of_le {{n : ℕ}} (hn : n ≤ {N}) :
    (completeBipartiteGraph (Fin 2) (Fin n)).ECCAt {k} :=
  match n, hn with
{cases}

end SimpleGraph.TwoDegenerate.K2n
"""


def main():
    compare = '--check' in sys.argv
    only = [int(a) for a in sys.argv[1:] if a.isdigit()]
    files = {}
    for k, N in THRESHOLDS.items():
        if only and k not in only:
            continue
        orders, Ws = {}, {}
        for r in range(k + 1):
            types, W = setup(k, r)
            order = branch_order(k, r)
            orders[r], Ws[r] = order, W[order]
            keys = [[x in types[i] for x in range(2 * k - r)] for i in order]
            files[f'Keys/K{k}R{r}.lean'] = keys_file(k, r, keys, Ws[r])
        for n in range(N + 1):
            T = target(k, n)
            certs = []
            for r in range(k + 1):
                t = build(Ws[r], n, T)
                assert check(Ws[r], 0, [1] * (k * k), n, t, T), (k, n, r)
                certs.append(t)
            print(f'k = {k}, n = {n}: nodes', [count(t, 'nodes') for t in certs], flush=True)
            files[f'Cert/K{k}N{n}.lean'] = cert_file(k, n, certs)
        files[f'Positive{k}.lean'] = positive_file(k)
    ok = True
    for rel, src in files.items():
        path = os.path.join(HERE, rel)
        if compare:
            same = os.path.exists(path) and open(path).read() == src
            ok &= same
            if not same:
                print('DIFFERS', rel)
        else:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            open(path, 'w').write(src)
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
