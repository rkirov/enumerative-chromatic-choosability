/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import TwoDegenerate.Counterexample
import TwoDegenerate.K2n.Main
import TwoDegenerate.K2nSqrt.Main

/-!
# Two-degenerate graphs and enumerative chromatic choosability

`TwoDegenerate.Counterexample` refutes the proposed uniform theorem that every 2-degenerate graph
is enumeratively chromatic-choosable at every list size at least four.  It gives an exact,
kernel-checked four-list witness on `K₂,₂₆`.

`TwoDegenerate.K2n.Main` proves that `K₂,₂₅` *is* enumeratively chromatic-choosable at four,
so `K₂,ₙ` is ECC at four exactly for `n ≤ 25`: a reduction of every four-list assignment to one
numeric inequality per hub-list overlap (`TwoDegenerate/K2n/Reduction.lean`), each closed by a
kernel-checked AM–GM branch-and-bound certificate (`TwoDegenerate/K2n/Checker.lean`,
`TwoDegenerate/K2n/R0.lean` … `R4.lean`).

`TwoDegenerate.K2nSqrt.Main` proves that `K₂,ₙ` is ECC at every `k ≥ 300` with `n ≤ k²`, so
`τ(K₂,ₙ) = O(√n)`; with Theorem 4 of Kaul–Kumar–Mudrock–Rewers–Shin–To (arXiv:2202.03431) this
settles their Conjecture 5, `τ(K₂,ₙ) = Θ(√n)`. The proof is class AM–GM over the hub-colour pairs
(`TwoDegenerate/K2nSqrt/Classes.lean`) and a four-regime real inequality
(`TwoDegenerate/K2nSqrt/Analytic.lean`).
-/
