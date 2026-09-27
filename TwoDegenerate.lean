/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import TwoDegenerate.Counterexample
import TwoDegenerate.K2n.Main

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
-/
