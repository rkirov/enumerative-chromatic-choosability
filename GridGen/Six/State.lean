/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.Pattern
import GridGen.Six.Pins

/-!
# Height six at `k = 6`: the bound for one state

For a proper previous column `s` and next `6`-lists `B₁, …, B₆`, the successors are the proper
colourings from `Aᵢ = Bᵢ.erase sᵢ`, of sizes `nᵢ = 5 + [sᵢ ∉ Bᵢ]`.

* **The count** (`N6g_le_card`, `GridGen/Six/Count.lean`): `|sts A|` is at least the greedy
  value `N6g` of the interval relaxation (`greedy_min6`). Codex's `N*` is this value, checked at
  all 614,383 nonempty relaxations (`ai_research_notes/cx/h6k6/NOTE.md`, review §3); only the
  inequality, proved symbolically, is needed here. For the kernel, `N6g` is the difference of
  two natural-number polynomials (`N6gP`, `N6gM`, `N6gPM_eq`).
* **The state bound** (`state66`): with the pattern lemma (`pattern66`),
  `10¹² · N6g(n, e) · GU ≤ R(n, o(s)) · NUo · GB`, i.e. `GB ≥ GU · (1 + V)`,
  `V = 10¹² N6g / (R · NU) - 1` (the review's state value).
-/

namespace GridGen.Six

open Finset

/-! ### The greedy value in natural numbers -/

/-- The positive part of `N6g`, with the greedy profile in truncated subtraction. -/
def N6gP (n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 : ℕ) : ℕ :=
  let t1 := e1 + e2 - n2
  let t2 := e2 + e3 - n3
  let t3 := e3 + e4 - n4
  let t4 := e4 + e5 - n5
  let q1 := min t1 t2
  let q2 := min t2 t3
  let q3 := min t3 t4
  let p1 := q1 + q2 - t2
  let p2 := q2 + q3 - t3
  p1 * n6 + q1 * e5 + t1 * t4 + t1 * n4 * n5 * n6 + e1 * q3 + e1 * e3 * n5 * n6
    + e1 * n3 * e4 * n6 + e1 * n3 * n4 * e5 + n1 * p2 + n1 * t2 * n5 * n6 + n1 * e2 * e4 * n6
    + n1 * e2 * n4 * e5 + n1 * n2 * t3 * n6 + n1 * n2 * e3 * e5 + n1 * n2 * n3 * t4
    + n1 * n2 * n3 * n4 * n5 * n6

/-- The negative part of `N6g`. -/
def N6gM (n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 : ℕ) : ℕ :=
  let t1 := e1 + e2 - n2
  let t2 := e2 + e3 - n3
  let t3 := e3 + e4 - n4
  let t4 := e4 + e5 - n5
  let q1 := min t1 t2
  let q2 := min t2 t3
  let q3 := min t3 t4
  let p1 := q1 + q2 - t2
  let p2 := q2 + q3 - t3
  min p1 p2 + q1 * n5 * n6 + t1 * e4 * n6 + t1 * n4 * e5 + e1 * t3 * n6 + e1 * e3 * e5
    + e1 * n3 * t4 + e1 * n3 * n4 * n5 * n6 + n1 * q2 * n6 + n1 * t2 * e5 + n1 * e2 * t4
    + n1 * e2 * n4 * n5 * n6 + n1 * n2 * q3 + n1 * n2 * e3 * n5 * n6 + n1 * n2 * n3 * e4 * n6
    + n1 * n2 * n3 * n4 * e5

theorem N6gPM_eq (n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 : ℕ) :
    (N6gP n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 : ℤ) - N6gM n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5
      = N6g n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 := by
  simp only [N6gP, N6gM, N6g, H6, N6z]
  have c1 : ((e1 + e2 - n2 : ℕ) : ℤ) = max 0 ((e1 : ℤ) + e2 - n2) := by omega
  have c2 : ((e2 + e3 - n3 : ℕ) : ℤ) = max 0 ((e2 : ℤ) + e3 - n3) := by omega
  have c3 : ((e3 + e4 - n4 : ℕ) : ℤ) = max 0 ((e3 : ℤ) + e4 - n4) := by omega
  have c4 : ((e4 + e5 - n5 : ℕ) : ℤ) = max 0 ((e4 : ℤ) + e5 - n5) := by omega
  set T1 := e1 + e2 - n2
  set T2 := e2 + e3 - n3
  set T3 := e3 + e4 - n4
  set T4 := e4 + e5 - n5
  have m1 : ((min T1 T2 : ℕ) : ℤ) = min (T1 : ℤ) T2 := by omega
  have m2 : ((min T2 T3 : ℕ) : ℤ) = min (T2 : ℤ) T3 := by omega
  have m3 : ((min T3 T4 : ℕ) : ℤ) = min (T3 : ℤ) T4 := by omega
  have p1 : ((min T1 T2 + min T2 T3 - T2 : ℕ) : ℤ)
      = max 0 (min (T1 : ℤ) T2 + min (T2 : ℤ) T3 - T2) := by omega
  have p2 : ((min T2 T3 + min T3 T4 - T3 : ℕ) : ℤ)
      = max 0 (min (T2 : ℤ) T3 + min (T3 : ℤ) T4 - T3) := by omega
  have x : ((min (min T1 T2 + min T2 T3 - T2) (min T2 T3 + min T3 T4 - T3) : ℕ) : ℤ)
      = min (max 0 (min (T1 : ℤ) T2 + min (T2 : ℤ) T3 - T2))
          (max 0 (min (T2 : ℤ) T3 + min (T3 : ℤ) T4 - T3)) := by omega
  push_cast
  rw [p1, p2, c1, c2, c3, c4]
  ring

/-! ### The state bound -/

/-- **The bound for one state**, in the sizes of the successor lists. -/
theorem state66 {w : Wt6} (hw : InCone6 w) {B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ}
    (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6) (hB₄ : B₄.card = 6)
    (hB₅ : B₅.card = 6) (hB₆ : B₆.card = 6) {s : T6} (hs : Proper s) :
    (1000000000000 : ℝ) * (N6g (B₁.erase (r1 s)).card (B₂.erase (r2 s)).card
        (B₃.erase (r3 s)).card (B₄.erase (r4 s)).card (B₅.erase (r5 s)).card
        (B₆.erase (r6 s)).card
        ((B₁.erase (r1 s)) ∩ (B₂.erase (r2 s))).card ((B₂.erase (r2 s)) ∩ (B₃.erase (r3 s))).card
        ((B₃.erase (r3 s)) ∩ (B₄.erase (r4 s))).card ((B₄.erase (r4 s)) ∩ (B₅.erase (r5 s))).card
        ((B₅.erase (r5 s)) ∩ (B₆.erase (r6 s))).card : ℝ) * GU 6 w s
      ≤ Rof (B₁.erase (r1 s)).card (B₂.erase (r2 s)).card (B₃.erase (r3 s)).card
          (B₄.erase (r4 s)).card (B₅.erase (r5 s)).card (B₆.erase (r6 s)).card (orb s)
          * NUo (orb s) * GB w B₁ B₂ B₃ B₄ B₅ B₆ s := by
  have c1 := card_erase56 hB₁ (r1 s)
  have c2 := card_erase56 hB₂ (r2 s)
  have c3 := card_erase56 hB₃ (r3 s)
  have c4 := card_erase56 hB₄ (r4 s)
  have c5 := card_erase56 hB₅ (r5 s)
  have c6 := card_erase56 hB₆ (r6 s)
  have hp := pattern66 hw (orb s) c1 c2 c3 c4 c5 c6
  have hN := N6g_le_card (A₁ := B₁.erase (r1 s)) (A₂ := B₂.erase (r2 s))
    (A₃ := B₃.erase (r3 s)) (A₄ := B₄.erase (r4 s)) (A₅ := B₅.erase (r5 s))
    (A₆ := B₆.erase (r6 s)) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hN' : (N6g (B₁.erase (r1 s)).card (B₂.erase (r2 s)).card (B₃.erase (r3 s)).card
        (B₄.erase (r4 s)).card (B₅.erase (r5 s)).card (B₆.erase (r6 s)).card
        ((B₁.erase (r1 s)) ∩ (B₂.erase (r2 s))).card ((B₂.erase (r2 s)) ∩ (B₃.erase (r3 s))).card
        ((B₃.erase (r3 s)) ∩ (B₄.erase (r4 s))).card ((B₄.erase (r4 s)) ∩ (B₅.erase (r5 s))).card
        ((B₅.erase (r5 s)) ∩ (B₆.erase (r6 s))).card : ℝ)
      ≤ (sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))
          (B₅.erase (r5 s)) (B₆.erase (r6 s))).card := by exact_mod_cast hN
  have hU : 0 ≤ GU 6 w s := GU_nonneg hw s
  rw [GU_six w hs] at hU ⊢
  unfold GB
  have := mul_le_mul_of_nonneg_left hN' (by positivity : (0 : ℝ) ≤ 1000000000000)
  have := mul_le_mul_of_nonneg_right this hU
  linarith

end GridGen.Six
