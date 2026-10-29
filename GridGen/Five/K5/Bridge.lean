/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.K5.Cone
import GridGen.Explicit

/-!
# Height five at `k = 5`: the statement and the bridge to GridGen's hypotheses

`GridGen/Five/Statement.lean`, `Bridge.lean` and `Final.lean` at `k = 5`, with the weights in the
cone `InCone5` (`GridGen/Five/K5/Cone.lean`) in place of the `k = 6` box.

* `Seam55Holds`: for every weight in the cone, every previous column with lists `X` of four or
  five colours and every next column with `5`-lists `B`, the weighted successors from `B`
  dominate the uniform prediction, summed over the proper states of `X`.
* `Init55Holds`: a column of `5`-lists, weighted by pattern, weighs at least the uniform column.

The reference `Φ` of GridGen at `k = 5` is `fseq5 i · gw (wseq5 i)` on proper states (`Φ_eq5`),
with `wseq5 i` in the cone (`wseq5_inCone`), so the two inequalities give GridGen's explicit
two-step, first-seam and initial hypotheses, and `ecc_pathG_four_of_holds5` the grid.
-/

namespace GridGen.Five.K5

open Finset SimpleGraph ListColoring GridGen.Five
open scoped SimpleGraph

/-! ### The statement -/

/-- **The height-five seam inequality at `k = 5`**, on the cone. -/
def Seam55Holds : Prop :=
  ∀ (w : Wt5), InCone5 w →
  ∀ (X₁ X₂ X₃ X₄ X₅ B₁ B₂ B₃ B₄ B₅ : Finset ℕ),
    (4 ≤ X₁.card ∧ X₁.card ≤ 5) → (4 ≤ X₂.card ∧ X₂.card ≤ 5) →
    (4 ≤ X₃.card ∧ X₃.card ≤ 5) → (4 ≤ X₄.card ∧ X₄.card ≤ 5) →
    (4 ≤ X₅.card ∧ X₅.card ≤ 5) →
    B₁.card = 5 → B₂.card = 5 → B₃.card = 5 → B₄.card = 5 → B₅.card = 5 →
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 5 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GB w B₁ B₂ B₃ B₄ B₅ s

/-- **The height-five initial inequality at `k = 5`**, on the cone. -/
def Init55Holds : Prop :=
  ∀ (w : Wt5), InCone5 w →
  ∀ (X₁ X₂ X₃ X₄ X₅ : Finset ℕ),
    X₁.card = 5 → X₂.card = 5 → X₃.card = 5 → X₄.card = 5 → X₅.card = 5 →
    ∑ s ∈ sts (range 5) (range 5) (range 5) (range 5) (range 5), gw w s
      ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, gw w s

/-! ### The reference at `k = 5` -/

/-- **The reference by pattern** at `k = 5`. -/
theorem Φ_eq5 (i : ℕ) {s : State V5} (hs : Proper (toT s)) :
    (Φ (pathG 4) 5 i s : ℝ) = fseq5 i * gw (wseq5 i) (toT s) := by
  unfold Φ
  rw [F_eq_Fu, Fu_eq5 i _ (proper_patCap (by norm_num) hs) (rowsIn_patCap (by norm_num) s),
    gw_congr _ (samePat_patCap (by norm_num) s)]

/-- **One step of the reference** at `k = 5`. -/
theorem Φ_succ_eq5 (i : ℕ) {s : State V5} (hs : Proper (toT s)) :
    (Φ (pathG 4) 5 (i + 1) s : ℝ) = fseq5 i * GU 5 (wseq5 i) (toT s) := by
  unfold Φ
  rw [F_eq_Fu, Fu_succ_eq5 i (proper_patCap (by norm_num) hs) (rowsIn_patCap (by norm_num) s),
    GU_congr 5 _ (canon_congr (samePat_patCap (by norm_num) s))]

theorem sum_succ_Φ5 (i : ℕ) (B : Lists V5) (s : State V5) :
    ∑ t ∈ (states (pathG 4) B).filter (Compat s), (Φ (pathG 4) 5 i t : ℝ)
      = fseq5 i * GB (wseq5 i) (B q1) (B q2) (B q3) (B q4) (B q5) (toT s) := by
  rw [sum_states5_filter, GB, G, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Φ_eq5 i (by rw [toT_ofT]; exact proper_of_mem_sts ht), toT_ofT]

theorem seam_sum5 (hS : Seam55Holds) (i : ℕ) (X B : Lists V5)
    (hX : ∀ v, 5 - 1 ≤ (X v).card ∧ (X v).card ≤ 5) (hB : ∀ v, (B v).card = 5) :
    ∑ t ∈ sts (X q1) (X q2) (X q3) (X q4) (X q5), (Φ (pathG 4) 5 (i + 1) (ofT t) : ℝ)
      ≤ ∑ t ∈ sts (X q1) (X q2) (X q3) (X q4) (X q5),
          ∑ u ∈ (states (pathG 4) B).filter (Compat (ofT t)), (Φ (pathG 4) 5 i u : ℝ) := by
  have hl : ∀ t ∈ sts (X q1) (X q2) (X q3) (X q4) (X q5),
      (Φ (pathG 4) 5 (i + 1) (ofT t) : ℝ) = fseq5 i * GU 5 (wseq5 i) t := by
    intro t ht
    rw [Φ_succ_eq5 i (by rw [toT_ofT]; exact proper_of_mem_sts ht), toT_ofT]
  have hr : ∀ t ∈ sts (X q1) (X q2) (X q3) (X q4) (X q5),
      ∑ u ∈ (states (pathG 4) B).filter (Compat (ofT t)), (Φ (pathG 4) 5 i u : ℝ)
        = fseq5 i * GB (wseq5 i) (B q1) (B q2) (B q3) (B q4) (B q5) t := by
    intro t _
    rw [sum_succ_Φ5 i B (ofT t), toT_ofT]
  rw [Finset.sum_congr rfl hl, Finset.sum_congr rfl hr, ← Finset.mul_sum, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (hS _ (wseq5_inCone i) _ _ _ _ _ _ _ _ _ _ (hX q1) (hX q2) (hX q3) (hX q4) (hX q5) (hB q1)
      (hB q2) (hB q3) (hB q4) (hB q5))
    (fseq5_pos i).le

/-- **The explicit two-step inequality for `pathG 4` at `k = 5`.** -/
theorem twoStepExplicit_of_seam5 (hS : Seam55Holds) : TwoStepExplicit (pathG 4) 5 := by
  intro L hL j s₀ _ i
  have key := seam_sum5 hS i (fun v => (L (j + 1) v).erase (s₀ v)) (L (j + 1 + 1))
    (fun v => ⟨by have := Finset.pred_card_le_card_erase (s := L (j + 1) v) (a := s₀ v)
                  rw [hL (j + 1) v] at this; exact this,
               by have := Finset.card_erase_le (s := L (j + 1) v) (a := s₀ v)
                  rw [hL (j + 1) v] at this; exact this⟩)
    (fun v => hL (j + 1 + 1) v)
  rw [← sum_states5_filter (L (j + 1)) s₀ (fun s => (Φ (pathG 4) 5 (i + 1) s : ℝ)),
    ← sum_states5_filter (L (j + 1)) s₀
      (fun s => ∑ u ∈ (states (pathG 4) (L (j + 1 + 1))).filter (Compat s),
        (Φ (pathG 4) 5 i u : ℝ))] at key
  unfold cols
  exact_mod_cast key

/-- **The explicit first seam for `pathG 4` at `k = 5`.** -/
theorem firstSeamExplicit_of_seam5 (hS : Seam55Holds) : FirstSeamExplicit (pathG 4) 5 := by
  intro L hL i
  have key := seam_sum5 hS i (L 0) (L 1)
    (fun v => ⟨by rw [hL 0 v]; norm_num, by rw [hL 0 v]⟩) (fun v => hL 1 v)
  rw [← sum_states5 (L 0) (fun s => (Φ (pathG 4) 5 (i + 1) s : ℝ)),
    ← sum_states5 (L 0) (fun s => ∑ u ∈ (states (pathG 4) (L 1)).filter (Compat s),
        (Φ (pathG 4) 5 i u : ℝ))] at key
  unfold cols
  exact_mod_cast key

/-- **The initial condition for `pathG 4` at `k = 5`.** -/
theorem init_of_init55 (hI : Init55Holds) : Init (pathG 4) 5 := by
  intro X hX n
  have hL : ∑ s ∈ states (pathG 4) (unif 5), (F (pathG 4) 5 n s : ℝ)
      = fseq5 n * ∑ t ∈ sts (range 5) (range 5) (range 5) (range 5) (range 5), gw (wseq5 n) t := by
    rw [sum_states5, Finset.mul_sum]
    simp only [unif_apply5]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [F_eq_Fu, toT_ofT, Fu_eq5 n t (proper_of_mem_sts ht)]
    rw [mem_sts] at ht
    exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1⟩
  have hR : ∑ s ∈ states (pathG 4) X, (Φ (pathG 4) 5 n s : ℝ)
      = fseq5 n * ∑ t ∈ sts (X q1) (X q2) (X q3) (X q4) (X q5), gw (wseq5 n) t := by
    rw [sum_states5, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Φ_eq5 n (by rw [toT_ofT]; exact proper_of_mem_sts ht), toT_ofT]
  have key : ∑ s ∈ states (pathG 4) (unif 5), (F (pathG 4) 5 n s : ℝ)
      ≤ ∑ s ∈ states (pathG 4) X, (Φ (pathG 4) 5 n s : ℝ) := by
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_left
      (hI _ (wseq5_inCone n) _ _ _ _ _ (hX q1) (hX q2) (hX q3) (hX q4) (hX q5)) (fseq5_pos n).le
  exact_mod_cast key

/-- **`P₅ □ P_{n+1}` is `5`-ECC, given the height-five seam and initial inequalities at
`k = 5`.** -/
theorem ecc_pathG_four_of_holds5 (hS : Seam55Holds) (hI : Init55Holds) (n : ℕ) :
    (pathG 4 □ pathG n).ECCAt 5 :=
  ecc_of_explicit (pathG 4) (twoStepExplicit_of_seam5 hS) (firstSeamExplicit_of_seam5 hS)
    (init_of_init55 hI) n

end GridGen.Five.K5
