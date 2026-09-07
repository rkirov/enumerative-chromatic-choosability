import Grid3.Three.GraphBridge

/-!
# Final count inequality from an actual-colour entropy model

`colConst_le_col_of_model` is the last analytic/model step needed by `Assembly.entropy_half`.
It concludes the actual `pathG` grid counting inequality, and accepts either the nonuniform
root bound or a root deficit paid by one strong seam. All support, count, and recurrence
bridges are discharged here.

What is NOT proved here: construction of these laws and kernels from an arbitrary three-list
assignment. In particular, the hypotheses below must still be supplied by canonicalization,
the finite certificate, and pattern-preserving transport. This is not an unconditional ECC
theorem.
-/

namespace Grid3.Three

open SimpleGraph ListColoring Finset Real
open scoped SimpleGraph

/-- A normalized nonnegative path measure has nonempty positive support. -/
theorem path_support_card_pos {S : Type*} [Fintype S]
    (alpha : S → ℝ) (K : ℕ → S → S → ℝ) (n : ℕ)
    (hα : ∀ s, 0 ≤ alpha s) (hαsum : ∑ s, alpha s = 1)
    (hK : ∀ k c s, 0 ≤ K k c s) (hKn : ∀ k c, ∑ s, K k c s = 1) :
    0 < (Finset.univ.filter (fun p : PState S n => 0 < mu alpha K n p)).card := by
  classical
  have hsum := mu_sum_one alpha K hαsum hKn n
  obtain ⟨p, _, hp⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun p _ => mu_nonneg alpha K hα hK n p)).mp (by rw [hsum]; norm_num)
  exact Finset.card_pos.mpr ⟨p, by simp [hp]⟩

/-- The actual height-three grid count inequality from local colour-level model data.
Only constructing the data remains; no global measure or colouring-count obligations are hidden.
The seam bounds may freely mix collision, fourth-root, rowwise collision, and exact Parry proofs. -/
theorem colConst_le_col_of_model (n C : ℕ)
    (L : ListAssignment (PathV 2 × PathV n))
    (law : ℕ → (Fin 3 → Fin C) → ℝ)
    (K : ℕ → (Fin 3 → Fin C) → (Fin 3 → Fin C) → ℝ)
    (hL : ∀ k s, 0 ≤ law k s) (hLsum : ∑ s, law 0 s = 1)
    (hK : ∀ k c s, 0 ≤ K k c s) (hKn : ∀ k c, ∑ s, K k c s = 1)
    (hstep : ∀ k, k < n → ∀ s, ∑ c, law k c * K k c s = law (k + 1) s)
    (hval : ∀ (j : Fin (n + 1)) s, 0 < law j s →
      ∀ i, (s i).val ∈ L ((Model.gridIso n).symm (i, j)))
    (hvert : ∀ (j : Fin (n + 1)) s, 0 < law j s →
      ∀ i i', i.val + 1 = i'.val → s i ≠ s i')
    (hcompat : ∀ k, k < n → ∀ c s, 0 < law k c → 0 < K k c s → ∀ i, c i ≠ s i)
    (hseam : ∀ k, k < n → Real.log rho ≤ ∑ c, law k c * rowH (K k) c)
    (hroot : Real.log 12 ≤ H (law 0) ∨
      (Real.log 12 - Real.log (18 / 17) ≤ H (law 0) ∧
        ∃ j : Fin n, Real.log rho + Real.log (18 / 17) ≤ ∑ c, law j c * rowH (K j) c)) :
    (pathG 2 □ pathG n).colConst 3 ≤ (pathG 2 □ pathG n).col L := by
  let L' : Model.Vtx (n + 1) → Finset ℕ := L ∘ (Model.gridIso n).symm
  let N := (Model.properC (Model.gridAdj (n + 1)) L').card
  have hcard := Model.support_card_le_properC n L' law K hL hK hstep hval hvert hcompat
  have hN : 0 < N := lt_of_lt_of_le
    (path_support_card_pos (law 0) K n (hL 0) hLsum hK hKn) hcard
  have hbound : (a n : ℝ) ≤ N := by
    rcases hroot with hroot | ⟨hroot, j, hbonus⟩
    · exact entropy_from_row_bounds (n + 1) N law K (hL 0) hLsum hK hKn
        hstep hN hcard hroot hseam
    · exact entropy_from_row_bounds_one_bonus (n + 1) N law K j (Real.log (18 / 17))
        (hL 0) hLsum hK hKn hstep hN hcard hroot hseam hbonus
  have hNeq : (pathG 2 □ pathG n).col L = N := Model.col_eq_properC n L
  rw [← Model.colConst_three_eq_a, ← hNeq] at hbound
  exact_mod_cast hbound

end Grid3.Three
