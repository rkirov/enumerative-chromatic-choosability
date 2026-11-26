/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.MarkTerms

/-!
# Cyclic sums: closing a face at any of its edges

The count of a face with all its sides loaded, written as a sum over the colourings of the
cycle (`cycSum`). It is invariant under rotation (`cycSum_rot`), and read at any edge `r` it is
the face profile of the other sides glued to the table of `r` (`cycSum_root`). So a face can be
closed at whichever side a case analysis prefers (`close_glue`, `close_count`), and the expansion
of the side classes into alternatives commutes with it (`cycSum_expand`).

Formalized by Claude (milestone M3 of `ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`).
-/

namespace Outerplanar

open Finset

variable {m : ℕ}

/-- **The sum over the colourings of a cycle of length `m + 2`** of the products of its edge
tables; the table `F i` sits between the lists `C i` and `C (i + 1)`. -/
noncomputable def cycSum (C : Fin (m + 2) → Finset ℕ) (F : Fin (m + 2) → ℕ → ℕ → ℝ) : ℝ :=
  ∑ g ∈ Fintype.piFinset C, ∏ i, F i (g i) (g (i + 1))

theorem cycSum_nonneg (C : Fin (m + 2) → Finset ℕ) {F : Fin (m + 2) → ℕ → ℕ → ℝ}
    (hF : ∀ i c d, 0 ≤ F i c d) : 0 ≤ cycSum C F :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => hF _ _ _

/-- **Rotation.** -/
theorem cycSum_rot (C : Fin (m + 2) → Finset ℕ) (F : Fin (m + 2) → ℕ → ℕ → ℝ) (s : Fin (m + 2)) :
    cycSum (fun i => C (i + s)) (fun i => F (i + s)) = cycSum C F := by
  unfold cycSum
  refine Finset.sum_nbij' (fun g j => g (j - s)) (fun g i => g (i + s)) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    rw [Fintype.mem_piFinset] at hg ⊢
    intro j
    have := hg (j - s)
    rwa [sub_add_cancel] at this
  · intro g hg
    rw [Fintype.mem_piFinset] at hg ⊢
    exact fun i => hg (i + s)
  · intro g _; funext i; simp
  · intro g _; funext j; simp
  · intro g _
    refine Fintype.prod_equiv (Equiv.addRight s) _ _ fun i => ?_
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    congr 2
    rw [show i + s + 1 - s = i + 1 by abel]

/-- The tables of a face with its root edge: the path edges, then the root table. -/
def cycF (E : Fin (m + 1) → ℕ → ℕ → ℝ) (W' : ℕ → ℕ → ℝ) : Fin (m + 2) → ℕ → ℕ → ℝ :=
  Fin.lastCases (motive := fun _ => ℕ → ℕ → ℝ) W' E

theorem cycF_castSucc (E : Fin (m + 1) → ℕ → ℕ → ℝ) (W' : ℕ → ℕ → ℝ) (j : Fin (m + 1)) :
    cycF E W' j.castSucc = E j := by simp [cycF]

theorem cycF_last (E : Fin (m + 1) → ℕ → ℕ → ℝ) (W' : ℕ → ℕ → ℝ) :
    cycF E W' (Fin.last (m + 1)) = W' := by simp [cycF]

/-- **A face glued to its root table is a cyclic sum.** -/
theorem closing_eq (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ) (E : Fin (m + 1) → ℕ → ℕ → ℝ)
    (W' : ℕ → ℕ → ℝ) :
    ∑ d ∈ Lv, ∑ c ∈ Lu, W' d c * faceSum Li (fun _ _ => 1) E c d
      = cycSum (pathList Lu Lv Li) (cycF E W') := by
  classical
  unfold cycSum faceSum
  simp only [Finset.prod_const_one, one_mul, Finset.mul_sum]
  rw [← Finset.sum_product', ← Finset.sum_product']
  refine Finset.sum_nbij' (fun x => pathCol x.1.2 x.1.1 x.2)
    (fun g => ((g (Fin.last (m + 1)), g 0), fun k => g k.castSucc.succ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨d, c⟩, h⟩ hx
    rw [Finset.mem_product, Finset.mem_product, Fintype.mem_piFinset] at hx
    rw [Fintype.mem_piFinset]
    intro i
    exact pathCol_mem hx.1.2 hx.1.1 hx.2 i
  · intro g hg
    rw [Fintype.mem_piFinset] at hg
    rw [Finset.mem_product, Finset.mem_product, Fintype.mem_piFinset]
    refine ⟨⟨?_, ?_⟩, fun k => ?_⟩
    · have := hg (Fin.last (m + 1))
      rwa [show pathList Lu Lv Li (Fin.last (m + 1)) = Lv from
        consSnoc_last _ _ _ _ (by simp)] at this
    · have := hg 0
      rwa [show pathList Lu Lv Li 0 = Lu from consSnoc_zero _ _ _ _ rfl] at this
    · have := hg k.castSucc.succ
      rwa [show pathList Lu Lv Li k.castSucc.succ = Li k from
        consSnoc_mid _ _ _ _ k (by simp)] at this
  · rintro ⟨⟨d, c⟩, h⟩ _
    simp only [Prod.mk.injEq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← Fin.succ_last, pathCol_succ_last]
    · simp [pathCol]
    · funext k; exact pathCol_succ_castSucc c d h k
  · intro g _
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [pathCol]
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · rw [pathCol_succ_last, Fin.succ_last]
      · rw [pathCol_succ_castSucc]
  · rintro ⟨⟨d, c⟩, h⟩ _
    simp only
    symm
    rw [Fin.prod_univ_castSucc (f := fun x => cycF E W' x (pathCol c d h x) (pathCol c d h (x + 1))),
      cycF_last, mul_comm]
    congr 1
    · rw [Fin.last_add_one, ← Fin.succ_last, pathCol_succ_last]
      simp [pathCol]
    · refine Finset.prod_congr rfl fun j _ => ?_
      rw [cycF_castSucc, Fin.coeSucc_eq_succ]

/-- The lists of a cycle are the lists of the path around it. -/
theorem pathList_cyc (C : Fin (m + 2) → Finset ℕ) :
    pathList (C 0) (C (Fin.last (m + 1))) (fun k : Fin m => C k.castSucc.succ) = C := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pathList]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [Fin.succ_last]; exact consSnoc_last _ _ _ _ (by simp)
    · exact consSnoc_mid _ _ _ _ k (by simp)

/-- **A cyclic sum read at the edge `r`**: the root edge of the face is `r`, the path starts at
`r + 1`. -/
theorem cycSum_root (C : Fin (m + 2) → Finset ℕ) (F : Fin (m + 2) → ℕ → ℕ → ℝ) (r : Fin (m + 2)) :
    cycSum C F = ∑ d ∈ C r, ∑ c ∈ C (r + 1), F r d c *
      faceSum (fun k : Fin m => C (k.castSucc.succ + (r + 1))) (fun _ _ => 1)
        (fun j => F (j.castSucc + (r + 1))) c d := by
  have hl : Fin.last (m + 1) + (r + 1) = r := by
    rw [add_comm r 1, ← add_assoc, Fin.last_add_one, zero_add]
  rw [← cycSum_rot C F (r + 1)]
  have e := closing_eq (C (0 + (r + 1))) (C (Fin.last (m + 1) + (r + 1)))
    (fun k : Fin m => C (k.castSucc.succ + (r + 1))) (fun j => F (j.castSucc + (r + 1)))
    (F (Fin.last (m + 1) + (r + 1)))
  rw [zero_add, hl] at e
  rw [e]
  congr 1
  · have := pathList_cyc (fun i => C (i + (r + 1)))
    simp only [zero_add, hl] at this
    exact this.symm
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [cycF_last, hl]
    · rw [cycF_castSucc]

/-- The lists of the face read at `r`. -/
theorem pathList_root (C : Fin (m + 2) → Finset ℕ) (r : Fin (m + 2)) (i : Fin (m + 2)) :
    pathList (C (r + 1)) (C r) (fun k : Fin m => C (k.castSucc.succ + (r + 1))) i
      = C (i + (r + 1)) := by
  have hl : Fin.last (m + 1) + (r + 1) = r := by
    rw [add_comm r 1, ← add_assoc, Fin.last_add_one, zero_add]
  have := congrFun (pathList_cyc (fun i => C (i + (r + 1)))) i
  simp only [zero_add, hl] at this
  exact this

/-- The sides of the face read at `r`, from the sides of the cycle. -/
theorem side_root {C : Fin (m + 2) → Finset ℕ} {F : Fin (m + 2) → ℕ → ℕ → ℝ}
    (Q : Fin (m + 2) → Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → Prop)
    (h : ∀ i, Q i (C i) (C (i + 1)) (F i)) (r : Fin (m + 2)) (j : Fin (m + 1)) :
    Q (j.castSucc + (r + 1))
      (pathList (C (r + 1)) (C r) (fun k : Fin m => C (k.castSucc.succ + (r + 1))) j.castSucc)
      (pathList (C (r + 1)) (C r) (fun k : Fin m => C (k.castSucc.succ + (r + 1))) j.succ)
      (F (j.castSucc + (r + 1))) := by
  rw [pathList_root, pathList_root, ← Fin.coeSucc_eq_succ,
    show j.castSucc + 1 + (r + 1) = j.castSucc + (r + 1) + 1 by abel]
  exact h _

/-- The product of the constants of the face read at `r`. -/
theorem prod_root (f : Fin (m + 2) → ℝ) (r : Fin (m + 2)) :
    (∏ j : Fin (m + 1), f (j.castSucc + (r + 1))) * f r = ∏ i, f i := by
  have hl : Fin.last (m + 1) + (r + 1) = r := by
    rw [add_comm r 1, ← add_assoc, Fin.last_add_one, zero_add]
  have := Fin.prod_univ_castSucc (fun i => f (i + (r + 1)))
  rw [hl] at this
  rw [← this]
  exact Fintype.prod_equiv (Equiv.addRight (r + 1)) _ _ fun i => rfl

/-- **Closing at the edge `r` by the glue**: the face read at `r` has the hexagon bound, and so
has the table of `r`. -/
theorem close_glue (C : Fin (m + 2) → Finset ℕ) (hC : ∀ i, (C i).card = 3)
    (F : Fin (m + 2) → ℕ → ℕ → ℝ) (hF0 : ∀ i c d, 0 ≤ F i c d) (r : Fin (m + 2)) {N M : ℝ}
    (hN : 0 < N) (hM : 0 < M)
    (hface : Hex (C (r + 1)) (C r) (faceSum (fun k : Fin m => C (k.castSucc.succ + (r + 1)))
      (fun _ _ => 1) (fun j => F (j.castSucc + (r + 1)))) N)
    (hroot : Hex (C r) (C (r + 1)) (F r) M) :
    6 * (N * M) ≤ cycSum C F := by
  rw [cycSum_root C F r]
  have key := Hex.glue (hC _) (hC _) hface hroot.swap' hN hM
    (faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one) fun j c d => hF0 _ c d)
    (fun c d => hF0 r d c)
  refine key.trans (le_of_eq ?_)
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => mul_comm _ _

/-- **Closing at a constant edge `r` by the count**: the table of `r` is at least `M` on proper
pairs and the face read at `r` has at least `X` colourings with different ends. -/
theorem close_count (C : Fin (m + 2) → Finset ℕ) (F : Fin (m + 2) → ℕ → ℕ → ℝ)
    (hF0 : ∀ i c d, 0 ≤ F i c d) (r : Fin (m + 2)) {M X : ℝ} (hM : 0 ≤ M)
    (hroot : Dominant (C r) (C (r + 1)) (F r) M)
    (hcount : X ≤ ∑ c ∈ C (r + 1), ∑ d ∈ C r, if c = d then 0 else
      faceSum (fun k : Fin m => C (k.castSucc.succ + (r + 1))) (fun _ _ => 1)
        (fun j => F (j.castSucc + (r + 1))) c d) :
    M * X ≤ cycSum C F := by
  rw [cycSum_root C F r, Finset.sum_comm]
  have hFn := faceSum_nonneg (fun k : Fin m => C (k.castSucc.succ + (r + 1))) (fun _ _ => 1)
    (fun j => F (j.castSucc + (r + 1))) (fun _ _ _ => zero_le_one) fun j c d => hF0 _ c d
  calc M * X ≤ M * ∑ c ∈ C (r + 1), ∑ d ∈ C r, if c = d then 0 else
        faceSum (fun k : Fin m => C (k.castSucc.succ + (r + 1))) (fun _ _ => 1)
          (fun j => F (j.castSucc + (r + 1))) c d := mul_le_mul_of_nonneg_left hcount hM
    _ = ∑ c ∈ C (r + 1), ∑ d ∈ C r, M * (if c = d then 0 else
        faceSum (fun k : Fin m => C (k.castSucc.succ + (r + 1))) (fun _ _ => 1)
          (fun j => F (j.castSucc + (r + 1))) c d) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by rw [Finset.mul_sum]
    _ ≤ _ := by
        refine Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun d hd => ?_
        split_ifs with hcd
        · rw [mul_zero]; exact mul_nonneg (hF0 _ _ _) (hFn _ _)
        · exact mul_le_mul_of_nonneg_right (hroot d hd c hc (Ne.symm hcd)) (hFn _ _)

/-- **The expansion of a cyclic sum**: each table dominates a sum of alternatives on its lists. -/
theorem cycSum_expand {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Fin (m + 2) → Finset ℕ)
    (F : Fin (m + 2) → ℕ → ℕ → ℝ) (G : Fin (m + 2) → ι → ℕ → ℕ → ℝ)
    (hG0 : ∀ i r c d, 0 ≤ G i r c d)
    (hle : ∀ i, ∀ c ∈ C i, ∀ d ∈ C (i + 1), ∑ r, G i r c d ≤ F i c d) :
    ∑ ρ : Fin (m + 2) → ι, cycSum C (fun i => G i (ρ i)) ≤ cycSum C F := by
  unfold cycSum
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun g hg => ?_
  have hmem : ∀ i, g i ∈ C i := fun i => Fintype.mem_piFinset.mp hg i
  calc ∑ ρ : Fin (m + 2) → ι, ∏ i, G i (ρ i) (g i) (g (i + 1))
      = ∏ i, ∑ r, G i r (g i) (g (i + 1)) := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ ≤ ∏ i, F i (g i) (g (i + 1)) :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun r _ => hG0 i r _ _)
          fun i _ => hle i _ (hmem i) _ (hmem (i + 1))

end Outerplanar
