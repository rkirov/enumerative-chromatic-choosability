/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Mix
import Outerplanar.LongDesign6
import Outerplanar.BlockFaces

/-!
# Branching at faces of length at least six

**`ecc_three_of_blocks_squareOK`**: a graph with a block decomposition (`Outerplanar/BlockModel.lean`)
is 3-ECC if at every square of every block, seen from any of its edges, at most one child region
contains an even face. Bridges, cut vertices, odd faces and even faces of length at least six are
unrestricted, and there is no bound on the number of even faces. **`ecc_three_of_blocks_noSquare`**
is the special case where no block has a square face.

The proof instantiates the generic building of `Outerplanar/BranchBuild.lean` with two tags. A
region without even faces carries the greedy class (`Dominant`). Every other region carries the
mixture class `BMix` of `Outerplanar/Mix.lean`: a mixture of the constant one and a member of
`(17/16) · B`.

* `bmix_face` — the face rule. Expand the mixtures on the path edges multilinearly. A term with no
  loaded edge is a bare face: odd faces are greedy (`domFaceClosed_odd`), even faces are mixtures
  (`bmix_even_bare`). A term with one loaded edge is in the ball class with its full constant
  (`BallFaceClosed`). A term with `s ≥ 2` loaded edges is a member of the ball class: at odd faces
  with the full constant (`ballOddClosed`, `ballTriClosed`), at even faces of length at least six
  with the factor `16/17` (`ballEvenSix`: `ballHex` and `ballEvenLong`), and
  `(16/17)(17/16)^s ≥ 17/16`. At squares at most one edge may be loaded.
* `lfSys`, `lfRule`, `lfV` — the class system, the face rule and the vertex rule, with their
  soundness (`lfRule_sound`, `lf_glue`, `lfV_sound`, `lfSys_transposable`).
* `ruleOn_lf` — the face rule holds at the root face of every side (`marksR_side`).

This is the theorem of the research note
`ai_research_notes/OUTERPLANAR_BRANCHING_SQUARES_2026-11-23.md` (another AI session of this
repository's collaboration). In the note the condition at squares is asked only from a chosen root
(and branches at a cut vertex may be put on either incident path edge); here it is asked from every
edge of the square, with the branches at an interior vertex of a face counted with the path edge
after it. Formalized by Claude.
-/

namespace Outerplanar

open Finset

/-! ### The face rule -/

theorem prod_gain {n : ℕ} (ρ : Fin n → Fin 2) :
    ∏ j, (if ρ j = 0 then (1 : ℝ) else 17 / 16) = (17 / 16) ^ (univ.filter fun j => ¬ ρ j = 0).card := by
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]

theorem fin_two_ne_zero {r : Fin 2} (h : ¬ r = 0) : r = 1 := by
  rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with h' | h'
  · exact absurd h' h
  · exact h'

/-- **The face rule of the mixture class.** The path edges in `P` are greedy; at squares at
most one path edge is not. -/
theorem bmix_face {m : ℕ} (hm1 : 1 ≤ m) (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ)
    (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 < A j) (P : Fin (m + 1) → Prop)
    (hE : ∀ j, BMix (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j))
    (hP : ∀ j, P j →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j))
    (hshort : m = 2 → ∀ j j', ¬ P j → ¬ P j' → j = j') :
    BMix Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  classical
  have hrep : ∀ j, ∃ (u v : ℝ) (Y : ℕ → ℕ → ℝ), 0 ≤ u ∧ 0 ≤ v ∧ A j ≤ u + v ∧
      (∀ c d, 0 ≤ Y c d) ∧
      InBall (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) Y (v * (17 / 16)) ∧
      (∀ c ∈ pathList Lu Lv Li j.castSucc, ∀ d ∈ pathList Lu Lv Li j.succ, c ≠ d →
        u + Y c d ≤ E j c d) ∧ (P j → v = 0) := fun j => by
    by_cases hPj : P j
    · refine ⟨A j, 0, fun _ _ => 0, (hA j).le, le_refl 0, by simp, fun _ _ => le_refl 0,
        by rw [zero_mul]; exact InBall.zero fun _ _ => le_refl 0,
        fun c hc d hd hcd => by simpa using hP j hPj c hc d hd hcd, fun _ => rfl⟩
    · obtain ⟨u, v, Y, h1, h2, h3, h4, h5, h6⟩ := hE j
      exact ⟨u, v, Y, h1, h2, h3, h4, h5, h6, fun h => absurd h hPj⟩
  choose u v Y hu hv huv hY0 hY hEY hPv using hrep
  set w : Fin (m + 1) → Fin 2 → ℝ := fun j r => if r = 0 then u j else v j with hw
  set G : Fin (m + 1) → Fin 2 → ℕ → ℕ → ℝ :=
    fun j r c d => if c ≠ d then (if r = 0 then u j else Y j c d) else 0 with hG
  have hG0 : ∀ j r c d, 0 ≤ G j r c d := fun j r c d => by
    simp only [hG]
    split_ifs
    · exact hu j
    · exact hY0 j c d
    · exact le_refl 0
  have hw0 : ∀ j r, 0 ≤ w j r := fun j r => by
    simp only [hw]
    split_ifs
    · exact hu j
    · exact hv j
  have hα := faceConst3_pos m
  have hle : ∀ c ∈ Lu, ∀ d ∈ Lv, c ≠ d →
      faceSum Li (fun _ _ => 1) (fun j c d => ∑ r, G j r c d) c d
        ≤ faceSum Li (fun _ _ => 1) E c d := fun c hc d hd _ => by
    refine faceSum_le_of_le (fun j c d => Finset.sum_nonneg fun r _ => hG0 j r c d)
      (fun j c hc d hd => ?_) hc hd
    rw [Fin.sum_univ_two]
    by_cases hcd : c = d
    · simp only [hG, hcd, ne_eq, not_true_eq_false, ite_false, add_zero]
      exact hE0 _ _ _
    · simp only [hG, ne_eq, hcd, not_false_eq_true, ite_true, one_ne_zero, ite_false]
      exact hEY j c hc d hd hcd
  refine BMix.mono ?_ hle
  have hfun : faceSum Li (fun _ _ => 1) (fun j c d => ∑ r, G j r c d)
      = fun c d => ∑ ρ : Fin (m + 1) → Fin 2,
          faceSum Li (fun _ _ => 1) (fun j => G j (ρ j)) c d :=
    funext fun c => funext fun d => faceSum_sum2 Li G c d
  rw [hfun]
  have hconst : faceConst3 m * ∏ j, A j
      ≤ ∑ ρ : Fin (m + 1) → Fin 2, faceConst3 m * ∏ j, w j (ρ j) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hα.le
    have e : ∀ j, u j + v j = ∑ r, w j r := fun j => by
      simp only [hw, Fin.sum_univ_two, ite_true, one_ne_zero, ite_false]
    calc ∏ j, A j ≤ ∏ j, (u j + v j) :=
          Finset.prod_le_prod₀ (fun j _ => (hA j).le) fun j _ => huv j
      _ = ∑ ρ : Fin (m + 1) → Fin 2, ∏ j, w j (ρ j) := by
          simp only [e]
          rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine BMix.weaken hconst (BMix.finsum univ _ _ (fun ρ _ c d => faceSum_nonneg _ _ _
    (fun _ _ _ => zero_le_one) (fun j c d => hG0 j (ρ j) c d) c d) fun ρ _ => ?_)
  -- one term
  have hT0 : ∀ c d, 0 ≤ faceSum Li (fun _ _ => 1) (fun j => G j (ρ j)) c d :=
    faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one) (fun j c d => hG0 j (ρ j) c d)
  by_cases hz : ∃ j, w j (ρ j) = 0
  · obtain ⟨j, hj⟩ := hz
    rw [Finset.prod_eq_zero (mem_univ j) hj, mul_zero]
    exact BMix.zero hT0
  push Not at hz
  have hwpos : ∀ j, 0 < w j (ρ j) := fun j => lt_of_le_of_ne (hw0 j (ρ j)) (hz j).symm
  -- the two kinds of path edges
  have hG_0 : ∀ j, ρ j = 0 → G j (ρ j) = fun c d => if c ≠ d then u j else 0 := fun j h => by
    funext c d; simp only [hG, h, ite_true]
  have hG_1 : ∀ j, ¬ ρ j = 0 → G j (ρ j) = fun c d => if c ≠ d then Y j c d else 0 :=
    fun j h => by funext c d; simp only [hG, h, ite_false]
  have hw_0 : ∀ j, ρ j = 0 → w j (ρ j) = u j := fun j h => by simp only [hw, h, ite_true]
  have hw_1 : ∀ j, ¬ ρ j = 0 → w j (ρ j) = v j := fun j h => by simp only [hw, h, ite_false]
  have hdom : ∀ j, ρ j = 0 → Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
      (G j (ρ j)) (w j (ρ j)) := fun j h c _ d _ hcd => by
    rw [hG_0 j h, hw_0 j h]
    simp [hcd]
  set A' : Fin (m + 1) → ℝ := fun j => w j (ρ j) * (if ρ j = 0 then 1 else 17 / 16) with hA'
  have hA'pos : ∀ j, 0 < A' j := fun j => mul_pos (hwpos j) (by split_ifs <;> norm_num)
  have hball : ∀ j, InBall (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
      (G j (ρ j)) (A' j) := fun j => by
    by_cases h : ρ j = 0
    · have : A' j = w j (ρ j) := by simp only [hA', h, ite_true, mul_one]
      rw [this]
      exact Dominant.inBall (hw0 j (ρ j)) (hdom j h)
    · have : A' j = v j * (17 / 16) := by simp only [hA', h, ite_false, hw_1 j h]
      rw [this, hG_1 j h]
      exact (hY j).mask (hY0 j)
  set s := (univ.filter fun j => ¬ ρ j = 0).card with hs
  have hprodA' : ∏ j, A' j = (∏ j, w j (ρ j)) * (17 / 16) ^ s := by
    rw [hA', Finset.prod_mul_distrib, prod_gain]
  have hW0 : 0 ≤ ∏ j, w j (ρ j) := prod_nonneg fun j _ => hw0 j (ρ j)
  have hK0 : 0 ≤ faceConst3 m * ∏ j, w j (ρ j) := mul_nonneg hα.le hW0
  rcases Nat.lt_or_ge s 2 with hs2 | hs2
  · rcases Nat.lt_or_ge s 1 with hs1 | hs1
    · -- a bare face
      have h0 : ∀ j, ρ j = 0 := fun j => by
        by_contra h
        have : j ∈ univ.filter fun j => ¬ ρ j = 0 := mem_filter.mpr ⟨mem_univ j, h⟩
        have := card_pos.mpr ⟨j, this⟩
        omega
      rcases Nat.even_or_odd m with he | ho
      · exact bmix_even_bare he (by obtain ⟨k, hk⟩ := he; omega) Lu Lv Li hLu hLv hLi _
          (fun j c d => hG0 j (ρ j) c d) _ (fun j => hw0 j (ρ j)) fun j => hdom j (h0 j)
      · exact BMix.of_dom hK0 (domFaceClosed_odd m ho Lu Lv Li hLi _
          (fun j c d => hG0 j (ρ j) c d) _ hwpos fun j => hdom j (h0 j))
    · -- one loaded edge
      obtain ⟨j₀, hj₀⟩ := card_eq_one.mp (show s = 1 by omega)
      have hρ : ∀ j, j ≠ j₀ → ρ j = 0 := fun j hj => by
        by_contra h
        have : j ∈ univ.filter fun j => ¬ ρ j = 0 := mem_filter.mpr ⟨mem_univ j, h⟩
        rw [hj₀] at this
        exact hj (mem_singleton.mp this)
      have hb := ballFaceClosed_of_bare (ballFaceBare_all m) Lu Lv Li hLu hLv hLi j₀
        (fun j => G j (ρ j)) (fun j c d => hG0 j (ρ j) c d) A' hA'pos (hball j₀)
        fun j hj => by
          have : A' j = w j (ρ j) := by simp only [hA', hρ j hj, ite_true, mul_one]
          rw [this]
          exact hdom j (hρ j hj)
      refine BMix.of_ball hK0 hT0 ?_
      rw [hprodA', show s = 1 by omega, pow_one, ← mul_assoc] at hb
      exact hb
  · -- at least two loaded edges
    obtain ⟨j₁, hj₁, j₂, hj₂, hj₁₂⟩ := one_lt_card.mp (show 1 < s by omega)
    have hρ₁ := (mem_filter.mp hj₁).2
    have hρ₂ := (mem_filter.mp hj₂).2
    have hgain : (17 / 16 : ℝ) ^ 2 ≤ (17 / 16) ^ s := pow_le_pow_right₀ (by norm_num) hs2
    refine BMix.of_ball hK0 hT0 ?_
    rcases Nat.even_or_odd m with he | ho
    · -- even faces: at least six
      have h4 : 4 ≤ m := by
        by_contra h
        have hm24 : m = 2 := by obtain ⟨k, hk⟩ := he; omega
        have hnP : ∀ j, ¬ ρ j = 0 → ¬ P j := fun j hj hPj => by
          have := hwpos j
          rw [hw_1 j hj, hPv j hPj] at this
          exact lt_irrefl 0 this
        exact hj₁₂ (hshort hm24 j₁ j₂ (hnP j₁ hρ₁) (hnP j₂ hρ₂))
      have hb := ballEvenSix m he h4 Lu Lv Li hLu hLv hLi (fun j => G j (ρ j))
        (fun j c d => hG0 j (ρ j) c d) A' hA'pos hball
      refine hb.weaken (by positivity) ?_
      rw [hprodA']
      have : (17 / 16 : ℝ) ≤ 16 / 17 * (17 / 16) ^ s := by
        calc (17 / 16 : ℝ) = 16 / 17 * (17 / 16) ^ 2 := by norm_num
          _ ≤ 16 / 17 * (17 / 16) ^ s := mul_le_mul_of_nonneg_left hgain (by norm_num)
      calc (faceConst3 m * ∏ j, w j (ρ j)) * (17 / 16)
          ≤ (faceConst3 m * ∏ j, w j (ρ j)) * (16 / 17 * (17 / 16) ^ s) :=
          mul_le_mul_of_nonneg_left this hK0
        _ = 16 / 17 * faceConst3 m * ((∏ j, w j (ρ j)) * (17 / 16) ^ s) := by ring
    · -- odd faces
      have hb : InBall Lu Lv (faceSum Li (fun _ _ => 1) fun j => G j (ρ j))
          (faceConst3 m * ∏ j, A' j) := by
        rcases Nat.lt_or_ge m 3 with h3 | h3
        · obtain rfl : m = 1 := by obtain ⟨k, hk⟩ := ho; omega
          rw [faceConst3_one, one_mul]
          exact ballTriClosed Lu Lv Li hLu hLv hLi _ (fun j c d => hG0 j (ρ j) c d) A' hA'pos
            hball
        · exact ballOddClosed m ho h3 Lu Lv Li hLu hLv hLi _ (fun j c d => hG0 j (ρ j) c d) A'
            hA'pos hball
      refine hb.weaken (by positivity) ?_
      rw [hprodA']
      have : (17 / 16 : ℝ) ≤ (17 / 16) ^ s :=
        le_trans (by norm_num) hgain
      calc (faceConst3 m * ∏ j, w j (ρ j)) * (17 / 16)
          ≤ (faceConst3 m * ∏ j, w j (ρ j)) * (17 / 16) ^ s :=
          mul_le_mul_of_nonneg_left this hK0
        _ = faceConst3 m * ((∏ j, w j (ρ j)) * (17 / 16) ^ s) := by ring

/-! ### The class system -/

/-- The classes: `false` greedy, `true` the mixture class. -/
def lfCls : Bool → Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop
  | false, S, T, W, A => Dominant S T W A
  | true, S, T, W, A => BMix S T W A

theorem lfCls_bmix {t : Bool} {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (h : lfCls t S T W A) : BMix S T W A := by
  cases t
  · exact BMix.of_dom hA h
  · exact h

/-- **The class system of the branching theorem.** -/
def lfSys : ClassSys where
  Tag := Bool
  plain := false
  cls := lfCls
  of_dom := fun t S T W A hA h => by
    cases t
    · exact h
    · exact BMix.of_dom hA h
  dom_of_plain := fun _ _ _ _ h => h
  mul_dom := fun t S T W W' A A' hA hA' hW _ hd h => by
    cases t
    · exact Dominant.mul hA' hA hd h
    · exact BMix.mul_dom hA' hW hd h

/-- **The face rule**: a side without even faces has an odd root face and children without even
faces; at squares at most one child has even faces. -/
def lfRule : Bool → (m : ℕ) → (Fin (m + 1) → Bool) → Prop
  | false, m, τ => Odd m ∧ ∀ j, τ j = false
  | true, m, τ => 1 ≤ m ∧ (m = 2 → ∀ j j', τ j = true → τ j' = true → j = j')

theorem lfRule_sound {t : Bool} {m : ℕ} {τ : Fin (m + 1) → Bool} (h : lfRule t m τ) :
    lfSys.RuleSound t m τ := by
  intro Lu Lv Li hLu hLv hLi E hE0 A hA hE
  cases t
  · obtain ⟨ho, hτ⟩ := h
    have hE' : ∀ j, Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j)
        (A j) := fun j => by
      have := hE j
      rw [hτ j] at this
      exact this
    exact domFaceClosed_odd m ho Lu Lv Li hLi E hE0 A hA hE'
  · obtain ⟨hm1, hsh⟩ := h
    refine bmix_face hm1 Lu Lv Li hLu hLv hLi E hE0 A hA (fun j => τ j = false)
      (fun j => lfCls_bmix (hA j).le (hE j)) (fun j hj => ?_) fun hm j j' h1 h2 =>
        hsh hm j j' (by simpa using h1) (by simpa using h2)
    have := hE j
    rw [hj] at this
    exact this

theorem lf_glue (t₁ t₂ : Bool) : lfSys.GlueSound t₁ t₂ := by
  intro S T W W' A A' hS hT h0 h0' hA hA' h₁ h₂
  have b₁ := lfCls_bmix hA.le h₁
  have b₂ := (lfCls_bmix hA'.le h₂).swap
  have hb := (BMix.mul hA'.le b₁ b₂).inBall (by positivity)
  have key := hb.sum_ge hS hT (by positivity) fun c d => mul_nonneg (h0 c d) (h0' d c)
  rw [Finset.sum_comm]
  refine key.trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => mul_comm _ _

/-- **The vertex rule**: a region without even faces splits into regions without even faces. -/
def lfV (t t₀ t₁ : Bool) : Prop := t = true ∨ (t₀ = false ∧ t₁ = false)

theorem lfV_sound {t t₀ t₁ : Bool} (h : lfV t t₀ t₁) : lfSys.VertexSound t t₀ t₁ := by
  intro Lv Ly Lw hv hy hw W X X' hW hX hX' A A₁ A₂ hA hA₁ hA₂ h₀ h₁ h₂
  have hX'D : Dominant Lw Lv X' A₂ := h₂
  set F : ℕ → ℝ := fun c => ∑ e ∈ Lw, X c e * X' e c with hF
  have hF0 : ∀ c, 0 ≤ F c := fun c => Finset.sum_nonneg fun e _ =>
    mul_nonneg (hX _ _) (hX' _ _)
  have hconst : A * (2 * A₁ * A₂) = A * (A₂ * (2 * A₁)) := by ring
  rcases h with rfl | ⟨rfl, rfl⟩
  · -- the mixture class
    have hb₀ := lfCls_bmix hA.le h₀
    have hb₁ := lfCls_bmix hA₁.le h₁
    have hL := lift_bmix (U := Ly) hv hw hy hb₁
    have hL' : BMix Lv Ly (fun c _ => A₂ * liftV Lw X c) (A₂ * (2 * A₁)) :=
      BMix.mul_dom (W := fun c _ => liftV Lw X c) (W' := fun _ _ => A₂) hA₂.le
        (fun c _ => liftV_nonneg hX c) (fun _ _ _ _ _ => le_refl _) hL
    have hB : BMix Lv Ly (fun c _ => F c) (A₂ * (2 * A₁)) :=
      hL'.mono fun c hc _ _ _ => branch_ge hX hX' hX'D hc
    show BMix Lv Ly (fun c d => W c d * F c) (A * (2 * A₁ * A₂))
    rw [hconst]
    exact BMix.mul (by positivity) hb₀ hB
  · -- greedy
    have hW : Dominant Lv Ly W A := h₀
    have hXD : Dominant Lv Lw X A₁ := h₁
    have hFD : Dominant Lv Ly (fun c _ => F c) (A₂ * (2 * A₁)) := fun c hc d hd hcd => by
      have k1 := lift_dom (U := Ly) hA₁.le hw hXD c hc d hd hcd
      have k2 := branch_ge hX hX' hX'D hc
      simp only at k1 ⊢
      nlinarith
    refine lfSys.of_dom t _ _ _ _ (by positivity) ?_
    show Dominant Lv Ly (fun c d => W c d * F c) (A * (2 * A₁ * A₂))
    rw [hconst]
    exact Dominant.mul hA.le (by positivity) hW hFD

theorem lfSys_transposable : lfSys.Transposable := fun t S T W A h => by
  cases t
  · exact Dominant.swap h
  · exact BMix.swap h

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Every graph built by ears, pendant edges and reorientations under the branching rules is
3-ECC.** -/
theorem ecc_three_of_lfBuiltW (G : SimpleGraph V) [DecidableRel G.Adj] {tg : V → V → Bool}
    (h : TagBuiltW G lfSys lfRule (fun _ _ => True) lfV univ tg) : G.ECCAt 3 :=
  ecc_three_of_tagBuiltW G (fun _ _ _ hr => lfRule_sound hr) (fun t₁ t₂ _ => lf_glue t₁ t₂)
    (fun _ _ _ hr => lfV_sound hr) lfSys_transposable h

/-! ### Block decompositions -/

namespace BlockDecomp

variable (D : BlockDecomp G ι)

/-- **The tag of a region**: whether it contains an even face. -/
noncomputable def lfTag (U : Finset V) : Bool := decide (0 < D.marksR U)

/-- At every square of every block, seen from any of its edges, at most one child region contains
an even face. -/
def SquareOK : Prop :=
  ∀ (j : ι) (c a b : Fin (D.n j)) (m : ℕ) (r : Fin (m + 2) → Fin (D.n j)),
    (D.vH j c).Adj a b → a < b → RootEnum (D.vH j c) a b m r → m = 2 →
    ∀ i i', 0 < D.marksR (childR (D.vψ j c) (D.vhang j c) r i) →
      0 < D.marksR (childR (D.vψ j c) (D.vhang j c) r i') → i = i'

variable {D}

/-- **The face rule holds at the root face of every side.** -/
theorem ruleOn_lf (hD : D.SquareOK) (U : Finset V) :
    RuleOn (R := lfSys) D lfRule D.lfTag U := by
  intro j c a b m r hadj hab he _
  have hms := marksR_side hadj hab he
  unfold lfTag
  rcases Nat.eq_zero_or_pos (D.marksR (sideR (D.vψ j c) (D.vhang j c) a b)) with h0 | hpos
  · rw [h0] at hms
    have hodd : ¬ Even (m + 2) := fun hev => by simp [hev] at hms; omega
    have hch : ∀ i, D.marksR (childR (D.vψ j c) (D.vhang j c) r i) = 0 := fun i => by
      have := Finset.single_le_sum (f := fun i => D.marksR (childR (D.vψ j c) (D.vhang j c) r i))
        (fun _ _ => Nat.zero_le _) (mem_univ i)
      omega
    rw [h0]
    show lfRule false m _
    refine ⟨?_, fun i => by simp [hch i]⟩
    rcases Nat.even_or_odd m with he' | ho
    · exact absurd (by obtain ⟨k, hk⟩ := he'; exact ⟨k + 1, by omega⟩) hodd
    · exact ho
  · have ht : decide (0 < D.marksR (sideR (D.vψ j c) (D.vhang j c) a b)) = true :=
      decide_eq_true hpos
    rw [ht]
    exact ⟨he.one_le, fun hm i i' h1 h2 => hD j c a b m r hadj hab he hm i i'
      (of_decide_eq_true h1) (of_decide_eq_true h2)⟩

theorem splitOK_lf : SplitOK (R := lfSys) D lfV D.lfTag := by
  intro j z₀ X hx hX
  have h := marksR_union (sep_brR hx hX)
  unfold lfTag lfV
  rw [h]
  rcases Nat.eq_zero_or_pos (D.marksR X + D.marksR (D.brR j z₀)) with h0 | hpos
  · right
    exact ⟨decide_eq_false (by omega), decide_eq_false (by omega)⟩
  · left
    exact decide_eq_true hpos

end BlockDecomp

open BlockDecomp

/-- **A graph with a block decomposition is 3-ECC if at every square of every block, seen from any
of its edges, at most one child region contains an even face.** Bridges, cut vertices, isolated
vertices, odd faces and even faces of length at least six are unrestricted; there is no bound on the
number of even faces. -/
theorem ecc_three_of_blocks_squareOK (D : BlockDecomp G ι) (hD : D.SquareOK) : G.ECCAt 3 := by
  classical
  have key : ∀ (n : ℕ) (s : Finset V), s.card ≤ n → (∀ v ∈ s, ∀ w, G.Reachable v w → w ∈ s) →
      ∃ tg, TagBuiltW G lfSys lfRule (fun _ _ => True) lfV s tg := by
    intro n
    induction n with
    | zero =>
      intro s hs _
      have : s = ∅ := card_eq_zero.mp (by omega)
      subst this
      exact ⟨_, TagBuiltW.empty (fun _ _ => false)⟩
    | succ n ih =>
      intro s hs hcl
      rcases s.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
      · exact ⟨_, TagBuiltW.empty (fun _ _ => false)⟩
      set K := compR G v₀ with hK
      have hKs : K ⊆ s := fun w hw => hcl v₀ hv₀ w (mem_compR.mp hw)
      have hv₀K : v₀ ∈ K := mem_compR.mpr (SimpleGraph.Reachable.refl _)
      have hcl' : ∀ v ∈ s \ K, ∀ w, G.Reachable v w → w ∈ s \ K := by
        intro v hv w hw
        obtain ⟨hvs, hvK⟩ := mem_sdiff.mp hv
        refine mem_sdiff.mpr ⟨hcl v hvs w hw, fun hwK => hvK ?_⟩
        exact mem_compR.mpr ((mem_compR.mp hwK).trans hw.symm)
      have hcard : (s \ K).card ≤ n := by
        have := card_lt_card ((ssubset_iff_of_subset (sdiff_subset (s := s) (t := K))).mpr
          ⟨v₀, hv₀, fun h => (mem_sdiff.mp h).2 hv₀K⟩)
        omega
      obtain ⟨tg', hT'⟩ := ih (s \ K) hcard hcl'
      have hset : s \ K ∪ K = s := sdiff_union_of_subset hKs
      by_cases hblk : ∃ (i : ι) (y : Fin (D.n i)), G.Reachable v₀ (D.ψ i y)
      · obtain ⟨i, y₀, h₀⟩ := hblk
        have hn := D.two_le i
        have hpq : (D.H i).Adj ⟨0, by omega⟩ ⟨1, by omega⟩ := (D.diss i).1 _ _ rfl
        have hr : G.Reachable v₀ (D.ψ i ⟨0, by omega⟩) := h₀.trans (block_reachable _ _)
        obtain ⟨tg, h⟩ := buildComp (D := D) (R := lfSys) (rule := lfRule)
          (glue := fun _ _ => True) (vrule := lfV) (tagR := D.lfTag) splitOK_lf i _ _ hpq
          trivial (ruleOn_lf hD _) (ruleOn_lf hD _) (s \ K) tg' hT'
          (fun v hv hrv => (mem_sdiff.mp hv).2 (mem_compR.mpr (hr.trans hrv)))
        rw [halves_union hpq.ne, compR_eq hr, ← hK, hset] at h
        exact ⟨tg, h⟩
      · -- an isolated vertex
        push Not at hblk
        have hiso : ∀ w, ¬ G.Adj v₀ w := fun w h => by
          obtain ⟨i, a, b, -, ha, -⟩ := (D.adj v₀ w).mp h
          exact hblk i a (by rw [ha])
        have hK1 : K = {v₀} := by
          ext w
          rw [mem_singleton, mem_compR]
          refine ⟨fun h => ?_, fun h => h ▸ SimpleGraph.Reachable.refl _⟩
          exact reach_closed (G' := G) (s := v₀) (P := fun w => w = v₀) rfl
            (fun u w _ huw hu => absurd (hu ▸ huw) (hiso w)) h
        have := TagBuiltW.iso (s \ K) tg' v₀ (fun h => (mem_sdiff.mp h).2 hv₀K)
          (fun z _ => hiso z) hT'
        have hs' : insert v₀ (s \ K) = s := by rw [insert_eq, union_comm, ← hK1, hset]
        rw [hs'] at this
        exact ⟨tg', this⟩
  obtain ⟨tg, h⟩ := key _ univ le_rfl fun _ _ _ _ => mem_univ _
  exact ecc_three_of_lfBuiltW G h

/-- **A graph with a block decomposition none of whose blocks has a square face is 3-ECC**, with
any number of even faces. -/
theorem ecc_three_of_blocks_noSquare (D : BlockDecomp G ι)
    (hsq : ∀ (i : ι) (F : Finset (Fin (D.n i))), IsFace (D.H i) F → F.card ≠ 4) :
    G.ECCAt 3 := by
  refine ecc_three_of_blocks_squareOK D fun j c a b m r hadj hab he hm => ?_
  exfalso
  have hmem : rootOcc j c a b ∈ D.facesR (sideR (D.vψ j c) (D.vhang j c) a b) := by
    rw [facesR_side hadj hab he]
    exact mem_insert_self _ _
  have hF := (mem_facesR.mp hmem).1
  have hcard := card_rootOcc (D := D) he
  have := hsq _ _ hF
  omega

end Outerplanar

/-! The two statements depend on no axioms beyond the three standard ones. -/

/-- info: 'Outerplanar.ecc_three_of_blocks_squareOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Outerplanar.ecc_three_of_blocks_squareOK

/-- info: 'Outerplanar.ecc_three_of_blocks_noSquare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Outerplanar.ecc_three_of_blocks_noSquare
