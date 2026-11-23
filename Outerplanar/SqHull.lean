/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.SqHullData0
import Outerplanar.SqHullData1
import Outerplanar.SqHullData2
import Outerplanar.SqHullData3
import Outerplanar.SqHullData4
import Outerplanar.SqHullData5
import Outerplanar.SqData.Table

/-!
# A square over a branch in the hull class

**`tb_square_hull`**: a square whose loaded path edge has a profile of the hull class
(`Outerplanar/HullClass.lean`), and greedy profiles on its other path edges, has the four-cell
bound `1/2` on its root edge. With the matching bound (`hasPot_face3`) this is the last
single-face lemma of the six-even-face theorem: a square above a branch with one square.

The proof follows `ballFaceBare_two_of_cover` (`Outerplanar/Square.lean`): the lists are put in
normal form, the covering table of `Outerplanar/SqData/` puts the pattern below one of 52
patterns, and for each of those and each loaded edge the certificates of
`Outerplanar/SqHullData*.lean` give the bound (`sqHullOK_all`, through `genHull_of_case`).

Part of the formalization of the six-even-face theorem (research note
`ai_research_notes/OUTERPLANAR_SIX_EVEN_2026-11-23.md`, by a ChatGPT session; there checked
over 4202 list configurations, minimum `171500 / 9⁶`, which is also the minimum here).
-/

namespace Outerplanar

open Finset

/-- **Every pattern of the list passes, at every loaded edge.** -/
theorem sqHullOK_all : ∀ q, q < SqData.qs.length → ∀ e,
    SqHullOK (patOfCode (SqData.qs.getD q 0)) e := by
  intro q hq e
  have hq' : q < 52 := by
    have : SqData.qs.length = 52 := rfl
    omega
  interval_cases q <;> fin_cases e
  · exact genHull_of_case SqHullData.hc0_0 SqHullData.hc0_0_ok
  · exact genHull_of_case SqHullData.hc0_1 SqHullData.hc0_1_ok
  · exact genHull_of_case SqHullData.hc0_2 SqHullData.hc0_2_ok
  · exact genHull_of_case SqHullData.hc1_0 SqHullData.hc1_0_ok
  · exact genHull_of_case SqHullData.hc1_1 SqHullData.hc1_1_ok
  · exact genHull_of_case SqHullData.hc1_2 SqHullData.hc1_2_ok
  · exact genHull_of_case SqHullData.hc2_0 SqHullData.hc2_0_ok
  · exact genHull_of_case SqHullData.hc2_1 SqHullData.hc2_1_ok
  · exact genHull_of_case SqHullData.hc2_2 SqHullData.hc2_2_ok
  · exact genHull_of_case SqHullData.hc3_0 SqHullData.hc3_0_ok
  · exact genHull_of_case SqHullData.hc3_1 SqHullData.hc3_1_ok
  · exact genHull_of_case SqHullData.hc3_2 SqHullData.hc3_2_ok
  · exact genHull_of_case SqHullData.hc4_0 SqHullData.hc4_0_ok
  · exact genHull_of_case SqHullData.hc4_1 SqHullData.hc4_1_ok
  · exact genHull_of_case SqHullData.hc4_2 SqHullData.hc4_2_ok
  · exact genHull_of_case SqHullData.hc5_0 SqHullData.hc5_0_ok
  · exact genHull_of_case SqHullData.hc5_1 SqHullData.hc5_1_ok
  · exact genHull_of_case SqHullData.hc5_2 SqHullData.hc5_2_ok
  · exact genHull_of_case SqHullData.hc6_0 SqHullData.hc6_0_ok
  · exact genHull_of_case SqHullData.hc6_1 SqHullData.hc6_1_ok
  · exact genHull_of_case SqHullData.hc6_2 SqHullData.hc6_2_ok
  · exact genHull_of_case SqHullData.hc7_0 SqHullData.hc7_0_ok
  · exact genHull_of_case SqHullData.hc7_1 SqHullData.hc7_1_ok
  · exact genHull_of_case SqHullData.hc7_2 SqHullData.hc7_2_ok
  · exact genHull_of_case SqHullData.hc8_0 SqHullData.hc8_0_ok
  · exact genHull_of_case SqHullData.hc8_1 SqHullData.hc8_1_ok
  · exact genHull_of_case SqHullData.hc8_2 SqHullData.hc8_2_ok
  · exact genHull_of_case SqHullData.hc9_0 SqHullData.hc9_0_ok
  · exact genHull_of_case SqHullData.hc9_1 SqHullData.hc9_1_ok
  · exact genHull_of_case SqHullData.hc9_2 SqHullData.hc9_2_ok
  · exact genHull_of_case SqHullData.hc10_0 SqHullData.hc10_0_ok
  · exact genHull_of_case SqHullData.hc10_1 SqHullData.hc10_1_ok
  · exact genHull_of_case SqHullData.hc10_2 SqHullData.hc10_2_ok
  · exact genHull_of_case SqHullData.hc11_0 SqHullData.hc11_0_ok
  · exact genHull_of_case SqHullData.hc11_1 SqHullData.hc11_1_ok
  · exact genHull_of_case SqHullData.hc11_2 SqHullData.hc11_2_ok
  · exact genHull_of_case SqHullData.hc12_0 SqHullData.hc12_0_ok
  · exact genHull_of_case SqHullData.hc12_1 SqHullData.hc12_1_ok
  · exact genHull_of_case SqHullData.hc12_2 SqHullData.hc12_2_ok
  · exact genHull_of_case SqHullData.hc13_0 SqHullData.hc13_0_ok
  · exact genHull_of_case SqHullData.hc13_1 SqHullData.hc13_1_ok
  · exact genHull_of_case SqHullData.hc13_2 SqHullData.hc13_2_ok
  · exact genHull_of_case SqHullData.hc14_0 SqHullData.hc14_0_ok
  · exact genHull_of_case SqHullData.hc14_1 SqHullData.hc14_1_ok
  · exact genHull_of_case SqHullData.hc14_2 SqHullData.hc14_2_ok
  · exact genHull_of_case SqHullData.hc15_0 SqHullData.hc15_0_ok
  · exact genHull_of_case SqHullData.hc15_1 SqHullData.hc15_1_ok
  · exact genHull_of_case SqHullData.hc15_2 SqHullData.hc15_2_ok
  · exact genHull_of_case SqHullData.hc16_0 SqHullData.hc16_0_ok
  · exact genHull_of_case SqHullData.hc16_1 SqHullData.hc16_1_ok
  · exact genHull_of_case SqHullData.hc16_2 SqHullData.hc16_2_ok
  · exact genHull_of_case SqHullData.hc17_0 SqHullData.hc17_0_ok
  · exact genHull_of_case SqHullData.hc17_1 SqHullData.hc17_1_ok
  · exact genHull_of_case SqHullData.hc17_2 SqHullData.hc17_2_ok
  · exact genHull_of_case SqHullData.hc18_0 SqHullData.hc18_0_ok
  · exact genHull_of_case SqHullData.hc18_1 SqHullData.hc18_1_ok
  · exact genHull_of_case SqHullData.hc18_2 SqHullData.hc18_2_ok
  · exact genHull_of_case SqHullData.hc19_0 SqHullData.hc19_0_ok
  · exact genHull_of_case SqHullData.hc19_1 SqHullData.hc19_1_ok
  · exact genHull_of_case SqHullData.hc19_2 SqHullData.hc19_2_ok
  · exact genHull_of_case SqHullData.hc20_0 SqHullData.hc20_0_ok
  · exact genHull_of_case SqHullData.hc20_1 SqHullData.hc20_1_ok
  · exact genHull_of_case SqHullData.hc20_2 SqHullData.hc20_2_ok
  · exact genHull_of_case SqHullData.hc21_0 SqHullData.hc21_0_ok
  · exact genHull_of_case SqHullData.hc21_1 SqHullData.hc21_1_ok
  · exact genHull_of_case SqHullData.hc21_2 SqHullData.hc21_2_ok
  · exact genHull_of_case SqHullData.hc22_0 SqHullData.hc22_0_ok
  · exact genHull_of_case SqHullData.hc22_1 SqHullData.hc22_1_ok
  · exact genHull_of_case SqHullData.hc22_2 SqHullData.hc22_2_ok
  · exact genHull_of_case SqHullData.hc23_0 SqHullData.hc23_0_ok
  · exact genHull_of_case SqHullData.hc23_1 SqHullData.hc23_1_ok
  · exact genHull_of_case SqHullData.hc23_2 SqHullData.hc23_2_ok
  · exact genHull_of_case SqHullData.hc24_0 SqHullData.hc24_0_ok
  · exact genHull_of_case SqHullData.hc24_1 SqHullData.hc24_1_ok
  · exact genHull_of_case SqHullData.hc24_2 SqHullData.hc24_2_ok
  · exact genHull_of_case SqHullData.hc25_0 SqHullData.hc25_0_ok
  · exact genHull_of_case SqHullData.hc25_1 SqHullData.hc25_1_ok
  · exact genHull_of_case SqHullData.hc25_2 SqHullData.hc25_2_ok
  · exact genHull_of_case SqHullData.hc26_0 SqHullData.hc26_0_ok
  · exact genHull_of_case SqHullData.hc26_1 SqHullData.hc26_1_ok
  · exact genHull_of_case SqHullData.hc26_2 SqHullData.hc26_2_ok
  · exact genHull_of_case SqHullData.hc27_0 SqHullData.hc27_0_ok
  · exact genHull_of_case SqHullData.hc27_1 SqHullData.hc27_1_ok
  · exact genHull_of_case SqHullData.hc27_2 SqHullData.hc27_2_ok
  · exact genHull_of_case SqHullData.hc28_0 SqHullData.hc28_0_ok
  · exact genHull_of_case SqHullData.hc28_1 SqHullData.hc28_1_ok
  · exact genHull_of_case SqHullData.hc28_2 SqHullData.hc28_2_ok
  · exact genHull_of_case SqHullData.hc29_0 SqHullData.hc29_0_ok
  · exact genHull_of_case SqHullData.hc29_1 SqHullData.hc29_1_ok
  · exact genHull_of_case SqHullData.hc29_2 SqHullData.hc29_2_ok
  · exact genHull_of_case SqHullData.hc30_0 SqHullData.hc30_0_ok
  · exact genHull_of_case SqHullData.hc30_1 SqHullData.hc30_1_ok
  · exact genHull_of_case SqHullData.hc30_2 SqHullData.hc30_2_ok
  · exact genHull_of_case SqHullData.hc31_0 SqHullData.hc31_0_ok
  · exact genHull_of_case SqHullData.hc31_1 SqHullData.hc31_1_ok
  · exact genHull_of_case SqHullData.hc31_2 SqHullData.hc31_2_ok
  · exact genHull_of_case SqHullData.hc32_0 SqHullData.hc32_0_ok
  · exact genHull_of_case SqHullData.hc32_1 SqHullData.hc32_1_ok
  · exact genHull_of_case SqHullData.hc32_2 SqHullData.hc32_2_ok
  · exact genHull_of_case SqHullData.hc33_0 SqHullData.hc33_0_ok
  · exact genHull_of_case SqHullData.hc33_1 SqHullData.hc33_1_ok
  · exact genHull_of_case SqHullData.hc33_2 SqHullData.hc33_2_ok
  · exact genHull_of_case SqHullData.hc34_0 SqHullData.hc34_0_ok
  · exact genHull_of_case SqHullData.hc34_1 SqHullData.hc34_1_ok
  · exact genHull_of_case SqHullData.hc34_2 SqHullData.hc34_2_ok
  · exact genHull_of_case SqHullData.hc35_0 SqHullData.hc35_0_ok
  · exact genHull_of_case SqHullData.hc35_1 SqHullData.hc35_1_ok
  · exact genHull_of_case SqHullData.hc35_2 SqHullData.hc35_2_ok
  · exact genHull_of_case SqHullData.hc36_0 SqHullData.hc36_0_ok
  · exact genHull_of_case SqHullData.hc36_1 SqHullData.hc36_1_ok
  · exact genHull_of_case SqHullData.hc36_2 SqHullData.hc36_2_ok
  · exact genHull_of_case SqHullData.hc37_0 SqHullData.hc37_0_ok
  · exact genHull_of_case SqHullData.hc37_1 SqHullData.hc37_1_ok
  · exact genHull_of_case SqHullData.hc37_2 SqHullData.hc37_2_ok
  · exact genHull_of_case SqHullData.hc38_0 SqHullData.hc38_0_ok
  · exact genHull_of_case SqHullData.hc38_1 SqHullData.hc38_1_ok
  · exact genHull_of_case SqHullData.hc38_2 SqHullData.hc38_2_ok
  · exact genHull_of_case SqHullData.hc39_0 SqHullData.hc39_0_ok
  · exact genHull_of_case SqHullData.hc39_1 SqHullData.hc39_1_ok
  · exact genHull_of_case SqHullData.hc39_2 SqHullData.hc39_2_ok
  · exact genHull_of_case SqHullData.hc40_0 SqHullData.hc40_0_ok
  · exact genHull_of_case SqHullData.hc40_1 SqHullData.hc40_1_ok
  · exact genHull_of_case SqHullData.hc40_2 SqHullData.hc40_2_ok
  · exact genHull_of_case SqHullData.hc41_0 SqHullData.hc41_0_ok
  · exact genHull_of_case SqHullData.hc41_1 SqHullData.hc41_1_ok
  · exact genHull_of_case SqHullData.hc41_2 SqHullData.hc41_2_ok
  · exact genHull_of_case SqHullData.hc42_0 SqHullData.hc42_0_ok
  · exact genHull_of_case SqHullData.hc42_1 SqHullData.hc42_1_ok
  · exact genHull_of_case SqHullData.hc42_2 SqHullData.hc42_2_ok
  · exact genHull_of_case SqHullData.hc43_0 SqHullData.hc43_0_ok
  · exact genHull_of_case SqHullData.hc43_1 SqHullData.hc43_1_ok
  · exact genHull_of_case SqHullData.hc43_2 SqHullData.hc43_2_ok
  · exact genHull_of_case SqHullData.hc44_0 SqHullData.hc44_0_ok
  · exact genHull_of_case SqHullData.hc44_1 SqHullData.hc44_1_ok
  · exact genHull_of_case SqHullData.hc44_2 SqHullData.hc44_2_ok
  · exact genHull_of_case SqHullData.hc45_0 SqHullData.hc45_0_ok
  · exact genHull_of_case SqHullData.hc45_1 SqHullData.hc45_1_ok
  · exact genHull_of_case SqHullData.hc45_2 SqHullData.hc45_2_ok
  · exact genHull_of_case SqHullData.hc46_0 SqHullData.hc46_0_ok
  · exact genHull_of_case SqHullData.hc46_1 SqHullData.hc46_1_ok
  · exact genHull_of_case SqHullData.hc46_2 SqHullData.hc46_2_ok
  · exact genHull_of_case SqHullData.hc47_0 SqHullData.hc47_0_ok
  · exact genHull_of_case SqHullData.hc47_1 SqHullData.hc47_1_ok
  · exact genHull_of_case SqHullData.hc47_2 SqHullData.hc47_2_ok
  · exact genHull_of_case SqHullData.hc48_0 SqHullData.hc48_0_ok
  · exact genHull_of_case SqHullData.hc48_1 SqHullData.hc48_1_ok
  · exact genHull_of_case SqHullData.hc48_2 SqHullData.hc48_2_ok
  · exact genHull_of_case SqHullData.hc49_0 SqHullData.hc49_0_ok
  · exact genHull_of_case SqHullData.hc49_1 SqHullData.hc49_1_ok
  · exact genHull_of_case SqHullData.hc49_2 SqHullData.hc49_2_ok
  · exact genHull_of_case SqHullData.hc50_0 SqHullData.hc50_0_ok
  · exact genHull_of_case SqHullData.hc50_1 SqHullData.hc50_1_ok
  · exact genHull_of_case SqHullData.hc50_2 SqHullData.hc50_2_ok
  · exact genHull_of_case SqHullData.hc51_0 SqHullData.hc51_0_ok
  · exact genHull_of_case SqHullData.hc51_1 SqHullData.hc51_1_ok
  · exact genHull_of_case SqHullData.hc51_2 SqHullData.hc51_2_ok

/-- The covering statement for the hull property. -/
theorem sqHullCover (d0 d1 d2 dr : Fin 3 → Bool) (ρ : Fin 3 → Fin 3) (hρ : Function.Bijective ρ)
    (hcons : NormCons d0 d1 d2 dr ρ) :
    ∃ π π₀ π₁ : Fin 3 → Fin 3, Function.Bijective π ∧ Function.Bijective π₀ ∧
      Function.Bijective π₁ ∧ ∃ Q : Pat, (∀ e, SqHullOK Q e) ∧
        PatLE (normPat d0 d1 d2 dr ρ π π₀ π₁) Q :=
  pcover_of_table (Good := fun Q => ∀ e, SqHullOK Q e) (fun q hq e => sqHullOK_all q hq e)
    SqData.chunk_all d0 d1 d2 dr ρ hρ hcons

/-- The four-cell class at a root edge from its index form, after renumbering both
enumerations by one bijection. -/
theorem tb_of_idx_perm {Lu Lv : Finset ℕ} {F : ℕ → ℕ → ℝ} {A τ : ℝ}
    (h : ∀ α β : Fin 3 → ℕ, Function.Injective α → Function.Injective β → (∀ a, α a ∈ Lu) →
      (∀ b, β b ∈ Lv) → (∀ a b, α a = β b → a = b) →
      ∃ π : Fin 3 → Fin 3, Function.Bijective π ∧
        ∀ i j k l : Fin 6, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
          τ ^ 2 * A ^ 6 ≤ F (α (π (offPair i).1)) (β (π (offPair i).2)) ^ 2
            * F (α (π (offPair j).1)) (β (π (offPair j).2)) ^ 2
            * F (α (π (offPair k).1)) (β (π (offPair k).2))
            * F (α (π (offPair l).1)) (β (π (offPair l).2))) :
    TB Lu Lv F A τ := by
  refine tb_of_idx fun α β hα hβ hαm hβm hal => ?_
  obtain ⟨π, hπ, hb⟩ := h α β hα hβ hαm hβm hal
  obtain ⟨πi, hπi⟩ : ∃ πi : Fin 3 → Fin 3, ∀ x, π (πi x) = x :=
    ⟨fun x => (hπ.2 x).choose, fun x => (hπ.2 x).choose_spec⟩
  have hπiinj : Function.Injective πi := fun x y e => by rw [← hπi x, ← hπi y, e]
  have hcell : ∀ r : Fin 6, ∃ r', offPair r' = (πi (offPair r).1, πi (offPair r).2) := fun r =>
    offPair_surj _ _ fun e => offPair_ne r (hπiinj e)
  choose κ hκ using hcell
  have hκinj : Function.Injective κ := fun r r' e => by
    apply offPair_injective
    have h1 := hκ r
    have h2 := hκ r'
    rw [e, h2] at h1
    exact Prod.ext (hπiinj (congrArg Prod.fst h1).symm) (hπiinj (congrArg Prod.snd h1).symm)
  have hval : ∀ r, F (α (π (offPair (κ r)).1)) (β (π (offPair (κ r)).2))
      = F (α (offPair r).1) (β (offPair r).2) := fun r => by
    rw [hκ r, hπi, hπi]
  intro i j k l hij hik hil hjk hjl hkl
  have := hb (κ i) (κ j) (κ k) (κ l) (fun e => hij (hκinj e)) (fun e => hik (hκinj e))
    (fun e => hil (hκinj e)) (fun e => hjk (hκinj e)) (fun e => hjl (hκinj e))
    (fun e => hkl (hκinj e))
  rwa [hval, hval, hval, hval] at this

/-- **A square over the hull class, bare form**: the other path edges carry `[c ≠ d]`. -/
theorem tb_square_hull_bare (Lu Lv : Finset ℕ) (Li : Fin 2 → Finset ℕ) (hLu : Lu.card = 3)
    (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3) (j₀ : Fin 3) (W : ℕ → ℕ → ℝ)
    (hW : ∀ c d, 0 ≤ W c d) (A : ℝ) (hA : 0 < A)
    (hin : HullC (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) W A) :
    TB Lu Lv (faceSum Li (fun _ _ => 1)
      (fun j => if j = j₀ then W else fun c d => if c ≠ d then 1 else 0)) (faceConst3 2 * A)
      (1 / 2) := by
  have h3 : faceConst3 2 = 3 := by norm_num [faceConst3]
  rw [h3]
  have _ := hLu
  refine tb_of_idx_perm fun α β hα hβ hαm hβm hal => ?_
  -- enumerations in normal form
  obtain ⟨g₀, hg₀, hg₀m, hg₀a⟩ := exists_aligned (hLi 0) hα
  obtain ⟨g₁, hg₁, hg₁m, hg₁a⟩ := exists_aligned (hLi 1) hg₀
  obtain ⟨δ, hδ, hδm, hδa⟩ := exists_aligned hLv hg₁
  have hρex : ∀ b, ∃ t, δ t = β b := fun b => by
    have h := hβm b
    rw [← image_enum hLv hδ hδm] at h
    obtain ⟨t, -, ht⟩ := mem_image.mp h
    exact ⟨t, ht⟩
  choose ρ hρ using hρex
  have hρinj : Function.Injective ρ := fun b b' e => hβ (by rw [← hρ b, ← hρ b', e])
  have hρb : Function.Bijective ρ := ⟨hρinj, Finite.injective_iff_surjective.mp hρinj⟩
  -- the pattern in normal form
  have e01 : ∀ a s, α a = g₀ s ↔ a = s ∧ decide (α a = g₀ a) = true := fun a s =>
    ⟨fun e => by
      obtain rfl := hg₀a s a e.symm
      exact ⟨rfl, decide_eq_true e⟩, fun ⟨e, h⟩ => by rw [← e]; exact of_decide_eq_true h⟩
  have e12 : ∀ s t, g₀ s = g₁ t ↔ s = t ∧ decide (g₀ s = g₁ s) = true := fun s t =>
    ⟨fun e => by
      obtain rfl := hg₁a t s e.symm
      exact ⟨rfl, decide_eq_true e⟩, fun ⟨e, h⟩ => by rw [← e]; exact of_decide_eq_true h⟩
  have e23 : ∀ t b, g₁ t = β b ↔ t = ρ b ∧ decide (g₁ t = δ t) = true := fun t b =>
    ⟨fun e => by
      have e' : δ (ρ b) = g₁ t := by rw [hρ b, e]
      obtain rfl := hδa (ρ b) t e'
      exact ⟨rfl, decide_eq_true e'.symm⟩, fun ⟨e, h⟩ => by
      rw [← hρ b, ← e]; exact of_decide_eq_true h⟩
  have e03 : ∀ a b, α a = β b ↔ a = b ∧ decide (α a = β a) = true := fun a b =>
    ⟨fun e => by
      obtain rfl := hal a b e
      exact ⟨rfl, decide_eq_true e⟩, fun ⟨e, h⟩ => by rw [← e]; exact of_decide_eq_true h⟩
  have hcons : NormCons (fun a => decide (α a = g₀ a)) (fun s => decide (g₀ s = g₁ s))
      (fun t => decide (g₁ t = δ t)) (fun a => decide (α a = β a)) ρ := by
    refine ⟨fun b h0 h1 h2 => ?_, fun a h0 h1 hr => ?_, fun a h0 h2 hr => ?_,
      fun a h1 h2 hr => ?_⟩
    · have e : α (ρ b) = β b := by
        rw [of_decide_eq_true h0, of_decide_eq_true h1, of_decide_eq_true h2, hρ b]
      obtain h := hal _ _ e
      exact ⟨h, by rw [h] at e; exact decide_eq_true e⟩
    · have e : g₁ a = β a := by
        rw [← of_decide_eq_true h1, ← of_decide_eq_true h0, of_decide_eq_true hr]
      have h := ((e23 a a).mp e).1
      exact ⟨h.symm, ((e23 a a).mp e).2⟩
    · have e : g₀ a = g₁ (ρ a) := by
        rw [← of_decide_eq_true h0, of_decide_eq_true hr, of_decide_eq_true h2, hρ a]
      have h := ((e12 a (ρ a)).mp e).1
      exact ⟨h.symm, ((e12 a (ρ a)).mp e).2⟩
    · have e : α a = g₀ (ρ a) := by
        rw [of_decide_eq_true h1, of_decide_eq_true h2, hρ a, of_decide_eq_true hr]
      have h := ((e01 a (ρ a)).mp e).1
      exact ⟨h.symm, ((e01 a (ρ a)).mp e).2⟩
  obtain ⟨π, π₀, π₁, hπ, hπ₀, hπ₁, Q, hQ, hle⟩ := sqHullCover _ _ _ _ ρ hρb hcons
  refine ⟨π, hπ, ?_⟩
  -- the renumbered enumerations
  have hα' : Function.Injective fun a => α (π a) := hα.comp hπ.1
  have hβ' : Function.Injective fun b => β (π b) := hβ.comp hπ.1
  have hγ₀ : Function.Injective fun s => g₀ (π₀ s) := hg₀.comp hπ₀.1
  have hγ₁ : Function.Injective fun t => g₁ (π₁ t) := hg₁.comp hπ₁.1
  have hP : patOf (fun a => α (π a)) (fun s => g₀ (π₀ s)) (fun t => g₁ (π₁ t))
        (fun b => β (π b))
      = normPat (fun a => decide (α a = g₀ a)) (fun s => decide (g₀ s = g₁ s))
        (fun t => decide (g₁ t = δ t)) (fun a => decide (α a = β a)) ρ π π₀ π₁ := by
    unfold patOf normPat
    congr 1
    · funext a s
      rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.and_eq_true, decide_eq_true_iff]
      exact e01 _ _
    · funext s t
      rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.and_eq_true, decide_eq_true_iff]
      exact e12 _ _
    · funext t b
      rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.and_eq_true, decide_eq_true_iff]
      exact e23 _ _
    · funext a b
      rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.and_eq_true, decide_eq_true_iff]
      exact (e03 _ _).trans ⟨fun ⟨e, h⟩ => ⟨hπ.1 e, h⟩, fun ⟨e, h⟩ => ⟨by rw [e], h⟩⟩
  have hok : SqHullOK (patOf (fun a => α (π a)) (fun s => g₀ (π₀ s)) (fun t => g₁ (π₁ t))
      (fun b => β (π b))) j₀ := by
    rw [hP]
    exact (hQ j₀).mono hle
  -- the loaded edge in index form
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := pathList_two Lu Lv Li
  have hidx : IdxHull (sqEl (patOf (fun a => α (π a)) (fun s => g₀ (π₀ s))
      (fun t => g₁ (π₁ t)) (fun b => β (π b))) j₀)
      (sqW (fun a => α (π a)) (fun s => g₀ (π₀ s)) (fun t => g₁ (π₁ t)) (fun b => β (π b)) W j₀)
      A := by
    fin_cases j₀
    · have h := hin
      rw [show Fin.castSucc (⟨0, by decide⟩ : Fin 3) = Fin.castSucc (0 : Fin 3) from rfl,
        show Fin.succ (⟨0, by decide⟩ : Fin 3) = Fin.succ (0 : Fin 3) from rfl, l0, l1] at h
      exact h.idx hα' hγ₀ (fun a => hαm _) fun s => hg₀m _
    · have h := hin
      rw [show Fin.castSucc (⟨1, by decide⟩ : Fin 3) = Fin.castSucc (1 : Fin 3) from rfl,
        show Fin.succ (⟨1, by decide⟩ : Fin 3) = Fin.succ (1 : Fin 3) from rfl, l2, l3] at h
      exact h.idx hγ₀ hγ₁ (fun s => hg₀m _) fun t => hg₁m _
    · have h := hin
      rw [show Fin.castSucc (⟨2, by decide⟩ : Fin 3) = Fin.castSucc (2 : Fin 3) from rfl,
        show Fin.succ (⟨2, by decide⟩ : Fin 3) = Fin.succ (2 : Fin 3) from rfl, l4, l5] at h
      exact h.idx hγ₁ hβ' (fun t => hg₁m _) fun b => hβm _
  have hsqW : ∀ s t, 0 ≤ sqW (fun a => α (π a)) (fun s => g₀ (π₀ s)) (fun t => g₁ (π₁ t))
      (fun b => β (π b)) W j₀ s t := fun s t => by
    unfold sqW
    split_ifs <;> exact hW _ _
  intro i j k l hij hik hil hjk hjl hkl
  have key := hok _ hsqW A hA hidx i j k l hij hik hil hjk hjl hkl
  have hg := fun a b => genF_le_faceSum hLi hγ₀ hγ₁ (fun s => hg₀m _) (fun t => hg₁m _) hW j₀ a b
    (α := fun a => α (π a)) (β := fun b => β (π b))
  have hn := genF_nonneg (sqB₁ (patOf (fun a => α (π a)) (fun s => g₀ (π₀ s))
    (fun t => g₁ (π₁ t)) (fun b => β (π b))) j₀) (sqEl (patOf (fun a => α (π a))
    (fun s => g₀ (π₀ s)) (fun t => g₁ (π₁ t)) (fun b => β (π b))) j₀)
    (sqB₂ (patOf (fun a => α (π a)) (fun s => g₀ (π₀ s)) (fun t => g₁ (π₁ t))
      (fun b => β (π b))) j₀) hsqW
  exact key.trans (four_le (hn _ _) (hn _ _) (hn _ _) (hn _ _) (hg _ _) (hg _ _) (hg _ _)
    (hg _ _))

/-- Greedy profiles on the other path edges only help: the face sum against the bare one. -/
theorem faceSum_bare_mul_le {m : ℕ} {Lu Lv : Finset ℕ} {Li : Fin m → Finset ℕ} (j₀ : Fin (m + 1))
    {E : Fin (m + 1) → ℕ → ℕ → ℝ} (hE0 : ∀ j c d, 0 ≤ E j c d) {A : Fin (m + 1) → ℝ}
    (hA : ∀ j, 0 ≤ A j)
    (hdom : ∀ j, j ≠ j₀ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j))
    {c d : ℕ} (hc : c ∈ Lu) (hd : d ∈ Lv) :
    faceSum Li (fun _ _ => 1) (fun j => if j = j₀ then E j₀ else fun c d => if c ≠ d then 1 else 0)
        c d * ∏ j ∈ univ.erase j₀, A j ≤ faceSum Li (fun _ _ => 1) E c d := by
  set E' : Fin (m + 1) → ℕ → ℕ → ℝ :=
    fun j => if j = j₀ then E j₀ else fun c d => if c ≠ d then 1 else 0 with hE'
  unfold faceSum
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun g hg => ?_
  simp only [Finset.prod_const_one, one_mul]
  have hmem : ∀ i : Fin (m + 2), pathCol c d g i ∈ pathList Lu Lv Li i := fun i =>
    pathCol_mem hc hd (fun j => Fintype.mem_piFinset.mp hg j) i
  by_cases hall : ∀ j : Fin (m + 1), j ≠ j₀ → pathCol c d g j.castSucc ≠ pathCol c d g j.succ
  · have e1 : ∏ j : Fin (m + 1), E' j (pathCol c d g j.castSucc) (pathCol c d g j.succ)
        = E j₀ (pathCol c d g j₀.castSucc) (pathCol c d g j₀.succ) := by
      rw [← Finset.mul_prod_erase univ _ (mem_univ j₀)]
      have : ∏ j ∈ univ.erase j₀, E' j (pathCol c d g j.castSucc) (pathCol c d g j.succ) = 1 :=
        Finset.prod_eq_one fun j hj => by
          have hne := Finset.ne_of_mem_erase hj
          simp only [hE', hne, ite_false, hall j hne, ne_eq, not_false_eq_true, ite_true]
      rw [this, mul_one]
      simp only [hE', ite_true]
    rw [e1, ← Finset.mul_prod_erase univ _ (mem_univ j₀)]
    refine mul_le_mul_of_nonneg_left ?_ (hE0 _ _ _)
    exact Finset.prod_le_prod₀ (fun j _ => hA j) fun j hj =>
      hdom j (Finset.ne_of_mem_erase hj) _ (hmem _) _ (hmem _) (hall j (Finset.ne_of_mem_erase hj))
  · obtain ⟨j, hj, heq⟩ : ∃ j : Fin (m + 1), j ≠ j₀ ∧
        pathCol c d g j.castSucc = pathCol c d g j.succ := by
      by_contra hne
      exact hall fun j hj heq => hne ⟨j, hj, heq⟩
    have e0 : ∏ j : Fin (m + 1), E' j (pathCol c d g j.castSucc) (pathCol c d g j.succ) = 0 :=
      Finset.prod_eq_zero (mem_univ j) (by simp only [hE', hj, ite_false, heq, ne_eq,
        not_true_eq_false])
    rw [e0, zero_mul]
    exact Finset.prod_nonneg fun j _ => hE0 _ _ _

/-- **A square over the hull class has the four-cell bound `1/2`.** -/
theorem tb_square_hull (Lu Lv : Finset ℕ) (Li : Fin 2 → Finset ℕ) (hLu : Lu.card = 3)
    (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3) (j₀ : Fin 3) (E : Fin 3 → ℕ → ℕ → ℝ)
    (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin 3 → ℝ) (hA : ∀ j, 0 < A j)
    (hH : HullC (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) (E j₀) (A j₀))
    (hdom : ∀ j, j ≠ j₀ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    TB Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 2 * ∏ j, A j) (1 / 2) := by
  set K : ℝ := ∏ j ∈ univ.erase j₀, A j with hK
  have hKpos : 0 < K := Finset.prod_pos fun j _ => hA j
  have hbare := tb_square_hull_bare Lu Lv Li hLu hLv hLi j₀ (E j₀) (hE0 j₀) (A j₀) (hA j₀) hH
  have hKtb : TB Lu Lv (fun _ _ => K) K 1 :=
    Dominant.tb (fun _ _ _ _ _ => le_refl K) hKpos.le
  have hmul := hbare.mul hKtb
  have hconst : faceConst3 2 * ∏ j, A j = faceConst3 2 * A j₀ * K := by
    rw [hK, ← Finset.mul_prod_erase univ A (mem_univ j₀)]
    ring
  rw [hconst, show (1 / 2 : ℝ) = 1 / 2 * 1 by ring]
  have hE'0 : ∀ j c d, 0 ≤ (if j = j₀ then E j₀ else fun c d => if c ≠ d then (1 : ℝ) else 0)
      c d := fun j c d => by
    split_ifs
    · exact hE0 _ _ _
    · simp only []; split_ifs <;> norm_num
  refine hmul.mono (fun c d => mul_nonneg (faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one) hE'0 c d)
    hKpos.le) fun c hc d hd _ => ?_
  exact faceSum_bare_mul_le j₀ hE0 (fun j => (hA j).le) hdom hc hd

end Outerplanar
