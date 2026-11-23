/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.HullClass
import Outerplanar.TransportFace

/-!
# The hull class through faces of odd length

* `face_vec_transport` — the vector form of the transport lemma: for a face with one loaded
  path edge `j₀` and greedy edges elsewhere, and enumerations of the root lists along a matched
  family, the root six-vector dominates `dd` times a doubly stochastic mixture of a matched
  six-vector of the loaded edge.
* `hullC_transport` — at a face of odd length (`dd = α`) the hull class passes from the loaded
  edge to the root, with the constant of the face.

Part of the formalization of the six-even-face theorem (research note
`ai_research_notes/OUTERPLANAR_SIX_EVEN_2026-11-23.md`).
-/

namespace Outerplanar

open Finset

/-- The walk form of the vector transport. -/
theorem walks_vec_transport (L₁ L₂ : List (Fin 3 → Fin 3 → ℝ))
    (h₁ : ∀ M ∈ L₁, ∀ a b, 0 ≤ M a b) (h₂ : ∀ M ∈ L₂, ∀ a b, 0 ≤ M a b)
    (M : Fin 3 → Fin 3 → ℝ) (hM : ∀ a b, 0 ≤ M a b) (hm₁ : 1 ≤ mnP L₁) (hm₂ : 1 ≤ mnP L₂)
    {σ : Fin 3 → Fin 3} (hσ : Function.Injective σ) :
    ∃ D, DS D ∧ ∀ k, dd L₁.length L₂.length * ∑ z, D k z * M (offPair z).1 (offPair z).2
      ≤ pw (L₁ ++ M :: L₂) (offPair k).1 (σ (offPair k).2) := by
  obtain ⟨D, hD, hle⟩ := exists_ds_le hσ L₁.length L₂.length
  refine ⟨D, hD, fun k => ?_⟩
  have hsplit := pw_split_ge L₁ L₂ h₁ h₂ M hM (offPair k).1 (σ (offPair k).2)
  calc dd L₁.length L₂.length * ∑ z, D k z * M (offPair z).1 (offPair z).2
      = ∑ z, (dd L₁.length L₂.length * D k z) * M (offPair z).1 (offPair z).2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
    _ ≤ ∑ z, Cmat L₁.length L₂.length σ k z * M (offPair z).1 (offPair z).2 :=
        Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right (hle k z) (hM _ _)
    _ ≤ mnP L₁ * mnP L₂ * ∑ z, Cmat L₁.length L₂.length σ k z * M (offPair z).1 (offPair z).2 := by
        refine le_mul_of_one_le_left (Finset.sum_nonneg fun z _ =>
          mul_nonneg (Cmat_nonneg _ _ _ _ _) (hM _ _)) ?_
        exact one_le_mul_of_one_le_of_one_le hm₁ hm₂
    _ ≤ _ := hsplit

/-- **The vector transport lemma**, all constants one. -/
theorem face_vec_transport (m : ℕ) (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ)
    (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3) (j₀ : Fin (m + 1))
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d)
    (hD : ∀ j, j ≠ j₀ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) 1)
    {α β : Fin 3 → ℕ} (hα : Function.Injective α) (hβ : Function.Injective β)
    (hαm : ∀ a, α a ∈ Lu) (hβm : ∀ b, β b ∈ Lv) :
    ∃ ζ ξ : Fin 3 → ℕ, Function.Injective ζ ∧ Function.Injective ξ ∧
      (∀ a, ζ a ∈ pathList Lu Lv Li j₀.castSucc) ∧ (∀ b, ξ b ∈ pathList Lu Lv Li j₀.succ) ∧
      Aligned ζ ξ ∧ ∃ D, DS D ∧ ∀ r, dd j₀ (m - j₀) * ∑ z, D r z * E j₀ (ζ (offPair z).1)
        (ξ (offPair z).2) ≤ faceSum Li (fun _ _ => 1) E (α (offPair r).1) (β (offPair r).2) := by
  obtain ⟨ζ, h0, hζ, hchain⟩ := framesFin m Lu Lv Li hLv hLi α hα hαm
  -- the last enumeration and the monodromy
  have hlast : ∀ b, ζ (Fin.last (m + 1)) b ∈ Lv := fun b => by
    have := (hζ (Fin.last (m + 1))).2 b
    rwa [show pathList Lu Lv Li (Fin.last (m + 1)) = Lv from consSnoc_last _ _ _ _ (by simp)]
      at this
  have himg : ∀ b, ∃ x, ζ (Fin.last (m + 1)) x = β b := fun b => by
    have hb : β b ∈ univ.image (ζ (Fin.last (m + 1))) := by
      rw [image_enum hLv (hζ _).1 hlast]
      exact hβm b
    obtain ⟨x, -, hx⟩ := mem_image.mp hb
    exact ⟨x, hx⟩
  choose σ hσ using himg
  have hσinj : Function.Injective σ := fun b b' e => hβ (by rw [← hσ b, ← hσ b', e])
  -- the tables, split at the loaded edge
  set T := pathTabs ζ E with hTdef
  set Mst := idxM (E j₀) (ζ j₀.castSucc) (ζ j₀.succ) with hMst
  have hlenT : T.length = m + 1 := by simp [hTdef, pathTabs]
  have hj₀ : j₀.val < T.length := by rw [hlenT]; exact j₀.isLt
  have hsplit : T = T.take j₀ ++ Mst :: T.drop (j₀ + 1) := by
    conv_lhs => rw [← List.take_append_drop j₀.val T]
    congr 1
    rw [List.drop_eq_getElem_cons hj₀]
    congr 1
    simp only [hTdef, pathTabs, List.getElem_ofFn, hMst, Fin.eta]
  have hTnn : ∀ M ∈ T, ∀ a b, 0 ≤ M a b := by
    intro M hM a b
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).mp hM
    exact hE0 _ _ _
  have hdomT : ∀ j : Fin (m + 1), j ≠ j₀ → 1 ≤ mn (idxM (E j) (ζ j.castSucc) (ζ j.succ)) :=
    fun j hj => one_le_mn_of_dom (hD j hj) (hζ _).2 (hζ _).2 (hchain j)
  have hL₁ : ∀ M ∈ T.take j₀, 1 ≤ mn M := by
    intro M hM
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hM
    have hi' : i < j₀.val := by simp at hi; omega
    rw [List.getElem_take]
    simp only [hTdef, pathTabs, List.getElem_ofFn]
    exact hdomT ⟨i, by omega⟩ fun e => by
      have := congrArg Fin.val e
      simp at this
      omega
  have hL₂ : ∀ M ∈ T.drop (j₀ + 1), 1 ≤ mn M := by
    intro M hM
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hM
    rw [List.getElem_drop]
    simp only [hTdef, pathTabs, List.getElem_ofFn]
    exact hdomT ⟨j₀ + 1 + i, by simp at hi; omega⟩ fun e => by
      have := congrArg Fin.val e
      simp at this
      omega
  have hlen₁ : (T.take j₀).length = j₀.val := by
    rw [List.length_take, hlenT]; omega
  have hlen₂ : (T.drop (j₀ + 1)).length = m - j₀.val := by
    rw [List.length_drop, hlenT]; omega
  obtain ⟨D, hDS, hle⟩ := walks_vec_transport (T.take j₀) (T.drop (j₀ + 1))
    (fun M hM => hTnn M (List.mem_of_mem_take hM)) (fun M hM => hTnn M (List.mem_of_mem_drop hM))
    Mst (fun a b => hE0 _ _ _) (one_le_mnP _ hL₁) (one_le_mnP _ hL₂) hσinj
  rw [← hsplit, hlen₁, hlen₂] at hle
  refine ⟨ζ j₀.castSucc, ζ j₀.succ, (hζ _).1, (hζ _).1, (hζ _).2, (hζ _).2, hchain j₀, D, hDS,
    fun r => ?_⟩
  have hcell := pw_le_faceSum hζ E hE0 (offPair r).1 (σ (offPair r).2)
  rw [h0, hσ] at hcell
  exact (hle r).trans hcell

/-- **The hull class through a face of odd length** with one loaded edge, normalised. -/
theorem hullC_transport_one (m : ℕ) (hm : Odd m) (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ)
    (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3) (j₀ : Fin (m + 1))
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d)
    (hH : HullC (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) (E j₀) 1)
    (hD : ∀ j, j ≠ j₀ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) 1) :
    HullC Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m) := by
  have hdd : dd j₀ (m - j₀) = faceConst3 m := by
    have e : (j₀ : ℕ) + (m - j₀) = m := by omega
    unfold dd
    rw [e, ← faceConst3_eq_dN]
    have : ¬ Odd (m + 1) := by
      rw [Nat.odd_add_one, not_not]; exact hm
    simp [this]
  refine hullC_of_idx (fun α β hα hβ hαm hβm _ => ?_) ?_
  · obtain ⟨ζ, ξ, hζ, hξ, hζm, hξm, hal, D, hDS, hle⟩ :=
      face_vec_transport m Lu Lv Li hLv hLi j₀ E hE0 hD hα hβ hαm hβm
    have hchild := hH.1 _ _ (matched_of_enum hζ hξ hζm hξm)
      (fun i e => offPair_ne i (hal _ _ e))
    have := (hchild.ds hDS).smul (dd_nonneg j₀ (m - j₀))
    rw [mul_one, hdd] at this
    refine this.mono fun r => ?_
    have h := hle r
    rw [hdd] at h
    exact h
  · -- the floor
    have h := dom_face_bare Lu Lv Li hLi E hE0 (fun j => if j = j₀ then 2 / 3 else 1)
      (fun j => by split_ifs <;> norm_num) fun j => by
        by_cases hj : j = j₀
        · subst hj; simpa using hH.2
        · simpa [hj] using hD j hj
    have hprod : ∏ j, (if j = j₀ then (2 / 3 : ℝ) else 1) = 2 / 3 := by
      rw [Finset.prod_ite_eq' univ j₀]; simp
    obtain ⟨k, rfl⟩ := hm
    rw [hprod, oddB_odd] at h
    exact fun c hc d hd hcd => le_trans (le_of_eq (by ring)) (h c hc d hd hcd)

/-- **The hull class through a face of odd length** with one loaded edge. -/
theorem hullC_transport (m : ℕ) (hm : Odd m) (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ)
    (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3) (j₀ : Fin (m + 1))
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 < A j)
    (hH : HullC (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) (E j₀) (A j₀))
    (hD : ∀ j, j ≠ j₀ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    HullC Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  have hP : 0 < ∏ j, A j := Finset.prod_pos fun j _ => hA j
  have key := hullC_transport_one m hm Lu Lv Li hLv hLi j₀ (fun j c d => E j c d / A j)
    (fun j c d => div_nonneg (hE0 j c d) (hA j).le) (hH.div (hA j₀))
    (fun j hj => (hD j hj).div (hA j))
  refine HullC.of_div hP ?_
  have e : (fun c d => faceSum Li (fun _ _ => 1) E c d / ∏ j, A j)
      = faceSum Li (fun _ _ => 1) (fun j c d => E j c d / A j) := by
    funext c d
    rw [faceSum_div]
  rw [e]
  exact key

end Outerplanar
