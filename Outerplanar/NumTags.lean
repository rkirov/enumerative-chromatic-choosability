/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.BareEven
import Outerplanar.TagBuilt
import Outerplanar.HallTri
import Outerplanar.HexWalks
import Outerplanar.Transport2
import Outerplanar.SqHull
import Outerplanar.HullTransport

/-!
# A numeric tag system

An instance of the class systems of `Outerplanar/TagBuilt.lean` in which a tag is a triple of
numbers:

* `mb` — whether the rank-one bound `HasPot` (the matching bound) is demanded;
* `tv` — a constant `τ ∈ [0, 1]` for the four-cell bound `TB`;
* `fl` — a floor `f ∈ [0, 1]`: the profile is `Dominant` with constant `f A`.

Every class also contains the hexagon bound `Hex`, so two sides of any tags glue.
One face rule, `numRule`, collects the single-face lemmas proved so far as numeric
conditions on the tags of the root and of the path edges:

* hexagon bound: every odd face (`hex_tri`, `hexOddClosed`), and every face of length at least
  four whose path edges carry the matching bound;
* matching bound: faces of length at least four (`hasPot_face3`), and triangles with
  `2 τ₀ τ₁ ≥ 1` (Hall, `hasPot_tri`);
* four-cell bound: from the floor (`τ ≤ F³`), by transport through a face with one
  non-greedy side (`tb_transport`, with the other sides' floors), at triangles (`τ₀ τ₁`,
  `tb_tri`), at squares (`3/4` times the floors, `tb_square`), and at odd faces of length at
  least five with two non-greedy sides (`τ₁ τ₂` times the other floors, `tb_transport2`);
* floor: `F = (oddB m / α) ∏ fⱼ` (`dom_face_bare`).

**`ecc_three_of_numBuilt`**: every graph built by ears following `numRule` is 3-ECC.

A fourth field `hull` demands the hull class of `Outerplanar/HullClass.lean` (a bare square, and
what an odd face transports from one such side). It feeds the four-cell disjunct of a square
over a branch with one square (`tb_square_hull`).

Every single-face step of the six-even-face theorem is a rule of the catalogue, with the tags
`NTag.plain = ⟨true, 1, 1, false⟩` (odd-only), `tSq = ⟨true, 3/4, 2/3, true⟩` (one square),
`tLong = ⟨true, 3/4, 10/11, false⟩` (one longer even face), `tTwo = ⟨true, 1/2, 0, false⟩`
(two marks), `tMB` and `tHex`: `numRule_odd_one`, `numRule_bare_square`, `numRule_bare_long`,
`numRule_even_one`, `numRule_square_long`, `numRule_square_hull`, `numRule_tri`,
`numRule_odd_two`, `numRule_mb`, `numRule_hex_odd`, `numRule_hex_even`. That every
2-connected outerplanar graph with at most six even faces is built by these rules (weak dual
tree, centroid) is the combinatorial part of the research note, not formalized here, as for
`OneLoadBuilt`.

Part of the formalization of the six-even-face theorem (proof in
`ai_research_notes/OUTERPLANAR_SIX_EVEN_2026-11-23.md`, by a ChatGPT session; audited and
extended by Claude).
-/

namespace Outerplanar

open Finset

/-! ### Small facts about the classes -/

section Facts

variable {S T : Finset ℕ} {W W' : ℕ → ℕ → ℝ} {A A' : ℝ}

theorem TB.zero (h0 : ∀ c d, 0 ≤ W c d) : TB S T W A 0 := by
  intro p q _ _ i j k l _ _ _ _ _ _
  rw [zero_pow two_ne_zero, zero_mul]
  exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (h0 _ _) 2) (pow_nonneg (h0 _ _) 2))
    (h0 _ _)) (h0 _ _)

theorem Dominant.le (h : Dominant S T W A) (hle : A' ≤ A) : Dominant S T W A' :=
  fun c hc d hd hcd => hle.trans (h c hc d hd hcd)

/-- A floor gives the four-cell bound with the cube of the floor. -/
theorem Dominant.tb_floor {F N : ℝ} (h : Dominant S T W (F * N)) (hF : 0 ≤ F) (hN : 0 ≤ N) :
    TB S T W N (F ^ 3) := by
  have := (h.tb (mul_nonneg hF hN)).scale
  rwa [one_mul] at this

theorem Hex.swap (h : Hex T S W A) : Hex S T (fun c d => W d c) A := fun p q hm hpq =>
  h q p hm.symm fun i => (hpq i).symm

end Facts

/-! ### Tags and classes -/

/-- A numeric tag: the matching bound demanded or not, a four-cell constant, a floor. -/
structure NTag where
  mb : Bool
  tv : ℝ
  fl : ℝ
  tv0 : 0 ≤ tv
  tv1 : tv ≤ 1
  fl0 : 0 ≤ fl
  fl1 : fl ≤ 1
  hull : Bool

/-- The tag of a greedy profile. -/
def NTag.plain : NTag := ⟨true, 1, 1, zero_le_one, le_refl _, zero_le_one, le_refl _, false⟩

/-- The class of a numeric tag. -/
def ncls (t : NTag) (S T : Finset ℕ) (W : ℕ → ℕ → ℝ) (A : ℝ) : Prop :=
  Hex S T W A ∧ (t.mb = true → HasPot S T W A) ∧ TB S T W A t.tv ∧ Dominant S T W (t.fl * A) ∧
    (t.hull = true → HullC S T W A)

/-- The numeric class system. -/
def numSys : ClassSys where
  Tag := NTag
  plain := NTag.plain
  cls := ncls
  of_dom t S T W A hA h :=
    ⟨h.hex hA, fun _ => h.hasPot, (h.tb hA).anti t.tv0 t.tv1,
      h.le (mul_le_of_le_one_left hA t.fl1), fun _ => HullC.of_dom hA h⟩
  dom_of_plain S T W A h := by
    have := h.2.2.2.1
    simpa [NTag.plain] using this
  mul_dom t S T W W' A A' hA hA' h0 h0' hD h := by
    refine ⟨(hD.hex hA').mul hA' hA h.1, fun hmb => HasPot.mul hA' hA hD.hasPot (h.2.1 hmb),
      ?_, ?_, fun hh => HullC.mul_dom hA hA' h0 hD (h.2.2.2.2 hh)⟩
    · have := TB.mul (hD.tb hA') h.2.2.1
      rwa [one_mul] at this
    · have := Dominant.mul hA' (mul_nonneg t.fl0 hA) hD h.2.2.2.1
      rwa [mul_left_comm] at this

/-! ### The face rule -/

/-- The floor of a face: the path count over the constant, times the floors of the sides. -/
noncomputable def faceFloor (m : ℕ) (τ : Fin (m + 1) → NTag) : ℝ :=
  oddB m / faceConst3 m * ∏ j, (τ j).fl

/-- **The face rule.** A face with `m` interior vertices and path tags `τ` may carry the tag
`t` on its root edge. -/
def numRule (t : NTag) (m : ℕ) (τ : Fin (m + 1) → NTag) : Prop :=
  1 ≤ m ∧
  (Odd m ∨ (2 ≤ m ∧ ∀ j, (τ j).mb = true)) ∧
  (t.mb = true → (∀ j, (τ j).mb = true) ∧
      (2 ≤ m ∨ ∀ j j', j ≠ j' → 1 ≤ 2 * ((τ j).tv * (τ j').tv))) ∧
  (t.tv ≤ faceFloor m τ ^ 3 ∨
    (∃ j₀ : Fin (m + 1), t.tv ≤ (τ j₀).tv * (dd j₀ (m - j₀) / faceConst3 m) ^ 3
      * (∏ j ∈ univ.erase j₀, (τ j).fl) ^ 3) ∨
    (m = 1 ∧ ∀ j j', j ≠ j' → t.tv ≤ (τ j).tv * (τ j').tv) ∨
    (m = 2 ∧ t.tv ≤ 3 / 4 * (∏ j, (τ j).fl) ^ 3) ∨
    (Odd m ∧ 3 ≤ m ∧ ∃ j₁ j₂ : Fin (m + 1), j₁ < j₂ ∧ t.tv ≤ (τ j₁).tv * (τ j₂).tv
      * (∏ j ∈ univ.filter (fun j => ¬(j = j₁ ∨ j = j₂)), (τ j).fl) ^ 3) ∨
    (m = 2 ∧ ∃ j₀ : Fin (m + 1), (τ j₀).hull = true ∧ (∀ j, j ≠ j₀ → (τ j).fl = 1) ∧
      t.tv ≤ 1 / 2)) ∧
  t.fl ≤ faceFloor m τ ∧
  (t.hull = true → (m = 2 ∧ ∀ j, (τ j).fl = 1) ∨
    (Odd m ∧ ∃ j₀ : Fin (m + 1), (τ j₀).hull = true ∧ ∀ j, j ≠ j₀ → (τ j).fl = 1))

section Sound

variable {t : NTag} {m : ℕ} {τ : Fin (m + 1) → NTag}

/-- The floors of the sides, as `Dominant` profiles with the scaled constants. -/
theorem prod_fl_mul (A : Fin (m + 1) → ℝ) :
    ∏ j, (τ j).fl * A j = (∏ j, (τ j).fl) * ∏ j, A j := Finset.prod_mul_distrib

theorem faceFloor_nonneg : 0 ≤ faceFloor m τ :=
  mul_nonneg (div_nonneg (oddB_nonneg m) (faceConst3_pos m).le)
    (Finset.prod_nonneg fun j _ => (τ j).fl0)

/-- The floor at the root. -/
theorem num_floor {Lu Lv : Finset ℕ} {Li : Fin m → Finset ℕ} (hLi : ∀ j, (Li j).card = 3)
    {E : Fin (m + 1) → ℕ → ℕ → ℝ} (hE0 : ∀ j c d, 0 ≤ E j c d) {A : Fin (m + 1) → ℝ}
    (hA : ∀ j, 0 < A j)
    (hE : ∀ j, Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j)
      ((τ j).fl * A j)) :
    Dominant Lu Lv (faceSum Li (fun _ _ => 1) E) (faceFloor m τ * (faceConst3 m * ∏ j, A j)) := by
  have h := dom_face_bare Lu Lv Li hLi E hE0 (fun j => (τ j).fl * A j)
    (fun j => mul_nonneg (τ j).fl0 (hA j).le) hE
  have e : oddB m * ∏ j, (τ j).fl * A j = faceFloor m τ * (faceConst3 m * ∏ j, A j) := by
    rw [prod_fl_mul, faceFloor]
    have := (faceConst3_pos m).ne'
    field_simp
  rwa [e] at h

theorem prod_erase_split (j₀ : Fin (m + 1)) (A : Fin (m + 1) → ℝ) :
    ∏ j, (if j = j₀ then A j else (τ j).fl * A j)
      = (∏ j ∈ univ.erase j₀, (τ j).fl) * ∏ j, A j := by
  have e : ∀ j, (if j = j₀ then A j else (τ j).fl * A j)
      = (if j = j₀ then 1 else (τ j).fl) * A j := fun j => by split_ifs <;> simp
  simp only [e, Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.mul_prod_erase univ _ (mem_univ j₀)]
  simp only [↓reduceIte, one_mul]
  exact Finset.prod_congr rfl fun j hj => by simp [(mem_erase.mp hj).1]

theorem prod_two_split (j₁ j₂ : Fin (m + 1)) (A : Fin (m + 1) → ℝ) :
    ∏ j, (if j = j₁ ∨ j = j₂ then A j else (τ j).fl * A j)
      = (∏ j ∈ univ.filter (fun j => ¬(j = j₁ ∨ j = j₂)), (τ j).fl) * ∏ j, A j := by
  have e : ∀ j, (if j = j₁ ∨ j = j₂ then A j else (τ j).fl * A j)
      = (if j = j₁ ∨ j = j₂ then 1 else (τ j).fl) * A j := fun j => by split_ifs <;> simp
  simp only [e, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul]

/-- **The face rule is sound.** -/
theorem numRule_sound (hr : numRule t m τ) : numSys.RuleSound t m τ := by
  intro Lu Lv Li hLu hLv hLi E hE0 A hA hE
  obtain ⟨hm1, hhex, hmb, htb, hfl, hhull⟩ := hr
  change ∀ j, ncls (τ j) _ _ (E j) (A j) at hE
  change ncls t Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j)
  have hP : 0 < ∏ j, A j := Finset.prod_pos fun j _ => hA j
  have hN : 0 < faceConst3 m * ∏ j, A j := mul_pos (faceConst3_pos m) hP
  have hW0 : ∀ c d, 0 ≤ faceSum Li (fun _ _ => 1) E c d :=
    faceSum_nonneg Li _ E (fun _ _ _ => zero_le_one) hE0
  -- the matching bound at the root, when the sides carry it
  have hpot : (∀ j, (τ j).mb = true) →
      (2 ≤ m ∨ ∀ j j', j ≠ j' → 1 ≤ 2 * ((τ j).tv * (τ j').tv)) →
      HasPot Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
    intro hall hcase
    rcases Nat.lt_or_ge m 2 with hlt | h2
    · obtain rfl : m = 1 := by omega
      have hpair := hcase.resolve_left (by omega)
      have h := hasPot_tri hLu hLv hLi hE0 hA (fun j => (hE j).2.1 (hall j))
        (fun j => (hE j).2.2.1) (hpair 0 1 (by decide))
      rwa [faceConst3_one, one_mul]
    · exact hasPot_face3 h2 Lu Lv Li hLu hLv hLi E hE0 A hA fun j => (hE j).2.1 (hall j)
  -- the hexagon bound
  have hhex' : Hex Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
    rcases hhex with hodd | ⟨h2, hall⟩
    · rcases Nat.lt_or_ge m 3 with hlt | h3
      · obtain rfl : m = 1 := by obtain ⟨k, hk⟩ := hodd; omega
        have h := hex_tri hLi hE0 (fun j => (hA j).le) fun j => (hE j).1
        rwa [faceConst3_one, one_mul]
      · exact hexOddClosed m hodd h3 Lu Lv Li hLu hLv hLi E hE0 A hA fun j => (hE j).1
    · exact (hpot hall (Or.inl h2)).hex hLu hLv hN.le
  -- the floor
  have hfloor := num_floor hLi hE0 hA fun j => (hE j).2.2.2.1
  -- the four-cell bound
  have htb' : TB Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) t.tv := by
    rcases htb with hF | ⟨j₀, hj₀⟩ | ⟨rfl, hpair⟩ | ⟨rfl, hsq⟩ | ⟨hodd, h3, j₁, j₂, h12, hj⟩ |
        ⟨rfl, j₀, hj₀h, hj₀f, hj₀t⟩
    · exact (hfloor.tb_floor faceFloor_nonneg hN.le).anti t.tv0 hF
    · by_cases hpos : ∀ j ∈ univ.erase j₀, 0 < (τ j).fl
      · set A' : Fin (m + 1) → ℝ := fun j => if j = j₀ then A j else (τ j).fl * A j
          with hA'def
        have hA' : ∀ j, 0 < A' j := fun j => by
          simp only [hA'def]
          split_ifs with h
          · exact hA j
          · exact mul_pos (hpos j (mem_erase.mpr ⟨h, mem_univ j⟩)) (hA j)
        have hT : TB (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) (E j₀) (A' j₀)
            (τ j₀).tv := by
          simp only [hA'def, ↓reduceIte]
          exact (hE j₀).2.2.1
        have hD : ∀ j, j ≠ j₀ → Dominant (pathList Lu Lv Li j.castSucc)
            (pathList Lu Lv Li j.succ) (E j) (A' j) := fun j hj => by
          simp only [hA'def, hj, ↓reduceIte]
          exact (hE j).2.2.2.1
        have h := tb_transport m Lu Lv Li hLv hLi j₀ E hE0 A' hA' hT hD
        rw [show ∏ j, A' j = (∏ j ∈ univ.erase j₀, (τ j).fl) * ∏ j, A j from
          prod_erase_split j₀ A, mul_left_comm] at h
        exact h.scale.anti t.tv0 hj₀
      · simp only [not_forall, not_lt] at hpos
        obtain ⟨j, hj, hle⟩ := hpos
        have h0 : ∏ j ∈ univ.erase j₀, (τ j).fl = 0 :=
          Finset.prod_eq_zero hj (le_antisymm hle (τ j).fl0)
        rw [h0] at hj₀
        refine (TB.zero hW0).anti t.tv0 ?_
        simpa using hj₀
    · have h := tb_tri hLi hE0 fun j => (hE j).2.2.1
      rw [faceConst3_one, one_mul]
      exact h.anti t.tv0 (hpair 0 1 (by decide))
    · have h := tb_square Lu Lv Li hLi E hE0 (fun j => (τ j).fl * A j)
        (fun j => mul_nonneg (τ j).fl0 (hA j).le) fun j => (hE j).2.2.2.1
      rw [prod_fl_mul, mul_left_comm] at h
      exact h.scale.anti t.tv0 hsq
    · by_cases hpos : ∀ j ∈ univ.filter (fun j => ¬(j = j₁ ∨ j = j₂)), 0 < (τ j).fl
      · set A' : Fin (m + 1) → ℝ := fun j => if j = j₁ ∨ j = j₂ then A j else (τ j).fl * A j
          with hA'def
        have hA' : ∀ j, 0 < A' j := fun j => by
          simp only [hA'def]
          split_ifs with h
          · exact hA j
          · exact mul_pos (hpos j (mem_filter.mpr ⟨mem_univ j, h⟩)) (hA j)
        have hT₁ : TB (pathList Lu Lv Li j₁.castSucc) (pathList Lu Lv Li j₁.succ) (E j₁) (A' j₁)
            (τ j₁).tv := by
          simp only [hA'def, true_or, ↓reduceIte]
          exact (hE j₁).2.2.1
        have hT₂ : TB (pathList Lu Lv Li j₂.castSucc) (pathList Lu Lv Li j₂.succ) (E j₂) (A' j₂)
            (τ j₂).tv := by
          simp only [hA'def, or_true, ↓reduceIte]
          exact (hE j₂).2.2.1
        have hD : ∀ j, j ≠ j₁ → j ≠ j₂ → Dominant (pathList Lu Lv Li j.castSucc)
            (pathList Lu Lv Li j.succ) (E j) (A' j) := fun j h1 h2 => by
          simp only [hA'def, h1, h2, or_self, ↓reduceIte]
          exact (hE j).2.2.2.1
        have h := tb_transport2 m hodd h3 Lu Lv Li hLv hLi j₁ j₂ h12 E hE0 A' hA' hT₁ hT₂ hD
        rw [show ∏ j, A' j = (∏ j ∈ univ.filter (fun j => ¬(j = j₁ ∨ j = j₂)), (τ j).fl)
            * ∏ j, A j from prod_two_split j₁ j₂ A, mul_left_comm] at h
        exact h.scale.anti t.tv0 hj
      · simp only [not_forall, not_lt] at hpos
        obtain ⟨j, hj', hle⟩ := hpos
        have h0 : ∏ j ∈ univ.filter (fun j => ¬(j = j₁ ∨ j = j₂)), (τ j).fl = 0 :=
          Finset.prod_eq_zero hj' (le_antisymm hle (τ j).fl0)
        rw [h0] at hj
        refine (TB.zero hW0).anti t.tv0 ?_
        simpa using hj
    · have h := tb_square_hull Lu Lv Li hLu hLv hLi j₀ E hE0 A hA ((hE j₀).2.2.2.2 hj₀h)
        fun j hj => by
          have := (hE j).2.2.2.1
          rwa [hj₀f j hj, one_mul] at this
      exact h.anti t.tv0 hj₀t
  -- the hull class
  have hhull' : t.hull = true → HullC Lu Lv (faceSum Li (fun _ _ => 1) E)
      (faceConst3 m * ∏ j, A j) := by
    intro ht
    rcases hhull ht with ⟨rfl, hall⟩ | ⟨hodd, j₀, hj₀, hothers⟩
    · exact hullC_square Lu Lv Li hLi E hE0 A (fun j => (hA j).le) fun j => by
        have := (hE j).2.2.2.1
        rwa [hall j, one_mul] at this
    · exact hullC_transport m hodd Lu Lv Li hLv hLi j₀ E hE0 A hA ((hE j₀).2.2.2.2 hj₀)
        fun j hj => by
          have := (hE j).2.2.2.1
          rwa [hothers j hj, one_mul] at this
  exact ⟨hhex', fun h => (hmb h).elim fun hall hc => hpot hall hc, htb',
    hfloor.le (mul_le_mul_of_nonneg_right hfl hN.le), hhull'⟩

/-- **Any two tags glue**: every class contains the hexagon bound. -/
theorem num_glue (t₁ t₂ : NTag) : numSys.GlueSound t₁ t₂ := by
  intro S T W W' A A' hS hT h0 h0' hA hA' h₁ h₂
  change ncls t₁ S T W A at h₁
  change ncls t₂ T S W' A' at h₂
  have h := Hex.glue hS hT h₁.1 h₂.1.swap hA hA' h0 fun c d => h0' d c
  rw [Finset.sum_comm]
  refine h.trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => mul_comm _ _

end Sound

/-! ### A catalogue of rules -/

section Catalogue

/-- One square below (the bare-square constants). -/
noncomputable def tSq : NTag :=
  ⟨true, 3 / 4, 2 / 3, by norm_num, by norm_num, by norm_num, by norm_num, true⟩

/-- One even face of length at least six below. -/
noncomputable def tLong : NTag :=
  ⟨true, 3 / 4, 10 / 11, by norm_num, by norm_num, by norm_num, by norm_num, false⟩

/-- Two marks below. -/
noncomputable def tTwo : NTag := ⟨true, 1 / 2, 0, by norm_num, by norm_num, le_refl _, by norm_num, false⟩

/-- The matching bound only. -/
def tMB : NTag := ⟨true, 0, 0, le_refl _, by norm_num, le_refl _, by norm_num, false⟩

/-- The hexagon bound only. -/
def tHex : NTag := ⟨false, 0, 0, le_refl _, by norm_num, le_refl _, by norm_num, false⟩

theorem dd_face {m : ℕ} (j₀ : Fin (m + 1)) :
    dd j₀ (m - j₀) = faceConst3 m - if Even m then 1 else 0 := by
  have e : (j₀ : ℕ) + (m - j₀) = m := by omega
  unfold dd
  rw [e, ← faceConst3_eq_dN]
  simp [Nat.odd_add_one, Nat.not_odd_iff_even]

theorem oddB_div_odd {m : ℕ} (hm : Odd m) : oddB m / faceConst3 m = 1 := by
  obtain ⟨k, rfl⟩ := hm
  rw [oddB_odd, div_self (faceConst3_pos _).ne']

theorem oddB_div_even {m : ℕ} (hm : Even m) (h4 : 4 ≤ m) : 10 / 11 ≤ oddB m / faceConst3 m := by
  have hα : 11 ≤ faceConst3 m := by
    obtain ⟨k, rfl⟩ := hm
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    have e : k' + 2 + (k' + 2) = 2 * k' + 4 := by ring
    rw [e]
    exact faceConst3_ge_eleven k'
  have e : oddB m = faceConst3 m - 1 := by
    obtain ⟨k, hk⟩ := hm
    rw [hk, ← two_mul, oddB_even]
  rw [e, le_div_iff₀ (by linarith)]
  linarith

variable {m : ℕ} {τ : Fin (m + 1) → NTag}

theorem prod_fl_single (j₀ : Fin (m + 1)) (hdom : ∀ j, j ≠ j₀ → τ j = NTag.plain) :
    ∏ j, (τ j).fl = (τ j₀).fl :=
  Finset.prod_eq_single j₀ (fun j _ hj => by rw [hdom j hj]; rfl) (by simp)

theorem prod_fl_erase (j₀ : Fin (m + 1)) (hdom : ∀ j, j ≠ j₀ → τ j = NTag.plain) :
    ∏ j ∈ univ.erase j₀, (τ j).fl = 1 :=
  Finset.prod_eq_one fun j hj => by rw [hdom j (mem_erase.mp hj).1]; rfl

/-- **Odd faces preserve a tag** on one side, with greedy sides elsewhere (at a triangle the
matching bound needs `τ ≥ 1/2`). -/
theorem numRule_odd_one (hm : Odd m) (j₀ : Fin (m + 1)) (hdom : ∀ j, j ≠ j₀ → τ j = NTag.plain)
    (hmb : (τ j₀).mb = true → 3 ≤ m ∨ 1 ≤ 2 * (τ j₀).tv) : numRule (τ j₀) m τ := by
  have hα := (faceConst3_pos m).ne'
  have hdd : dd j₀ (m - j₀) = faceConst3 m := by
    rw [dd_face]
    simp [Nat.not_even_iff_odd.mpr hm]
  refine ⟨hm.pos, Or.inl hm, fun h => ⟨fun j => ?_, ?_⟩, Or.inr (Or.inl ⟨j₀, ?_⟩), ?_,
    fun h => Or.inr ⟨hm, j₀, h, fun j hj => by rw [hdom j hj]; rfl⟩⟩
  · by_cases hj : j = j₀
    · rw [hj]; exact h
    · rw [hdom j hj]; rfl
  · rcases hmb h with h3 | h2
    · left; omega
    · right
      intro j j' hjj'
      have h1 := (τ j₀).tv1
      by_cases hj : j = j₀
      · rw [hj, hdom j' (fun e => hjj' (hj.trans e.symm))]
        change 1 ≤ 2 * ((τ j₀).tv * 1)
        linarith
      · rw [hdom j hj]
        by_cases hj' : j' = j₀
        · rw [hj']
          change 1 ≤ 2 * (1 * (τ j₀).tv)
          linarith
        · rw [hdom j' hj']
          change (1 : ℝ) ≤ 2 * (1 * 1)
          norm_num
  · rw [hdd, div_self hα, prod_fl_erase j₀ hdom]
    simp
  · rw [faceFloor, oddB_div_odd hm, one_mul, prod_fl_single j₀ hdom]

/-- **A bare square** carries `tSq`. -/
theorem numRule_bare_square : numRule tSq 2 fun _ => NTag.plain := by
  have hF : faceFloor 2 (fun _ => NTag.plain) = 2 / 3 := by
    simp only [faceFloor, NTag.plain, Finset.prod_const_one, mul_one]
    have h2 : oddB 2 = 2 := by
      show oddB (0 + 2) = 2
      rw [oddB_add_two, oddB]
      norm_num
    rw [h2]
    norm_num [faceConst3]
  refine ⟨by norm_num, Or.inr ⟨le_refl _, fun _ => rfl⟩, fun _ => ⟨fun _ => rfl, Or.inl le_rfl⟩,
    Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))), ?_, fun _ => Or.inl ⟨rfl, fun _ => rfl⟩⟩
  · simp [tSq, NTag.plain]
  · rw [hF]
    simp [tSq]

/-- **A bare even face of length at least six** carries `tLong`. -/
theorem numRule_bare_long (hm : Even m) (h4 : 4 ≤ m) : numRule tLong m fun _ => NTag.plain := by
  have hF : 10 / 11 ≤ faceFloor m (fun _ => NTag.plain) := by
    simp only [faceFloor, NTag.plain, Finset.prod_const_one, mul_one]
    exact oddB_div_even hm h4
  refine ⟨by omega, Or.inr ⟨by omega, fun _ => rfl⟩, fun _ => ⟨fun _ => rfl, Or.inl (by omega)⟩,
    Or.inl ?_, hF, fun h => absurd h (by simp [tLong])⟩
  calc tLong.tv = 3 / 4 := rfl
    _ ≤ (10 / 11) ^ 3 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) hF 3

/-- **An even face of length at least six with one singly marked side** carries `tTwo`. -/
theorem numRule_even_one (hm : Even m) (h4 : 4 ≤ m) (j₀ : Fin (m + 1))
    (hdom : ∀ j, j ≠ j₀ → τ j = NTag.plain) (hmb : (τ j₀).mb = true) (htv : 3 / 4 ≤ (τ j₀).tv) :
    numRule tTwo m τ := by
  have hall : ∀ j, (τ j).mb = true := fun j => by
    by_cases hj : j = j₀
    · rw [hj]; exact hmb
    · rw [hdom j hj]; rfl
  have hdd : 10 / 11 ≤ dd j₀ (m - j₀) / faceConst3 m := by
    rw [dd_face]
    simp only [hm, ↓reduceIte]
    have e : oddB m = faceConst3 m - 1 := by
      obtain ⟨k, hk⟩ := hm
      rw [hk, ← two_mul, oddB_even]
    rw [← e]
    exact oddB_div_even hm h4
  refine ⟨by omega, Or.inr ⟨by omega, hall⟩, fun _ => ⟨hall, Or.inl (by omega)⟩,
    Or.inr (Or.inl ⟨j₀, ?_⟩), ?_, fun h => absurd h (by simp [tTwo])⟩
  · rw [prod_fl_erase j₀ hdom, one_pow, mul_one]
    calc tTwo.tv = 1 / 2 := rfl
      _ ≤ 3 / 4 * (10 / 11) ^ 3 := by norm_num
      _ ≤ _ := mul_le_mul htv (pow_le_pow_left₀ (by norm_num) hdd 3) (by positivity)
        (τ j₀).tv0
  · exact faceFloor_nonneg

/-- **A square over one even face of length at least six** carries `tTwo`, by comparison with
the bare square. -/
theorem numRule_square_long {τ : Fin 3 → NTag} (j₀ : Fin 3) (hdom : ∀ j, j ≠ j₀ → τ j = NTag.plain)
    (hmb : (τ j₀).mb = true) (hfl : 10 / 11 ≤ (τ j₀).fl) : numRule tTwo 2 τ := by
  have hall : ∀ j, (τ j).mb = true := fun j => by
    by_cases hj : j = j₀
    · rw [hj]; exact hmb
    · rw [hdom j hj]; rfl
  refine ⟨by norm_num, Or.inr ⟨le_refl _, hall⟩, fun _ => ⟨hall, Or.inl le_rfl⟩,
    Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))), faceFloor_nonneg,
    fun h => absurd h (by simp [tTwo])⟩
  rw [prod_fl_single j₀ hdom]
  calc tTwo.tv = 1 / 2 := rfl
    _ ≤ 3 / 4 * (10 / 11) ^ 3 := by norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hfl 3) (by norm_num)

/-- **A triangle** with side tags `τ 0`, `τ 1` carries any tag below the product of their
four-cell constants and floors; the matching bound needs `2 τ₀ τ₁ ≥ 1` (Hall). -/
theorem numRule_tri {τ : Fin 2 → NTag} (t : NTag)
    (hmb : t.mb = true → (τ 0).mb = true ∧ (τ 1).mb = true ∧ 1 ≤ 2 * ((τ 0).tv * (τ 1).tv))
    (htv : t.tv ≤ (τ 0).tv * (τ 1).tv) (hfl : t.fl ≤ (τ 0).fl * (τ 1).fl) (hh : t.hull = false) :
    numRule t 1 τ := by
  have hF : faceFloor 1 τ = (τ 0).fl * (τ 1).fl := by
    rw [faceFloor, oddB_div_odd (m := 1) ⟨0, rfl⟩, one_mul, Fin.prod_univ_two]
  have hpair : ∀ (P : ℝ → ℝ → Prop), (∀ x y, P x y → P y x) → P (τ 0).tv (τ 1).tv →
      ∀ j j' : Fin 2, j ≠ j' → P (τ j).tv (τ j').tv := by
    intro P hP h j j' hjj'
    fin_cases j <;> fin_cases j' <;> first | exact absurd rfl hjj' | exact h | exact hP _ _ h
  refine ⟨le_refl _, Or.inl ⟨0, rfl⟩, fun h => ⟨fun j => ?_, Or.inr ?_⟩,
    Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩)), by rw [hF]; exact hfl, fun h => absurd h (by simp [hh])⟩
  · obtain ⟨h0, h1, -⟩ := hmb h
    fin_cases j
    · exact h0
    · exact h1
  · exact hpair (fun x y => 1 ≤ 2 * (x * y)) (fun x y hxy => by rwa [mul_comm y x])
      (hmb h).2.2
  · exact hpair (fun x y => t.tv ≤ x * y) (fun x y hxy => by rwa [mul_comm y x]) htv

/-- **An odd face of length at least five with two marked sides** carries any tag below the
product of their four-cell constants (`tb_transport2`), with greedy sides elsewhere. -/
theorem numRule_odd_two (hm : Odd m) (h3 : 3 ≤ m) (t : NTag) (j₁ j₂ : Fin (m + 1))
    (h12 : j₁ < j₂) (hdom : ∀ j, j ≠ j₁ → j ≠ j₂ → τ j = NTag.plain)
    (hmb : t.mb = true → (τ j₁).mb = true ∧ (τ j₂).mb = true)
    (htv : t.tv ≤ (τ j₁).tv * (τ j₂).tv) (hfl : t.fl ≤ (τ j₁).fl * (τ j₂).fl)
    (hh : t.hull = false) : numRule t m τ := by
  have hne : j₁ ≠ j₂ := ne_of_lt h12
  have hprod : ∏ j, (τ j).fl = (τ j₁).fl * (τ j₂).fl := by
    rw [← Finset.prod_pair (f := fun j => (τ j).fl) hne]
    refine (Finset.prod_subset (subset_univ _) fun j _ hj => ?_).symm
    simp only [mem_insert, mem_singleton, not_or] at hj
    rw [hdom j hj.1 hj.2]
    rfl
  have hrest : ∏ j ∈ univ.filter (fun j => ¬(j = j₁ ∨ j = j₂)), (τ j).fl = 1 :=
    Finset.prod_eq_one fun j hj => by
      simp only [mem_filter, mem_univ, true_and, not_or] at hj
      rw [hdom j hj.1 hj.2]
      rfl
  refine ⟨hm.pos, Or.inl hm, fun h => ⟨fun j => ?_, Or.inl (by omega)⟩,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hm, h3, j₁, j₂, h12, by rw [hrest]; simpa using htv⟩)))),
    ?_, fun h => absurd h (by simp [hh])⟩
  · by_cases h1 : j = j₁
    · rw [h1]; exact (hmb h).1
    · by_cases h2 : j = j₂
      · rw [h2]; exact (hmb h).2
      · rw [hdom j h1 h2]; rfl
  · rw [faceFloor, oddB_div_odd hm, one_mul, hprod]
    exact hfl

/-- **A square over a branch with one square** (a side of the hull class, greedy sides elsewhere)
carries `tTwo` (`tb_square_hull`). -/
theorem numRule_square_hull {τ : Fin 3 → NTag} (j₀ : Fin 3)
    (hdom : ∀ j, j ≠ j₀ → τ j = NTag.plain) (hmb : (τ j₀).mb = true) (hh : (τ j₀).hull = true) :
    numRule tTwo 2 τ := by
  have hall : ∀ j, (τ j).mb = true := fun j => by
    by_cases hj : j = j₀
    · rw [hj]; exact hmb
    · rw [hdom j hj]; rfl
  exact ⟨by norm_num, Or.inr ⟨le_refl _, hall⟩, fun _ => ⟨hall, Or.inl le_rfl⟩,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, j₀, hh, fun j hj => by rw [hdom j hj]; rfl,
      le_refl _⟩)))), faceFloor_nonneg, fun h => absurd h (by simp [tTwo])⟩

/-- **The matching bound through faces of length at least four.** -/
theorem numRule_mb (h2 : 2 ≤ m) (hall : ∀ j, (τ j).mb = true) : numRule tMB m τ :=
  ⟨by omega, Or.inr ⟨h2, hall⟩, fun _ => ⟨hall, Or.inl h2⟩,
    Or.inl (pow_nonneg faceFloor_nonneg 3), faceFloor_nonneg, fun h => absurd h (by simp [tMB])⟩

/-- **The hexagon bound through odd faces**, whatever the sides. -/
theorem numRule_hex_odd (hm : Odd m) : numRule tHex m τ :=
  ⟨hm.pos, Or.inl hm, fun h => absurd h (by simp [tHex]),
    Or.inl (pow_nonneg faceFloor_nonneg 3), faceFloor_nonneg, fun h => absurd h (by simp [tHex])⟩

/-- **The hexagon bound through even faces** whose sides have the matching bound. -/
theorem numRule_hex_even (h2 : 2 ≤ m) (hall : ∀ j, (τ j).mb = true) : numRule tHex m τ :=
  ⟨by omega, Or.inr ⟨h2, hall⟩, fun h => absurd h (by simp [tHex]),
    Or.inl (pow_nonneg faceFloor_nonneg 3), faceFloor_nonneg, fun h => absurd h (by simp [tHex])⟩

end Catalogue

/-! ### The theorem -/

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Graphs built by ears following the numeric face rule are 3-ECC.** -/
theorem ecc_three_of_numBuilt {tg : V → V → NTag}
    (h : TagBuilt G numSys numRule (fun _ _ => True) univ tg) : G.ECCAt 3 :=
  ecc_three_of_tagBuilt G (fun _ _ _ hr => numRule_sound hr) (fun t₁ t₂ _ => num_glue t₁ t₂) h

end Outerplanar
