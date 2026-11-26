/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.MarkTwo

/-!
# A square with two singly marked sides

Research note `ai_research_notes/OUTERPLANAR_ELEVEN_AND_CENTRAL_SQUARE_2026-11-23.md`, "Three
marks": *at a square with two active single marks on different sides the output has bijection
product `q²`. Its floor is `4/9`. Indeed at a root pair with at least three legal paths, the two
child floors give `4/9` after division by three. At a deficient root pair the permitted interior
colour sets are the same two-set `{x, y}`, and the walks use `(x, y)` and `(y, x)`. At each side
the two edge pairs are distinct and in one matched family … Each active child therefore has
geometric mean at least `√(2/3)` on these two paths. AM–GM and the ordinary divisor three give at
least `(2/3)(√(2/3))² = 4/9`. Capping the output as in the seven-face proof gives `AB`, since
`(q²)^191 (4/9)^27 ≥ A^600`.*

* `PairB S T W κ` — two distinct cells of any matched family of proper cells have product at
  least `κ`; from the hull class (`κ = 2/3 A²`, `hull_pair`) and from greedy profiles (`κ = A²`).
* `fam_of_enum` — an enumeration of one list and an aligned enumeration of the other give a
  matched family of proper cells.
* **`floor_square`** — the floor of a square from floors `B j` and pair bounds `κ j` on its sides:
  every target `t` with `t ≤ 3 ∏ B` and `t² ≤ 4 ∏ κ`. At a deficient root pair `(c, d)` the two
  walks `c x y d` and `c y x d` have product of weights at least `∏ κ`.
* `p3_square_two` — two one-mark tables on two sides of a square: the floor `4/9` (of the
  ordinary count), the bijection product `q²`, and the ball with gain `17/16` by capping.
* **`mx3_square_two`** — a square with two sides in the one-mark class and a greedy third side is
  in the mixture class `BMix` (`= Mx P3`).

The theorem of the note is due to another AI session of this repository's collaboration; audited
and formalized by Claude.
-/

namespace Outerplanar

open Finset

/-! ### Pair bounds -/

/-- Two distinct cells of any matched family of proper cells have product at least `κ`. -/
def PairB (S T : Finset ℕ) (W : ℕ → ℕ → ℝ) (κ : ℝ) : Prop :=
  ∀ p q : Fin 6 → ℕ, Matched S T p q → (∀ i, p i ≠ q i) → ∀ i i', i ≠ i' →
    κ ≤ W (p i) (q i) * W (p i') (q i')

section Pair

variable {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {A κ : ℝ}

theorem HullC.pairB (hA : 0 ≤ A) (h : HullC S T W A) : PairB S T W (2 / 3 * A ^ 2) :=
  fun _ _ hm hpq _ _ hii => hull_pair hA h hm hpq hii

theorem Dominant.pairB (hA : 0 ≤ A) (h : Dominant S T W A) : PairB S T W (A ^ 2) :=
  fun p q hm hpq i i' _ => by
    have h1 := h _ (hm.mem i).1 _ (hm.mem i).2 (hpq i)
    have h2 := h _ (hm.mem i').1 _ (hm.mem i').2 (hpq i')
    rw [sq]
    exact mul_le_mul h1 h2 hA (hA.trans h1)

theorem PairB.swap (h : PairB S T W κ) : PairB T S (fun d c => W c d) κ :=
  fun p q hm hpq i i' hii => h q p hm.symm (fun i => (hpq i).symm) i i' hii

/-- An enumeration `β` of `T` and an aligned enumeration of `S` give a matched family of proper
cells `(γ a, β b)`, `a ≠ b`. -/
theorem fam_of_enum (hS : S.card = 3) {β : Fin 3 → ℕ} (hβ : Function.Injective β)
    (hβm : ∀ b, β b ∈ T) :
    ∃ γ : Fin 3 → ℕ, (∀ a, γ a ∈ S) ∧ Function.Injective γ ∧ (∀ a b, γ a = β b → a = b) ∧
      Matched S T (fun i => γ (offPair i).1) (fun i => β (offPair i).2) ∧
      ∀ i, γ (offPair i).1 ≠ β (offPair i).2 := by
  obtain ⟨γ, hγ, hγm, hal⟩ := exists_aligned hS hβ
  refine ⟨γ, hγm, hγ, fun a b e => (hal a b e).symm, ⟨γ, β, hγ, hβ, hγm, hβm, fun a b hab => ?_⟩,
    fun i e => offPair_ne i (hal _ _ e).symm⟩
  obtain ⟨i, hi⟩ := offPair_surj a b hab
  exact ⟨i, by simp [hi], by simp [hi]⟩

/-- In an aligned family a common colour has the index it has in `β`. -/
theorem aligned_idx (hS : S.card = 3) {γ β : Fin 3 → ℕ} (hγm : ∀ a, γ a ∈ S)
    (hγ : Function.Injective γ) (hal : ∀ a b, γ a = β b → a = b) {b : Fin 3} (hb : β b ∈ S) :
    γ b = β b := by
  obtain ⟨a, ha⟩ := enum_surj hS hγ hγm hb
  obtain rfl := hal a b ha
  exact ha

end Pair

/-! ### The floor of a square -/

/-- **The floor of a square from floors and pair bounds on its sides.** -/
theorem floor_square (Lu Lv : Finset ℕ) (Li : Fin 2 → Finset ℕ) (hLu : Lu.card = 3)
    (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3) (E : Fin 3 → ℕ → ℕ → ℝ)
    (hE0 : ∀ j c d, 0 ≤ E j c d) (B κ : Fin 3 → ℝ) (hB0 : ∀ j, 0 ≤ B j)
    (hB : ∀ j, Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (B j))
    (hP : ∀ j, PairB (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (κ j))
    (hκ0 : ∀ j, 0 ≤ κ j) {t : ℝ} (ht0 : 0 ≤ t) (ht3 : t ≤ 3 * ∏ j, B j)
    (ht2 : t ^ 2 ≤ 4 * ∏ j, κ j) :
    Dominant Lu Lv (faceSum Li (fun _ _ => 1) E) t := by
  intro c hc d hd hcd
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := pathList_two Lu Lv Li
  have hP0 : PairB Lu (Li 0) (E 0) (κ 0) := by have := hP 0; rwa [l0, l1] at this
  have hP1 : PairB (Li 0) (Li 1) (E 1) (κ 1) := by have := hP 1; rwa [l2, l3] at this
  have hP2 : PairB (Li 1) Lv (E 2) (κ 2) := by have := hP 2; rwa [l4, l5] at this
  have hW : (∏ j, B j) * bsq (Li 0) (Li 1) c d ≤ faceSum Li (fun _ _ => 1) E c d := by
    have := faceSum_ge_bare Lu Lv Li E hE0 B hB0 hB hc hd
    rw [faceSum_two Li (fun _ => neP)] at this
    exact this
  have hPB : 0 ≤ ∏ j, B j := Finset.prod_nonneg fun j _ => hB0 j
  by_cases h3 : 3 ≤ bsq (Li 0) (Li 1) c d
  · have : (∏ j, B j) * 3 ≤ (∏ j, B j) * bsq (Li 0) (Li 1) c d :=
      mul_le_mul_of_nonneg_left h3 hPB
    linarith
  push Not at h3
  -- the deficient pair
  have hge := bsq_ge (hLi 0) (hLi 1) c d
  have hc1 : c ∈ Li 0 := by
    by_contra h
    linarith [hge.2 (Or.inl h)]
  have hd1 : d ∈ Li 1 := by
    by_contra h
    linarith [hge.2 (Or.inr h)]
  have hU := (card_erase_three (hLi 0)).1 hc1
  have hV := (card_erase_three (hLi 1)).1 hd1
  rw [bsq_eq, hU, hV] at h3
  have hI2 : 2 ≤ ((Li 0).erase c ∩ (Li 1).erase d).card := by
    by_contra h
    push Not at h
    have : (((Li 0).erase c ∩ (Li 1).erase d).card : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp h
    push_cast at h3
    linarith
  have hIU : (Li 0).erase c ∩ (Li 1).erase d = (Li 0).erase c :=
    Finset.eq_of_subset_of_card_le inter_subset_left (by omega)
  have hIV : (Li 0).erase c ∩ (Li 1).erase d = (Li 1).erase d :=
    Finset.eq_of_subset_of_card_le inter_subset_right (by omega)
  obtain ⟨x, y, hxy, hUxy⟩ := card_eq_two.mp hU
  have hx : x ∈ (Li 0).erase c := by rw [hUxy]; simp
  have hy : y ∈ (Li 0).erase c := by rw [hUxy]; simp
  have hx' : x ∈ (Li 1).erase d := by rw [← hIV, hIU]; exact hx
  have hy' : y ∈ (Li 1).erase d := by rw [← hIV, hIU]; exact hy
  obtain ⟨hxc, hx0⟩ := mem_erase.mp hx
  obtain ⟨hyc, hy0⟩ := mem_erase.mp hy
  obtain ⟨hxd, hx1⟩ := mem_erase.mp hx'
  obtain ⟨hyd, hy1⟩ := mem_erase.mp hy'
  -- two walks
  set X := E 0 c x * E 1 x y * E 2 y d with hX
  set X' := E 0 c y * E 1 y x * E 2 x d with hX'
  have hsum : X + X' ≤ faceSum Li (fun _ _ => 1) E c d := by
    rw [faceSum_two]
    have hterm : ∀ x' ∈ Li 0, ∀ y' ∈ Li 1, 0 ≤ E 0 c x' * E 1 x' y' * E 2 y' d :=
      fun x' _ y' _ => mul_nonneg (mul_nonneg (hE0 _ _ _) (hE0 _ _ _)) (hE0 _ _ _)
    have hinner : ∀ x' ∈ Li 0, 0 ≤ ∑ y' ∈ Li 1, E 0 c x' * E 1 x' y' * E 2 y' d :=
      fun x' hx' => Finset.sum_nonneg fun y' hy' => hterm x' hx' y' hy'
    have hsub : ({x, y} : Finset ℕ) ⊆ Li 0 := by
      intro z hz
      rcases mem_insert.mp hz with rfl | hz
      · exact hx0
      · rw [mem_singleton.mp hz]; exact hy0
    have k1 := Finset.sum_le_sum_of_subset_of_nonneg hsub fun x' hx' _ => hinner x' hx'
    rw [Finset.sum_pair hxy] at k1
    have kx := Finset.single_le_sum (f := fun y' => E 0 c x * E 1 x y' * E 2 y' d)
      (fun y' hy' => hterm x hx0 y' hy') hy1
    have ky := Finset.single_le_sum (f := fun y' => E 0 c y * E 1 y y' * E 2 y' d)
      (fun y' hy' => hterm y hy0 y' hy') hx1
    linarith
  -- the pair bounds along the two walks
  have k0 : κ 0 ≤ E 0 c x * E 0 c y := by
    obtain ⟨γ, hγm, hγ, hal, hm, hpq⟩ := fam_of_enum (T := Li 0) hLu
      (injective_three hxc.symm hyc.symm hxy)
      (fun b => by fin_cases b <;> simp [hc1, hx0, hy0])
    have e0 : γ 0 = c := aligned_idx hLu hγm hγ hal (b := 0) (by simpa using hc)
    have := hP0 _ _ hm hpq 0 1 (by decide)
    simpa [offPair, e0] using this
  have k1 : κ 1 ≤ E 1 x y * E 1 y x := by
    obtain ⟨γ, hγm, hγ, hal, hm, hpq⟩ := fam_of_enum (T := Li 1) (hLi 0)
      (injective_three hxy hxd hyd) (fun b => by fin_cases b <;> simp [hx1, hy1, hd1])
    have e0 : γ 0 = x := aligned_idx (hLi 0) hγm hγ hal (b := 0) (by simpa using hx0)
    have e1 : γ 1 = y := aligned_idx (hLi 0) hγm hγ hal (b := 1) (by simpa using hy0)
    have := hP1 _ _ hm hpq 0 2 (by decide)
    simpa [offPair, e0, e1] using this
  have k2 : κ 2 ≤ E 2 y d * E 2 x d := by
    obtain ⟨γ, hγm, hγ, hal, hm, hpq⟩ := fam_of_enum (T := Li 1) hLv
      (injective_three hyd.symm hxd.symm hxy.symm) (fun b => by fin_cases b <;> simp [hx1, hy1, hd1])
    have e0 : γ 0 = d := aligned_idx hLv hγm hγ hal (b := 0) (by simpa using hd)
    have := hP2.swap _ _ hm hpq 0 1 (by decide)
    simpa [offPair, e0] using this
  have hXX : κ 0 * κ 1 * κ 2 ≤ X * X' := by
    have e : X * X' = (E 0 c x * E 0 c y) * (E 1 x y * E 1 y x) * (E 2 y d * E 2 x d) := by
      rw [hX, hX']; ring
    rw [e]
    have a0 := hκ0 0
    have a1 := hκ0 1
    have a2 := hκ0 2
    exact mul_le_mul (mul_le_mul k0 k1 a1 (a0.trans k0)) k2 a2
      (mul_nonneg (a0.trans k0) (a1.trans k1))
  have hX0 : 0 ≤ X := mul_nonneg (mul_nonneg (hE0 _ _ _) (hE0 _ _ _)) (hE0 _ _ _)
  have hX0' : 0 ≤ X' := mul_nonneg (mul_nonneg (hE0 _ _ _) (hE0 _ _ _)) (hE0 _ _ _)
  rw [Fin.prod_univ_three] at ht2
  have hsq : t ^ 2 ≤ (X + X') ^ 2 := by nlinarith [sq_nonneg (X - X')]
  have : t ≤ X + X' := by nlinarith
  linarith

/-! ### Two singly marked sides -/

theorem card_two_filter {n : ℕ} {j₁ j₂ : Fin n} (h12 : j₁ ≠ j₂) :
    (univ.filter fun j => j = j₁ ∨ j = j₂).card = 2 := by
  rw [Finset.filter_or, Finset.filter_eq', Finset.filter_eq', if_pos (mem_univ _),
    if_pos (mem_univ _), Finset.card_union_of_disjoint (by simpa using h12)]
  simp

theorem prod_two_ite {n : ℕ} {j₁ j₂ : Fin n} (h12 : j₁ ≠ j₂) (a : ℝ) :
    ∏ j, (if j = j₁ ∨ j = j₂ then a else 1) = a ^ 2 := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, card_two_filter h12]

theorem prod_two_ite_mul {n : ℕ} {j₁ j₂ : Fin n} (h12 : j₁ ≠ j₂) (a : ℝ) (A : Fin n → ℝ) :
    ∏ j, ((if j = j₁ ∨ j = j₂ then a else 1) * A j) = a ^ 2 * ∏ j, A j := by
  rw [Finset.prod_mul_distrib, prod_two_ite h12]

theorem BijGe.rescale {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {N Q g : ℝ} (hg : 0 < g)
    (h : BijGe S T W N Q) : BijGe S T W (N * g) (Q / g ^ 3) := fun α β hα hβ hαm hβm hne => by
  have := h α β hα hβ hαm hβm hne
  calc Q / g ^ 3 * (N * g) ^ 3 = Q * N ^ 3 := by field_simp
    _ ≤ _ := this

/-- **Two one-mark tables on two sides of a square give the ball with gain `17/16`.** -/
theorem p3_square_two (Lu Lv : Finset ℕ) (Li : Fin 2 → Finset ℕ) (hLu : Lu.card = 3)
    (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3) (E : Fin 3 → ℕ → ℕ → ℝ)
    (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin 3 → ℝ) (hA : ∀ j, 0 < A j) {j₁ j₂ : Fin 3}
    (h12 : j₁ ≠ j₂)
    (hP₁ : P1 (pathList Lu Lv Li j₁.castSucc) (pathList Lu Lv Li j₁.succ) (E j₁) (A j₁))
    (hP₂ : P1 (pathList Lu Lv Li j₂.castSucc) (pathList Lu Lv Li j₂.succ) (E j₂) (A j₂))
    (hD : ∀ j, j ≠ j₁ → j ≠ j₂ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    InBall Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 2 * (∏ j, A j) * (17 / 16)) := by
  have h3 : faceConst3 2 = 3 := by norm_num [faceConst3]
  rw [h3]
  have hP0 : 0 < ∏ j, A j := Finset.prod_pos fun j _ => hA j
  set act : Fin 3 → Prop := fun j => j = j₁ ∨ j = j₂ with hact
  have hPa : ∀ j, act j → P1 (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j)
      (A j) := fun j hj => by
    rcases hj with rfl | rfl
    · exact hP₁
    · exact hP₂
  have hDa : ∀ j, ¬ act j → Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
      (E j) (A j) := fun j hj => hD j (fun e => hj (Or.inl e)) fun e => hj (Or.inr e)
  have hpos : ∀ j, ∀ c ∈ pathList Lu Lv Li j.castSucc, ∀ d ∈ pathList Lu Lv Li j.succ, c ≠ d →
      0 < E j c d := fun j c hc d hd hcd => by
    by_cases hj : act j
    · exact lt_of_lt_of_le (by have := hA j; positivity) ((hPa j hj).1 c hc d hd hcd)
    · exact lt_of_lt_of_le (hA j) (hDa j hj c hc d hd hcd)
  -- floor `4/9` of the count `3`
  have hfl : Dominant Lu Lv (faceSum Li (fun _ _ => 1) E) (4 / 3 * ∏ j, A j) := by
    refine floor_square Lu Lv Li hLu hLv hLi E hE0
      (fun j => (if act j then 2 / 3 else 1) * A j)
      (fun j => (if act j then 2 / 3 else 1) * A j ^ 2)
      (fun j => mul_nonneg (by split_ifs <;> norm_num) (hA j).le)
      (fun j => by
        by_cases hj : act j
        · simpa [hj] using (hPa j hj).1
        · simpa [hj] using hDa j hj)
      (fun j => by
        by_cases hj : act j
        · simpa [hj] using (hPa j hj).2.2.2.2.pairB (hA j).le
        · simpa [hj] using (hDa j hj).pairB (hA j).le)
      (fun j => mul_nonneg (by split_ifs <;> norm_num) (sq_nonneg _)) (by positivity) ?_ ?_
    · rw [show (fun j => (if act j then (2 : ℝ) / 3 else 1) * A j)
        = fun j => (if j = j₁ ∨ j = j₂ then (2 : ℝ) / 3 else 1) * A j from rfl,
        prod_two_ite_mul h12]
      nlinarith
    · rw [show (fun j => (if act j then (2 : ℝ) / 3 else 1) * A j ^ 2)
        = fun j => (if j = j₁ ∨ j = j₂ then (2 : ℝ) / 3 else 1) * A j ^ 2 from rfl,
        prod_two_ite_mul h12, Finset.prod_pow]
      nlinarith [sq_nonneg (∏ j, A j)]
  -- bijections: `q²`
  have hbij : BijGe Lu Lv (faceSum Li (fun _ _ => 1) E) (3 * ∏ j, A j) ((32 / 27) ^ 2) := by
    have key := bijGe_face (le_refl 2) Lu Lv Li hLu hLv hLi E hE0 A
      (fun j => if j = j₁ ∨ j = j₂ then 32 / 27 else 1) hA
      (fun j => by split_ifs <;> norm_num) hpos fun j => by
        by_cases hj : act j
        · simpa [show j = j₁ ∨ j = j₂ from hj] using (hPa j hj).2.1
        · simpa [show ¬ (j = j₁ ∨ j = j₂) from hj] using (hDa j hj).bijGe (hA j).le
    rwa [prod_two_ite h12, h3] at key
  -- the cap
  set N : ℝ := 3 * (∏ j, A j) * (17 / 16) with hN
  have hNpos : 0 < N := by positivity
  have hb' := hbij.rescale (g := 17 / 16) (by norm_num)
  refine cap_ball (l := 64 / 153) (Q := (32 / 27) ^ 2 / (17 / 16) ^ 3) hNpos (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one) hE0)
    (hfl.le (by rw [hN]; nlinarith)) hb'

/-- The tables of the three-mark class: the ball with gain `17/16`. -/
def P3 (S T : Finset ℕ) (Y : ℕ → ℕ → ℝ) (v : ℝ) : Prop := InBall S T Y (v * (17 / 16))

/-- The three-mark class is the mixture class of `Outerplanar/Mix.lean`. -/
theorem bmix_iff (S T : Finset ℕ) (W : ℕ → ℕ → ℝ) (N : ℝ) : BMix S T W N ↔ Mx P3 S T W N :=
  Iff.rfl

theorem cone3 : ConeP P3 where
  zero S T := by unfold P3; rw [zero_mul]; exact InBall.zero fun _ _ => le_rfl
  add := by
    intro S T Y Y' v v' hv hv' h0 h0' h h'
    have := InBall.add (by positivity) (by positivity) h0 h0' h h'
    unfold P3
    rwa [show v * (17 / 16) + v' * (17 / 16) = (v + v') * (17 / 16) by ring] at this
  smul := by
    intro S T Y v l hl hv h0 h
    have := InBall.smul hl (by positivity) h
    unfold P3
    rwa [show l * (v * (17 / 16)) = l * v * (17 / 16) by ring] at this
  mono := fun h0 hle h => InBall.mono h h0 hle
  weaken := fun hv' hle _ h => InBall.weaken (by positivity) (by linarith) h

theorem p2_p3 {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} (h : P2 S T Y v) : P3 S T Y v := h.2.2.2

theorem p1_p3 {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} (h : P1 S T Y v) : P3 S T Y v := h.2.2.2.1

/-- **A square with two sides in the one-mark class and a greedy third side is in `BMix`.** -/
theorem mx3_square_two (Lu Lv : Finset ℕ) (Li : Fin 2 → Finset ℕ) (hLu : Lu.card = 3)
    (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3) (E : Fin 3 → ℕ → ℕ → ℝ)
    (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin 3 → ℝ) (hA : ∀ j, 0 < A j) (j₁ j₂ : Fin 3)
    (h12 : j₁ ≠ j₂)
    (hK₁ : Mx P1 (pathList Lu Lv Li j₁.castSucc) (pathList Lu Lv Li j₁.succ) (E j₁) (A j₁))
    (hK₂ : Mx P1 (pathList Lu Lv Li j₂.castSucc) (pathList Lu Lv Li j₂.succ) (E j₂) (A j₂))
    (hD : ∀ j, j ≠ j₁ → j ≠ j₂ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    BMix Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 2 * ∏ j, A j) := by
  have hE : ∀ j, Mx P1 (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j) :=
    fun j => by
      by_cases h1 : j = j₁
      · subst h1; exact hK₁
      · by_cases h2 : j = j₂
        · subst h2; exact hK₂
        · exact Mx.of_dom cone1 (hA j).le (hD j h1 h2)
  obtain ⟨u, v, Y, hu, hv, huv, hY0, hY, hEY, hDv⟩ :=
    mx_data (Pc := fun _ => P1) (fun _ => cone1) hA hE (fun j => j ≠ j₁ ∧ j ≠ j₂)
      fun j hj => hD j hj.1 hj.2
  refine (bmix_iff _ _ _ _).mpr (mx_expand cone3 Lu Lv Li E hE0 A hA hu hv huv hY0 hEY
    fun ρ hρ => ?_)
  have h0 : ∀ j, j ≠ j₁ → j ≠ j₂ → ρ j = 0 := fun j h1 h2 => term_D hDv hρ j ⟨h1, h2⟩
  have hG0 := gT_nonneg hu hY0
  have hG0' : ∀ j c d, 0 ≤ gT u Y j (ρ j) c d := fun j c d => hG0 j (ρ j) c d
  have hFn := faceSum_nonneg Li (fun _ _ => 1) _ (fun _ _ _ => zero_le_one) hG0'
  have hdomj : ∀ j, ρ j = 0 → Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
      (gT u Y j (ρ j)) (wT u v j (ρ j)) := fun j hj => gT_dom _ _ j hj
  have hPj : ∀ j, ρ j ≠ 0 → P1 (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
      (gT u Y j (ρ j)) (wT u v j (ρ j)) := fun j hj => gT_P cone1 j hj (hY0 j) (hY j)
  have hw := wT_prod_pos hρ
  by_cases r1 : ρ j₁ = 0 <;> by_cases r2 : ρ j₂ = 0
  · refine (bmix_iff _ _ _ _).mp (bmix_square Lu Lv Li hLi _ hG0' _ (fun j => (hρ j).le)
      fun j => hdomj j ?_)
    by_cases h1 : j = j₁
    · rwa [h1]
    · by_cases h2 : j = j₂
      · rwa [h2]
      · exact h0 j h1 h2
  · refine Mx.of_P hw hFn (ball_one hLu hLv hLi hG0' hρ (by norm_num) (hPj j₂ r2).2.2.2.1
      fun j hj => hdomj j ?_)
    by_cases h1 : j = j₁
    · rwa [h1]
    · exact h0 j h1 hj
  · refine Mx.of_P hw hFn (ball_one hLu hLv hLi hG0' hρ (by norm_num) (hPj j₁ r1).2.2.2.1
      fun j hj => hdomj j ?_)
    by_cases h2 : j = j₂
    · rwa [h2]
    · exact h0 j hj h2
  · exact Mx.of_P hw hFn (p3_square_two Lu Lv Li hLu hLv hLi _ hG0' _ hρ h12 (hPj j₁ r1)
      (hPj j₂ r2) fun j h1 h2 => hdomj j (h0 j h1 h2))

end Outerplanar
