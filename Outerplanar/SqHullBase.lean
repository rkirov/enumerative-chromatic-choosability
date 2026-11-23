/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.HullClass
import Outerplanar.SquareCert

/-!
# A square over a branch in the hull class: index form and certificates

The square of `Outerplanar/Square.lean` (patterns `Pat` of equal colours, loaded edge `e`),
now with the hull class (`Outerplanar/HullClass.lean`) on its loaded edge. The goal is the
four-cell bound `1/2` at the root.

* `IdxHull El w A` — the hull class of an index table `w` whose equal colours are `El`, and
  `HullC.idx` from the colour form.
* `GenHull B₁ El B₂` — the four-cell bound `1/2` at the root of the index form `genF`, for every
  loaded table in the hull class; `SqHullOK P e` for a pattern. Fewer equal colours make it
  weaker (`SqHullOK.mono`).
* `pcover_of_table` — the covering table of `Outerplanar/SqData/` for any property of patterns.
* `HCase` — a certificate: a pattern code, a loaded edge, a bijection `σ₀` of the indices of the
  loaded edge (the matched family used there), the thread table `T` (root cell, family cell)
  and the floor term `F`. `genHull_of_case`: the checked conditions give `SqHullOK`. The root
  vector is affine in the hull vertex, `R = 4 ΣT + F − 2 T_i − T_j − T_k`, so each vertex is a
  few additions; the four-cell bound of a vertex follows from the products of pairs
  (`quad_bound`): `R_i² R_j² R_k R_l ≥ L ∏R / U` for `L`, `U` the least and the greatest product of
  two entries. Weighted AM–GM over the mixture finishes.

Part of the formalization of the six-even-face theorem (research note
`ai_research_notes/OUTERPLANAR_SIX_EVEN_2026-11-23.md`, the square over a branch with one
square; there checked over 4202 list configurations, here over the 52 maximal patterns of the
square cover).
-/

namespace Outerplanar

open Finset

/-! ### The index form of the hull class -/

/-- The hull class of an index table. -/
def IdxHull (El : BMat) (w : Fin 3 → Fin 3 → ℝ) (A : ℝ) : Prop :=
  (∀ σ, Compat σ El → HullV A fun k => w (offPair k).1 (σ (offPair k).2)) ∧
    ∀ c d, El c d = false → 2 / 3 * A ≤ w c d

theorem HullC.idx {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {A : ℝ} (h : HullC S T W A)
    {ζ ξ : Fin 3 → ℕ} (hζ : Function.Injective ζ) (hξ : Function.Injective ξ)
    (hζm : ∀ a, ζ a ∈ S) (hξm : ∀ b, ξ b ∈ T) :
    IdxHull (fun c d => decide (ζ c = ξ d)) (fun c d => W (ζ c) (ξ d)) A := by
  refine ⟨fun σ ⟨hσ, hc⟩ => ?_, fun c d hcd =>
    h.2 _ (hζm c) _ (hξm d) (of_decide_eq_false hcd)⟩
  have hm : Matched S T (fun k => ζ (offPair k).1) (fun k => ξ (σ (offPair k).2)) :=
    ⟨ζ, ξ ∘ σ, hζ, hξ.comp hσ, hζm, fun b => hξm _, fun a b hab => by
      obtain ⟨i, hi⟩ := offPair_surj a b hab
      exact ⟨i, by show ζ (offPair i).1 = ζ a; rw [hi],
        by show ξ (σ (offPair i).2) = ξ (σ b); rw [hi]⟩⟩
  have hne : ∀ i, ζ (offPair i).1 ≠ ξ (σ (offPair i).2) := fun i e =>
    offPair_ne i (hσ (hc _ _ (decide_eq_true e)))
  exact h.1 _ _ hm hne

theorem IdxHull.mono_el {El El' : BMat} {w : Fin 3 → Fin 3 → ℝ} {A : ℝ} (h : IdxHull El w A)
    (hle : ∀ s t, El s t = true → El' s t = true) : IdxHull El' w A :=
  ⟨fun σ ⟨hσ, hc⟩ => h.1 σ ⟨hσ, fun c d hcd => hc c d (hle c d hcd)⟩, fun c d hcd =>
    h.2 c d (Bool.eq_false_iff.mpr fun h' => by rw [hle c d h'] at hcd; exact Bool.noConfusion hcd)⟩

/-! ### The property of a pattern -/

/-- The four-cell bound `1/2` at the root, for every loaded table in the hull class. -/
def GenHull (B₁ : Fin 3 → Fin 3 → ℕ) (El : BMat) (B₂ : Fin 3 → Fin 3 → ℕ) : Prop :=
  ∀ w : Fin 3 → Fin 3 → ℝ, (∀ s t, 0 ≤ w s t) → ∀ A : ℝ, 0 < A → IdxHull El w A →
    ∀ i j k l : Fin 6, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      (1 / 2) ^ 2 * (3 * A) ^ 6 ≤ genF B₁ El B₂ w (offPair i).1 (offPair i).2 ^ 2
        * genF B₁ El B₂ w (offPair j).1 (offPair j).2 ^ 2
        * genF B₁ El B₂ w (offPair k).1 (offPair k).2
        * genF B₁ El B₂ w (offPair l).1 (offPair l).2

theorem genF_mono' {B₁ B₁' B₂ B₂' : Fin 3 → Fin 3 → ℕ} {El El' : BMat}
    {w : Fin 3 → Fin 3 → ℝ} (hw : ∀ s t, 0 ≤ w s t) (h1 : ∀ a s, B₁ a s ≤ B₁' a s)
    (h2 : ∀ t b, B₂ t b ≤ B₂' t b) (hE : ∀ s t, El' s t = true → El s t = true) (a b : Fin 3) :
    genF B₁ El B₂ w a b ≤ genF B₁' El' B₂' w a b := by
  unfold genF
  refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ => ?_
  by_cases hs : El s t = true
  · simp only [hs, ite_true]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hw _ _)) (Nat.cast_nonneg _)
  · have hs' : El' s t = false := by
      cases h' : El' s t
      · rfl
      · exact absurd (hE s t h') hs
    simp only [hs, hs', Bool.false_eq_true, ite_false]
    exact mul_le_mul (mul_le_mul_of_nonneg_right (by exact_mod_cast h1 a s) (hw _ _))
      (by exact_mod_cast h2 t b) (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (hw _ _))

theorem GenHull.mono {B₁ B₁' B₂ B₂' : Fin 3 → Fin 3 → ℕ} {El El' : BMat}
    (h : GenHull B₁ El B₂) (h1 : ∀ a s, B₁ a s ≤ B₁' a s) (h2 : ∀ t b, B₂ t b ≤ B₂' t b)
    (hE : ∀ s t, El' s t = true → El s t = true) : GenHull B₁' El' B₂' := by
  intro w hw A hA hidx i j k l hij hik hil hjk hjl hkl
  have key := h w hw A hA (hidx.mono_el hE) i j k l hij hik hil hjk hjl hkl
  have hg := genF_mono' hw h1 h2 hE
  have hn := genF_nonneg B₁ El B₂ hw
  exact key.trans (four_le (hn _ _) (hn _ _) (hn _ _) (hn _ _) (hg _ _) (hg _ _) (hg _ _)
    (hg _ _))

/-- The square with pattern `P` and loaded edge `e`. -/
def SqHullOK (P : Pat) (e : Fin 3) : Prop := GenHull (sqB₁ P e) (sqEl P e) (sqB₂ P e)

theorem SqHullOK.mono {P Q : Pat} (h : PatLE P Q) {e : Fin 3} (hQ : SqHullOK Q e) :
    SqHullOK P e := by
  unfold SqHullOK at hQ ⊢
  refine hQ.mono (fun a s => ?_) (fun t b => ?_) fun s t => ?_
  · unfold sqB₁
    by_cases h0 : e = 0
    · rw [ite_eq_left h0, ite_eq_left h0]
    · rw [ite_eq_right h0, ite_eq_right h0]
      by_cases h1 : e = 1
      · rw [ite_eq_left h1, ite_eq_left h1]
        exact nb_le (h.h01 a s)
      · rw [ite_eq_right h1, ite_eq_right h1]
        exact arc2_le h.h01 h.h12 a s
  · unfold sqB₂
    by_cases h0 : e = 0
    · rw [ite_eq_left h0, ite_eq_left h0]
      exact arc2_le h.h12 h.h23 t b
    · rw [ite_eq_right h0, ite_eq_right h0]
      by_cases h1 : e = 1
      · rw [ite_eq_left h1, ite_eq_left h1]
        exact nb_le (h.h23 t b)
      · rw [ite_eq_right h1, ite_eq_right h1]
  · unfold sqEl
    split_ifs
    · exact h.h01 s t
    · exact h.h12 s t
    · exact h.h23 s t

/-! ### The covering table for any property -/

/-- **The covering table of `Outerplanar/SqData/` for any property of patterns.** -/
theorem pcover_of_table {Good : Pat → Prop} {tbl : ℕ} {qs : List ℕ}
    (hQ : ∀ q, q < qs.length → Good (patOfCode (qs.getD q 0)))
    (htbl : ∀ kr, kr < 8 → ∀ r, r < 6 → covChunk tbl qs kr r = true)
    (d0 d1 d2 dr : Fin 3 → Bool) (ρ : Fin 3 → Fin 3) (hρ : Function.Bijective ρ)
    (hcons : NormCons d0 d1 d2 dr ρ) :
    ∃ π π₀ π₁ : Fin 3 → Fin 3, Function.Bijective π ∧ Function.Bijective π₀ ∧
      Function.Bijective π₁ ∧ ∃ Q : Pat, Good Q ∧ PatLE (normPat d0 d1 d2 dr ρ π π₀ π₁) Q := by
  obtain ⟨k0, hk0, rfl⟩ := exists_bits d0
  obtain ⟨k1, hk1, rfl⟩ := exists_bits d1
  obtain ⟨k2, hk2, rfl⟩ := exists_bits d2
  obtain ⟨kr, hkr, rfl⟩ := exists_bits dr
  obtain ⟨r, rfl⟩ := exists_perm6 ρ hρ.1
  have h := all8_lt (all8_lt (all8_lt (htbl kr hkr r.val r.isLt) hk2) hk1) hk0
  unfold covOK at h
  split_ifs at h with hodd
  · rw [not_violates hcons] at h
    cases h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hp, hp0⟩, hp1⟩, hq⟩, hle⟩ := h
    exact ⟨_, _, _, perm6_bij ⟨_, hp⟩, perm6_bij ⟨_, hp0⟩, perm6_bij ⟨_, hp1⟩, _, hQ _ hq,
      patLE_of_b hle⟩

/-! ### Certificates -/

/-- The bijections of `Fin 3`, in the order of `bperm`. -/
def sigOf (i : Fin 6) : Fin 3 → Fin 3 :=
  ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]] i

theorem sigOf_inj : ∀ i : Fin 6, ∀ a b : Fin 3, sigOf i a = sigOf i b → a = b := by decide

/-- A certified case of a square over the hull class. -/
structure HCase where
  /-- the pattern code -/
  code : ℕ
  /-- the loaded edge -/
  e : Fin 3
  /-- the bijection of the matched family on the loaded edge -/
  si : Fin 6
  /-- the thread table, `6 r + z` for the root cell `r` and the family cell `z` -/
  T : List ℕ
  /-- the floor term of the root cell `r` -/
  F : List ℕ

/-- An entry of the thread table. -/
def HCase.t (c : HCase) (r z : Fin 6) : ℕ := c.T.getD (6 * r.val + z.val) 0

/-- An entry of the floor term. -/
def HCase.f (c : HCase) (r : Fin 6) : ℕ := c.F.getD r.val 0

/-- The family is compatible with the equal colours of the loaded edge. -/
def HCase.consOK (c : HCase) : Prop :=
  ∀ s t : Fin 3, sqEl (patOfCode c.code) c.e s t = true → t = sigOf c.si s

/-- The thread table is right. -/
def HCase.tabOK (c : HCase) : Prop :=
  ∀ r z : Fin 6, c.t r z = sqB₁ (patOfCode c.code) c.e (offPair r).1 (offPair z).1 *
    sqB₂ (patOfCode c.code) c.e (sigOf c.si (offPair z).2) (offPair r).2

/-- The floor term at one index of the loaded edge. -/
def flT (P : Pat) (e : Fin 3) (σ : Fin 3 → Fin 3) (r : Fin 6) (s : Fin 3) : ℕ :=
  if sqEl P e s (σ s) = true then 0 else sqB₁ P e (offPair r).1 s * sqB₂ P e (σ s) (offPair r).2

/-- The floor term is right. -/
def HCase.flOK (c : HCase) : Prop :=
  ∀ r : Fin 6, c.f r = 2 * (flT (patOfCode c.code) c.e (sigOf c.si) r 0 +
    flT (patOfCode c.code) c.e (sigOf c.si) r 1 + flT (patOfCode c.code) c.e (sigOf c.si) r 2)

/-- The sum of a row of the thread table. -/
def HCase.row (c : HCase) (r : Fin 6) : ℕ :=
  c.t r 0 + c.t r 1 + c.t r 2 + c.t r 3 + c.t r 4 + c.t r 5

/-- The least product of two of six numbers. -/
def vL (R : Fin 6 → ℕ) : ℕ :=
  min (min (min (min (min (R 0 * R 1) (R 0 * R 2)) (min (R 0 * R 3) (R 0 * R 4))) (min (min (R 0 * R 5) (R 1 * R 2)) (min (R 1 * R 3) (R 1 * R 4)))) (min (min (R 1 * R 5) (R 2 * R 3)) (min (R 2 * R 4) (R 2 * R 5)))) (min (min (R 3 * R 4) (R 3 * R 5)) (R 4 * R 5))

/-- The greatest product of two of six numbers. -/
def vU (R : Fin 6 → ℕ) : ℕ :=
  max (max (max (max (max (R 0 * R 1) (R 0 * R 2)) (max (R 0 * R 3) (R 0 * R 4))) (max (max (R 0 * R 5) (R 1 * R 2)) (max (R 1 * R 3) (R 1 * R 4)))) (max (max (R 1 * R 5) (R 2 * R 3)) (max (R 2 * R 4) (R 2 * R 5)))) (max (max (R 3 * R 4) (R 3 * R 5)) (R 4 * R 5))

/-- The check of one vertex: `4 L ∏ ≥ 9⁶ U`. -/
def vok (R : Fin 6 → ℕ) : Bool :=
  decide (0 < vL R) && decide (531441 * vU R ≤ 4 * vL R * (R 0 * R 1 * R 2 * R 3 * R 4 * R 5))

/-- The root value at the vertex `(i, j, k)`. -/
def HCase.rv (c : HCase) (i j k r : Fin 6) : ℕ :=
  4 * c.row r + c.f r - (2 * c.t r i + c.t r j + c.t r k)

/-- The root value at the constant vertex. -/
def HCase.r3 (c : HCase) (r : Fin 6) : ℕ := 3 * c.row r + c.f r

/-- All vertices pass. -/
def HCase.vertOK (c : HCase) : Prop :=
  vok c.r3 = true ∧ ∀ i j k : Fin 6, i ≠ j → i ≠ k → j < k → vok (c.rv i j k) = true

/-! ### The vertex check -/

theorem vL_le_lt (R : Fin 6 → ℕ) : ∀ x y : Fin 6, x < y → vL R ≤ R x * R y := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;> first | exact absurd hxy (by decide) | exact (min_le_of_left_le (min_le_of_left_le (min_le_of_left_le (min_le_of_left_le (min_le_of_left_le le_rfl))))) | exact (min_le_of_left_le (min_le_of_left_le (min_le_of_left_le (min_le_of_left_le (min_le_of_right_le le_rfl))))) | exact (min_le_of_left_le (min_le_of_left_le (min_le_of_left_le (min_le_of_right_le (min_le_of_left_le le_rfl))))) | exact (min_le_of_left_le (min_le_of_left_le (min_le_of_left_le (min_le_of_right_le (min_le_of_right_le le_rfl))))) | exact (min_le_of_left_le (min_le_of_left_le (min_le_of_right_le (min_le_of_left_le (min_le_of_left_le le_rfl))))) | exact (min_le_of_left_le (min_le_of_left_le (min_le_of_right_le (min_le_of_left_le (min_le_of_right_le le_rfl))))) | exact (min_le_of_left_le (min_le_of_left_le (min_le_of_right_le (min_le_of_right_le (min_le_of_left_le le_rfl))))) | exact (min_le_of_left_le (min_le_of_left_le (min_le_of_right_le (min_le_of_right_le (min_le_of_right_le le_rfl))))) | exact (min_le_of_left_le (min_le_of_right_le (min_le_of_left_le (min_le_of_left_le le_rfl)))) | exact (min_le_of_left_le (min_le_of_right_le (min_le_of_left_le (min_le_of_right_le le_rfl)))) | exact (min_le_of_left_le (min_le_of_right_le (min_le_of_right_le (min_le_of_left_le le_rfl)))) | exact (min_le_of_left_le (min_le_of_right_le (min_le_of_right_le (min_le_of_right_le le_rfl)))) | exact (min_le_of_right_le (min_le_of_left_le (min_le_of_left_le le_rfl))) | exact (min_le_of_right_le (min_le_of_left_le (min_le_of_right_le le_rfl))) | exact (min_le_of_right_le (min_le_of_right_le le_rfl))

theorem le_vU_lt (R : Fin 6 → ℕ) : ∀ x y : Fin 6, x < y → R x * R y ≤ vU R := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;> first | exact absurd hxy (by decide) | exact (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left le_rfl))))) | exact (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_right le_rfl))))) | exact (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_right (le_max_of_le_left le_rfl))))) | exact (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_right (le_max_of_le_right le_rfl))))) | exact (le_max_of_le_left (le_max_of_le_left (le_max_of_le_right (le_max_of_le_left (le_max_of_le_left le_rfl))))) | exact (le_max_of_le_left (le_max_of_le_left (le_max_of_le_right (le_max_of_le_left (le_max_of_le_right le_rfl))))) | exact (le_max_of_le_left (le_max_of_le_left (le_max_of_le_right (le_max_of_le_right (le_max_of_le_left le_rfl))))) | exact (le_max_of_le_left (le_max_of_le_left (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right le_rfl))))) | exact (le_max_of_le_left (le_max_of_le_right (le_max_of_le_left (le_max_of_le_left le_rfl)))) | exact (le_max_of_le_left (le_max_of_le_right (le_max_of_le_left (le_max_of_le_right le_rfl)))) | exact (le_max_of_le_left (le_max_of_le_right (le_max_of_le_right (le_max_of_le_left le_rfl)))) | exact (le_max_of_le_left (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right le_rfl)))) | exact (le_max_of_le_right (le_max_of_le_left (le_max_of_le_left le_rfl))) | exact (le_max_of_le_right (le_max_of_le_left (le_max_of_le_right le_rfl))) | exact (le_max_of_le_right (le_max_of_le_right le_rfl))

theorem pair_bounds (R : Fin 6 → ℕ) {L U : ℕ}
    (hL : ∀ x y : Fin 6, x < y → L ≤ R x * R y) (hU : ∀ x y : Fin 6, x < y → R x * R y ≤ U)
    (x y : Fin 6) (hxy : x ≠ y) : L ≤ R x * R y ∧ R x * R y ≤ U := by
  rcases lt_or_gt_of_ne hxy with h | h
  · exact ⟨hL x y h, hU x y h⟩
  · rw [mul_comm]; exact ⟨hL y x h, hU y x h⟩

/-- **The four-cell bound from the products of pairs.** -/
theorem quad_bound (R : Fin 6 → ℕ) {L U : ℕ} (hL0 : 0 < L)
    (hp : ∀ x y : Fin 6, x ≠ y → L ≤ R x * R y ∧ R x * R y ≤ U)
    (hmain : 531441 * U ≤ 4 * L * ∏ z, R z) (i j k l : Fin 6) (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    531441 ≤ 4 * (R i ^ 2 * R j ^ 2 * R k * R l) := by
  set s : Finset (Fin 6) := {i, j, k, l} with hs
  have hs4 : s.card = 4 := by
    rw [hs, card_insert_of_notMem (by simp [hij, hik, hil]),
      card_insert_of_notMem (by simp [hjk, hjl]), card_pair hkl]
  have hc2 : (univ \ s).card = 2 := by
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin, hs4]
  obtain ⟨x, y, hxy, hC⟩ := card_eq_two.mp hc2
  have hprod : ∏ z, R z = (R i * R j * R k * R l) * (R x * R y) := by
    rw [← Finset.prod_sdiff (subset_univ s), hC, Finset.prod_pair hxy, mul_comm]
    congr 1
    rw [hs, prod_insert (by simp [hij, hik, hil]), prod_insert (by simp [hjk, hjl]),
      prod_pair hkl]
    ring
  have hU0 : 0 < U := lt_of_lt_of_le hL0 ((hp i j hij).1.trans (hp i j hij).2)
  have h1 : L * ∏ z, R z ≤ U * (R i ^ 2 * R j ^ 2 * R k * R l) := by
    rw [hprod]
    have e1 := (hp i j hij).1
    have e2 := (hp x y hxy).2
    calc L * ((R i * R j * R k * R l) * (R x * R y))
        = (L * (R i * R j * R k * R l)) * (R x * R y) := by ring
      _ ≤ (R i * R j * (R i * R j * R k * R l)) * U :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ e1) e2
      _ = U * (R i ^ 2 * R j ^ 2 * R k * R l) := by ring
  have h2 : 531441 * U ≤ 4 * U * (R i ^ 2 * R j ^ 2 * R k * R l) := by
    calc 531441 * U ≤ 4 * L * ∏ z, R z := hmain
      _ = 4 * (L * ∏ z, R z) := by ring
      _ ≤ 4 * (U * (R i ^ 2 * R j ^ 2 * R k * R l)) := Nat.mul_le_mul_left _ h1
      _ = 4 * U * (R i ^ 2 * R j ^ 2 * R k * R l) := by ring
  have h3 : U * 531441 ≤ U * (4 * (R i ^ 2 * R j ^ 2 * R k * R l)) := by
    calc U * 531441 = 531441 * U := mul_comm _ _
      _ ≤ _ := h2
      _ = U * (4 * (R i ^ 2 * R j ^ 2 * R k * R l)) := by ring
  exact Nat.le_of_mul_le_mul_left h3 hU0

/-- A passed vertex has the four-cell bound `9⁶ / 4`. -/
theorem vok_quad {R : Fin 6 → ℕ} (h : vok R = true) (i j k l : Fin 6) (hij : i ≠ j)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    (531441 / 4 : ℝ) ≤ (R i : ℝ) ^ 2 * (R j : ℝ) ^ 2 * (R k : ℝ) * (R l : ℝ) := by
  simp only [vok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hL0, hmain⟩ := h
  have hprod : ∏ z, R z = R 0 * R 1 * R 2 * R 3 * R 4 * R 5 := Fin.prod_univ_six R
  have key := quad_bound R hL0 (pair_bounds R (vL_le_lt R) (le_vU_lt R))
    (by rw [hprod]; exact hmain) i j k l hij hik hil hjk hjl hkl
  have : ((531441 : ℕ) : ℝ) ≤ ((4 * (R i ^ 2 * R j ^ 2 * R k * R l) : ℕ) : ℝ) := by
    exact_mod_cast key
  push_cast at this
  linarith

/-! ### From a checked case to the four-cell bound -/

/-- The nine cells of the loaded edge: the six cells of the family `σ` and the three others. -/
theorem sum_cells (si : Fin 6) (f : Fin 3 → Fin 3 → ℝ) :
    ∑ s, ∑ t, f s t
      = ∑ z : Fin 6, f (offPair z).1 (sigOf si (offPair z).2) + ∑ s, f s (sigOf si s) := by
  fin_cases si <;> simp [Fin.sum_univ_three, Fin.sum_univ_six, offPair, sigOf] <;> ring

theorem sum_vtx (g : Fin 6 → ℝ) (t : Tr) :
    ∑ z, g z * vtx t z = 4 * ∑ z, g z - 2 * g t.1 - g t.2.1 - g t.2.2 := by
  have e : ∀ z, g z * vtx t z = 4 * g z - 2 * (if z = t.1 then g z else 0)
      - (if z = t.2.1 then g z else 0) - (if z = t.2.2 then g z else 0) := fun z => by
    unfold vtx
    split_ifs <;> ring
  simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', mem_univ, ite_true]

theorem HCase.row_eq (c : HCase) (r : Fin 6) : c.row r = ∑ z, c.t r z := by
  rw [Fin.sum_univ_six]; rfl

theorem HCase.r3_cast (c : HCase) (r : Fin 6) :
    (c.r3 r : ℝ) = 3 * ∑ z, (c.t r z : ℝ) + c.f r := by
  unfold HCase.r3
  rw [c.row_eq]
  push_cast
  ring

theorem HCase.rv_cast (c : HCase) {t : Tr} (ht : t.ok) (r : Fin 6) :
    (c.rv t.1 t.2.1 t.2.2 r : ℝ) = ∑ z, (c.t r z : ℝ) * vtx t z + c.f r := by
  obtain ⟨h1, h2, h3⟩ := ht
  have hsub : c.t r t.1 + c.t r t.2.1 + c.t r t.2.2 ≤ c.row r := by
    rw [c.row_eq]
    have hs : ({t.1, t.2.1, t.2.2} : Finset (Fin 6)) ⊆ univ := subset_univ _
    have := Finset.sum_le_sum_of_subset (f := fun z => c.t r z) hs
    rwa [sum_insert (by simp [h1, h2]), sum_pair h3, ← add_assoc] at this
  have hle : 2 * c.t r t.1 + c.t r t.2.1 + c.t r t.2.2 ≤ 4 * c.row r + c.f r := by omega
  unfold HCase.rv
  rw [Nat.cast_sub hle, sum_vtx, c.row_eq]
  push_cast
  ring

theorem vtx_swap (t : Tr) : vtx (t.1, t.2.2, t.2.1) = vtx t := by
  funext z
  unfold vtx
  ring

/-- **A checked case gives the four-cell bound.** -/
theorem genHull_of_case (c : HCase) (hc : c.consOK ∧ c.tabOK ∧ c.flOK ∧ c.vertOK) :
    SqHullOK (patOfCode c.code) c.e := by
  obtain ⟨hcons, htab, hfl, hv3, hvt⟩ := hc
  intro w hw A hA hidx i j k l hij hik hil hjk hjl hkl
  obtain ⟨μ₀, μ, h0, hμ, hok, h1, hx⟩ :=
    hidx.1 (sigOf c.si) ⟨fun a b e => sigOf_inj _ a b e, fun s t h => (hcons s t h).symm⟩
  have hflo := hidx.2
  set P := patOfCode c.code with hP
  set σ := sigOf c.si with hσ
  set G : Fin 6 → ℝ := fun r => genF (sqB₁ P c.e) (sqEl P c.e) (sqB₂ P c.e) w (offPair r).1
    (offPair r).2 with hG
  -- the root value against the mixture
  have hlow : ∀ r, A * (μ₀ * (3 * ∑ z, (c.t r z : ℝ) + c.f r)
      + ∑ t, μ t * (∑ z, (c.t r z : ℝ) * vtx t z + c.f r)) ≤ 3 * G r := by
    intro r
    set D : Fin 3 → ℝ := fun s => if sqEl P c.e s (σ s) = true then 0 else
      (sqB₁ P c.e (offPair r).1 s : ℝ) * w s (σ s) * (sqB₂ P c.e (σ s) (offPair r).2 : ℝ)
      with hD
    have hfam : ∀ z : Fin 6, (if sqEl P c.e (offPair z).1 (σ (offPair z).2) = true then (0 : ℝ)
        else (sqB₁ P c.e (offPair r).1 (offPair z).1 : ℝ) * w (offPair z).1 (σ (offPair z).2)
          * (sqB₂ P c.e (σ (offPair z).2) (offPair r).2 : ℝ))
        = (c.t r z : ℝ) * w (offPair z).1 (σ (offPair z).2) := by
      intro z
      have hne : sqEl P c.e (offPair z).1 (σ (offPair z).2) = false := by
        cases h' : sqEl P c.e (offPair z).1 (σ (offPair z).2)
        · rfl
        · exact absurd (sigOf_inj _ _ _ (hcons _ _ h')).symm (offPair_ne z)
      rw [hne, htab r z]
      simp only [Bool.false_eq_true, ite_false]
      push_cast
      ring
    have hGr : G r = ∑ z, (c.t r z : ℝ) * w (offPair z).1 (σ (offPair z).2) + ∑ s, D s := by
      show genF _ _ _ _ _ _ = _
      unfold genF
      rw [sum_cells c.si]
      congr 1
      exact Finset.sum_congr rfl fun z _ => hfam z
    have hdiag : ∀ s, 2 / 3 * A * (flT P c.e σ r s : ℝ) ≤ D s := by
      intro s
      simp only [hD, flT]
      split_ifs with h
      · simp
      · push_cast
        have hw' := hflo s (σ s) (by simpa using h)
        have hb : 0 ≤ (sqB₁ P c.e (offPair r).1 s : ℝ) * (sqB₂ P c.e (σ s) (offPair r).2 : ℝ) :=
          mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        nlinarith
    have hA1 : ∑ z, (c.t r z : ℝ) * (A * (3 * μ₀ + ∑ t, μ t * vtx t z))
        ≤ 3 * ∑ z, (c.t r z : ℝ) * w (offPair z).1 (σ (offPair z).2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun z _ => ?_
      have := hx z
      have ht0 : (0 : ℝ) ≤ c.t r z := Nat.cast_nonneg _
      nlinarith
    have hA2 : A * (c.f r : ℝ) ≤ 3 * ∑ s, D s := by
      rw [hfl r, Fin.sum_univ_three]
      push_cast
      linarith [hdiag 0, hdiag 1, hdiag 2]
    have hsc : ∑ z, (c.t r z : ℝ) * (∑ t, μ t * vtx t z)
        = ∑ t, μ t * ∑ z, (c.t r z : ℝ) * vtx t z := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun z _ => by ring
    have hsplit2 : ∑ t, μ t * (∑ z, (c.t r z : ℝ) * vtx t z + c.f r)
        = ∑ t, μ t * ∑ z, (c.t r z : ℝ) * vtx t z + (∑ t, μ t) * c.f r := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => by ring
    have hexp : ∑ z, (c.t r z : ℝ) * (A * (3 * μ₀ + ∑ t, μ t * vtx t z))
        = A * (3 * μ₀ * ∑ z, (c.t r z : ℝ) + ∑ z, (c.t r z : ℝ) * (∑ t, μ t * vtx t z)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [hsplit2, hGr]
    rw [hexp, hsc] at hA1
    have hμs : ∑ t, μ t = 1 - μ₀ := by linarith
    rw [hμs]
    nlinarith [hA1, hA2]
  -- weighted AM–GM over the mixture
  set ω : Option Tr → ℝ := fun o => o.elim μ₀ μ with hω
  set val : Option Tr → Fin 6 → ℝ := fun o r => o.elim (3 * ∑ z, (c.t r z : ℝ) + c.f r)
    (fun t => ∑ z, (c.t r z : ℝ) * vtx t z + c.f r) with hval
  have hω0 : ∀ o, 0 ≤ ω o := fun o => by cases o <;> simp [hω, h0, hμ]
  have hω1 : ∑ o, ω o = 1 := by rw [Fintype.sum_option]; exact h1
  have hval0 : ∀ o r, 0 ≤ val o r := fun o r => by
    cases o
    · exact add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun z _ => Nat.cast_nonneg _))
        (Nat.cast_nonneg _)
    · exact add_nonneg (Finset.sum_nonneg fun z _ => mul_nonneg (Nat.cast_nonneg _)
        (vtx_nonneg _ _)) (Nat.cast_nonneg _)
  set g : Fin 6 → ℝ := fun r => ∏ o, val o r ^ ω o with hg
  have hg0 : ∀ r, 0 ≤ g r := fun r => Finset.prod_nonneg fun o _ => Real.rpow_nonneg (hval0 o r) _
  have hAg : ∀ r, A * g r ≤ 3 * G r := fun r => by
    have hgm := Real.geom_mean_le_arith_mean_weighted univ ω (fun o => val o r)
      (fun o _ => hω0 o) hω1 (fun o _ => hval0 o r)
    have hmix : ∑ o, ω o * val o r = μ₀ * (3 * ∑ z, (c.t r z : ℝ) + c.f r)
        + ∑ t, μ t * (∑ z, (c.t r z : ℝ) * vtx t z + c.f r) := by
      rw [Fintype.sum_option]
      rfl
    rw [hmix] at hgm
    exact (mul_le_mul_of_nonneg_left hgm hA.le).trans (hlow r)
  -- each vertex in the mixture passes
  set Y : ℝ := 531441 / 4 with hY
  have hvert : ∀ o, ω o ≠ 0 →
      Y ≤ val o i ^ 2 * val o j ^ 2 * val o k * val o l := by
    intro o ho
    cases o with
    | none =>
      have := vok_quad hv3 i j k l hij hik hil hjk hjl hkl
      simpa only [hval, Option.elim, HCase.r3_cast] using this
    | some t =>
      have htok := hok t ho
      obtain ⟨t1, t2, t3⟩ := t
      obtain ⟨h12, h13, h23⟩ := htok
      rcases lt_or_gt_of_ne h23 with hlt | hgt
      · have := vok_quad (hvt t1 t2 t3 h12 h13 hlt) i j k l hij hik hil hjk hjl hkl
        simpa only [hval, Option.elim, HCase.rv_cast c (t := (t1, t2, t3)) ⟨h12, h13, h23⟩] using this
      · have := vok_quad (hvt t1 t3 t2 h13 h12 hgt) i j k l hij hik hil hjk hjl hkl
        have e := vtx_swap (t1, t2, t3)
        simp only [HCase.rv_cast c (t := (t1, t3, t2)) ⟨h13, h12, Ne.symm h23⟩] at this
        simpa only [hval, Option.elim, show vtx (t1, t3, t2) = vtx (t1, t2, t3) from e] using this
  have hgY : Y ≤ g i ^ 2 * g j ^ 2 * g k * g l := by
    have hprod : g i ^ 2 * g j ^ 2 * g k * g l
        = ∏ o, (val o i ^ 2 * val o j ^ 2 * val o k * val o l) ^ ω o := by
      simp only [hg, ← Finset.prod_pow]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun o _ => ?_
      rw [rpow_sq_comm (hval0 _ _), rpow_sq_comm (hval0 _ _),
        Real.mul_rpow (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hval0 _ _))
          (hval0 _ _),
        Real.mul_rpow (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hval0 _ _),
        Real.mul_rpow (sq_nonneg _) (sq_nonneg _)]
    rw [hprod]
    have hY0 : (0 : ℝ) ≤ Y := by norm_num [hY]
    calc Y = Y ^ (∑ o, ω o) := by rw [hω1, Real.rpow_one]
      _ = ∏ o, Y ^ ω o := Real.rpow_sum_of_nonneg hY0 fun o _ => hω0 o
      _ ≤ _ := Finset.prod_le_prod₀ (fun o _ => Real.rpow_nonneg hY0 _) fun o _ => by
          by_cases ho : ω o = 0
          · rw [ho, Real.rpow_zero, Real.rpow_zero]
          · exact Real.rpow_le_rpow hY0 (hvert o ho) (hω0 o)
  -- assemble
  have hG0 : ∀ r, 0 ≤ A * g r := fun r => mul_nonneg hA.le (hg0 r)
  have key := four_le (hG0 i) (hG0 j) (hG0 k) (hG0 l) (hAg i) (hAg j) (hAg k) (hAg l)
  have hA6 : 0 ≤ A ^ 6 := by positivity
  have e1 : (A * g i) ^ 2 * (A * g j) ^ 2 * (A * g k) * (A * g l)
      = A ^ 6 * (g i ^ 2 * g j ^ 2 * g k * g l) := by ring
  have e2 : (3 * G i) ^ 2 * (3 * G j) ^ 2 * (3 * G k) * (3 * G l)
      = 729 * (G i ^ 2 * G j ^ 2 * G k * G l) := by ring
  rw [e1, e2] at key
  have := mul_le_mul_of_nonneg_left hgY hA6
  show (1 / 2) ^ 2 * (3 * A) ^ 6 ≤ G i ^ 2 * G j ^ 2 * G k * G l
  calc (1 / 2) ^ 2 * (3 * A) ^ 6 = A ^ 6 * Y / 729 := by rw [hY]; ring
    _ ≤ 729 * (G i ^ 2 * G j ^ 2 * G k * G l) / 729 :=
        div_le_div_of_nonneg_right (this.trans key) (by norm_num)
    _ = _ := by ring

end Outerplanar
