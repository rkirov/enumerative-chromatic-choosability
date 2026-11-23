/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.HexWalks
import Mathlib.Analysis.Convex.Birkhoff

/-!
# Transport through a face with one loaded edge: the walk-count matrix

Align the lists of a face along its path (`Outerplanar/OddBall.lean`). The colourings that use
only good pairs are walks on three indices. Let the loaded edge be step `j` of the path,
with `j` steps before it and `s` after it. The root family consists of the cells
`k ↦ (a, σ b)` with `(a, b) = offPair k`; the child family on the loaded edge consists of the
cells `z ↦ (x, y) = offPair z`. The number of walks from root cell `k` through child cell `z` is

`Cmat j s σ k z = cnt j a x · cnt s y (σ b)`.

**`exists_ds_le`**: for every bijection `σ` there is a doubly stochastic `D` with
`dd j s · D ≤ Cmat j s σ`, where `dd j s = α − [n odd]`, `n = j + 1 + s` and `α = dN n` (the
number of walks of a cycle). The base cases `j, s ≤ 1` are explicit permutations, checked by
`decide`. Each step `j → j + 2` adds `2 ^ j` times a matrix with all line sums `2 ^ (s + 1)`,
because `cnt (j + 2) = cnt j + 2 ^ j`; the step `s → s + 2` is symmetric.

This is the transport lemma of the research note
`ai_research_notes/OUTERPLANAR_SIX_EVEN_2026-11-23.md` ("Transport to one distinguished side
of a face"); there it is proved by a min-cut check of the base cases, here by explicit
permutations (`ai_research_notes/outerplanar/sixeven_lean/base_perms.py` found them).
-/

namespace Outerplanar

open Finset

/-! ### Walk counts -/

theorem cnt_add_two (k : ℕ) (a b : Fin 3) : cnt (k + 2) a b = cnt k a b + 2 ^ k := by
  have h1 := dN_add_two k
  have h2 := two_pow_eq k
  have h3 := dN_succ k
  have h4 : sN (k + 2) = 2 * dN (k + 1) := sN_succ (k + 1)
  unfold cnt
  split_ifs <;> omega

theorem cnt_symm (k : ℕ) (a b : Fin 3) : cnt k a b = cnt k b a := by
  unfold cnt
  by_cases h : a = b
  · simp [h]
  · simp [h, Ne.symm h]

theorem sum_cnt (k : ℕ) (b : Fin 3) : ∑ y : Fin 3, cnt k y b = 2 ^ k := by
  have h := two_pow_eq k
  fin_cases b <;> simp [Fin.sum_univ_three, cnt] <;> omega

theorem sum_offPair_snd (f : Fin 3 → ℝ) : ∑ z : Fin 6, f (offPair z).2 = 2 * ∑ y, f y := by
  simp [Fin.sum_univ_six, Fin.sum_univ_three, offPair]
  ring

theorem sum_offPair_fst (f : Fin 3 → ℝ) : ∑ z : Fin 6, f (offPair z).1 = 2 * ∑ y, f y := by
  simp [Fin.sum_univ_six, Fin.sum_univ_three, offPair]
  ring

theorem sum_comp_bij {σ : Fin 3 → Fin 3} (hσ : Function.Injective σ) (f : Fin 3 → ℝ) :
    ∑ b, f (σ b) = ∑ y, f y :=
  Function.Bijective.sum_comp (Finite.injective_iff_bijective.mp hσ) f

/-! ### Doubly stochastic matrices on the six cells -/

/-- Nonnegative, all row and column sums one. -/
def DS (D : Fin 6 → Fin 6 → ℝ) : Prop :=
  (∀ k z, 0 ≤ D k z) ∧ (∀ k, ∑ z, D k z = 1) ∧ ∀ z, ∑ k, D k z = 1

theorem DS.mix {D D' : Fin 6 → Fin 6 → ℝ} (h : DS D) (h' : DS D') {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : 0 < a + b) :
    DS fun k z => (a * D k z + b * D' k z) / (a + b) := by
  obtain ⟨h0, hr, hc⟩ := h
  obtain ⟨h0', hr', hc'⟩ := h'
  refine ⟨fun k z => div_nonneg (add_nonneg (mul_nonneg ha (h0 k z)) (mul_nonneg hb (h0' k z)))
    hab.le, fun k => ?_, fun z => ?_⟩
  · rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hr, hr',
      mul_one, mul_one, div_self hab.ne']
  · rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hc, hc',
      mul_one, mul_one, div_self hab.ne']

/-- The matrix of a bijection of the cells. -/
def pmat (f : Fin 6 → Fin 6) : Fin 6 → Fin 6 → ℝ := fun k z => if f k = z then 1 else 0

theorem pmat_ds {f : Fin 6 → Fin 6} (hf : Function.Injective f) : DS (pmat f) := by
  have hb := Finite.injective_iff_bijective.mp hf
  refine ⟨fun k z => by unfold pmat; split_ifs <;> norm_num, fun k => ?_, fun z => ?_⟩
  · simp [pmat]
  · have := hb.sum_comp (fun z' => if z' = z then (1 : ℝ) else 0)
    simpa [pmat] using this

theorem ds_one : DS (pmat id) := pmat_ds Function.injective_id

/-! ### The walk-count matrix -/

/-- Walks from the root cell `k` (ends `(a, σ b)`) through the child cell `z` at the loaded
step, `j` steps before it and `s` after it. -/
def Cmat (j s : ℕ) (σ : Fin 3 → Fin 3) (k z : Fin 6) : ℝ :=
  (cnt j (offPair k).1 (offPair z).1 : ℝ) * (cnt s (offPair z).2 (σ (offPair k).2) : ℝ)

theorem Cmat_nonneg (j s : ℕ) (σ : Fin 3 → Fin 3) (k z : Fin 6) : 0 ≤ Cmat j s σ k z := by
  unfold Cmat; positivity

/-- The guaranteed number of walks per cell: the cycle count, one less for an odd number of
steps. -/
noncomputable def dd (j s : ℕ) : ℝ :=
  (dN (j + s + 1) : ℝ) - if Odd (j + s + 1) then 1 else 0

theorem dN_add_two' (n : ℕ) : dN (n + 2) = dN n + 2 ^ n := by
  have h1 := dN_add_two n
  have h2 := two_pow_eq n
  have h3 := dN_succ n
  omega

theorem dd_add_two_left (j s : ℕ) : dd (j + 2) s = dd j s + 2 ^ j * 2 ^ (s + 1) := by
  unfold dd
  have e : j + 2 + s + 1 = (j + s + 1) + 2 := by omega
  rw [e, dN_add_two']
  have hp : Odd (j + s + 1 + 2) ↔ Odd (j + s + 1) := by
    constructor
    · rintro ⟨r, hr⟩; exact ⟨r - 1, by omega⟩
    · rintro ⟨r, hr⟩; exact ⟨r + 1, by omega⟩
  simp only [hp]
  push_cast
  rw [← pow_add, show j + (s + 1) = j + s + 1 by omega]
  ring

theorem dd_add_two_right (j s : ℕ) : dd j (s + 2) = dd j s + 2 ^ s * 2 ^ (j + 1) := by
  unfold dd
  have e : j + (s + 2) + 1 = (j + s + 1) + 2 := by omega
  rw [e, dN_add_two']
  have hp : Odd (j + s + 1 + 2) ↔ Odd (j + s + 1) := by
    constructor
    · rintro ⟨r, hr⟩; exact ⟨r - 1, by omega⟩
    · rintro ⟨r, hr⟩; exact ⟨r + 1, by omega⟩
  simp only [hp]
  push_cast
  rw [← pow_add, show s + (j + 1) = j + s + 1 by omega]
  ring

theorem dd_nonneg (j s : ℕ) : 0 ≤ dd j s := by
  unfold dd
  have := dN_pos (j + s)
  split_ifs
  · have : (1 : ℝ) ≤ (dN (j + s + 1) : ℝ) := by exact_mod_cast this
    linarith
  · rw [sub_zero]; positivity

/-- The increment of `j → j + 2`. -/
def Gmat (s : ℕ) (σ : Fin 3 → Fin 3) (k z : Fin 6) : ℝ :=
  (cnt s (offPair z).2 (σ (offPair k).2) : ℝ)

/-- The increment of `s → s + 2`. -/
def Hmat (j : ℕ) (k z : Fin 6) : ℝ := (cnt j (offPair k).1 (offPair z).1 : ℝ)

theorem Cmat_add_two_left (j s : ℕ) (σ : Fin 3 → Fin 3) (k z : Fin 6) :
    Cmat (j + 2) s σ k z = Cmat j s σ k z + 2 ^ j * Gmat s σ k z := by
  unfold Cmat Gmat
  rw [cnt_add_two]
  push_cast
  ring

theorem Cmat_add_two_right (j s : ℕ) (σ : Fin 3 → Fin 3) (k z : Fin 6) :
    Cmat j (s + 2) σ k z = Cmat j s σ k z + 2 ^ s * Hmat j k z := by
  unfold Cmat Hmat
  rw [cnt_add_two]
  push_cast
  ring

theorem Gmat_ds (s : ℕ) {σ : Fin 3 → Fin 3} (hσ : Function.Injective σ) :
    DS fun k z => Gmat s σ k z / 2 ^ (s + 1) := by
  have hpos : (0 : ℝ) < 2 ^ (s + 1) := by positivity
  have hsum : ∀ b : Fin 3, ∑ y : Fin 3, (cnt s y b : ℝ) = 2 ^ s := fun b => by
    exact_mod_cast sum_cnt s b
  refine ⟨fun k z => div_nonneg (by unfold Gmat; positivity) hpos.le, fun k => ?_, fun z => ?_⟩
  · rw [← Finset.sum_div, div_eq_one_iff_eq hpos.ne']
    unfold Gmat
    rw [sum_offPair_snd (fun y => (cnt s y (σ (offPair k).2) : ℝ)), hsum, pow_succ]
    ring
  · rw [← Finset.sum_div, div_eq_one_iff_eq hpos.ne']
    unfold Gmat
    have := sum_offPair_snd (fun b => (cnt s (offPair z).2 (σ b) : ℝ))
    rw [this, sum_comp_bij hσ (fun b => (cnt s (offPair z).2 b : ℝ))]
    have h2 : ∑ y : Fin 3, (cnt s (offPair z).2 y : ℝ) = 2 ^ s := by
      rw [← hsum (offPair z).2]
      exact Finset.sum_congr rfl fun y _ => by rw [cnt_symm]
    rw [h2, pow_succ]
    ring

theorem Hmat_ds (j : ℕ) : DS fun k z => Hmat j k z / 2 ^ (j + 1) := by
  have hpos : (0 : ℝ) < 2 ^ (j + 1) := by positivity
  have hsum : ∀ b : Fin 3, ∑ y : Fin 3, (cnt j y b : ℝ) = 2 ^ j := fun b => by
    exact_mod_cast sum_cnt j b
  have hsum' : ∀ a : Fin 3, ∑ y : Fin 3, (cnt j a y : ℝ) = 2 ^ j := fun a => by
    rw [← hsum a]
    exact Finset.sum_congr rfl fun y _ => by rw [cnt_symm]
  refine ⟨fun k z => div_nonneg (by unfold Hmat; positivity) hpos.le, fun k => ?_, fun z => ?_⟩
  · rw [← Finset.sum_div, div_eq_one_iff_eq hpos.ne']
    unfold Hmat
    rw [sum_offPair_fst (fun x => (cnt j (offPair k).1 x : ℝ)), hsum', pow_succ]
    ring
  · rw [← Finset.sum_div, div_eq_one_iff_eq hpos.ne']
    unfold Hmat
    rw [sum_offPair_fst (fun a => (cnt j a (offPair z).1 : ℝ)), hsum, pow_succ]
    ring

/-! ### The base cases -/

/-- Explicit permutations of the cells for the base cases: `t = 0` for `(j, s) = (0, 1)`,
`t = 1` for `(1, 0)`, `t = 2, 3` for `(1, 1)`. -/
def bperm (σ : Fin 3 → Fin 3) (t : Fin 4) : Fin 6 → Fin 6 :=
  if σ 0 = 0 ∧ σ 1 = 1 then
    ![![1, 0, 3, 2, 5, 4], ![5, 3, 4, 1, 2, 0], ![2, 4, 0, 5, 1, 3], ![3, 2, 5, 4, 0, 1]] t
  else if σ 0 = 0 ∧ σ 1 = 2 then
    ![![0, 1, 3, 2, 5, 4], ![3, 5, 4, 0, 2, 1], ![2, 3, 5, 4, 1, 0], ![5, 4, 0, 1, 3, 2]] t
  else if σ 0 = 1 ∧ σ 1 = 0 then
    ![![1, 0, 3, 2, 4, 5], ![4, 3, 5, 1, 0, 2], ![3, 2, 4, 5, 1, 0], ![5, 4, 1, 0, 2, 3]] t
  else if σ 0 = 1 ∧ σ 1 = 2 then
    ![![0, 1, 2, 3, 4, 5], ![3, 2, 5, 4, 0, 1], ![2, 3, 4, 5, 1, 0], ![4, 5, 1, 0, 3, 2]] t
  else if σ 0 = 2 ∧ σ 1 = 0 then
    ![![0, 1, 2, 3, 4, 5], ![4, 5, 1, 0, 3, 2], ![3, 2, 5, 4, 0, 1], ![5, 3, 4, 1, 2, 0]] t
  else
    ![![1, 0, 2, 3, 5, 4], ![5, 2, 1, 4, 3, 0], ![2, 3, 4, 5, 0, 1], ![4, 5, 0, 1, 2, 3]] t

/-- The integer walk counts of the base cases. -/
def cN (j s : ℕ) (σ : Fin 3 → Fin 3) (k z : Fin 6) : ℕ :=
  cnt j (offPair k).1 (offPair z).1 * cnt s (offPair z).2 (σ (offPair k).2)

set_option maxHeartbeats 1000000 in
theorem bperm_ok : ∀ σ : Fin 3 → Fin 3, (∀ a b, σ a = σ b → a = b) →
    (∀ t k k', bperm σ t k = bperm σ t k' → k = k') ∧
    (∀ k, 1 ≤ cN 0 1 σ k (bperm σ 0 k)) ∧ (∀ k, 1 ≤ cN 1 0 σ k (bperm σ 1 k)) ∧
    (∀ k, bperm σ 2 k ≠ bperm σ 3 k ∧ 1 ≤ cN 1 1 σ k (bperm σ 2 k) ∧
      1 ≤ cN 1 1 σ k (bperm σ 3 k)) := by
  decide +kernel

theorem Cmat_eq_cN (j s : ℕ) (σ : Fin 3 → Fin 3) (k z : Fin 6) :
    Cmat j s σ k z = (cN j s σ k z : ℝ) := by
  unfold Cmat cN
  push_cast
  ring

theorem le_Cmat_of_perm {j s : ℕ} {σ : Fin 3 → Fin 3} {f : Fin 6 → Fin 6}
    (hf : ∀ k, 1 ≤ cN j s σ k (f k)) (k z : Fin 6) : pmat f k z ≤ Cmat j s σ k z := by
  rw [Cmat_eq_cN]
  unfold pmat
  split_ifs with h
  · rw [← h]
    exact_mod_cast hf k
  · positivity

theorem exists_ds_base (j s : ℕ) (hj : j < 2) (hs : s < 2) {σ : Fin 3 → Fin 3}
    (hσ : Function.Injective σ) :
    ∃ D, DS D ∧ ∀ k z, dd j s * D k z ≤ Cmat j s σ k z := by
  obtain ⟨hinj, h01, h10, h11⟩ := bperm_ok σ fun a b e => hσ e
  have hd : ∀ t, DS (pmat (bperm σ t)) := fun t => pmat_ds fun k k' e => hinj t k k' e
  interval_cases j <;> interval_cases s
  · -- one step: no guaranteed walk
    refine ⟨pmat id, ds_one, fun k z => ?_⟩
    have : dd 0 0 = 0 := by norm_num [dd, dN_succ, dN_zero, sN_zero]
    rw [this, zero_mul]
    exact Cmat_nonneg _ _ _ _ _
  · refine ⟨pmat (bperm σ 0), hd 0, fun k z => ?_⟩
    have : dd 0 1 = 1 := by
      norm_num [dd, dN_succ, sN_succ, dN_zero, sN_zero]
    rw [this, one_mul]
    exact le_Cmat_of_perm h01 k z
  · refine ⟨pmat (bperm σ 1), hd 1, fun k z => ?_⟩
    have : dd 1 0 = 1 := by
      norm_num [dd, dN_succ, sN_succ, dN_zero, sN_zero]
    rw [this, one_mul]
    exact le_Cmat_of_perm h10 k z
  · refine ⟨fun k z => (1 * pmat (bperm σ 2) k z + 1 * pmat (bperm σ 3) k z) / (1 + 1),
      (hd 2).mix (hd 3) zero_le_one zero_le_one (by norm_num), fun k z => ?_⟩
    have : dd 1 1 = 2 := by
      have h3 : Odd (1 + 1 + 1) := ⟨1, rfl⟩
      simp only [dd, h3, ite_true]
      norm_num [dN_succ, sN_succ, dN_zero, sN_zero]
    rw [this, Cmat_eq_cN]
    obtain ⟨hne, h2, h3⟩ := h11 k
    unfold pmat
    by_cases e2 : bperm σ 2 k = z <;> by_cases e3 : bperm σ 3 k = z
    · exact absurd (e2.trans e3.symm) hne
    · simp only [e2, e3, ite_true, ite_false]
      rw [← e2]; norm_num; exact_mod_cast h2
    · simp only [e2, e3, ite_true, ite_false]
      rw [← e3]; norm_num; exact_mod_cast h3
    · simp only [e2, e3, ite_false]; norm_num

/-! ### The transport lemma -/

theorem exists_ds_le_j (s : ℕ) (hs : s < 2) {σ : Fin 3 → Fin 3} (hσ : Function.Injective σ) :
    ∀ j, ∃ D, DS D ∧ ∀ k z, dd j s * D k z ≤ Cmat j s σ k z
  | 0 => exists_ds_base 0 s (by norm_num) hs hσ
  | 1 => exists_ds_base 1 s (by norm_num) hs hσ
  | j + 2 => by
    obtain ⟨D, hD, hle⟩ := exists_ds_le_j s hs hσ j
    have hc : (0 : ℝ) < 2 ^ j * 2 ^ (s + 1) := by positivity
    refine ⟨fun k z => (dd j s * D k z + 2 ^ j * 2 ^ (s + 1) * (Gmat s σ k z / 2 ^ (s + 1)))
      / (dd j s + 2 ^ j * 2 ^ (s + 1)),
      hD.mix (Gmat_ds s hσ) (dd_nonneg j s) hc.le (by linarith [dd_nonneg j s]), fun k z => ?_⟩
    rw [dd_add_two_left, mul_div_cancel₀ _ (by linarith [dd_nonneg j s] : dd j s + 2 ^ j * 2 ^ (s + 1) ≠ 0),
      Cmat_add_two_left]
    have h2 : (2 : ℝ) ^ j * 2 ^ (s + 1) * (Gmat s σ k z / 2 ^ (s + 1)) = 2 ^ j * Gmat s σ k z := by
      field_simp
    rw [h2]
    linarith [hle k z]

/-- **The transport lemma.** -/
theorem exists_ds_le {σ : Fin 3 → Fin 3} (hσ : Function.Injective σ) :
    ∀ j s, ∃ D, DS D ∧ ∀ k z, dd j s * D k z ≤ Cmat j s σ k z
  | j, 0 => exists_ds_le_j 0 (by norm_num) hσ j
  | j, 1 => exists_ds_le_j 1 (by norm_num) hσ j
  | j, s + 2 => by
    obtain ⟨D, hD, hle⟩ := exists_ds_le hσ j s
    have hc : (0 : ℝ) < 2 ^ s * 2 ^ (j + 1) := by positivity
    refine ⟨fun k z => (dd j s * D k z + 2 ^ s * 2 ^ (j + 1) * (Hmat j k z / 2 ^ (j + 1)))
      / (dd j s + 2 ^ s * 2 ^ (j + 1)),
      hD.mix (Hmat_ds j) (dd_nonneg j s) hc.le (by linarith [dd_nonneg j s]), fun k z => ?_⟩
    rw [dd_add_two_right, mul_div_cancel₀ _ (by linarith [dd_nonneg j s] : dd j s + 2 ^ s * 2 ^ (j + 1) ≠ 0),
      Cmat_add_two_right]
    have h2 : (2 : ℝ) ^ s * 2 ^ (j + 1) * (Hmat j k z / 2 ^ (j + 1)) = 2 ^ s * Hmat j k z := by
      field_simp
    rw [h2]
    linarith [hle k z]

/-! ### Mixing by a doubly stochastic matrix (Birkhoff) -/

theorem rpow_sq_comm {x : ℝ} (hx : 0 ≤ x) (w : ℝ) : (x ^ w) ^ 2 = (x ^ 2) ^ w := by
  have h1 : (x ^ w) ^ 2 = (x ^ w) ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast _ 2).symm
  have h2 : x ^ 2 = x ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast _ 2).symm
  rw [h1, h2, ← Real.rpow_mul hx, ← Real.rpow_mul hx, mul_comm]

/-- A doubly stochastic matrix is a convex combination of permutations. -/
theorem DS.exists_perms {D : Fin 6 → Fin 6 → ℝ} (hD : DS D) :
    ∃ (s : Finset (Equiv.Perm (Fin 6))) (w : Equiv.Perm (Fin 6) → ℝ), (∀ σ ∈ s, 0 ≤ w σ) ∧
      ∑ σ ∈ s, w σ = 1 ∧ ∀ (k : Fin 6) (M : Fin 6 → ℝ),
        ∑ z, D k z * M z = ∑ σ ∈ s, w σ * M (σ k) := by
  have hmem : Matrix.of D ∈ doublyStochastic ℝ (Fin 6) :=
    mem_doublyStochastic_iff_sum.mpr hD
  have hmem' : Matrix.of D ∈ convexHull ℝ {x | ∃ σ : Equiv.Perm (Fin 6), σ.permMatrix ℝ = x} := by
    rw [← doublyStochastic_eq_convexHull_permMatrix]
    exact hmem
  have hr : {x | ∃ σ : Equiv.Perm (Fin 6), σ.permMatrix ℝ = x}
      = Set.range fun σ : Equiv.Perm (Fin 6) => σ.permMatrix ℝ := rfl
  rw [hr, convexHull_range_eq_exists_affineCombination] at hmem'
  obtain ⟨s, w, hw0, hw1, hcomb⟩ := hmem'
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw1] at hcomb
  refine ⟨s, w, hw0, hw1, fun k M => ?_⟩
  have hentry : ∀ z, D k z = ∑ σ ∈ s, w σ * (σ.permMatrix ℝ) k z := by
    intro z
    have := congrFun (congrFun hcomb k) z
    rw [Matrix.of_apply] at this
    rw [← this, Matrix.sum_apply]
    exact Finset.sum_congr rfl fun σ _ => by rw [Matrix.smul_apply, smul_eq_mul]
  simp_rw [hentry, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp [Pi.single_apply]

/-- **Mixing preserves the four-cell bound.** If `p ≥ c · D M` with `D` doubly stochastic and
every four distinct cells of `M` have `M_i² M_j² M_k M_l ≥ Y`, then the same holds for `p`
with `c⁶ Y`. -/
theorem four_mix {M : Fin 6 → ℝ} (hM : ∀ z, 0 ≤ M z) {Y : ℝ} (hY : 0 ≤ Y)
    (hT : ∀ i j k l : Fin 6, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      Y ≤ M i ^ 2 * M j ^ 2 * M k * M l)
    {D : Fin 6 → Fin 6 → ℝ} (hD : DS D) {c : ℝ} (hc : 0 ≤ c) {p : Fin 6 → ℝ}
    (hp : ∀ k, c * ∑ z, D k z * M z ≤ p k) :
    ∀ i j k l : Fin 6, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      c ^ 6 * Y ≤ p i ^ 2 * p j ^ 2 * p k * p l := by
  intro i j k l hij hik hil hjk hjl hkl
  obtain ⟨s, w, hw0, hw1, hsum⟩ := hD.exists_perms
  set g : Fin 6 → ℝ := fun k => ∏ σ ∈ s, M (σ k) ^ w σ with hg
  have hg0 : ∀ k, 0 ≤ g k := fun k => Finset.prod_nonneg fun σ _ =>
    Real.rpow_nonneg (hM _) _
  have hpg : ∀ k, c * g k ≤ p k := fun k => by
    refine le_trans ?_ (hp k)
    rw [hsum k M]
    exact mul_le_mul_of_nonneg_left (Real.geom_mean_le_arith_mean_weighted s w (fun σ => M (σ k))
      hw0 hw1 fun σ _ => hM _) hc
  have hprod : g i ^ 2 * g j ^ 2 * g k * g l
      = ∏ σ ∈ s, (M (σ i) ^ 2 * M (σ j) ^ 2 * M (σ k) * M (σ l)) ^ w σ := by
    simp only [hg, ← Finset.prod_pow]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun σ _ => ?_
    rw [rpow_sq_comm (hM _), rpow_sq_comm (hM _),
      Real.mul_rpow (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hM _)) (hM _),
      Real.mul_rpow (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hM _),
      Real.mul_rpow (sq_nonneg _) (sq_nonneg _)]
  have hgY : Y ≤ g i ^ 2 * g j ^ 2 * g k * g l := by
    rw [hprod]
    calc Y = Y ^ (∑ σ ∈ s, w σ) := by rw [hw1, Real.rpow_one]
      _ = ∏ σ ∈ s, Y ^ w σ := Real.rpow_sum_of_nonneg hY hw0
      _ ≤ _ := Finset.prod_le_prod₀ (fun σ _ => Real.rpow_nonneg hY _) fun σ hσ =>
          Real.rpow_le_rpow hY (hT _ _ _ _ (fun e => hij (σ.injective e))
            (fun e => hik (σ.injective e)) (fun e => hil (σ.injective e))
            (fun e => hjk (σ.injective e)) (fun e => hjl (σ.injective e))
            (fun e => hkl (σ.injective e))) (hw0 σ hσ)
  calc c ^ 6 * Y ≤ c ^ 6 * (g i ^ 2 * g j ^ 2 * g k * g l) :=
        mul_le_mul_of_nonneg_left hgY (by positivity)
    _ = (c * g i) ^ 2 * (c * g j) ^ 2 * (c * g k) * (c * g l) := by ring
    _ ≤ _ := four_le (mul_nonneg hc (hg0 i)) (mul_nonneg hc (hg0 j)) (mul_nonneg hc (hg0 k))
        (mul_nonneg hc (hg0 l)) (hpg i) (hpg j) (hpg k) (hpg l)

/-! ### The walks through one loaded step -/

/-- Splitting the walks at one step: the other steps are bounded by their smallest entries. -/
theorem pw_split_ge (L₁ L₂ : List (Fin 3 → Fin 3 → ℝ)) (h₁ : ∀ M ∈ L₁, ∀ a b, 0 ≤ M a b)
    (h₂ : ∀ M ∈ L₂, ∀ a b, 0 ≤ M a b) (M : Fin 3 → Fin 3 → ℝ) (hM : ∀ a b, 0 ≤ M a b)
    (a b : Fin 3) :
    mnP L₁ * mnP L₂ * ∑ z : Fin 6, (cnt L₁.length a (offPair z).1 : ℝ)
        * (cnt L₂.length (offPair z).2 b : ℝ) * M (offPair z).1 (offPair z).2
      ≤ pw (L₁ ++ M :: L₂) a b := by
  rw [pw_append]
  simp only [pw]
  have g1 := pw_ge L₁ h₁
  have g2 := pw_ge L₂ h₂
  have m1 := mnP_nonneg L₁ h₁
  have m2 := mnP_nonneg L₂ h₂
  have q2 : ∀ y, (cnt L₂.length y b : ℝ) * mnP L₂ ≤ pw L₂ y b := fun y => g2 y b
  have q1 : ∀ x, (cnt L₁.length a x : ℝ) * mnP L₁ ≤ pw L₁ a x := fun x => g1 a x
  have c0 : ∀ k : ℕ, ∀ x y : Fin 3, (0 : ℝ) ≤ (cnt k x y : ℝ) := fun _ _ _ => Nat.cast_nonneg _
  have inner : ∀ x : Fin 3, (cnt L₁.length a x : ℝ) * mnP L₁ *
      (M x (x + 1) * ((cnt L₂.length (x + 1) b : ℝ) * mnP L₂)
        + M x (x + 2) * ((cnt L₂.length (x + 2) b : ℝ) * mnP L₂))
      ≤ pw L₁ a x * (M x (x + 1) * pw L₂ (x + 1) b + M x (x + 2) * pw L₂ (x + 2) b) := by
    intro x
    refine mul_le_mul (q1 x) (add_le_add (mul_le_mul_of_nonneg_left (q2 _) (hM _ _))
      (mul_le_mul_of_nonneg_left (q2 _) (hM _ _)))
      (add_nonneg (mul_nonneg (hM _ _) (mul_nonneg (c0 _ _ _) m2))
        (mul_nonneg (hM _ _) (mul_nonneg (c0 _ _ _) m2)))
      ((mul_nonneg (c0 _ _ _) m1).trans (q1 x))
  have e : mnP L₁ * mnP L₂ * ∑ z : Fin 6, (cnt L₁.length a (offPair z).1 : ℝ)
        * (cnt L₂.length (offPair z).2 b : ℝ) * M (offPair z).1 (offPair z).2
      = ∑ x : Fin 3, (cnt L₁.length a x : ℝ) * mnP L₁ *
        (M x (x + 1) * ((cnt L₂.length (x + 1) b : ℝ) * mnP L₂)
          + M x (x + 2) * ((cnt L₂.length (x + 2) b : ℝ) * mnP L₂)) := by
    simp only [Fin.sum_univ_six, Fin.sum_univ_three, offPair]
    simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
    have e1 : (0 : Fin 3) + 1 = 1 := rfl
    have e2 : (0 : Fin 3) + 2 = 2 := rfl
    have e3 : (1 : Fin 3) + 1 = 2 := rfl
    have e4 : (1 : Fin 3) + 2 = 0 := rfl
    have e5 : (2 : Fin 3) + 1 = 0 := rfl
    have e6 : (2 : Fin 3) + 2 = 1 := rfl
    rw [e1, e2, e3, e4, e5, e6]
    ring
  rw [e]
  calc _ ≤ ∑ x : Fin 3, pw L₁ a x * (M x (x + 1) * pw L₂ (x + 1) b
          + M x (x + 2) * pw L₂ (x + 2) b) := Finset.sum_le_sum fun x _ => inner x
    _ = _ := by rw [Fin.sum_univ_three]

/-- **Transport of the four-cell bound through one loaded step**, at the level of indices:
`j = L₁.length` steps before the loaded table `M`, `s = L₂.length` after it, tables with
entries at least `A₁`, `A₂` in total elsewhere. -/
theorem walks_tb_transport (L₁ L₂ : List (Fin 3 → Fin 3 → ℝ)) (h₁ : ∀ M ∈ L₁, ∀ a b, 0 ≤ M a b)
    (h₂ : ∀ M ∈ L₂, ∀ a b, 0 ≤ M a b) (M : Fin 3 → Fin 3 → ℝ) (hM : ∀ a b, 0 ≤ M a b)
    {A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hm₁ : A₁ ≤ mnP L₁) (hm₂ : A₂ ≤ mnP L₂)
    {Y : ℝ} (hY : 0 ≤ Y)
    (hT : ∀ i j k l : Fin 6, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      Y ≤ M (offPair i).1 (offPair i).2 ^ 2 * M (offPair j).1 (offPair j).2 ^ 2
        * M (offPair k).1 (offPair k).2 * M (offPair l).1 (offPair l).2)
    {σ : Fin 3 → Fin 3} (hσ : Function.Injective σ) :
    ∀ i j k l : Fin 6, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      (A₁ * A₂ * dd L₁.length L₂.length) ^ 6 * Y ≤
        pw (L₁ ++ M :: L₂) (offPair i).1 (σ (offPair i).2) ^ 2
          * pw (L₁ ++ M :: L₂) (offPair j).1 (σ (offPair j).2) ^ 2
          * pw (L₁ ++ M :: L₂) (offPair k).1 (σ (offPair k).2)
          * pw (L₁ ++ M :: L₂) (offPair l).1 (σ (offPair l).2) := by
  obtain ⟨D, hD, hle⟩ := exists_ds_le hσ L₁.length L₂.length
  set Mv : Fin 6 → ℝ := fun z => M (offPair z).1 (offPair z).2 with hMv
  refine four_mix (M := Mv) (fun z => hM _ _) hY hT hD
    (mul_nonneg (mul_nonneg hA₁ hA₂) (dd_nonneg _ _)) fun k => ?_
  have hsplit := pw_split_ge L₁ L₂ h₁ h₂ M hM (offPair k).1 (σ (offPair k).2)
  have hD0 := hD.1
  calc A₁ * A₂ * dd L₁.length L₂.length * ∑ z, D k z * Mv z
      = A₁ * A₂ * ∑ z, (dd L₁.length L₂.length * D k z) * Mv z := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
    _ ≤ A₁ * A₂ * ∑ z, Cmat L₁.length L₂.length σ k z * Mv z :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ =>
          mul_le_mul_of_nonneg_right (hle k z) (hM _ _)) (mul_nonneg hA₁ hA₂)
    _ ≤ mnP L₁ * mnP L₂ * ∑ z, Cmat L₁.length L₂.length σ k z * Mv z :=
        mul_le_mul_of_nonneg_right (mul_le_mul hm₁ hm₂ hA₂ (hA₁.trans hm₁))
          (Finset.sum_nonneg fun z _ => mul_nonneg (Cmat_nonneg _ _ _ _ _) (hM _ _))
    _ = mnP L₁ * mnP L₂ * ∑ z : Fin 6, (cnt L₁.length (offPair k).1 (offPair z).1 : ℝ)
        * (cnt L₂.length (offPair z).2 (σ (offPair k).2) : ℝ)
        * M (offPair z).1 (offPair z).2 := by
        rfl
    _ ≤ _ := hsplit

end Outerplanar
