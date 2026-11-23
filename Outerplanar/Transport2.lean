/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Transport2Cert
import Outerplanar.TransportFace

/-!
# Transport of the four-cell bound through two loaded steps

The index form of the four-cell bound at a face of odd length with **two** loaded path edges,
the other path edges greedy. The research note
`ai_research_notes/OUTERPLANAR_SIX_EVEN_2026-11-23.md` proves `T ≥ (3/4)² (8/9)` here with
balanced walk designs and an entropy estimate for a rotation monodromy. This file proves the
lossless bound `T ≥ τ₁ τ₂` instead (Claude, 2026-11-23): only the two loaded steps need to be
balanced, and then designs without entropy loss exist for every monodromy.

* `BD D` — a *bi-design*: for each root cell `k` a probability law `D k` on pairs of cells (the
  cells used at the two loaded steps) whose two marginal matrices are doubly stochastic.
* `C2N j g s σ k z w` — the walks from the root cell `k` (ends `(a, σ b)`) through the cell `z`
  at the first loaded step and `w` at the second, with `j`, `g`, `s` steps before, between and
  after them.
* `exists_bd_le` — for `j + g + s` even and at least two there is a bi-design `D` with
  `α D ≤ C2N`, `α = dN (j + g + s + 2)` the number of walks between different indices. The base
  cases `j + g + s = 2` are the kernel-checked certificates of `Outerplanar/Transport2Cert.lean`;
  each step `+2` of a segment adds an exactly balanced increment, as `cnt (k + 2) = cnt k + 2ᵏ`.
* `two_mix` — weighted AM–GM with the law `D k`, and Birkhoff on each marginal (in logarithms).
* `walks_tb_transport2` — the index form: constant `(α A₁ A₂ A₃)⁶ Y₁ Y₂`.
-/

namespace Outerplanar

open Finset

/-! ### Bi-designs -/

/-- For each root cell a law on pairs of cells, with doubly stochastic marginals. -/
def BD (D : Fin 6 → Fin 6 → Fin 6 → ℝ) : Prop :=
  (∀ k z w, 0 ≤ D k z w) ∧ (∀ k, ∑ z, ∑ w, D k z w = 1) ∧
    (∀ z, ∑ k, ∑ w, D k z w = 1) ∧ ∀ w, ∑ k, ∑ z, D k z w = 1

theorem sum2_mix {a b : ℝ} (hab : 0 < a + b) {f f' : Fin 6 → Fin 6 → ℝ}
    (hf : ∑ x, ∑ y, f x y = 1) (hf' : ∑ x, ∑ y, f' x y = 1) :
    ∑ x, ∑ y, (a * f x y + b * f' x y) / (a + b) = 1 := by
  have e : ∑ x, ∑ y, (a * f x y + b * f' x y) / (a + b)
      = (a * ∑ x, ∑ y, f x y + b * ∑ x, ∑ y, f' x y) / (a + b) := by
    simp only [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [e, hf, hf', mul_one, mul_one, div_self hab.ne']

theorem BD.mix {D D' : Fin 6 → Fin 6 → Fin 6 → ℝ} (h : BD D) (h' : BD D') {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
    BD fun k z w => (a * D k z w + b * D' k z w) / (a + b) :=
  ⟨fun k z w => div_nonneg (add_nonneg (mul_nonneg ha (h.1 k z w)) (mul_nonneg hb (h'.1 k z w)))
      hab.le,
    fun k => sum2_mix hab (h.2.1 k) (h'.2.1 k),
    fun z => sum2_mix (f := fun k w => D k z w) (f' := fun k w => D' k z w) hab (h.2.2.1 z)
      (h'.2.2.1 z),
    fun w => sum2_mix (f := fun k z => D k z w) (f' := fun k z => D' k z w) hab (h.2.2.2 w)
      (h'.2.2.2 w)⟩

theorem BD.ds₁ {D : Fin 6 → Fin 6 → Fin 6 → ℝ} (h : BD D) : DS fun k z => ∑ w, D k z w :=
  ⟨fun k z => Finset.sum_nonneg fun w _ => h.1 k z w, h.2.1, h.2.2.1⟩

theorem BD.ds₂ {D : Fin 6 → Fin 6 → Fin 6 → ℝ} (h : BD D) : DS fun k w => ∑ z, D k z w :=
  ⟨fun k w => Finset.sum_nonneg fun z _ => h.1 k z w,
    fun k => by rw [Finset.sum_comm]; exact h.2.1 k, h.2.2.2⟩

/-- The bi-design of a pair of bijections. -/
def ppmat (f g : Fin 6 → Fin 6) (k z w : Fin 6) : ℝ := pmat f k z * pmat g k w

theorem sum_pmat_row (f : Fin 6 → Fin 6) (k : Fin 6) : ∑ z, pmat f k z = 1 := by
  simp [pmat]

theorem ppmat_bd {f g : Fin 6 → Fin 6} (hf : Function.Injective f)
    (hg : Function.Injective g) : BD (ppmat f g) := by
  have hf' := pmat_ds hf
  have hg' := pmat_ds hg
  refine ⟨fun k z w => mul_nonneg (hf'.1 k z) (hg'.1 k w), fun k => ?_, fun z => ?_,
    fun w => ?_⟩
  · simp only [ppmat, ← Finset.mul_sum, sum_pmat_row, mul_one]
  · simp only [ppmat, ← Finset.mul_sum, sum_pmat_row, mul_one]
    exact hf'.2.2 z
  · simp only [ppmat, ← Finset.sum_mul, sum_pmat_row, one_mul]
    exact hg'.2.2 w

theorem BD.avg5 {Ds : Fin 5 → Fin 6 → Fin 6 → Fin 6 → ℝ} (h : ∀ t, BD (Ds t)) :
    BD fun k z w => (∑ t, Ds t k z w) / 5 := by
  have e : ∀ F : Fin 5 → Fin 6 → Fin 6 → ℝ, (∀ t, ∑ x, ∑ y, F t x y = 1) →
      ∑ x, ∑ y, (∑ t, F t x y) / 5 = 1 := by
    intro F hF
    rw [show ∑ x, ∑ y, (∑ t, F t x y) / 5 = (∑ x, ∑ y, ∑ t, F t x y) / 5 by
      simp only [← Finset.sum_div]]
    rw [show ∑ x, ∑ y, ∑ t, F t x y = ∑ t, ∑ x, ∑ y, F t x y from
      (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans Finset.sum_comm]
    simp only [hF, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    norm_num
  exact ⟨fun k z w => div_nonneg (Finset.sum_nonneg fun t _ => (h t).1 k z w) (by norm_num),
    fun k => e (fun t => Ds t k) fun t => (h t).2.1 k,
    fun z => e (fun t k w => Ds t k z w) fun t => (h t).2.2.1 z,
    fun w => e (fun t k z => Ds t k z w) fun t => (h t).2.2.2 w⟩

/-! ### Walk counts and their increments -/

/-- The increment of `j → j + 2`. -/
def I1N (g s : ℕ) (σ : Fin 3 → Fin 3) (k z w : Fin 6) : ℕ :=
  cnt g (offPair z).2 (offPair w).1 * cnt s (offPair w).2 (σ (offPair k).2)

/-- The increment of `g → g + 2`. -/
def I2N (j s : ℕ) (σ : Fin 3 → Fin 3) (k z w : Fin 6) : ℕ :=
  cnt j (offPair k).1 (offPair z).1 * cnt s (offPair w).2 (σ (offPair k).2)

/-- The increment of `s → s + 2`. -/
def I3N (j g : ℕ) (k z w : Fin 6) : ℕ :=
  cnt j (offPair k).1 (offPair z).1 * cnt g (offPair z).2 (offPair w).1

theorem C2N_add_two_j (j g s : ℕ) (σ : Fin 3 → Fin 3) (k z w : Fin 6) :
    C2N (j + 2) g s σ k z w = C2N j g s σ k z w + 2 ^ j * I1N g s σ k z w := by
  unfold C2N I1N
  rw [cnt_add_two]
  ring

theorem C2N_add_two_g (j g s : ℕ) (σ : Fin 3 → Fin 3) (k z w : Fin 6) :
    C2N j (g + 2) s σ k z w = C2N j g s σ k z w + 2 ^ g * I2N j s σ k z w := by
  unfold C2N I2N
  rw [cnt_add_two]
  ring

theorem C2N_add_two_s (j g s : ℕ) (σ : Fin 3 → Fin 3) (k z w : Fin 6) :
    C2N j g (s + 2) σ k z w = C2N j g s σ k z w + 2 ^ s * I3N j g k z w := by
  unfold C2N I3N
  rw [cnt_add_two]
  ring

theorem sum_cnt_left (k : ℕ) (b : Fin 3) : ∑ y : Fin 3, (cnt k y b : ℝ) = 2 ^ k := by
  exact_mod_cast sum_cnt k b

theorem sum_cnt_right (k : ℕ) (a : Fin 3) : ∑ y : Fin 3, (cnt k a y : ℝ) = 2 ^ k := by
  rw [← sum_cnt_left k a]
  exact Finset.sum_congr rfl fun y _ => by rw [cnt_symm]

theorem sum_cell_fst_left (k : ℕ) (b : Fin 3) :
    ∑ z : Fin 6, (cnt k (offPair z).1 b : ℝ) = 2 * 2 ^ k := by
  rw [sum_offPair_fst (fun x => (cnt k x b : ℝ)), sum_cnt_left]

theorem sum_cell_snd_left (k : ℕ) (b : Fin 3) :
    ∑ z : Fin 6, (cnt k (offPair z).2 b : ℝ) = 2 * 2 ^ k := by
  rw [sum_offPair_snd (fun x => (cnt k x b : ℝ)), sum_cnt_left]

theorem sum_cell_fst_right (k : ℕ) (a : Fin 3) :
    ∑ z : Fin 6, (cnt k a (offPair z).1 : ℝ) = 2 * 2 ^ k := by
  rw [sum_offPair_fst (fun x => (cnt k a x : ℝ)), sum_cnt_right]

theorem sum_cell_snd_right (k : ℕ) (a : Fin 3) :
    ∑ z : Fin 6, (cnt k a (offPair z).2 : ℝ) = 2 * 2 ^ k := by
  rw [sum_offPair_snd (fun x => (cnt k a x : ℝ)), sum_cnt_right]

theorem sum_root_snd (s : ℕ) (y : Fin 3) {σ : Fin 3 → Fin 3} (hσ : Function.Injective σ) :
    ∑ k : Fin 6, (cnt s y (σ (offPair k).2) : ℝ) = 2 * 2 ^ s := by
  rw [sum_offPair_snd (fun b => (cnt s y (σ b) : ℝ)),
    sum_comp_bij hσ (fun b => (cnt s y b : ℝ)), sum_cnt_right]

theorem I1_bd (g s : ℕ) {σ : Fin 3 → Fin 3} (hσ : Function.Injective σ) :
    BD fun k z w => (I1N g s σ k z w : ℝ) / 2 ^ (g + s + 2) := by
  have hpos : (0 : ℝ) < 2 ^ (g + s + 2) := by positivity
  have hc : (2 : ℝ) ^ (g + s + 2) = 2 * 2 ^ g * (2 * 2 ^ s) := by ring
  have e : ∀ k z w, (I1N g s σ k z w : ℝ)
      = (cnt g (offPair z).2 (offPair w).1 : ℝ) * (cnt s (offPair w).2 (σ (offPair k).2) : ℝ) :=
    fun _ _ _ => by unfold I1N; push_cast; ring
  refine ⟨fun k z w => div_nonneg (Nat.cast_nonneg _) hpos.le, fun k => ?_, fun z => ?_,
    fun w => ?_⟩ <;> simp only [← Finset.sum_div, e] <;>
    rw [div_eq_one_iff_eq hpos.ne', hc]
  · rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, sum_cell_snd_left, ← Finset.mul_sum]
  · rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, sum_root_snd _ _ hσ, ← Finset.sum_mul, sum_cell_fst_right]
  · simp only [← Finset.sum_mul, sum_cell_snd_left, ← Finset.mul_sum, sum_root_snd _ _ hσ]

theorem I2_bd (j s : ℕ) {σ : Fin 3 → Fin 3} (hσ : Function.Injective σ) :
    BD fun k z w => (I2N j s σ k z w : ℝ) / 2 ^ (j + s + 2) := by
  have hpos : (0 : ℝ) < 2 ^ (j + s + 2) := by positivity
  have hc : (2 : ℝ) ^ (j + s + 2) = 2 * 2 ^ j * (2 * 2 ^ s) := by ring
  have e : ∀ k z w, (I2N j s σ k z w : ℝ)
      = (cnt j (offPair k).1 (offPair z).1 : ℝ) * (cnt s (offPair w).2 (σ (offPair k).2) : ℝ) :=
    fun _ _ _ => by unfold I2N; push_cast; ring
  refine ⟨fun k z w => div_nonneg (Nat.cast_nonneg _) hpos.le, fun k => ?_, fun z => ?_,
    fun w => ?_⟩ <;> simp only [← Finset.sum_div, e] <;>
    rw [div_eq_one_iff_eq hpos.ne', hc]
  · simp only [← Finset.mul_sum, sum_cell_snd_left, ← Finset.sum_mul, sum_cell_fst_right]
  · simp only [← Finset.mul_sum, sum_cell_snd_left, ← Finset.sum_mul, sum_cell_fst_left]
  · simp only [← Finset.sum_mul, sum_cell_fst_right, ← Finset.mul_sum, sum_root_snd _ _ hσ]

theorem I3_bd (j g : ℕ) :
    BD fun k z w => (I3N j g k z w : ℝ) / 2 ^ (j + g + 2) := by
  have hpos : (0 : ℝ) < 2 ^ (j + g + 2) := by positivity
  have hc : (2 : ℝ) ^ (j + g + 2) = 2 * 2 ^ j * (2 * 2 ^ g) := by ring
  have e : ∀ k z w, (I3N j g k z w : ℝ)
      = (cnt j (offPair k).1 (offPair z).1 : ℝ) * (cnt g (offPair z).2 (offPair w).1 : ℝ) :=
    fun _ _ _ => by unfold I3N; push_cast; ring
  refine ⟨fun k z w => div_nonneg (Nat.cast_nonneg _) hpos.le, fun k => ?_, fun z => ?_,
    fun w => ?_⟩ <;> simp only [← Finset.sum_div, e] <;>
    rw [div_eq_one_iff_eq hpos.ne', hc]
  · simp only [← Finset.mul_sum, sum_cell_fst_right, ← Finset.sum_mul]
  · simp only [← Finset.mul_sum, sum_cell_fst_right, ← Finset.sum_mul, sum_cell_fst_left]
  · rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, sum_cell_fst_left, ← Finset.mul_sum, sum_cell_snd_left]

/-! ### The base cases and the induction -/

theorem bd_of_cert {j g s : ℕ} {σ : Fin 3 → Fin 3} {fA fB : Fin 5 → Fin 6 → Fin 6}
    (hA : ∀ t k k', fA t k = fA t k' → k = k') (hB : ∀ t k k', fB t k = fB t k' → k = k')
    (hm : ∀ k t, mult5 fA fB k t ≤ C2N j g s σ k (fA t k) (fB t k)) :
    ∃ D, BD D ∧ ∀ k z w, 5 * D k z w ≤ (C2N j g s σ k z w : ℝ) := by
  refine ⟨fun k z w => (∑ t, ppmat (fA t) (fB t) k z w) / 5,
    BD.avg5 fun t => ppmat_bd (fun k k' e => hA t k k' e) (fun k k' e => hB t k k' e),
    fun k z w => ?_⟩
  show 5 * ((∑ t, ppmat (fA t) (fB t) k z w) / 5) ≤ _
  rw [mul_div_cancel₀ _ (by norm_num : (5 : ℝ) ≠ 0)]
  have hpp : ∀ t, ppmat (fA t) (fB t) k z w = if fA t k = z ∧ fB t k = w then 1 else 0 :=
    fun t => by
      unfold ppmat pmat
      split_ifs <;> simp_all
  by_cases hex : ∃ t, fA t k = z ∧ fB t k = w
  · obtain ⟨t, rfl, rfl⟩ := hex
    have key : ∑ t', ppmat (fA t') (fB t') k (fA t k) (fB t k) = (mult5 fA fB k t : ℝ) := by
      simp only [hpp, mult5, Fin.sum_univ_five]
      push_cast
      rfl
    rw [key]
    exact_mod_cast hm k t
  · simp only [not_exists, not_and] at hex
    rw [Finset.sum_eq_zero fun t _ => by
      rw [hpp]
      simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_and]
      exact hex t]
    exact Nat.cast_nonneg _

theorem exists_bd_base {j g s : ℕ} (h : j + g + s = 2) {σ : Fin 3 → Fin 3}
    (hσ : Function.Injective σ) :
    ∃ D, BD D ∧ ∀ k z w, (dN (j + g + s + 2) : ℝ) * D k z w ≤ (C2N j g s σ k z w : ℝ) := by
  have h5 : dN (j + g + s + 2) = 5 := by rw [h]; rfl
  rw [h5]
  push_cast
  have hσ' : ∀ a b, σ a = σ b → a = b := fun a b e => hσ e
  obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ :
      (j = 2 ∧ g = 0 ∧ s = 0) ∨ (j = 0 ∧ g = 2 ∧ s = 0) ∨ (j = 0 ∧ g = 0 ∧ s = 2) ∨
      (j = 1 ∧ g = 1 ∧ s = 0) ∨ (j = 1 ∧ g = 0 ∧ s = 1) ∨ (j = 0 ∧ g = 1 ∧ s = 1) := by
    omega
  · obtain ⟨hA, hB, hm⟩ := cert_ok0 σ hσ'
    exact bd_of_cert hA hB hm
  · obtain ⟨hA, hB, hm⟩ := cert_ok1 σ hσ'
    exact bd_of_cert hA hB hm
  · obtain ⟨hA, hB, hm⟩ := cert_ok2 σ hσ'
    exact bd_of_cert hA hB hm
  · obtain ⟨hA, hB, hm⟩ := cert_ok3 σ hσ'
    exact bd_of_cert hA hB hm
  · obtain ⟨hA, hB, hm⟩ := cert_ok4 σ hσ'
    exact bd_of_cert hA hB hm
  · obtain ⟨hA, hB, hm⟩ := cert_ok5 σ hσ'
    exact bd_of_cert hA hB hm

/-- One step of the induction: mixing a design with an exactly balanced increment. -/
theorem bd_step {α c : ℝ} (hα : 0 ≤ α) (hc : 0 < c) {D I : Fin 6 → Fin 6 → Fin 6 → ℝ}
    (hD : BD D) (hI : BD I) {C C' : Fin 6 → Fin 6 → Fin 6 → ℝ}
    (hle : ∀ k z w, α * D k z w ≤ C k z w) (hC : ∀ k z w, C' k z w = C k z w + c * I k z w) :
    ∃ D', BD D' ∧ ∀ k z w, (α + c) * D' k z w ≤ C' k z w := by
  refine ⟨fun k z w => (α * D k z w + c * I k z w) / (α + c),
    hD.mix hI hα hc.le (by linarith), fun k z w => ?_⟩
  show (α + c) * ((α * D k z w + c * I k z w) / (α + c)) ≤ _
  rw [mul_div_cancel₀ _ (by linarith : α + c ≠ 0), hC]
  linarith [hle k z w]

theorem even_sub_two {N : ℕ} (h : Even N) (h2 : 2 ≤ N) : Even (N - 2) := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r - 1, by omega⟩

/-- **Designs for two loaded steps.** -/
theorem exists_bd_le {σ : Fin 3 → Fin 3} (hσ : Function.Injective σ) :
    ∀ N j g s, j + g + s = N → Even N → 2 ≤ N →
      ∃ D, BD D ∧ ∀ k z w, (dN (j + g + s + 2) : ℝ) * D k z w ≤ (C2N j g s σ k z w : ℝ) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro j g s hN hev h2
  rcases Nat.lt_or_ge N 4 with hlt | h4
  · exact exists_bd_base (by obtain ⟨r, hr⟩ := hev; omega) hσ
  have hev' := even_sub_two hev h2
  rcases (by omega : 2 ≤ j ∨ 2 ≤ g ∨ 2 ≤ s) with hj | hg | hs
  · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
    obtain ⟨D, hD, hle⟩ := ih (N - 2) (by omega) j g s (by omega) hev' (by omega)
    have hα : (dN (j + 2 + g + s + 2) : ℝ)
        = dN (j + g + s + 2) + 2 ^ j * 2 ^ (g + s + 2) := by
      rw [show j + 2 + g + s + 2 = (j + g + s + 2) + 2 by ring, dN_add_two']
      push_cast
      ring
    rw [hα]
    refine bd_step (Nat.cast_nonneg _) (by positivity) hD (I1_bd g s hσ) hle fun k z w => ?_
    rw [C2N_add_two_j]
    push_cast
    field_simp
  · obtain ⟨g, rfl⟩ : ∃ g', g = g' + 2 := ⟨g - 2, by omega⟩
    obtain ⟨D, hD, hle⟩ := ih (N - 2) (by omega) j g s (by omega) hev' (by omega)
    have hα : (dN (j + (g + 2) + s + 2) : ℝ)
        = dN (j + g + s + 2) + 2 ^ g * 2 ^ (j + s + 2) := by
      rw [show j + (g + 2) + s + 2 = (j + g + s + 2) + 2 by ring, dN_add_two']
      push_cast
      ring
    rw [hα]
    refine bd_step (Nat.cast_nonneg _) (by positivity) hD (I2_bd j s hσ) hle fun k z w => ?_
    rw [C2N_add_two_g]
    push_cast
    field_simp
  · obtain ⟨s, rfl⟩ : ∃ s', s = s' + 2 := ⟨s - 2, by omega⟩
    obtain ⟨D, hD, hle⟩ := ih (N - 2) (by omega) j g s (by omega) hev' (by omega)
    have hα : (dN (j + g + (s + 2) + 2) : ℝ)
        = dN (j + g + s + 2) + 2 ^ s * 2 ^ (j + g + 2) := by
      rw [show j + g + (s + 2) + 2 = (j + g + s + 2) + 2 by ring, dN_add_two']
      push_cast
      ring
    rw [hα]
    refine bd_step (Nat.cast_nonneg _) (by positivity) hD (I3_bd j g) hle fun k z w => ?_
    rw [C2N_add_two_s]
    push_cast
    field_simp

/-! ### Mixing (weighted AM–GM and Birkhoff) -/

theorem cells_distinct : ∀ z : Fin 6, z ≠ z + 1 ∧ z ≠ z + 2 ∧ z ≠ z + 3 ∧ z + 1 ≠ z + 2 ∧
    z + 1 ≠ z + 3 ∧ z + 2 ≠ z + 3 := by decide

/-- A positive four-cell bound makes every cell positive. -/
theorem pos_of_four {M : Fin 6 → ℝ} (hM : ∀ z, 0 ≤ M z) {Y : ℝ} (hY : 0 < Y)
    (hT : ∀ i j k l : Fin 6, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      Y ≤ M i ^ 2 * M j ^ 2 * M k * M l) (z : Fin 6) : 0 < M z := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := cells_distinct z
  have := hT z (z + 1) (z + 2) (z + 3) h1 h2 h3 h4 h5 h6
  rcases (hM z).lt_or_eq with h | h
  · exact h
  · rw [← h] at this
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at this
    linarith

/-- The four-cell bound in logarithms survives a doubly stochastic matrix (Birkhoff). -/
theorem four_log {D : Fin 6 → Fin 6 → ℝ} (hD : DS D) {ℓ : Fin 6 → ℝ} {L : ℝ}
    (hT : ∀ i j k l : Fin 6, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      L ≤ 2 * ℓ i + 2 * ℓ j + ℓ k + ℓ l) :
    ∀ i j k l : Fin 6, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      L ≤ 2 * (∑ z, D i z * ℓ z) + 2 * (∑ z, D j z * ℓ z) + (∑ z, D k z * ℓ z)
        + ∑ z, D l z * ℓ z := by
  intro i j k l hij hik hil hjk hjl hkl
  obtain ⟨s, w, hw0, hw1, hsum⟩ := hD.exists_perms
  rw [hsum i ℓ, hsum j ℓ, hsum k ℓ, hsum l ℓ]
  calc L = ∑ σ ∈ s, w σ * L := by rw [← Finset.sum_mul, hw1, one_mul]
    _ ≤ ∑ σ ∈ s, w σ * (2 * ℓ (σ i) + 2 * ℓ (σ j) + ℓ (σ k) + ℓ (σ l)) :=
        Finset.sum_le_sum fun σ hσ => mul_le_mul_of_nonneg_left
          (hT _ _ _ _ (fun e => hij (σ.injective e)) (fun e => hik (σ.injective e))
            (fun e => hil (σ.injective e)) (fun e => hjk (σ.injective e))
            (fun e => hjl (σ.injective e)) (fun e => hkl (σ.injective e))) (hw0 σ hσ)
    _ = _ := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun σ _ => by ring

theorem log_four {x y z t : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ht : 0 < t) :
    Real.log (x ^ 2 * y ^ 2 * z * t)
      = 2 * Real.log x + 2 * Real.log y + Real.log z + Real.log t := by
  rw [Real.log_mul (by positivity) ht.ne', Real.log_mul (by positivity) hz.ne',
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- **Mixing through a bi-design.** If `p ≥ c · Σ D M₁ M₂` with `D` a bi-design and `M₁`, `M₂`
have four-cell bounds `Y₁`, `Y₂`, then `p` has the four-cell bound `c⁶ Y₁ Y₂`. -/
theorem two_mix {M₁ M₂ : Fin 6 → ℝ} (hM₁ : ∀ z, 0 ≤ M₁ z) (hM₂ : ∀ z, 0 ≤ M₂ z) {Y₁ Y₂ : ℝ}
    (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂)
    (hT₁ : ∀ i j k l : Fin 6, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      Y₁ ≤ M₁ i ^ 2 * M₁ j ^ 2 * M₁ k * M₁ l)
    (hT₂ : ∀ i j k l : Fin 6, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      Y₂ ≤ M₂ i ^ 2 * M₂ j ^ 2 * M₂ k * M₂ l)
    {D : Fin 6 → Fin 6 → Fin 6 → ℝ} (hD : BD D) {c : ℝ} (hc : 0 ≤ c) {p : Fin 6 → ℝ}
    (hp : ∀ k, c * ∑ z, ∑ w, D k z w * (M₁ z * M₂ w) ≤ p k) :
    ∀ i j k l : Fin 6, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      c ^ 6 * (Y₁ * Y₂) ≤ p i ^ 2 * p j ^ 2 * p k * p l := by
  intro i j k l hij hik hil hjk hjl hkl
  have hp0 : ∀ k, 0 ≤ p k := fun k => le_trans (mul_nonneg hc (Finset.sum_nonneg fun z _ =>
    Finset.sum_nonneg fun w _ => mul_nonneg (hD.1 k z w) (mul_nonneg (hM₁ z) (hM₂ w)))) (hp k)
  have hR : 0 ≤ p i ^ 2 * p j ^ 2 * p k * p l :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hp0 k)) (hp0 l)
  rcases hY₁.lt_or_eq with hY₁p | hY₁0
  swap
  · rw [← hY₁0, zero_mul, mul_zero]; exact hR
  rcases hY₂.lt_or_eq with hY₂p | hY₂0
  swap
  · rw [← hY₂0, mul_zero, mul_zero]; exact hR
  have hq₁ := pos_of_four hM₁ hY₁p hT₁
  have hq₂ := pos_of_four hM₂ hY₂p hT₂
  -- the exponent of the weighted geometric mean at a root cell
  set Λ : Fin 6 → ℝ := fun k => (∑ z, (∑ w, D k z w) * Real.log (M₁ z))
    + ∑ w, (∑ z, D k z w) * Real.log (M₂ w) with hΛ
  have hG : ∀ k, Real.exp (Λ k) ≤ ∑ z, ∑ w, D k z w * (M₁ z * M₂ w) := by
    intro k
    have hJ := convexOn_exp.map_sum_le (t := (univ : Finset (Fin 6 × Fin 6)))
      (w := fun zw => D k zw.1 zw.2) (p := fun zw => Real.log (M₁ zw.1) + Real.log (M₂ zw.2))
      (fun zw _ => hD.1 k zw.1 zw.2) (by rw [Fintype.sum_prod_type]; exact hD.2.1 k)
      (fun _ _ => Set.mem_univ _)
    simp only [smul_eq_mul] at hJ
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at hJ
    have e1 : ∑ z, ∑ w, D k z w * (Real.log (M₁ z) + Real.log (M₂ w)) = Λ k := by
      simp only [hΛ, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
      congr 1
      exact Finset.sum_comm
    have e2 : ∀ z w, Real.exp (Real.log (M₁ z) + Real.log (M₂ w)) = M₁ z * M₂ w := fun z w => by
      rw [Real.exp_add, Real.exp_log (hq₁ z), Real.exp_log (hq₂ w)]
    rw [e1] at hJ
    simp only [e2] at hJ
    exact hJ
  have hL₁ : ∀ i j k l : Fin 6, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      Real.log Y₁ ≤ 2 * Real.log (M₁ i) + 2 * Real.log (M₁ j) + Real.log (M₁ k)
        + Real.log (M₁ l) := fun i j k l h1 h2 h3 h4 h5 h6 => by
    rw [← log_four (hq₁ i) (hq₁ j) (hq₁ k) (hq₁ l)]
    exact Real.log_le_log hY₁p (hT₁ i j k l h1 h2 h3 h4 h5 h6)
  have hL₂ : ∀ i j k l : Fin 6, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      Real.log Y₂ ≤ 2 * Real.log (M₂ i) + 2 * Real.log (M₂ j) + Real.log (M₂ k)
        + Real.log (M₂ l) := fun i j k l h1 h2 h3 h4 h5 h6 => by
    rw [← log_four (hq₂ i) (hq₂ j) (hq₂ k) (hq₂ l)]
    exact Real.log_le_log hY₂p (hT₂ i j k l h1 h2 h3 h4 h5 h6)
  have hA := four_log hD.ds₁ hL₁ i j k l hij hik hil hjk hjl hkl
  have hB := four_log hD.ds₂ hL₂ i j k l hij hik hil hjk hjl hkl
  have hsum : Real.log Y₁ + Real.log Y₂ ≤ 2 * Λ i + 2 * Λ j + Λ k + Λ l := by
    simp only [hΛ]
    linarith
  have hsq : ∀ x : ℝ, Real.exp x ^ 2 = Real.exp (2 * x) := fun x => by
    rw [sq, ← Real.exp_add]
    ring_nf
  have hGY : Y₁ * Y₂
      ≤ Real.exp (Λ i) ^ 2 * Real.exp (Λ j) ^ 2 * Real.exp (Λ k) * Real.exp (Λ l) := by
    rw [hsq, hsq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    calc Y₁ * Y₂ = Real.exp (Real.log Y₁ + Real.log Y₂) := by
          rw [Real.exp_add, Real.exp_log hY₁p, Real.exp_log hY₂p]
      _ ≤ _ := Real.exp_le_exp.mpr hsum
  have hcp : ∀ k, c * Real.exp (Λ k) ≤ p k := fun k =>
    le_trans (mul_le_mul_of_nonneg_left (hG k) hc) (hp k)
  have he0 : ∀ k, 0 ≤ c * Real.exp (Λ k) := fun k => mul_nonneg hc (Real.exp_pos _).le
  calc c ^ 6 * (Y₁ * Y₂)
      ≤ c ^ 6 * (Real.exp (Λ i) ^ 2 * Real.exp (Λ j) ^ 2 * Real.exp (Λ k) * Real.exp (Λ l)) :=
        mul_le_mul_of_nonneg_left hGY (by positivity)
    _ = (c * Real.exp (Λ i)) ^ 2 * (c * Real.exp (Λ j)) ^ 2 * (c * Real.exp (Λ k))
          * (c * Real.exp (Λ l)) := by ring
    _ ≤ _ := four_le (he0 i) (he0 j) (he0 k) (he0 l) (hcp i) (hcp j) (hcp k) (hcp l)

/-! ### The walks through two loaded steps -/

/-- Splitting the walks at one step, keeping the walks after it. -/
theorem pw_split_left (L₁ L₂ : List (Fin 3 → Fin 3 → ℝ)) (h₁ : ∀ M ∈ L₁, ∀ a b, 0 ≤ M a b)
    (h₂ : ∀ M ∈ L₂, ∀ a b, 0 ≤ M a b) (M : Fin 3 → Fin 3 → ℝ) (hM : ∀ a b, 0 ≤ M a b)
    (a b : Fin 3) :
    mnP L₁ * ∑ z : Fin 6, (cnt L₁.length a (offPair z).1 : ℝ) * M (offPair z).1 (offPair z).2
        * pw L₂ (offPair z).2 b ≤ pw (L₁ ++ M :: L₂) a b := by
  rw [pw_append]
  simp only [pw]
  have g1 := pw_ge L₁ h₁
  have hq := pw_nonneg L₂ h₂
  have inner : ∀ x : Fin 3, (cnt L₁.length a x : ℝ) * mnP L₁ *
      (M x (x + 1) * pw L₂ (x + 1) b + M x (x + 2) * pw L₂ (x + 2) b)
      ≤ pw L₁ a x * (M x (x + 1) * pw L₂ (x + 1) b + M x (x + 2) * pw L₂ (x + 2) b) :=
    fun x => mul_le_mul_of_nonneg_right (g1 a x)
      (add_nonneg (mul_nonneg (hM _ _) (hq _ _)) (mul_nonneg (hM _ _) (hq _ _)))
  have e : mnP L₁ * ∑ z : Fin 6, (cnt L₁.length a (offPair z).1 : ℝ)
        * M (offPair z).1 (offPair z).2 * pw L₂ (offPair z).2 b
      = ∑ x : Fin 3, (cnt L₁.length a x : ℝ) * mnP L₁ *
        (M x (x + 1) * pw L₂ (x + 1) b + M x (x + 2) * pw L₂ (x + 2) b) := by
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

theorem pw_split2_ge (L₁ L₂ L₃ : List (Fin 3 → Fin 3 → ℝ)) (h₁ : ∀ M ∈ L₁, ∀ a b, 0 ≤ M a b)
    (h₂ : ∀ M ∈ L₂, ∀ a b, 0 ≤ M a b) (h₃ : ∀ M ∈ L₃, ∀ a b, 0 ≤ M a b)
    (M₁ M₂ : Fin 3 → Fin 3 → ℝ) (hM₁ : ∀ a b, 0 ≤ M₁ a b) (hM₂ : ∀ a b, 0 ≤ M₂ a b)
    (a b : Fin 3) :
    mnP L₁ * mnP L₂ * mnP L₃ * ∑ z : Fin 6, ∑ w : Fin 6,
      (cnt L₁.length a (offPair z).1 : ℝ) * (cnt L₂.length (offPair z).2 (offPair w).1 : ℝ)
        * (cnt L₃.length (offPair w).2 b : ℝ)
        * (M₁ (offPair z).1 (offPair z).2 * M₂ (offPair w).1 (offPair w).2)
      ≤ pw (L₁ ++ M₁ :: (L₂ ++ M₂ :: L₃)) a b := by
  have hR : ∀ M ∈ L₂ ++ M₂ :: L₃, ∀ a b, 0 ≤ M a b := by
    intro M hM
    rcases List.mem_append.mp hM with h | h
    · exact h₂ M h
    · rcases List.mem_cons.mp h with rfl | h
      · exact hM₂
      · exact h₃ M h
  refine le_trans (le_of_eq ?_) (le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum
    fun z _ => mul_le_mul_of_nonneg_left (pw_split_ge L₂ L₃ h₂ h₃ M₂ hM₂ (offPair z).2 b)
      (mul_nonneg (Nat.cast_nonneg _) (hM₁ _ _))) (mnP_nonneg L₁ h₁))
    (pw_split_left L₁ (L₂ ++ M₂ :: L₃) h₁ hR M₁ hM₁ a b))
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => by ring

/-- **Transport of the four-cell bound through two loaded steps**, at the level of indices:
`L₁`, `L₂`, `L₃` the tables before, between and after the loaded tables `M₁`, `M₂`, with
entries at least `A₁`, `A₂`, `A₃` in total. The total number of steps is even. -/
theorem walks_tb_transport2 (L₁ L₂ L₃ : List (Fin 3 → Fin 3 → ℝ))
    (h₁ : ∀ M ∈ L₁, ∀ a b, 0 ≤ M a b) (h₂ : ∀ M ∈ L₂, ∀ a b, 0 ≤ M a b)
    (h₃ : ∀ M ∈ L₃, ∀ a b, 0 ≤ M a b) (M₁ M₂ : Fin 3 → Fin 3 → ℝ) (hM₁ : ∀ a b, 0 ≤ M₁ a b)
    (hM₂ : ∀ a b, 0 ≤ M₂ a b) {A₁ A₂ A₃ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hA₃ : 0 ≤ A₃)
    (hm₁ : A₁ ≤ mnP L₁) (hm₂ : A₂ ≤ mnP L₂) (hm₃ : A₃ ≤ mnP L₃)
    (hev : Even (L₁.length + L₂.length + L₃.length))
    (h2 : 2 ≤ L₁.length + L₂.length + L₃.length) {Y₁ Y₂ : ℝ} (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂)
    (hT₁ : ∀ i j k l : Fin 6, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      Y₁ ≤ M₁ (offPair i).1 (offPair i).2 ^ 2 * M₁ (offPair j).1 (offPair j).2 ^ 2
        * M₁ (offPair k).1 (offPair k).2 * M₁ (offPair l).1 (offPair l).2)
    (hT₂ : ∀ i j k l : Fin 6, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      Y₂ ≤ M₂ (offPair i).1 (offPair i).2 ^ 2 * M₂ (offPair j).1 (offPair j).2 ^ 2
        * M₂ (offPair k).1 (offPair k).2 * M₂ (offPair l).1 (offPair l).2)
    {σ : Fin 3 → Fin 3} (hσ : Function.Injective σ) :
    ∀ i j k l : Fin 6, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      (A₁ * A₂ * A₃ * dN (L₁.length + L₂.length + L₃.length + 2)) ^ 6 * (Y₁ * Y₂) ≤
        pw (L₁ ++ M₁ :: (L₂ ++ M₂ :: L₃)) (offPair i).1 (σ (offPair i).2) ^ 2
          * pw (L₁ ++ M₁ :: (L₂ ++ M₂ :: L₃)) (offPair j).1 (σ (offPair j).2) ^ 2
          * pw (L₁ ++ M₁ :: (L₂ ++ M₂ :: L₃)) (offPair k).1 (σ (offPair k).2)
          * pw (L₁ ++ M₁ :: (L₂ ++ M₂ :: L₃)) (offPair l).1 (σ (offPair l).2) := by
  obtain ⟨D, hD, hle⟩ := exists_bd_le hσ _ L₁.length L₂.length L₃.length rfl hev h2
  have hA : 0 ≤ A₁ * A₂ * A₃ := mul_nonneg (mul_nonneg hA₁ hA₂) hA₃
  refine two_mix (M₁ := fun z => M₁ (offPair z).1 (offPair z).2)
    (M₂ := fun z => M₂ (offPair z).1 (offPair z).2) (fun z => hM₁ _ _) (fun z => hM₂ _ _)
    hY₁ hY₂ hT₁ hT₂ hD (mul_nonneg hA (Nat.cast_nonneg _)) fun k => ?_
  have hsplit := pw_split2_ge L₁ L₂ L₃ h₁ h₂ h₃ M₁ M₂ hM₁ hM₂ (offPair k).1 (σ (offPair k).2)
  have hMM : ∀ z w, 0 ≤ M₁ (offPair z).1 (offPair z).2 * M₂ (offPair w).1 (offPair w).2 :=
    fun z w => mul_nonneg (hM₁ _ _) (hM₂ _ _)
  have hC0 : 0 ≤ ∑ z : Fin 6, ∑ w : Fin 6, (C2N L₁.length L₂.length L₃.length σ k z w : ℝ)
      * (M₁ (offPair z).1 (offPair z).2 * M₂ (offPair w).1 (offPair w).2) :=
    Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun w _ =>
      mul_nonneg (Nat.cast_nonneg _) (hMM z w)
  calc A₁ * A₂ * A₃ * (dN (L₁.length + L₂.length + L₃.length + 2) : ℝ)
        * ∑ z, ∑ w, D k z w * (M₁ (offPair z).1 (offPair z).2 * M₂ (offPair w).1 (offPair w).2)
      = A₁ * A₂ * A₃ * ∑ z : Fin 6, ∑ w : Fin 6,
          ((dN (L₁.length + L₂.length + L₃.length + 2) : ℝ) * D k z w)
          * (M₁ (offPair z).1 (offPair z).2 * M₂ (offPair w).1 (offPair w).2) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => by ring
    _ ≤ A₁ * A₂ * A₃ * ∑ z : Fin 6, ∑ w : Fin 6,
          (C2N L₁.length L₂.length L₃.length σ k z w : ℝ)
          * (M₁ (offPair z).1 (offPair z).2 * M₂ (offPair w).1 (offPair w).2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun w _ =>
          mul_le_mul_of_nonneg_right (hle k z w) (hMM z w)) hA
    _ ≤ mnP L₁ * mnP L₂ * mnP L₃ * ∑ z : Fin 6, ∑ w : Fin 6,
          (C2N L₁.length L₂.length L₃.length σ k z w : ℝ)
          * (M₁ (offPair z).1 (offPair z).2 * M₂ (offPair w).1 (offPair w).2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul hm₁ hm₂ hA₂ (hA₁.trans hm₁)) hm₃ hA₃
          (mul_nonneg (hA₁.trans hm₁) (hA₂.trans hm₂))) hC0
    _ = _ := by
        congr 1
        refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => ?_
        unfold C2N
        push_cast
        ring
    _ ≤ _ := hsplit

/-! ### The face -/

/-- The normalised form: all constants one. -/
theorem tb_transport2_one (m : ℕ) (hm : Odd m) (h3 : 3 ≤ m) (Lu Lv : Finset ℕ)
    (Li : Fin m → Finset ℕ) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (j₁ j₂ : Fin (m + 1)) (h12 : j₁ < j₂) (E : Fin (m + 1) → ℕ → ℕ → ℝ)
    (hE0 : ∀ j c d, 0 ≤ E j c d) {τ₁ τ₂ : ℝ}
    (hT₁ : TB (pathList Lu Lv Li j₁.castSucc) (pathList Lu Lv Li j₁.succ) (E j₁) 1 τ₁)
    (hT₂ : TB (pathList Lu Lv Li j₂.castSucc) (pathList Lu Lv Li j₂.succ) (E j₂) 1 τ₂)
    (hD : ∀ j, j ≠ j₁ → j ≠ j₂ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) 1) :
    TB Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m) (τ₁ * τ₂) := by
  have h12' : j₁.val < j₂.val := h12
  refine tb_of_idx fun α β hα' hβ hαm hβm _ => ?_
  obtain ⟨ζ, h0, hζ, hchain⟩ := framesFin m Lu Lv Li hLv hLi α hα' hαm
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
  -- the tables, split at the two loaded edges
  set T := pathTabs ζ E with hTdef
  set M₁ := idxM (E j₁) (ζ j₁.castSucc) (ζ j₁.succ) with hM₁
  set M₂ := idxM (E j₂) (ζ j₂.castSucc) (ζ j₂.succ) with hM₂
  have hlenT : T.length = m + 1 := by simp [hTdef, pathTabs]
  have hget : ∀ (j : Fin (m + 1)) (h : j.val < T.length),
      T[j.val] = idxM (E j) (ζ j.castSucc) (ζ j.succ) := fun j h => by
    simp only [hTdef, pathTabs, List.getElem_ofFn, Fin.eta]
  have hsplit : T = T.take j₁ ++ M₁ :: ((T.drop (j₁ + 1)).take (j₂ - j₁ - 1)
      ++ M₂ :: T.drop (j₂ + 1)) := by
    have e1 : T.drop j₁ = M₁ :: T.drop (j₁ + 1) := by
      rw [List.drop_eq_getElem_cons (by omega : j₁.val < T.length), hget]
    have e2 : T.drop j₂ = M₂ :: T.drop (j₂ + 1) := by
      rw [List.drop_eq_getElem_cons (by omega : j₂.val < T.length), hget]
    have hd2 : (T.drop (j₁ + 1)).drop (j₂ - j₁ - 1) = T.drop j₂ := by
      rw [List.drop_drop]
      congr 1
      omega
    conv_lhs => rw [← List.take_append_drop j₁.val T, e1,
      ← List.take_append_drop (j₂ - j₁ - 1) (T.drop (j₁ + 1)), hd2, e2]
  have hTnn : ∀ M ∈ T, ∀ a b, 0 ≤ M a b := by
    intro M hM a b
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).mp hM
    exact hE0 _ _ _
  have hTi : ∀ (i : ℕ) (hi : i < T.length), i ≠ j₁ → i ≠ j₂ → 1 ≤ mn T[i] := by
    intro i hi h1 h2
    have hi' : i < m + 1 := by rw [hlenT] at hi; exact hi
    rw [hget ⟨i, hi'⟩ hi]
    exact one_le_mn_of_dom (hD ⟨i, hi'⟩ (fun e => h1 (congrArg Fin.val e))
      (fun e => h2 (congrArg Fin.val e))) (hζ _).2 (hζ _).2 (hchain _)
  have hL₁ : ∀ M ∈ T.take j₁, 1 ≤ mn M := by
    intro M hM
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hM
    have hi' : i < j₁.val := by simp at hi; omega
    rw [List.getElem_take]
    exact hTi i (by omega) (by omega) (by omega)
  have hL₂ : ∀ M ∈ (T.drop (j₁ + 1)).take (j₂ - j₁ - 1), 1 ≤ mn M := by
    intro M hM
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hM
    have hi' : i < j₂.val - j₁.val - 1 := by simp at hi; omega
    rw [List.getElem_take, List.getElem_drop]
    exact hTi (j₁ + 1 + i) (by omega) (by omega) (by omega)
  have hL₃ : ∀ M ∈ T.drop (j₂ + 1), 1 ≤ mn M := by
    intro M hM
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hM
    have hi' : i < m - j₂.val := by simp at hi; omega
    rw [List.getElem_drop]
    exact hTi (j₂ + 1 + i) (by omega) (by omega) (by omega)
  have hlen₁ : (T.take j₁).length = j₁.val := by rw [List.length_take, hlenT]; omega
  have hlen₂ : ((T.drop (j₁ + 1)).take (j₂ - j₁ - 1)).length = j₂.val - j₁.val - 1 := by
    rw [List.length_take, List.length_drop, hlenT]; omega
  have hlen₃ : (T.drop (j₂ + 1)).length = m - j₂.val := by
    rw [List.length_drop, hlenT]; omega
  have hsum : (T.take j₁).length + ((T.drop (j₁ + 1)).take (j₂ - j₁ - 1)).length
      + (T.drop (j₂ + 1)).length = m - 1 := by
    rw [hlen₁, hlen₂, hlen₃]; omega
  have hev : Even (m - 1) := by obtain ⟨r, hr⟩ := hm; exact ⟨r, by omega⟩
  have hT₁idx := hT₁.idx (hζ _).1 (hζ _).1 (hζ _).2 (hζ _).2 (hchain j₁)
  have hT₂idx := hT₂.idx (hζ _).1 (hζ _).1 (hζ _).2 (hζ _).2 (hchain j₂)
  rw [one_pow, mul_one] at hT₁idx hT₂idx
  have key := walks_tb_transport2 (T.take j₁) ((T.drop (j₁ + 1)).take (j₂ - j₁ - 1))
    (T.drop (j₂ + 1)) (fun M hM => hTnn M (List.mem_of_mem_take hM))
    (fun M hM => hTnn M (List.mem_of_mem_drop (List.mem_of_mem_take hM)))
    (fun M hM => hTnn M (List.mem_of_mem_drop hM)) M₁ M₂ (fun a b => hE0 _ _ _)
    (fun a b => hE0 _ _ _) zero_le_one zero_le_one zero_le_one (one_le_mnP _ hL₁)
    (one_le_mnP _ hL₂) (one_le_mnP _ hL₃) (by rw [hsum]; exact hev) (by rw [hsum]; omega)
    (sq_nonneg τ₁) (sq_nonneg τ₂) hT₁idx hT₂idx hσinj
  rw [← hsplit, hsum, show m - 1 + 2 = m + 1 by omega, one_mul, one_mul, one_mul] at key
  intro i j k l hij hik hil hjk hjl hkl
  have hcell : ∀ r : Fin 6, pw T (offPair r).1 (σ (offPair r).2)
      ≤ faceSum Li (fun _ _ => 1) E (α (offPair r).1) (β (offPair r).2) := fun r => by
    have := pw_le_faceSum hζ E hE0 (offPair r).1 (σ (offPair r).2)
    rwa [h0, hσ] at this
  have hp := pw_nonneg T hTnn
  calc (τ₁ * τ₂) ^ 2 * faceConst3 m ^ 6 = (dN (m + 1) : ℝ) ^ 6 * (τ₁ ^ 2 * τ₂ ^ 2) := by
        rw [faceConst3_eq_dN]; ring
    _ ≤ _ := key i j k l hij hik hil hjk hjl hkl
    _ ≤ _ := four_le (hp _ _) (hp _ _) (hp _ _) (hp _ _) (hcell i) (hcell j) (hcell k) (hcell l)

/-- **Transport through an odd face with two loaded edges**: the four-cell constants multiply. -/
theorem tb_transport2 (m : ℕ) (hm : Odd m) (h3 : 3 ≤ m) (Lu Lv : Finset ℕ)
    (Li : Fin m → Finset ℕ) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (j₁ j₂ : Fin (m + 1)) (h12 : j₁ < j₂) (E : Fin (m + 1) → ℕ → ℕ → ℝ)
    (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ) (hA : ∀ j, 0 < A j) {τ₁ τ₂ : ℝ}
    (hT₁ : TB (pathList Lu Lv Li j₁.castSucc) (pathList Lu Lv Li j₁.succ) (E j₁) (A j₁) τ₁)
    (hT₂ : TB (pathList Lu Lv Li j₂.castSucc) (pathList Lu Lv Li j₂.succ) (E j₂) (A j₂) τ₂)
    (hD : ∀ j, j ≠ j₁ → j ≠ j₂ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    TB Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) (τ₁ * τ₂) := by
  have hP : 0 < ∏ j, A j := Finset.prod_pos fun j _ => hA j
  have key := tb_transport2_one m hm h3 Lu Lv Li hLv hLi j₁ j₂ h12 (fun j c d => E j c d / A j)
    (fun j c d => div_nonneg (hE0 j c d) (hA j).le) (hT₁.div (hA j₁)) (hT₂.div (hA j₂))
    (fun j h1 h2 => (hD j h1 h2).div (hA j))
  refine TB.of_div hP ?_
  have e : (fun c d => faceSum Li (fun _ _ => 1) E c d / ∏ j, A j)
      = faceSum Li (fun _ _ => 1) (fun j c d => E j c d / A j) := by
    funext c d
    rw [faceSum_div]
  rw [e]
  exact key

end Outerplanar
