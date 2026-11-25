/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.SqMultiCheck
import Outerplanar.LoadedCert
import Outerplanar.Analytic

/-!
# Squares with three loaded edges: soundness of the checker

The checks of `Outerplanar/SqMultiCheck.lean` give real inequalities for the index form of a
square with three loaded path edges.

* `EdgeOK md E w N` — the table `w` (indices `Fin 3`, equal colours `E`) is in the class `md`
  with scale `N`: floors `w ≥ c N`, bijection products `≥ c N³`, six-family products `≥ c N⁶`,
  the ball class `IdxBall E w (c N)`, for each kind whose constant `c` is present.
* `ball_tv` — the ball class gives `E log w ≥ log A` for every law within total variation
  `3/200` of the uniform law on a matched family (product coupling of the excess and the
  deficit; each atom has mass `1/6 ≥ 3/200`).
* `pieces_bound` — the pieces of a valid list give `∑ M log w ≥ (∑ M) log N + log (num / den)`.
* `checkR_sound`, `checkC_sound` — a passing rooted record gives
  `∏ F(a, b) ^ n ≥ (N₀ N₁ N₂ tn / td) ^ N`, a passing closing record
  `∑ F(a, b) ≥ N₀ N₁ N₂ tn / td`, for the index face `faceN` (Gibbs per row).

Part of milestone M0 of `ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`.
-/

namespace Outerplanar.SqMulti

open Finset

/-! ### The core functions as finite sums -/

theorem sumN_eq (n : ℕ) (f : ℕ → ℕ) : sumN n f = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumN, ih, Finset.sum_range_succ]

theorem prodN_eq (n : ℕ) (f : ℕ → ℕ) : prodN n f = ∏ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [prodN, ih, Finset.prod_range_succ]

theorem allN_iff {n : ℕ} {p : ℕ → Bool} : allN n p = true ↔ ∀ i < n, p i = true := by
  induction n with
  | zero => simp [allN]
  | succ n ih =>
    rw [allN, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · exact h1 i h
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

theorem lall_iff {α : Type} {p : α → Bool} {l : List α} :
    lall p l = true ↔ ∀ x ∈ l, p x = true := by
  induction l with
  | nil => simp [lall]
  | cons x l ih => simp [lall, ih]

theorem lsum_map_cast {α : Type} (l : List α) (f : α → ℕ) :
    ((lsum (l.map f) : ℕ) : ℝ) = (l.map fun x => (f x : ℝ)).sum := by
  induction l with
  | nil => simp [lsum]
  | cons x l ih => simp [lsum, ih]

theorem lprod_map_cast {α : Type} (l : List α) (f : α → ℕ) :
    ((lprod (l.map f) : ℕ) : ℝ) = (l.map fun x => (f x : ℝ)).prod := by
  induction l with
  | nil => simp [lprod]
  | cons x l ih => simp [lprod, ih]

/-- A sum over the nine cells as a double sum over indices. -/
theorem sum_range9 (F : ℕ → ℝ) :
    ∑ c ∈ range 9, F c = ∑ x : Fin 3, ∑ y : Fin 3, F (3 * x.val + y.val) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Fin.sum_univ_three]
  norm_num
  ring

/-! ### Indices -/

/-- An index from a number. -/
def f3 (n : ℕ) : Fin 3 := ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩

/-- The bijection with number `sg`. -/
def p6 (sg : ℕ) (x : Fin 3) : Fin 3 := f3 (permN sg x.val)

theorem permN_lt : ∀ sg : Fin 6, ∀ x : Fin 3, permN sg.val x.val < 3 := by decide +kernel

theorem p6_val {sg : ℕ} (hsg : sg < 6) (x : Fin 3) : (p6 sg x).val = permN sg x.val :=
  Nat.mod_eq_of_lt (permN_lt ⟨sg, hsg⟩ x)

theorem p6_inj : ∀ sg : Fin 6, Function.Injective (p6 sg.val) := by decide +kernel

theorem p6_bij {sg : ℕ} (hsg : sg < 6) : Function.Bijective (p6 sg) :=
  ⟨p6_inj ⟨sg, hsg⟩, Finite.injective_iff_surjective.mp (p6_inj ⟨sg, hsg⟩)⟩

theorem cell_div (x y : Fin 3) : (3 * x.val + y.val) / 3 = x.val := by omega

theorem cell_mod (x y : Fin 3) : (3 * x.val + y.val) % 3 = y.val := by omega

theorem onPerm_cell {sg : ℕ} (hsg : sg < 6) (x y : Fin 3) :
    onPerm sg (3 * x.val + y.val) = decide (y = p6 sg x) := by
  unfold onPerm
  rw [cell_div, cell_mod]
  by_cases h : y = p6 sg x
  · subst h
    simp [p6_val hsg]
  · have h' : y.val ≠ permN sg x.val := fun e => h (Fin.ext (by rw [e, p6_val hsg]))
    simp [h, h']

/-- The equal colours of the edge `j` of a pattern code, as a matrix. -/
def edgeE (pat j : ℕ) : BMat := fun x y => eqc pat j (3 * x.val + y.val)

theorem compatB_iff {pat e sg : ℕ} (hsg : sg < 6) (h : compatB pat e sg = true) :
    Compat (p6 sg) (edgeE pat e) := by
  refine ⟨p6_inj ⟨sg, hsg⟩, fun x y hxy => ?_⟩
  have h1 := allN_iff.mp h (3 * x.val + y.val) (by omega)
  rw [onPerm_cell hsg] at h1
  simp only [edgeE] at hxy
  simp only [hxy, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h1
  exact h1.symm

/-- The sum over the matched family of `σ`: the cells off `σ`. -/
theorem sum_fam {σ : Fin 3 → Fin 3} (hσ : Function.Bijective σ) (g : Fin 3 → Fin 3 → ℝ) :
    ∑ x, ∑ y, (if y = σ x then 0 else g x y) = ∑ k, g (gp σ k).1 (gp σ k).2 := by
  have h1 := sum_colPair hσ g
  rw [Fintype.sum_sum_type] at h1
  have h2 : ∑ x, ∑ y, (if y = σ x then 0 else g x y) = ∑ x, ∑ y, g x y - ∑ x, g x (σ x) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_erase_add _ _ (mem_univ (σ x))]
    rw [← Finset.sum_erase_add _ _ (mem_univ (σ x))]
    simp only [ite_true]
    rw [Finset.sum_congr rfl fun y hy => ite_eq_right (Finset.ne_of_mem_erase hy)]
    ring
  rw [h2, ← h1]
  simp only [colPair]
  ring

/-! ### The classes -/

/-- The table `w` with equal colours `E` is in the class `md` with scale `N`. -/
structure EdgeOK (md : Mode) (E : BMat) (w : Fin 3 → Fin 3 → ℝ) (N : ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ w x y
  fl : 0 < md.fl.1 → ∀ x y, E x y = false → (md.fl.1 : ℝ) / md.fl.2 * N ≤ w x y
  bij : 0 < md.bij.1 → ∀ σ : Fin 3 → Fin 3, Function.Bijective σ → (∀ x, E x (σ x) = false) →
    (md.bij.1 : ℝ) / md.bij.2 * N ^ 3 ≤ ∏ x, w x (σ x)
  hx : 0 < md.hx.1 → ∀ σ, Compat σ E → (md.hx.1 : ℝ) / md.hx.2 * N ^ 6 ≤
    ∏ k, w (gp σ k).1 (gp σ k).2
  ball : 0 < md.ball.1 → IdxBall E w ((md.ball.1 : ℝ) / md.ball.2 * N)


/-! ### The ball class against a law in a total-variation ball -/

theorem gp_fam {σ : Fin 3 → Fin 3} (hσ : Function.Bijective σ) {a b : Fin 3} (h : b ≠ σ a) :
    ∃ k, gp σ k = (a, b) := by
  obtain ⟨b', rfl⟩ := hσ.2 b
  have hab : a ≠ b' := fun e => h (by rw [e])
  obtain ⟨k, hk⟩ := offPair_surj a b' hab
  exact ⟨k, by simp [gp, hk]⟩

theorem gp_good {σ : Fin 3 → Fin 3} {E : BMat} (hσ : Compat σ E) (k : Fin 6) :
    E (gp σ k).1 (gp σ k).2 = false := by
  cases h : E (gp σ k).1 (gp σ k).2
  · rfl
  · exact absurd (hσ.1 (hσ.2 _ _ h)) (offPair_ne k)

theorem pos_of_pow_le {A x : ℝ} {n : ℕ} (hA : 0 < A) (hn : n ≠ 0) (hx : 0 ≤ x) {R : ℝ}
    (_hR : 0 ≤ R) (h : A ^ 600 ≤ R * x ^ n) : 0 < x := by
  rcases hx.eq_or_lt with h0 | h0
  · rw [← h0, zero_pow hn, mul_zero] at h
    exact absurd h (not_le.mpr (pow_pos hA _))
  · exact h0

/-- The ball inequalities in logarithms. -/
theorem ballAt_log {σ : Fin 3 → Fin 3} {E : BMat} (hσ : Compat σ E) {w : Fin 3 → Fin 3 → ℝ}
    (hw : ∀ x y, 0 ≤ w x y) {A : ℝ} (hA : 0 < A) (hb : IdxBallAt σ E w A) :
    (∀ k, 0 < w (gp σ k).1 (gp σ k).2) ∧ (∀ c d, E c d = false → 0 < w c d) ∧
    ∀ k c d, E c d = false → 600 * Real.log A ≤
      100 * ∑ k', Real.log (w (gp σ k').1 (gp σ k').2)
        - 9 * Real.log (w (gp σ k).1 (gp σ k).2) + 9 * Real.log (w c d) := by
  have hP : ∀ k, 0 ≤ ∏ k' ∈ univ.erase k, w (gp σ k').1 (gp σ k').2 := fun k =>
    prod_nonneg fun _ _ => hw _ _
  have hcell : ∀ c d, E c d = false → 0 < w c d := fun c d hcd => by
    have h := hb 0 c d hcd
    exact pos_of_pow_le hA (by norm_num) (hw c d)
      (mul_nonneg (pow_nonneg (hP 0) _) (pow_nonneg (hw _ _) _)) h
  have hfam : ∀ k, 0 < w (gp σ k).1 (gp σ k).2 := fun k => hcell _ _ (gp_good hσ k)
  refine ⟨hfam, hcell, fun k c d hcd => ?_⟩
  have h := hb k c d hcd
  have hprod : 0 < ∏ k' ∈ univ.erase k, w (gp σ k').1 (gp σ k').2 :=
    prod_pos fun k' _ => hfam k'
  have hl := Real.log_le_log (pow_pos hA _) h
  have h1 : (∏ k' ∈ univ.erase k, w (gp σ k').1 (gp σ k').2) ^ 100 ≠ 0 :=
    pow_ne_zero _ hprod.ne'
  have h2 : w (gp σ k).1 (gp σ k).2 ^ 91 ≠ 0 := pow_ne_zero _ (hfam k).ne'
  have h3 : w c d ^ 9 ≠ 0 := pow_ne_zero _ (hcell c d hcd).ne'
  rw [Real.log_pow, Real.log_mul (mul_ne_zero h1 h2) h3, Real.log_mul h1 h2, Real.log_pow,
    Real.log_pow, Real.log_pow, Real.log_prod (fun k' _ => (hfam k').ne')] at hl
  rw [← Finset.add_sum_erase _ _ (mem_univ k)]
  push_cast at hl
  linarith

/-- **The ball class against a law within total variation `3/200` of the uniform law on a
matched family**: `y` is the (unnormalised) law, `λ` its mass. -/
theorem ball_tv {E : BMat} {σ : Fin 3 → Fin 3} (hσ : Compat σ E) (hσb : Function.Bijective σ)
    {w : Fin 3 → Fin 3 → ℝ} (hw : ∀ x y, 0 ≤ w x y) {A : ℝ} (hA : 0 < A)
    (hb : IdxBallAt σ E w A) (y : Fin 3 → Fin 3 → ℝ) (hy : ∀ a b, 0 ≤ y a b)
    (hyE : ∀ a b, E a b = true → y a b = 0)
    (htv : 200 * ∑ a, ∑ b, (if b = σ a then 6 * y a b
      else max (6 * y a b - ∑ a', ∑ b', y a' b') 0) ≤ 18 * ∑ a, ∑ b, y a b) :
    (∑ a, ∑ b, y a b) * Real.log A ≤ ∑ a, ∑ b, y a b * Real.log (w a b) := by
  obtain ⟨hfam, hcell, hlog⟩ := ballAt_log hσ hw hA hb
  set lam := ∑ a, ∑ b, y a b with hlam
  have hlam0 : 0 ≤ lam := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hy a b
  set S := ∑ k, Real.log (w (gp σ k).1 (gp σ k).2) with hS
  set l : Fin 3 → Fin 3 → ℝ := fun a b => Real.log (w a b) with hl
  -- the uniform law on the family, the excess and the deficit
  set u : Fin 3 → Fin 3 → ℝ := fun a b => if b = σ a then 0 else lam / 6 with hu
  set dp : Fin 3 → Fin 3 → ℝ := fun a b => max (y a b - u a b) 0 with hdp
  set dm : Fin 3 → Fin 3 → ℝ := fun a b => max (u a b - y a b) 0 with hdm
  have hsplit : ∀ a b, y a b = u a b + dp a b - dm a b := fun a b => by
    simp only [hdp, hdm]
    rcases le_total (y a b) (u a b) with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have hdp0 : ∀ a b, 0 ≤ dp a b := fun a b => le_max_right _ _
  have hdm0 : ∀ a b, 0 ≤ dm a b := fun a b => le_max_right _ _
  have hsumu : ∑ a, ∑ b, u a b = lam := by
    rw [hu, sum_fam hσb fun _ _ => lam / 6]
    simp
    ring
  have hsumul : ∑ a, ∑ b, u a b * l a b = lam / 6 * S := by
    have : ∀ a b, u a b * l a b = if b = σ a then 0 else lam / 6 * l a b := fun a b => by
      simp only [hu]; split_ifs <;> ring
    simp only [this]
    rw [sum_fam hσb, hS, Finset.mul_sum]
  set P := ∑ a, ∑ b, dp a b with hP
  have hsumdm : ∑ a, ∑ b, dm a b = P := by
    have h1 : ∑ a, ∑ b, y a b = ∑ a, ∑ b, u a b + ∑ a, ∑ b, dp a b - ∑ a, ∑ b, dm a b := by
      simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hsplit a b
    rw [hsumu, ← hlam] at h1
    linarith
  -- the total-variation test
  have htvP : 1200 * P ≤ 18 * lam := by
    have e : ∀ a b, (if b = σ a then 6 * y a b else max (6 * y a b - lam) 0) = 6 * dp a b :=
      fun a b => by
        simp only [hdp, hu]
        split_ifs
        · rw [sub_zero, max_eq_left (hy a b)]
        · rw [show 6 * y a b - lam = 6 * (y a b - lam / 6) by ring]
          rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 6), mul_zero]
    simp only [e, ← Finset.mul_sum] at htv
    rw [hP]
    linarith
  -- the hexagon part of the ball inequalities
  have hS6 : 6 * Real.log A ≤ S := by
    have := hlog 0 _ _ (gp_good hσ 0)
    linarith
  -- excess against deficit
  set β := (600 * Real.log A - 100 * S) / 9 with hβ
  have hpair : ∀ a b a' b', dp a b * dm a' b' * β ≤ dp a b * dm a' b' * (l a b - l a' b') := by
    intro a b a' b'
    rcases (hdp0 a b).eq_or_lt with h1 | h1
    · rw [← h1]; simp
    rcases (hdm0 a' b').eq_or_lt with h2 | h2
    · rw [← h2]; simp
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg h1.le h2.le)
    have hyu' : y a' b' < u a' b' := by
      by_contra hc
      simp only [hdm] at h2
      rw [max_eq_right (by linarith)] at h2
      exact lt_irrefl _ h2
    have hfa : b' ≠ σ a' := fun e => by
      simp only [hu, e, ite_true] at hyu'
      linarith [hy a' (σ a')]
    obtain ⟨k, hk⟩ := gp_fam hσb hfa
    have hyu : u a b < y a b := by
      by_contra hc
      simp only [hdp] at h1
      rw [max_eq_right (by linarith)] at h1
      exact lt_irrefl _ h1
    have hy0 : 0 < y a b := by
      have : 0 ≤ u a b := by
        simp only [hu]
        split_ifs
        · exact le_rfl
        · exact div_nonneg hlam0 (by norm_num)
      linarith
    have hE : E a b = false := by
      cases h : E a b
      · rfl
      · rw [hyE a b h] at hy0; exact absurd hy0 (lt_irrefl _)
    have := hlog k a b hE
    rw [hk] at this
    simp only [hl, hβ]
    linarith
  have hcross : P * (∑ a, ∑ b, dp a b * l a b - ∑ a, ∑ b, dm a b * l a b) ≥ P * P * β := by
    have e1 : P * (∑ a, ∑ b, dp a b * l a b - ∑ a, ∑ b, dm a b * l a b)
        = ∑ a, ∑ b, ∑ a', ∑ b', dp a b * dm a' b' * (l a b - l a' b') := by
      have : ∀ a b, ∑ a', ∑ b', dp a b * dm a' b' * (l a b - l a' b')
          = dp a b * l a b * P - dp a b * ∑ a', ∑ b', dm a' b' * l a' b' := by
        intro a b
        rw [← hsumdm, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun b' _ => by ring
      calc P * (∑ a, ∑ b, dp a b * l a b - ∑ a, ∑ b, dm a b * l a b)
          = (∑ a, ∑ b, dp a b * l a b) * P
            - (∑ a, ∑ b, dp a b) * ∑ a', ∑ b', dm a' b' * l a' b' := by rw [← hP]; ring
        _ = ∑ a, ∑ b, (dp a b * l a b * P - dp a b * ∑ a', ∑ b', dm a' b' * l a' b') := by
          simp only [Finset.sum_sub_distrib, Finset.sum_mul]
        _ = _ := (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => this a b).symm
    have e2 : P * P * β = ∑ a, ∑ b, ∑ a', ∑ b', dp a b * dm a' b' * β := by
      have : ∀ a b, ∑ a', ∑ b', dp a b * dm a' b' * β = dp a b * P * β := by
        intro a b
        rw [← hsumdm, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
      calc P * P * β = (∑ a, ∑ b, dp a b) * P * β := by rw [← hP]
        _ = ∑ a, ∑ b, dp a b * P * β := by simp only [Finset.sum_mul]
        _ = _ := (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => this a b).symm
    rw [e1, e2]
    exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
      Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ => hpair a b a' b'
  have hdl : P * β ≤ ∑ a, ∑ b, dp a b * l a b - ∑ a, ∑ b, dm a b * l a b := by
    rcases (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hdp0 a b :
        (0 : ℝ) ≤ P).eq_or_lt with h0 | h0
    · -- no excess: the law is uniform
      have hz : ∀ a b, dp a b = 0 := fun a b => by
        have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun a _ =>
          Finset.sum_nonneg fun b _ => hdp0 a b).mp h0.symm a (mem_univ a)
        exact (Finset.sum_eq_zero_iff_of_nonneg fun b _ => hdp0 a b).mp h1 b (mem_univ b)
      have hz' : ∀ a b, dm a b = 0 := fun a b => by
        have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun a _ =>
          Finset.sum_nonneg fun b _ => hdm0 a b).mp (hsumdm.trans h0.symm) a (mem_univ a)
        exact (Finset.sum_eq_zero_iff_of_nonneg fun b _ => hdm0 a b).mp h1 b (mem_univ b)
      have hP0' : P = 0 := by rw [hP]; simp [hz]
      rw [hP0']
      simp [hz, hz']
    · have := hcross
      nlinarith
  have hyl : ∑ a, ∑ b, y a b * l a b = lam / 6 * S + (∑ a, ∑ b, dp a b * l a b
      - ∑ a, ∑ b, dm a b * l a b) := by
    rw [← hsumul]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      rw [hsplit a b]; ring
  show lam * Real.log A ≤ ∑ a, ∑ b, y a b * l a b
  rw [hyl]
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hdp0 a b
  have key : lam * Real.log A ≤ lam / 6 * S + P * β := by
    rw [hβ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hS6) (by linarith : (0 : ℝ) ≤ 18 * lam - 1200 * P)]
  linarith

/-! ### One piece -/

/-- The value of the table of edge `j` on the cell `c`. -/
def wc (w : ℕ → Fin 3 → Fin 3 → ℝ) (j c : ℕ) : ℝ := w j (f3 (c / 3)) (f3 (c % 3))

theorem f3_val (x : Fin 3) : f3 x.val = x := Fin.ext (Nat.mod_eq_of_lt x.isLt)

theorem wc_cell (w : ℕ → Fin 3 → Fin 3 → ℝ) (j : ℕ) (x y : Fin 3) :
    wc w j (3 * x.val + y.val) = w j x y := by
  simp only [wc, cell_div, cell_mod, f3_val]

theorem cell_f3 {c : ℕ} (hc : c < 9) : 3 * (f3 (c / 3)).val + (f3 (c % 3)).val = c := by
  simp only [f3]
  omega

theorem dig_cast_sub (a b : ℕ) : ((a - b : ℕ) : ℝ) = max ((a : ℝ) - b) 0 := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h, max_eq_left (by simp [h])]
  · rw [Nat.sub_eq_zero_of_le h, max_eq_right (by simp [h])]
    simp

theorem log_ge_of_le {A N x : ℝ} (hA : 0 < A) (hN : 0 < N) (h : A * N ≤ x) :
    Real.log A + Real.log N ≤ Real.log x := by
  rw [← Real.log_mul hA.ne' hN.ne']
  exact Real.log_le_log (mul_pos hA hN) h

theorem natdiv_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : (0 : ℝ) < (a : ℝ) / b := by
  have : (0 : ℝ) < a := by exact_mod_cast ha
  have : (0 : ℝ) < b := by exact_mod_cast hb
  positivity

theorem log_natdiv {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Real.log ((a : ℝ) / b) = Real.log a - Real.log b :=
  Real.log_div (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')

theorem cell_cases {c : ℕ} (hc : c < 9) : ∃ x y : Fin 3, c = 3 * x.val + y.val :=
  ⟨f3 (c / 3), f3 (c % 3), (cell_f3 hc).symm⟩

theorem prod_pos_of_ge {ι : Type*} {s : Finset ι} {f : ι → ℝ} {B : ℝ} (hB : 0 < B)
    (hf : ∀ i ∈ s, 0 ≤ f i) (h : B ≤ ∏ i ∈ s, f i) : ∀ i ∈ s, 0 < f i := by
  intro i hi
  rcases (hf i hi).eq_or_lt with h0 | h0
  · have : ∏ i ∈ s, f i = 0 := Finset.prod_eq_zero hi h0.symm
    linarith
  · exact h0

theorem log_prod_ge {ι : Type*} {s : Finset ι} {f : ι → ℝ} {c N : ℝ} {n : ℕ} (hc : 0 < c)
    (hN : 0 < N) (hf : ∀ i ∈ s, 0 ≤ f i) (h : c * N ^ n ≤ ∏ i ∈ s, f i) :
    Real.log c + n * Real.log N ≤ ∑ i ∈ s, Real.log (f i) := by
  have hpos := prod_pos_of_ge (by positivity) hf h
  rw [← Real.log_prod (fun i hi => (hpos i hi).ne'), ← Real.log_pow,
    ← Real.log_mul hc.ne' (by positivity)]
  exact Real.log_le_log (by positivity) h

/-- **One piece, on its edge.** -/
theorem piece_edge {md : ℕ → Mode} {pat : ℕ} {w : ℕ → Fin 3 → Fin 3 → ℝ} {N : ℕ → ℝ}
    {p : ℕ × ℕ × ℕ × ℕ} (hp : pieceOK md pat p = true) (hN : 0 < N p.1)
    (hE : EdgeOK (md p.1) (edgeE pat p.1) (w p.1) (N p.1)) :
    (∀ c < 9, 0 < contrib p p.1 c → 0 < wc w p.1 c) ∧
    (∑ c ∈ range 9, (contrib p p.1 c : ℝ)) * Real.log (N p.1)
        + expo p * (Real.log (pconst md p).1 - Real.log (pconst md p).2)
      ≤ ∑ c ∈ range 9, (contrib p p.1 c : ℝ) * Real.log (wc w p.1 c) := by
  obtain ⟨e, kind, sg, v⟩ := p
  simp only [pieceOK, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨-, hp⟩ := hp
  simp only at hN hE ⊢
  have hcontrib : ∀ c, contrib (e, kind, sg, v) e c = if kind = 0 then (if c = sg then v else 0)
      else if kind = 1 then (if onPerm sg c then v else 0)
      else if kind = 2 then (if onPerm sg c then 0 else v) else dig WB v c := fun c => by
    simp [contrib]
  by_cases h0 : kind = 0
  · -- a floor
    subst h0
    have hc0 : ∀ c, contrib (e, 0, sg, v) e c = if c = sg then v else 0 := fun c => by
      simp [contrib]
    simp only [hc0]
    simp only [ite_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hp
    obtain ⟨⟨⟨hsg, heq⟩, hfl⟩, hfl2⟩ := hp
    have hw : ((md e).fl.1 : ℝ) / (md e).fl.2 * N e ≤ wc w e sg :=
      hE.fl hfl (f3 (sg / 3)) (f3 (sg % 3)) (by simp only [edgeE, cell_f3 hsg]; exact heq)
    have hpos : 0 < wc w e sg := lt_of_lt_of_le (mul_pos (natdiv_pos hfl hfl2) hN) hw
    refine ⟨fun c hc h => ?_, ?_⟩
    · split_ifs at h with hcs
      · rw [hcs]; exact hpos
      · exact absurd h (lt_irrefl 0)
    · have e1 : ∀ F : ℕ → ℝ, ∑ c ∈ range 9, (((if c = sg then v else 0 : ℕ) : ℝ) * F c)
          = v * F sg := fun F => by
        simp only [Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul]
        rw [Finset.sum_ite_eq' (range 9) sg, ite_eq_left (mem_range.mpr hsg)]
      have e2 : ∑ c ∈ range 9, (((if c = sg then v else 0 : ℕ) : ℝ)) = v := by
        simpa using e1 fun _ => 1
      rw [e1, e2]
      simp only [expo, pconst, ite_eq_right (by norm_num : (0 : ℕ) ≠ 3), ite_true]
      have := log_ge_of_le (natdiv_pos hfl hfl2) hN hw
      rw [log_natdiv hfl hfl2] at this
      have hv : (0 : ℝ) ≤ v := Nat.cast_nonneg v
      nlinarith
  by_cases h1 : kind = 1
  · -- a bijection
    subst h1
    rw [ite_eq_right (by decide), ite_eq_left rfl] at hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨⟨⟨hsg, hprop⟩, hb1⟩, hb2⟩ := hp
    have hc1 : ∀ c, contrib (e, 1, sg, v) e c = if onPerm sg c then v else 0 := fun c => by
      simp [contrib]
    simp only [hc1]
    have hprop' : ∀ x, edgeE pat e x (p6 sg x) = false := fun x => by
      have := allN_iff.mp hprop x.val x.isLt
      simp only [edgeE, p6_val hsg]
      simpa using this
    have hw := hE.bij hb1 (p6 sg) (p6_bij hsg) hprop'
    have hpos := prod_pos_of_ge (mul_pos (natdiv_pos hb1 hb2) (pow_pos hN 3))
      (fun x _ => hE.nonneg x _) hw
    refine ⟨fun c hc h => ?_, ?_⟩
    · obtain ⟨x, y, rfl⟩ := cell_cases hc
      rw [onPerm_cell hsg] at h
      rw [wc_cell]
      split_ifs at h with hxy
      · rw [of_decide_eq_true hxy]; exact hpos x (mem_univ x)
      · exact absurd h (lt_irrefl 0)
    · have e1 : ∀ F : Fin 3 → Fin 3 → ℝ, ∑ c ∈ range 9,
          (((if onPerm sg c then v else 0 : ℕ) : ℝ) * F (f3 (c / 3)) (f3 (c % 3)))
          = v * ∑ x, F x (p6 sg x) := fun F => by
        rw [sum_range9]
        simp only [onPerm_cell hsg, cell_div, cell_mod, f3_val, decide_eq_true_eq, Nat.cast_ite,
          Nat.cast_zero, ite_mul, zero_mul, Finset.sum_ite_eq', mem_univ, ite_true,
          Finset.mul_sum]
      have e2 := e1 fun _ _ => 1
      simp only [mul_one, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at e2
      rw [e2, show ∑ c ∈ range 9, ((if onPerm sg c = true then v else 0 : ℕ) : ℝ)
        * Real.log (wc w e c) = _ from e1 fun x y => Real.log (w e x y)]
      simp only [expo, pconst, ite_eq_right (by norm_num : (1 : ℕ) ≠ 3),
        ite_eq_right (by norm_num : (1 : ℕ) ≠ 0),
        ite_true]
      have := log_prod_ge (natdiv_pos hb1 hb2) hN (fun x _ => hE.nonneg x _) hw
      rw [log_natdiv hb1 hb2] at this
      have hv : (0 : ℝ) ≤ v := Nat.cast_nonneg v
      push_cast at this ⊢
      nlinarith [mul_le_mul_of_nonneg_left this hv]
  by_cases h2 : kind = 2
  · -- a matched six-family
    subst h2
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl] at hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨⟨⟨hsg, hcomp⟩, hh1⟩, hh2⟩ := hp
    have hc2 : ∀ c, contrib (e, 2, sg, v) e c = if onPerm sg c then 0 else v := fun c => by
      simp [contrib]
    simp only [hc2]
    have hw := hE.hx hh1 (p6 sg) (compatB_iff hsg hcomp)
    have hpos := prod_pos_of_ge (mul_pos (natdiv_pos hh1 hh2) (pow_pos hN 6))
      (fun k _ => hE.nonneg _ _) hw
    refine ⟨fun c hc h => ?_, ?_⟩
    · obtain ⟨x, y, rfl⟩ := cell_cases hc
      rw [onPerm_cell hsg] at h
      rw [wc_cell]
      split_ifs at h with hxy
      · exact absurd h (lt_irrefl 0)
      · obtain ⟨k, hk⟩ := gp_fam (p6_bij hsg) (by simpa using hxy)
        have := hpos k (mem_univ k)
        rwa [hk] at this
    · have e1 : ∀ F : Fin 3 → Fin 3 → ℝ, ∑ c ∈ range 9,
          (((if onPerm sg c then 0 else v : ℕ) : ℝ) * F (f3 (c / 3)) (f3 (c % 3)))
          = v * ∑ k, F (gp (p6 sg) k).1 (gp (p6 sg) k).2 := fun F => by
        rw [sum_range9]
        simp only [onPerm_cell hsg, cell_div, cell_mod, f3_val, decide_eq_true_eq, Nat.cast_ite,
          Nat.cast_zero, ite_mul, zero_mul]
        rw [sum_fam (p6_bij hsg) fun x y => (v : ℝ) * F x y, Finset.mul_sum]
      have e2 := e1 fun _ _ => 1
      simp only [mul_one, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at e2
      rw [e2, show ∑ c ∈ range 9, ((if onPerm sg c = true then 0 else v : ℕ) : ℝ)
        * Real.log (wc w e c) = _ from e1 fun x y => Real.log (w e x y)]
      simp only [expo, pconst, ite_eq_right (by norm_num : (2 : ℕ) ≠ 3),
        ite_eq_right (by norm_num : (2 : ℕ) ≠ 0),
        ite_eq_right (by norm_num : (2 : ℕ) ≠ 1), ite_true]
      have := log_prod_ge (natdiv_pos hh1 hh2) hN (fun k _ => hE.nonneg _ _) hw
      rw [log_natdiv hh1 hh2] at this
      have hv : (0 : ℝ) ≤ v := Nat.cast_nonneg v
      push_cast at this ⊢
      nlinarith [mul_le_mul_of_nonneg_left this hv]
  -- a ball piece
  rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2] at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨⟨⟨⟨h3, hsg⟩, hcomp⟩, hzero⟩, htv⟩, ha1⟩, ha2⟩ := hp
  subst h3
  have hc3 : ∀ c, contrib (e, 3, sg, v) e c = dig WB v c := fun c => by simp [contrib]
  simp only [hc3]
  set y : Fin 3 → Fin 3 → ℝ := fun a b => (dig WB v (3 * a.val + b.val) : ℝ) with hy
  have hyE : ∀ a b, edgeE pat e a b = true → y a b = 0 := fun a b h => by
    have := allN_iff.mp hzero (3 * a.val + b.val) (by omega)
    simp only [edgeE] at h
    simp only [h, Bool.not_true, Bool.false_or, beq_iff_eq] at this
    simp [hy, this]
  have hA : 0 < ((md e).ball.1 : ℝ) / (md e).ball.2 * N e := mul_pos (natdiv_pos ha1 ha2) hN
  have hb := hE.ball ha1 (p6 sg) (compatB_iff hsg hcomp)
  have hlam : ((sumN 9 (dig WB v) : ℕ) : ℝ) = ∑ a, ∑ b, y a b := by
    rw [sumN_eq, Nat.cast_sum, sum_range9]
  have htv' : 200 * ∑ a, ∑ b, (if b = p6 sg a then 6 * y a b
      else max (6 * y a b - ∑ a', ∑ b', y a' b') 0) ≤ 18 * ∑ a, ∑ b, y a b := by
    have h := htv
    simp only [tvOK, decide_eq_true_eq] at h
    have h' : ((200 * sumN 9 (fun c => if onPerm sg c = true then 6 * dig WB v c
        else 6 * dig WB v c - sumN 9 (dig WB v)) : ℕ) : ℝ)
        ≤ ((18 * sumN 9 (dig WB v) : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_mul, hlam, sumN_eq, Nat.cast_sum, sum_range9] at h'
    simp only [onPerm_cell hsg, decide_eq_true_eq, Nat.cast_ite, dig_cast_sub, Nat.cast_mul,
      hlam] at h'
    convert h' using 2
  have key := ball_tv (compatB_iff hsg hcomp) (p6_bij hsg) (hE.nonneg) hA hb y
    (fun a b => Nat.cast_nonneg _) hyE htv'
  obtain ⟨-, hcell, -⟩ := ballAt_log (compatB_iff hsg hcomp) hE.nonneg hA hb
  refine ⟨fun c hc h => ?_, ?_⟩
  · obtain ⟨x, x', rfl⟩ := cell_cases hc
    rw [wc_cell]
    apply hcell
    cases hq : edgeE pat e x x'
    · rfl
    · have := hyE x x' hq
      simp only [hy] at this
      have h0 : dig WB v (3 * x.val + x'.val) = 0 := by exact_mod_cast this
      omega
  · have e1 : ∀ F : Fin 3 → Fin 3 → ℝ, ∑ c ∈ range 9,
        ((dig WB v c : ℕ) : ℝ) * F (f3 (c / 3)) (f3 (c % 3)) = ∑ a, ∑ b, y a b * F a b :=
      fun F => by
        rw [sum_range9]
        simp only [cell_div, cell_mod, f3_val, hy]
    have e2 : ∑ c ∈ range 9, ((dig WB v c : ℕ) : ℝ) = ∑ a, ∑ b, y a b := by
      simpa using e1 fun _ _ => 1
    rw [e2, show ∑ c ∈ range 9, ((dig WB v c : ℕ) : ℝ) * Real.log (wc w e c) = _ from
      e1 fun a b => Real.log (w e a b)]
    simp only [expo, pconst, ite_eq_right (by norm_num : (3 : ℕ) ≠ 0),
        ite_eq_right (by norm_num : (3 : ℕ) ≠ 1),
      ite_eq_right (by norm_num : (3 : ℕ) ≠ 2), ite_true]
    rw [hlam]
    rw [Real.log_mul (natdiv_pos ha1 ha2).ne' hN.ne', log_natdiv ha1 ha2] at key
    linarith

theorem contrib_off {p : ℕ × ℕ × ℕ × ℕ} {j : ℕ} (h : j ≠ p.1) (c : ℕ) : contrib p j c = 0 := by
  simp [contrib, Ne.symm h]

/-- **One piece, on all edges.** -/
theorem piece_all {md : ℕ → Mode} {pat : ℕ} {w : ℕ → Fin 3 → Fin 3 → ℝ} {N : ℕ → ℝ}
    {p : ℕ × ℕ × ℕ × ℕ} (hp : pieceOK md pat p = true) (hN : ∀ j < 3, 0 < N j)
    (hE : ∀ j < 3, EdgeOK (md j) (edgeE pat j) (w j) (N j)) :
    (∀ j < 3, ∀ c < 9, 0 < contrib p j c → 0 < wc w j c) ∧
    ∑ j ∈ range 3, (∑ c ∈ range 9, (contrib p j c : ℝ)) * Real.log (N j)
        + expo p * (Real.log (pconst md p).1 - Real.log (pconst md p).2)
      ≤ ∑ j ∈ range 3, ∑ c ∈ range 9, (contrib p j c : ℝ) * Real.log (wc w j c) := by
  have he : p.1 < 3 := by
    simp only [pieceOK, Bool.and_eq_true, decide_eq_true_eq] at hp
    exact hp.1
  obtain ⟨h1, h2⟩ := piece_edge hp (hN _ he) (hE _ he)
  refine ⟨fun j hj c hc h => ?_, ?_⟩
  · by_cases hje : j = p.1
    · subst hje; exact h1 c hc h
    · rw [contrib_off hje] at h; exact absurd h (lt_irrefl 0)
  · have z1 : ∀ j ∈ range 3, j ≠ p.1 →
        (∑ c ∈ range 9, (contrib p j c : ℝ)) * Real.log (N j) = 0 := fun j _ hj => by
      simp [contrib_off hj]
    have z2 : ∀ j ∈ range 3, j ≠ p.1 →
        ∑ c ∈ range 9, (contrib p j c : ℝ) * Real.log (wc w j c) = 0 := fun j _ hj => by
      simp [contrib_off hj]
    rw [Finset.sum_eq_single_of_mem _ (mem_range.mpr he) z1,
      Finset.sum_eq_single_of_mem _ (mem_range.mpr he) z2]
    exact h2

/-- **The pieces of a valid list**: positivity where they put weight, and the bound
`∑ M log w ≥ ∑ (∑ M) log N + log num - log den`. -/
theorem pieces_bound {md : ℕ → Mode} {pat : ℕ} {w : ℕ → Fin 3 → Fin 3 → ℝ} {N : ℕ → ℝ}
    (hN : ∀ j < 3, 0 < N j) (hE : ∀ j < 3, EdgeOK (md j) (edgeE pat j) (w j) (N j)) :
    ∀ ps : List (ℕ × ℕ × ℕ × ℕ), lall (pieceOK md pat) ps = true →
    0 < (pnum md ps : ℝ) ∧ 0 < (pden md ps : ℝ) ∧
    (∀ j < 3, ∀ c < 9, 0 < pmarg ps j c → 0 < wc w j c) ∧
    ∑ j ∈ range 3, (∑ c ∈ range 9, (pmarg ps j c : ℝ)) * Real.log (N j)
        + (Real.log (pnum md ps) - Real.log (pden md ps))
      ≤ ∑ j ∈ range 3, ∑ c ∈ range 9, (pmarg ps j c : ℝ) * Real.log (wc w j c)
  | [], _ => by simp [pnum, pden, pmarg, lprod, lsum]
  | p :: ps, h => by
    simp only [lall, Bool.and_eq_true] at h
    obtain ⟨ih1, ih2, ih3, ih4⟩ := pieces_bound hN hE ps h.2
    obtain ⟨q3, q4⟩ := piece_all h.1 hN hE
    have hp1 : pieceOK md pat p = true := h.1
    have hcpos : 0 < (pconst md p).1 ∧ 0 < (pconst md p).2 := by
      obtain ⟨e, kind, sg, v⟩ := p
      simp only [pieceOK, Bool.and_eq_true, decide_eq_true_eq] at hp1
      simp only [pconst]
      split_ifs at hp1 ⊢ <;> simp_all
    have en : pnum md (p :: ps) = (pconst md p).1 ^ expo p * pnum md ps := by
      simp [pnum, lprod]
    have ed : pden md (p :: ps) = (pconst md p).2 ^ expo p * pden md ps := by
      simp [pden, lprod]
    have em : ∀ j c, pmarg (p :: ps) j c = contrib p j c + pmarg ps j c := fun j c => by
      simp [pmarg, lsum]
    have hc1 : (0 : ℝ) < (pconst md p).1 := by exact_mod_cast hcpos.1
    have hc2 : (0 : ℝ) < (pconst md p).2 := by exact_mod_cast hcpos.2
    refine ⟨?_, ?_, fun j hj c hc hpos => ?_, ?_⟩
    · rw [en]; push_cast; positivity
    · rw [ed]; push_cast; positivity
    · rw [em] at hpos
      rcases Nat.eq_zero_or_pos (contrib p j c) with h0 | h0
      · rw [h0, zero_add] at hpos; exact ih3 j hj c hc hpos
      · exact q3 j hj c hc h0
    · rw [en, ed]
      push_cast
      rw [Real.log_mul (by positivity) ih1.ne', Real.log_mul (by positivity) ih2.ne',
        Real.log_pow, Real.log_pow]
      simp only [em]
      push_cast
      simp only [add_mul, Finset.sum_add_distrib]
      linarith

/-! ### The walk law against the pieces -/

/-- **The walks of a law against the pieces of its marginals.** -/
theorem walks_bound {md : ℕ → Mode} {pat : ℕ} {w : ℕ → Fin 3 → Fin 3 → ℝ} {N : ℕ → ℝ}
    (hN : ∀ j < 3, 0 < N j) (hE : ∀ j < 3, EdgeOK (md j) (edgeE pat j) (w j) (N j))
    {ps : List (ℕ × ℕ × ℕ × ℕ)} (hps : lall (pieceOK md pat) ps = true) (s : Finset (ℕ × ℕ))
    (f : ℕ × ℕ → ℕ) (cell : ℕ → ℕ × ℕ → ℕ) (hcell : ∀ j < 3, ∀ x ∈ s, cell j x < 9)
    (hmarg : ∀ j < 3, ∀ c < 9, ∑ x ∈ s, (if cell j x = c then f x else 0) = pmarg ps j c) :
    0 < (pnum md ps : ℝ) ∧ 0 < (pden md ps : ℝ) ∧
    (∀ x ∈ s, 0 < f x → ∀ j < 3, 0 < wc w j (cell j x)) ∧
    ∑ j ∈ range 3, (∑ x ∈ s, (f x : ℝ)) * Real.log (N j)
        + (Real.log (pnum md ps) - Real.log (pden md ps))
      ≤ ∑ x ∈ s, (f x : ℝ) * ∑ j ∈ range 3, Real.log (wc w j (cell j x)) := by
  obtain ⟨h1, h2, h3, h4⟩ := pieces_bound hN hE ps hps
  have hmargR : ∀ j < 3, ∀ c < 9,
      (pmarg ps j c : ℝ) = ∑ x ∈ s, if cell j x = c then (f x : ℝ) else 0 := fun j hj c hc => by
    rw [← hmarg j hj c hc]
    push_cast
    rfl
  refine ⟨h1, h2, fun x hx hfx j hj => ?_, ?_⟩
  · have hc := hcell j hj x hx
    apply h3 j hj _ hc
    rw [← hmarg j hj _ hc]
    exact lt_of_lt_of_le (by simpa using hfx)
      (Finset.single_le_sum (f := fun x' => if cell j x' = cell j x then f x' else 0)
        (fun _ _ => Nat.zero_le _) hx)
  · have hsumc : ∀ j < 3, ∑ c ∈ range 9, (pmarg ps j c : ℝ) = ∑ x ∈ s, (f x : ℝ) := fun j hj => by
      rw [Finset.sum_congr rfl fun c hc => hmargR j hj c (mem_range.mp hc), Finset.sum_comm]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.sum_ite_eq, ite_eq_left (mem_range.mpr (hcell j hj x hx))]
    have hsuml : ∀ j < 3, ∑ c ∈ range 9, (pmarg ps j c : ℝ) * Real.log (wc w j c)
        = ∑ x ∈ s, (f x : ℝ) * Real.log (wc w j (cell j x)) := fun j hj => by
      rw [Finset.sum_congr rfl fun c hc => by rw [hmargR j hj c (mem_range.mp hc)]]
      simp only [Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.sum_ite_eq, ite_eq_left (mem_range.mpr (hcell j hj x hx))]
    rw [Finset.sum_congr rfl fun j hj => by rw [hsumc j (mem_range.mp hj)]] at h4
    rw [Finset.sum_congr rfl fun j hj => hsuml j (mem_range.mp hj), Finset.sum_comm] at h4
    simpa only [Finset.mul_sum] using h4

/-! ### The index face and rooted records -/

/-- The product of the three tables along the walk `q` of the row `(a, b)`. -/
def tW (w : ℕ → Fin 3 → Fin 3 → ℝ) (a q b : ℕ) : ℝ :=
  wc w 0 (cellOf 0 a q b) * wc w 1 (cellOf 1 a q b) * wc w 2 (cellOf 2 a q b)

/-- The face of the square in index form: the sum over the legal walks with root pair `(a, b)`. -/
def faceN (pat : ℕ) (w : ℕ → Fin 3 → Fin 3 → ℝ) (a b : ℕ) : ℝ :=
  ∑ q ∈ range 9, if legal pat a (q / 3) (q % 3) b = true then tW w a q b else 0

theorem cellOf_lt {j a q b : ℕ} (ha : a < 3) (hq : q < 9) (hb : b < 3) : cellOf j a q b < 9 := by
  unfold cellOf
  split_ifs <;> omega

theorem tW_log {w : ℕ → Fin 3 → Fin 3 → ℝ} {a q b : ℕ}
    (h : ∀ j < 3, 0 < wc w j (cellOf j a q b)) :
    0 < tW w a q b ∧
      Real.log (tW w a q b) = ∑ j ∈ range 3, Real.log (wc w j (cellOf j a q b)) := by
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  refine ⟨by unfold tW; positivity, ?_⟩
  unfold tW
  rw [Real.log_mul (by positivity) h2.ne', Real.log_mul h0.ne' h1.ne']
  simp [Finset.sum_range_succ]

theorem tW_nonneg {w : ℕ → Fin 3 → Fin 3 → ℝ} (hw : ∀ j < 3, ∀ x y, 0 ≤ w j x y)
    (a q b : ℕ) : 0 ≤ tW w a q b := by
  unfold tW wc
  have := hw 0 (by norm_num) (f3 (cellOf 0 a q b / 3)) (f3 (cellOf 0 a q b % 3))
  have := hw 1 (by norm_num) (f3 (cellOf 1 a q b / 3)) (f3 (cellOf 1 a q b % 3))
  have := hw 2 (by norm_num) (f3 (cellOf 2 a q b / 3)) (f3 (cellOf 2 a q b % 3))
  positivity

/-- **Gibbs on one row**: a law `k` on the walks of the row `(a, b)`, of mass `D`, bounds the
face from below. -/
theorem row_gibbs {pat : ℕ} {w : ℕ → Fin 3 → Fin 3 → ℝ} (hw : ∀ j < 3, ∀ x y, 0 ≤ w j x y)
    {a b D : ℕ} (hD : 0 < D) (kq : ℕ → ℕ) (hsum : ∑ q ∈ range 9, kq q = D)
    (hleg : ∀ q < 9, 0 < kq q → legal pat a (q / 3) (q % 3) b = true)
    (hpos : ∀ q < 9, 0 < kq q → ∀ j < 3, 0 < wc w j (cellOf j a q b)) :
    0 < faceN pat w a b ∧
    ∑ q ∈ range 9, (kq q : ℝ) * (∑ j ∈ range 3, Real.log (wc w j (cellOf j a q b))
        + Real.log D - Real.log (kq q)) ≤ D * Real.log (faceN pat w a b) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  set T : ℕ → ℝ := fun q => if legal pat a (q / 3) (q % 3) b = true then tW w a q b else 0
    with hT
  have hT0 : ∀ q ∈ range 9, 0 ≤ T q := fun q _ => by
    simp only [hT]; split_ifs
    · exact tW_nonneg hw _ _ _
    · exact le_rfl
  have hTpos : ∀ q ∈ range 9, 0 < kq q → 0 < T q := fun q hq hk => by
    simp only [hT, hleg q (mem_range.mp hq) hk, ite_true]
    exact (tW_log (hpos q (mem_range.mp hq) hk)).1
  -- some walk carries weight
  obtain ⟨q₀, hq₀, hk₀⟩ : ∃ q ∈ range 9, 0 < kq q := by
    by_contra hne
    have : ∑ q ∈ range 9, kq q = 0 := Finset.sum_eq_zero fun q hq => by
      by_contra h0
      exact hne ⟨q, hq, Nat.pos_of_ne_zero h0⟩
    omega
  have hF : 0 < faceN pat w a b :=
    lt_of_lt_of_le (hTpos q₀ hq₀ hk₀) (Finset.single_le_sum hT0 hq₀)
  refine ⟨hF, ?_⟩
  have hg := gibbs (range 9) (fun q => (kq q : ℝ) / D) T (fun q _ => by positivity)
    (by
      rw [← Finset.sum_div, show ((∑ q ∈ range 9, (kq q : ℝ))) = D by exact_mod_cast hsum]
      exact div_self hDr.ne')
    (fun q hq hp => hTpos q hq (by
      have : (0 : ℝ) < kq q := by
        have := mul_pos hp hDr
        rwa [div_mul_cancel₀ _ hDr.ne'] at this
      exact_mod_cast this)) hT0
  have hterm : ∀ q ∈ range 9, (kq q : ℝ) * (∑ j ∈ range 3, Real.log (wc w j (cellOf j a q b))
      + Real.log D - Real.log (kq q)) = D * ((kq q : ℝ) / D * Real.log (T q / (kq q / D))) := by
    intro q hq
    rcases Nat.eq_zero_or_pos (kq q) with h0 | h0
    · simp [h0]
    · have hk : (0 : ℝ) < kq q := by exact_mod_cast h0
      have hTq := hTpos q hq h0
      have hlogT : Real.log (T q) = ∑ j ∈ range 3, Real.log (wc w j (cellOf j a q b)) := by
        simp only [hT, hleg q (mem_range.mp hq) h0, ite_true]
        exact (tW_log (hpos q (mem_range.mp hq) h0)).2
      rw [Real.log_div hTq.ne' (by positivity), Real.log_div hk.ne' hDr.ne', hlogT]
      field_simp
      ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hg hDr.le

theorem natpow_ne_zero (a n : ℕ) : ((a : ℝ) ^ (n * a)) ≠ 0 := by
  rcases Nat.eq_zero_or_pos a with h | h
  · simp [h]
  · have : (0 : ℝ) < a := by exact_mod_cast h
    positivity

theorem sum_range3 (g : ℕ → ℝ) : ∑ j ∈ range 3, g j = g 0 + g 1 + g 2 := by
  simp [Finset.sum_range_succ]

/-- **Soundness of a rooted record**: `∏ F(a, b) ^ n ≥ (N₀ N₁ N₂ tn / td) ^ N`. -/
theorem checkR_sound {md : ℕ → Mode} {pat D : ℕ} {rows : List (ℕ × ℕ × ℕ)} {k : ℕ}
    {ps : List (ℕ × ℕ × ℕ × ℕ)} {tn td : ℕ} (h : checkR md pat D rows k ps tn td = true)
    {w : ℕ → Fin 3 → Fin 3 → ℝ} {N : ℕ → ℝ} (hN : ∀ j < 3, 0 < N j)
    (hE : ∀ j < 3, EdgeOK (md j) (edgeE pat j) (w j) (N j)) :
    (N 0 * N 1 * N 2 * tn / td) ^ rTot rows
      ≤ ∏ i ∈ range rows.length, faceN pat w (rA rows i) (rB rows i) ^ rN rows i := by
  simp only [checkR, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hD, htn⟩, htd⟩, hrows⟩, hps⟩, hmarg⟩, hent⟩ := h
  set R := rows.length with hR
  have hrow : ∀ i < R, rA rows i < 3 ∧ rB rows i < 3 ∧ 0 < rN rows i ∧
      ∑ q ∈ range 9, kk k i q = D ∧ ∀ q < 9, 0 < kk k i q →
        legal pat (rA rows i) (q / 3) (q % 3) (rB rows i) = true := fun i hi => by
    have := allN_iff.mp hrows i hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := this
    refine ⟨h1, h2, h3, by rw [← sumN_eq]; exact h4, fun q hq hk => ?_⟩
    have := allN_iff.mp h5 q hq
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    exact this.resolve_left (by omega)
  have hw : ∀ j < 3, ∀ x y, 0 ≤ w j x y := fun j hj => (hE j hj).nonneg
  set s : Finset (ℕ × ℕ) := range R ×ˢ range 9 with hs
  set f : ℕ × ℕ → ℕ := fun x => rN rows x.1 * kk k x.1 x.2 with hf
  set cell : ℕ → ℕ × ℕ → ℕ := fun j x => cellOf j (rA rows x.1) x.2 (rB rows x.1) with hcelldef
  have hcell : ∀ j < 3, ∀ x ∈ s, cell j x < 9 := fun j _ x hx => by
    obtain ⟨hi, hq⟩ := mem_product.mp hx
    obtain ⟨ha, hb, -⟩ := hrow x.1 (mem_range.mp hi)
    exact cellOf_lt ha (mem_range.mp hq) hb
  have hmarg' : ∀ j < 3, ∀ c < 9, ∑ x ∈ s, (if cell j x = c then f x else 0) = pmarg ps j c := by
    intro j hj c hc
    have := allN_iff.mp (allN_iff.mp hmarg j hj) c hc
    simp only [beq_iff_eq] at this
    rw [← this, wmargR, sumN_eq, hs, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sumN_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [hcelldef, hf, mul_ite, mul_zero]
  obtain ⟨hnum, hden, hpos, hbound⟩ := walks_bound hN hE hps s f cell hcell hmarg'
  -- Gibbs on each row
  have hg : ∀ i < R, 0 < faceN pat w (rA rows i) (rB rows i) ∧
      ∑ q ∈ range 9, (kk k i q : ℝ) * (∑ j ∈ range 3,
        Real.log (wc w j (cellOf j (rA rows i) q (rB rows i))) + Real.log D - Real.log (kk k i q))
        ≤ D * Real.log (faceN pat w (rA rows i) (rB rows i)) := fun i hi => by
    obtain ⟨-, -, hn, hsum, hleg⟩ := hrow i hi
    refine row_gibbs hw hD (kk k i) hsum hleg fun q hq hk j hj => ?_
    exact hpos (i, q) (mem_product.mpr ⟨mem_range.mpr hi, mem_range.mpr hq⟩)
      (Nat.mul_pos hn hk) j hj
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  -- the total mass
  have hmass : ∑ x ∈ s, (f x : ℝ) = rTot rows * D := by
    rw [hs, Finset.sum_product, rTot, sumN_eq, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hf, Nat.cast_mul]
    rw [← Finset.mul_sum, ← Nat.cast_sum, (hrow i (mem_range.mp hi)).2.2.2.1]
  -- the rows together
  have hsumrows : ∑ x ∈ s, (f x : ℝ) * ∑ j ∈ range 3, Real.log (wc w j (cell j x))
      + (∑ x ∈ s, (f x : ℝ)) * Real.log D - ∑ x ∈ s, (f x : ℝ) * Real.log (kk k x.1 x.2)
      ≤ D * ∑ i ∈ range R, (rN rows i : ℝ) * Real.log (faceN pat w (rA rows i) (rB rows i)) := by
    have e : ∑ x ∈ s, (f x : ℝ) * ∑ j ∈ range 3, Real.log (wc w j (cell j x))
        + (∑ x ∈ s, (f x : ℝ)) * Real.log D - ∑ x ∈ s, (f x : ℝ) * Real.log (kk k x.1 x.2)
        = ∑ i ∈ range R, (rN rows i : ℝ) * ∑ q ∈ range 9, (kk k i q : ℝ) * (∑ j ∈ range 3,
          Real.log (wc w j (cellOf j (rA rows i) q (rB rows i))) + Real.log D
            - Real.log (kk k i q)) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, hs,
        Finset.sum_product]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [hf, hcelldef, Nat.cast_mul]
      ring
    rw [e, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hn : (0 : ℝ) ≤ rN rows i := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left (hg i (mem_range.mp hi)).2 hn
    linarith
  -- the entropy check, in logarithms
  have hentR : (rTot rows * D : ℝ) * Real.log tn
      + ∑ x ∈ s, (f x : ℝ) * Real.log (kk k x.1 x.2) + Real.log (pden md ps)
      ≤ (rTot rows * D : ℝ) * (Real.log td + Real.log D) + Real.log (pnum md ps) := by
    have h' : ((tn ^ (rTot rows * D) * prodN R (fun i => prodN 9 fun q =>
        kk k i q ^ (rN rows i * kk k i q)) * pden md ps : ℕ) : ℝ)
        ≤ ((td ^ (rTot rows * D) * D ^ (rTot rows * D) * pnum md ps : ℕ) : ℝ) := by
      exact_mod_cast hent
    have htnr : (0 : ℝ) < tn := by exact_mod_cast htn
    have htdr : (0 : ℝ) < td := by exact_mod_cast htd
    simp only [prodN_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_prod] at h'
    have hP : 0 < ∏ i ∈ range R, ∏ q ∈ range 9, (kk k i q : ℝ) ^ (rN rows i * kk k i q) :=
      Finset.prod_pos fun i _ => Finset.prod_pos fun q _ => by
        rcases Nat.eq_zero_or_pos (kk k i q) with h0 | h0
        · simp [h0]
        · have : (0 : ℝ) < kk k i q := by exact_mod_cast h0
          positivity
    have hl := Real.log_le_log (by positivity) h'
    rw [Real.log_mul (by positivity) hden.ne', Real.log_mul (by positivity) hP.ne',
      Real.log_mul (by positivity) hnum.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_prod (fun i _ =>
        (Finset.prod_pos fun q _ => by
          rcases Nat.eq_zero_or_pos (kk k i q) with h0 | h0
          · simp [h0]
          · have : (0 : ℝ) < kk k i q := by exact_mod_cast h0
            positivity).ne')] at hl
    simp only [Real.log_prod (fun q _ => natpow_ne_zero _ _), Real.log_pow] at hl
    have e : ∑ x ∈ s, (f x : ℝ) * Real.log (kk k x.1 x.2)
        = ∑ i ∈ range R, ∑ q ∈ range 9, ((rN rows i * kk k i q : ℕ) : ℝ) * Real.log (kk k i q) := by
      rw [hs, Finset.sum_product]
    rw [e]
    push_cast at hl ⊢
    linarith
  -- assembly
  have hfin : (rTot rows : ℝ) * (Real.log (N 0) + Real.log (N 1) + Real.log (N 2)
      + Real.log tn - Real.log td)
      ≤ ∑ i ∈ range R, (rN rows i : ℝ) * Real.log (faceN pat w (rA rows i) (rB rows i)) := by
    rw [hmass, sum_range3] at hbound
    rw [hmass] at hsumrows
    have key : D * ((rTot rows : ℝ) * (Real.log (N 0) + Real.log (N 1) + Real.log (N 2)
        + Real.log tn - Real.log td))
        ≤ D * ∑ i ∈ range R, (rN rows i : ℝ) * Real.log (faceN pat w (rA rows i) (rB rows i)) := by
      nlinarith
    exact le_of_mul_le_mul_left key hDr
  have hN0 := hN 0 (by norm_num)
  have hN1 := hN 1 (by norm_num)
  have hN2 := hN 2 (by norm_num)
  have htnr : (0 : ℝ) < tn := by exact_mod_cast htn
  have htdr : (0 : ℝ) < td := by exact_mod_cast htd
  have hFpos : 0 < ∏ i ∈ range R, faceN pat w (rA rows i) (rB rows i) ^ rN rows i :=
    Finset.prod_pos fun i hi => pow_pos (hg i (mem_range.mp hi)).1 _
  rw [← Real.log_le_log_iff (by positivity) hFpos, Real.log_pow,
    Real.log_prod (fun i hi => (pow_pos (hg i (mem_range.mp hi)).1 _).ne'),
    Real.log_div (by positivity) htdr.ne', Real.log_mul (by positivity) htnr.ne',
    Real.log_mul (by positivity) hN2.ne', Real.log_mul hN0.ne' hN1.ne']
  simp only [Real.log_pow]
  linarith

/-! ### Closing records -/

/-- **Soundness of a closing record**: `∑ F(a, b) ≥ N₀ N₁ N₂ tn / td`, the sum over the root
pairs `i = 3 a + b` without equal colours. -/
theorem checkC_sound {md : ℕ → Mode} {pat D k : ℕ} {ps : List (ℕ × ℕ × ℕ × ℕ)} {tn td : ℕ}
    (h : checkC md pat D k ps tn td = true) {w : ℕ → Fin 3 → Fin 3 → ℝ} {N : ℕ → ℝ}
    (hN : ∀ j < 3, 0 < N j) (hE : ∀ j < 3, EdgeOK (md j) (edgeE pat j) (w j) (N j)) :
    N 0 * N 1 * N 2 * tn / td
      ≤ ∑ i ∈ range 9, if eqc pat 3 i = true then 0 else faceN pat w (i / 3) (i % 3) := by
  simp only [checkC, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hD, htn⟩, htd⟩, hleg⟩, hsum⟩, hps⟩, hmarg⟩, hent⟩ := h
  have hw : ∀ j < 3, ∀ x y, 0 ≤ w j x y := fun j hj => (hE j hj).nonneg
  set s : Finset (ℕ × ℕ) := range 9 ×ˢ range 9 with hs
  set f : ℕ × ℕ → ℕ := fun x => kk k x.1 x.2 with hf
  set cell : ℕ → ℕ × ℕ → ℕ := fun j x => cellOf j (x.1 / 3) x.2 (x.1 % 3) with hcelldef
  have hcell : ∀ j < 3, ∀ x ∈ s, cell j x < 9 := fun j _ x hx => by
    obtain ⟨hi, hq⟩ := mem_product.mp hx
    exact cellOf_lt (by have := mem_range.mp hi; omega) (mem_range.mp hq)
      (Nat.mod_lt _ (by norm_num))
  have hmarg' : ∀ j < 3, ∀ c < 9, ∑ x ∈ s, (if cell j x = c then f x else 0) = pmarg ps j c := by
    intro j hj c hc
    have := allN_iff.mp (allN_iff.mp hmarg j hj) c hc
    simp only [beq_iff_eq] at this
    rw [← this, wmargC, sumN_eq, hs, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sumN_eq]
  obtain ⟨hnum, hden, hpos, hbound⟩ := walks_bound hN hE hps s f cell hcell hmarg'
  have hlegal : ∀ x ∈ s, 0 < f x →
      legal pat (x.1 / 3) (x.2 / 3) (x.2 % 3) (x.1 % 3) = true ∧ eqc pat 3 x.1 = false := by
    intro x hx hfx
    obtain ⟨hi, hq⟩ := mem_product.mp hx
    have := allN_iff.mp (allN_iff.mp hleg x.1 (mem_range.mp hi)) x.2 (mem_range.mp hq)
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true'] at this
    exact this.resolve_left (by simp only [hf] at hfx; omega)
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  set T : ℕ × ℕ → ℝ := fun x => if legal pat (x.1 / 3) (x.2 / 3) (x.2 % 3) (x.1 % 3) = true ∧
    eqc pat 3 x.1 = false then tW w (x.1 / 3) x.2 (x.1 % 3) else 0 with hT
  have hT0 : ∀ x ∈ s, 0 ≤ T x := fun x _ => by
    simp only [hT]; split_ifs
    · exact tW_nonneg hw _ _ _
    · exact le_rfl
  have hTpos : ∀ x ∈ s, 0 < f x → 0 < T x := fun x hx hk => by
    simp only [hT, hlegal x hx hk, and_self, ite_true]
    exact (tW_log fun j hj => hpos x hx hk j hj).1
  have hsumT : ∑ x ∈ s, T x
      = ∑ i ∈ range 9, if eqc pat 3 i = true then 0 else faceN pat w (i / 3) (i % 3) := by
    rw [hs, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases he : eqc pat 3 i = true
    · simp [hT, he]
    · simp only [he, Bool.false_eq_true, ite_false, faceN, hT]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp
  have hmass : ∑ x ∈ s, (f x : ℝ) = D := by
    rw [hs, Finset.sum_product]
    simp only [hf]
    rw [← hsum, sumN_eq]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sumN_eq]
    push_cast
    rfl
  have hg := gibbs s (fun x => (f x : ℝ) / D) T (fun x _ => by positivity)
    (by rw [← Finset.sum_div, hmass]; exact div_self hDr.ne')
    (fun x hx hp => hTpos x hx (by
      have : (0 : ℝ) < f x := by
        have := mul_pos hp hDr
        rwa [div_mul_cancel₀ _ hDr.ne'] at this
      exact_mod_cast this)) hT0
  obtain ⟨x₀, hx₀, hk₀⟩ : ∃ x ∈ s, 0 < f x := by
    by_contra hne
    have : ∑ x ∈ s, (f x : ℝ) = 0 := Finset.sum_eq_zero fun x hx => by
      by_contra h0
      exact hne ⟨x, hx, by exact_mod_cast Nat.pos_of_ne_zero (by exact_mod_cast h0)⟩
    rw [hmass] at this
    exact hDr.ne' this
  have hC : 0 < ∑ x ∈ s, T x := lt_of_lt_of_le (hTpos x₀ hx₀ hk₀) (Finset.single_le_sum hT0 hx₀)
  have hterm : ∀ x ∈ s, (f x : ℝ) * (∑ j ∈ range 3, Real.log (wc w j (cell j x))
      + Real.log D - Real.log (f x)) = D * ((f x : ℝ) / D * Real.log (T x / (f x / D))) := by
    intro x hx
    rcases Nat.eq_zero_or_pos (f x) with h0 | h0
    · simp [h0]
    · have hk : (0 : ℝ) < f x := by exact_mod_cast h0
      have hTq := hTpos x hx h0
      have hlogT : Real.log (T x) = ∑ j ∈ range 3, Real.log (wc w j (cell j x)) := by
        simp only [hT, hlegal x hx h0, and_self, ite_true]
        exact (tW_log fun j hj => hpos x hx h0 j hj).2
      rw [Real.log_div hTq.ne' (by positivity), Real.log_div hk.ne' hDr.ne', hlogT]
      field_simp
      ring
  have hrows : ∑ x ∈ s, (f x : ℝ) * ∑ j ∈ range 3, Real.log (wc w j (cell j x))
      + (∑ x ∈ s, (f x : ℝ)) * Real.log D - ∑ x ∈ s, (f x : ℝ) * Real.log (f x)
      ≤ D * Real.log (∑ x ∈ s, T x) := by
    have e : ∑ x ∈ s, (f x : ℝ) * ∑ j ∈ range 3, Real.log (wc w j (cell j x))
        + (∑ x ∈ s, (f x : ℝ)) * Real.log D - ∑ x ∈ s, (f x : ℝ) * Real.log (f x)
        = ∑ x ∈ s, (f x : ℝ) * (∑ j ∈ range 3, Real.log (wc w j (cell j x))
          + Real.log D - Real.log (f x)) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [e, Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hg hDr.le
  have hentR : (D : ℝ) * Real.log tn + ∑ x ∈ s, (f x : ℝ) * Real.log (f x)
      + Real.log (pden md ps) ≤ (D : ℝ) * (Real.log td + Real.log D) + Real.log (pnum md ps) := by
    have h' : ((tn ^ D * prodN 9 (fun i => prodN 9 fun q => kk k i q ^ kk k i q)
        * pden md ps : ℕ) : ℝ) ≤ ((td ^ D * D ^ D * pnum md ps : ℕ) : ℝ) := by
      exact_mod_cast hent
    have htnr : (0 : ℝ) < tn := by exact_mod_cast htn
    have htdr : (0 : ℝ) < td := by exact_mod_cast htd
    simp only [prodN_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_prod] at h'
    have hq : ∀ i q, ((kk k i q : ℝ) ^ kk k i q) ≠ 0 := fun i q => by
      simp
    have hP : 0 < ∏ i ∈ range 9, ∏ q ∈ range 9, (kk k i q : ℝ) ^ kk k i q :=
      Finset.prod_pos fun i _ => Finset.prod_pos fun q _ =>
        lt_of_le_of_ne (by positivity) (hq i q).symm
    have hl := Real.log_le_log (by positivity) h'
    rw [Real.log_mul (by positivity) hden.ne', Real.log_mul (by positivity) hP.ne',
      Real.log_mul (by positivity) hnum.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_prod (fun i _ =>
        (Finset.prod_pos fun q _ => lt_of_le_of_ne (by positivity) (hq i q).symm).ne')] at hl
    simp only [Real.log_prod (fun q _ => hq _ q), Real.log_pow] at hl
    have e : ∑ x ∈ s, (f x : ℝ) * Real.log (f x)
        = ∑ i ∈ range 9, ∑ q ∈ range 9, (kk k i q : ℝ) * Real.log (kk k i q) := by
      rw [hs, Finset.sum_product]
    rw [e]
    linarith
  rw [hmass, sum_range3] at hbound
  rw [hmass] at hrows
  have hN0 := hN 0 (by norm_num)
  have hN1 := hN 1 (by norm_num)
  have hN2 := hN 2 (by norm_num)
  have htnr : (0 : ℝ) < tn := by exact_mod_cast htn
  have htdr : (0 : ℝ) < td := by exact_mod_cast htd
  have key : D * (Real.log (N 0) + Real.log (N 1) + Real.log (N 2) + Real.log tn - Real.log td)
      ≤ D * Real.log (∑ x ∈ s, T x) := by nlinarith
  have key' := le_of_mul_le_mul_left key hDr
  rw [← hsumT, ← Real.log_le_log_iff (by positivity) hC, Real.log_div (by positivity) htdr.ne',
    Real.log_mul (by positivity) htnr.ne', Real.log_mul (by positivity) hN2.ne',
    Real.log_mul hN0.ne' hN1.ne']
  linarith

end Outerplanar.SqMulti
