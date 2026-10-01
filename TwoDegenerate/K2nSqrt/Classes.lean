/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import TwoDegenerate.K2nSqrt.Analytic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Class AM–GM for `K₂,ₙ`

Fix hub lists `A`, `B` of size `k` and right lists `T w ⊆ A ∪ B` of size `k`. Split the hub-colour
pairs `A × B` by where the two colours lie: `I = A ∩ B`, `P = A \ B`, `Q = B \ A`, with `|I| = r`
and `|P| = |Q| = s = k - r`. The four classes are

* `D`: `(a, a)` with `a ∈ I` (`r` pairs);
* `O`: `(a, b)` with `a ≠ b` in `I` (`r (r - 1)` pairs);
* `M`: `I × Q` and `P × I` (`2 r s` pairs);
* `PQ`: `P × Q` (`s²` pairs).

On each class, AM–GM bounds the sum of `∏_w |T w \ {a, b}|` below by the class size times the
exponential of the mean of `∑_w log |T w \ {a, b}|` (`card_mul_exp_mean_le`). That mean is exact in
the per-list counts `i = |T w ∩ I|`, `j = |T w ∩ P|`, `l = |T w ∩ Q|` (`sum_log_cross`,
`sum_log_diag`, `sum_log_offDiag`), because `log |T \ {a, b}|` is `log k - ℓ (χ a + χ b) - δ χ a χ b`
with `ℓ = log (k / (k - 1))` and `δ = log ((k - 1)² / (k (k - 2)))` (`log_card_sdiff_pair`).
-/

namespace SimpleGraph.TwoDegenerate.K2nSqrt

open Finset Real

/-! ### AM–GM on a class -/

/-- AM–GM in exponential form: `|c| · exp (mean of log g) ≤ ∑ g`. -/
theorem card_mul_exp_mean_le {α : Type*} (c : Finset α) (g : α → ℝ) (hg : ∀ p ∈ c, 0 < g p) :
    (c.card : ℝ) * exp ((∑ p ∈ c, log (g p)) / c.card) ≤ ∑ p ∈ c, g p := by
  rcases c.eq_empty_or_nonempty with rfl | hne
  · simp
  have hc : (0 : ℝ) < c.card := by exact_mod_cast hne.card_pos
  have hJ := convexOn_exp.map_sum_le (t := c) (w := fun _ => (c.card : ℝ)⁻¹)
    (p := fun p => log (g p)) (fun _ _ => by positivity)
    (by rw [sum_const, nsmul_eq_mul]; field_simp) (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hJ
  rw [← mul_sum, ← mul_sum, sum_congr rfl fun p hp => exp_log (hg p hp)] at hJ
  rw [div_eq_inv_mul]
  calc (c.card : ℝ) * exp ((c.card : ℝ)⁻¹ * ∑ p ∈ c, log (g p))
      ≤ (c.card : ℝ) * ((c.card : ℝ)⁻¹ * ∑ p ∈ c, g p) := mul_le_mul_of_nonneg_left hJ hc.le
    _ = ∑ p ∈ c, g p := by field_simp

/-- Two-point AM–GM: `e^a + e^b ≥ 2 e^{(a+b)/2}`. -/
theorem two_mul_exp_mid_le (a b : ℝ) : 2 * exp ((a + b) / 2) ≤ exp a + exp b := by
  have h1 : exp a = exp (a / 2) ^ 2 := by rw [← exp_nat_mul]; ring_nf
  have h2 : exp b = exp (b / 2) ^ 2 := by rw [← exp_nat_mul]; ring_nf
  have h3 : exp ((a + b) / 2) = exp (a / 2) * exp (b / 2) := by rw [← exp_add]; ring_nf
  rw [h1, h2, h3]
  nlinarith [sq_nonneg (exp (a / 2) - exp (b / 2))]

/-! ### The per-pair logarithm -/

/-- Membership as `0` or `1`. -/
noncomputable def ind (T : Finset ℕ) (a : ℕ) : ℝ := if a ∈ T then 1 else 0

/-- `ℓ = log k - log (k - 1)`. -/
noncomputable def ell (k : ℕ) : ℝ := log k - log ((k : ℝ) - 1)

/-- `δ = 2 log (k - 1) - log k - log (k - 2)`. -/
noncomputable def del (k : ℕ) : ℝ := 2 * log ((k : ℝ) - 1) - log k - log ((k : ℝ) - 2)

theorem ind_mem (T : Finset ℕ) {a : ℕ} (h : a ∈ T) : ind T a = 1 := ite_eq_left h

theorem ind_not_mem (T : Finset ℕ) {a : ℕ} (h : a ∉ T) : ind T a = 0 := ite_eq_right h

theorem ind_mul_self (T : Finset ℕ) (a : ℕ) : ind T a * ind T a = ind T a := by
  unfold ind; split_ifs <;> norm_num

theorem sum_ind (X T : Finset ℕ) : ∑ a ∈ X, ind T a = ((X ∩ T).card : ℝ) := by
  simp only [ind]
  rw [sum_boole, filter_mem_eq_inter]

theorem card_sdiff_pair_real {k : ℕ} {T : Finset ℕ} (hT : T.card = k) {a b : ℕ} (hab : a ≠ b) :
    ((T \ {a, b}).card : ℝ) = k - (ind T a + ind T b) := by
  have h1 := card_sdiff_add_card_inter T {a, b}
  have h2 : T ∩ {a, b} = ({a, b} : Finset ℕ).filter (· ∈ T) := by
    ext x; simp only [mem_inter, mem_filter]; tauto
  rw [h2, card_filter, sum_pair hab, hT] at h1
  have h3 : ((T \ {a, b}).card : ℝ) + ((if a ∈ T then 1 else 0 : ℕ) : ℝ) +
      ((if b ∈ T then 1 else 0 : ℕ) : ℝ) = k := by
    rw [← h1]; push_cast; ring
  simp only [ind]
  split_ifs at h3 ⊢ <;> push_cast at h3 <;> linarith

theorem card_sdiff_single_real {k : ℕ} {T : Finset ℕ} (hT : T.card = k) (a : ℕ) :
    ((T \ {a, a}).card : ℝ) = k - ind T a := by
  rw [insert_eq_of_mem (mem_singleton_self a)]
  have h1 := card_sdiff_add_card_inter T {a}
  have h2 : T ∩ {a} = ({a} : Finset ℕ).filter (· ∈ T) := by
    ext x; simp only [mem_inter, mem_filter]; tauto
  rw [h2, card_filter, sum_singleton, hT] at h1
  have h3 : ((T \ {a}).card : ℝ) + ((if a ∈ T then 1 else 0 : ℕ) : ℝ) = k := by
    rw [← h1]; push_cast; ring
  simp only [ind]
  split_ifs at h3 ⊢ <;> push_cast at h3 <;> linarith

theorem log_card_sdiff_pair {k : ℕ} {T : Finset ℕ} (hT : T.card = k) {a b : ℕ} (hab : a ≠ b) :
    log ((T \ {a, b}).card : ℝ) =
      log k - ell k * (ind T a + ind T b) - del k * (ind T a * ind T b) := by
  rw [card_sdiff_pair_real hT hab]
  simp only [ind, ell, del]
  split_ifs <;> ring_nf

theorem log_card_sdiff_single {k : ℕ} {T : Finset ℕ} (hT : T.card = k) (a : ℕ) :
    log ((T \ {a, a}).card : ℝ) = log k - ell k * ind T a := by
  rw [card_sdiff_single_real hT a]
  simp only [ind, ell]
  split_ifs <;> ring_nf

/-! ### Class sums of the logarithm -/

/-- The logarithm summed over `X × Y` for disjoint `X`, `Y`. -/
theorem sum_log_cross {k : ℕ} {T X Y : Finset ℕ} (hT : T.card = k) (hXY : Disjoint X Y) :
    ∑ a ∈ X, ∑ b ∈ Y, log ((T \ {a, b}).card : ℝ) =
      X.card * Y.card * log k -
        ell k * ((X ∩ T).card * Y.card + X.card * (Y ∩ T).card) -
        del k * ((X ∩ T).card * (Y ∩ T).card) := by
  have hne : ∀ a ∈ X, ∀ b ∈ Y, a ≠ b := fun a ha b hb h =>
    disjoint_left.mp hXY ha (h ▸ hb)
  rw [sum_congr rfl fun a ha => sum_congr rfl fun b hb => log_card_sdiff_pair hT (hne a ha b hb)]
  have inner : ∀ a, ∑ b ∈ Y, (log k - ell k * (ind T a + ind T b) - del k * (ind T a * ind T b)) =
      Y.card * log k - ell k * (Y.card * ind T a + (Y ∩ T).card) -
        del k * (ind T a * (Y ∩ T).card) := by
    intro a
    rw [sum_sub_distrib, sum_sub_distrib, sum_const, ← mul_sum, ← mul_sum, sum_add_distrib,
      sum_const, ← mul_sum, sum_ind, nsmul_eq_mul, nsmul_eq_mul]
  rw [sum_congr rfl fun a _ => inner a, sum_sub_distrib, sum_sub_distrib, sum_const,
    ← mul_sum, ← mul_sum, sum_add_distrib, ← mul_sum, sum_const, ← sum_mul, sum_ind,
    nsmul_eq_mul, nsmul_eq_mul]
  ring

/-- The logarithm summed over the diagonal of `X`. -/
theorem sum_log_diag {k : ℕ} {T X : Finset ℕ} (hT : T.card = k) :
    ∑ a ∈ X, log ((T \ {a, a}).card : ℝ) = X.card * log k - ell k * (X ∩ T).card := by
  rw [sum_congr rfl fun a _ => log_card_sdiff_single hT a, sum_sub_distrib, sum_const,
    ← mul_sum, sum_ind, nsmul_eq_mul]

/-- The logarithm summed over the off-diagonal of `X`. -/
theorem sum_log_offDiag {k : ℕ} {T X : Finset ℕ} (hT : T.card = k) :
    ∑ p ∈ X.offDiag, log ((T \ {p.1, p.2}).card : ℝ) =
      X.card * (X.card - 1) * log k - 2 * ell k * (X ∩ T).card * (X.card - 1) -
        del k * ((X ∩ T).card * ((X ∩ T).card - 1)) := by
  set g : ℕ × ℕ → ℝ := fun p =>
    log k - ell k * (ind T p.1 + ind T p.2) - del k * (ind T p.1 * ind T p.2) with hg
  have hoff : ∑ p ∈ X.offDiag, log ((T \ {p.1, p.2}).card : ℝ) = ∑ p ∈ X.offDiag, g p :=
    sum_congr rfl fun p hp => log_card_sdiff_pair hT (mem_offDiag.mp hp).2.2
  have hsplit : ∑ p ∈ X ×ˢ X, g p = ∑ p ∈ X.diag, g p + ∑ p ∈ X.offDiag, g p := by
    rw [← diag_union_offDiag, sum_union (disjoint_diag_offDiag X)]
  have hdiag : ∑ p ∈ X.diag, g p = X.card * log k - 2 * ell k * (X ∩ T).card -
      del k * (X ∩ T).card := by
    rw [diag, sum_map]
    simp only [Function.Embedding.coeFn_mk, Function.diag, hg, ind_mul_self]
    rw [sum_sub_distrib, sum_sub_distrib, sum_const, ← mul_sum, ← mul_sum, sum_add_distrib,
      sum_ind, nsmul_eq_mul]
    ring
  have hprod : ∑ p ∈ X ×ˢ X, g p = X.card * X.card * log k -
      ell k * ((X ∩ T).card * X.card + X.card * (X ∩ T).card) -
      del k * ((X ∩ T).card * (X ∩ T).card) := by
    rw [sum_product]
    simp only [hg]
    have inner : ∀ a, ∑ b ∈ X, (log k - ell k * (ind T a + ind T b) -
        del k * (ind T a * ind T b)) =
        X.card * log k - ell k * (X.card * ind T a + (X ∩ T).card) -
          del k * (ind T a * (X ∩ T).card) := by
      intro a
      rw [sum_sub_distrib, sum_sub_distrib, sum_const, ← mul_sum, ← mul_sum, sum_add_distrib,
        sum_const, ← mul_sum, sum_ind, nsmul_eq_mul, nsmul_eq_mul]
    rw [sum_congr rfl fun a _ => inner a, sum_sub_distrib, sum_sub_distrib, sum_const,
      ← mul_sum, ← mul_sum, sum_add_distrib, ← mul_sum, sum_const, ← sum_mul, sum_ind,
      nsmul_eq_mul, nsmul_eq_mul]
    ring
  rw [hoff]
  linarith

/-! ### `ℓ` and `δ` -/

theorem ell_ge {k : ℕ} (hk : 3 ≤ k) : 1 / (k : ℝ) ≤ ell k := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have h := log_le_sub_one_of_pos (div_pos (by linarith) (by linarith) : 0 < ((k : ℝ) - 1) / k)
  rw [log_div (by linarith) (by linarith)] at h
  have hk0 : (k : ℝ) ≠ 0 := by linarith
  have : ((k : ℝ) - 1) / k - 1 = -(1 / k) := by field_simp; ring
  simp only [ell]; linarith

theorem ell_pos {k : ℕ} (hk : 3 ≤ k) : 0 < ell k := by
  have := ell_ge hk
  have : (0 : ℝ) < 1 / k := div_pos one_pos (by exact_mod_cast (by omega : 0 < k))
  linarith

theorem del_nonneg {k : ℕ} (hk : 3 ≤ k) : 0 ≤ del k := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have h : 0 ≤ log (((k : ℝ) - 1) ^ 2 / (k * ((k : ℝ) - 2))) :=
    log_nonneg (by rw [le_div_iff₀ (by nlinarith)]; nlinarith)
  rw [log_div (by nlinarith) (by nlinarith), log_mul (by linarith) (by linarith), log_pow] at h
  simp only [del]; push_cast at h; linarith

theorem del_le {k : ℕ} (hk : 3 ≤ k) : del k ≤ 1 / (k * ((k : ℝ) - 2)) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (k : ℝ) - 2 ≠ 0 := by linarith
  have hk0 : (k : ℝ) ≠ 0 := by linarith
  have h := log_le_sub_one_of_pos
    (div_pos (by nlinarith) (by nlinarith) : 0 < ((k : ℝ) - 1) ^ 2 / (k * ((k : ℝ) - 2)))
  rw [log_div (by nlinarith) (by nlinarith), log_mul (by linarith) (by linarith), log_pow] at h
  have : ((k : ℝ) - 1) ^ 2 / (k * ((k : ℝ) - 2)) - 1 = 1 / (k * ((k : ℝ) - 2)) := by
    field_simp; ring
  simp only [del]; push_cast at h; linarith

/-! ### Per-list counts -/

theorem card_parts {k : ℕ} {A B T : Finset ℕ} (hTsub : T ⊆ A ∪ B) (hT : T.card = k) :
    (A ∩ B ∩ T).card + (A \ B ∩ T).card + (B \ A ∩ T).card = k := by
  have hU : T = (A ∩ B ∩ T) ∪ (A \ B ∩ T) ∪ (B \ A ∩ T) := by
    ext x
    simp only [mem_union, mem_inter, mem_sdiff]
    constructor
    · intro hx
      have := hTsub hx
      rw [mem_union] at this
      by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> tauto
    · tauto
  have d1 : Disjoint (A ∩ B ∩ T) (A \ B ∩ T) := by
    rw [disjoint_left]; intro x h1 h2; simp only [mem_inter, mem_sdiff] at h1 h2; tauto
  have d2 : Disjoint ((A ∩ B ∩ T) ∪ (A \ B ∩ T)) (B \ A ∩ T) := by
    rw [disjoint_left]; intro x h1 h2; simp only [mem_union, mem_inter, mem_sdiff] at h1 h2; tauto
  have := congr_arg Finset.card hU
  rw [card_union_of_disjoint d2, card_union_of_disjoint d1] at this
  omega

/-! ### The pair product -/

/-- `∏_w |T w \ {a, b}|`, the number of colourings of the right side for hub colours `a`, `b`. -/
noncomputable def pf {n : ℕ} (T : Fin n → Finset ℕ) (a b : ℕ) : ℝ :=
  ∏ w, ((T w \ {a, b}).card : ℝ)

theorem card_sdiff_pair_pos {k : ℕ} (hk : 3 ≤ k) {T : Finset ℕ} (hT : T.card = k) (a b : ℕ) :
    (0 : ℝ) < (T \ {a, b}).card := by
  have h1 := le_card_sdiff ({a, b} : Finset ℕ) T
  have h2 : ({a, b} : Finset ℕ).card ≤ 2 := card_le_two
  have : 0 < (T \ {a, b}).card := by omega
  exact_mod_cast this

theorem pf_pos {k n : ℕ} (hk : 3 ≤ k) {T : Fin n → Finset ℕ} (hT : ∀ w, (T w).card = k)
    (a b : ℕ) : 0 < pf T a b :=
  prod_pos fun w _ => card_sdiff_pair_pos hk (hT w) a b

theorem log_pf {k n : ℕ} (hk : 3 ≤ k) {T : Fin n → Finset ℕ} (hT : ∀ w, (T w).card = k)
    (a b : ℕ) : log (pf T a b) = ∑ w, log ((T w \ {a, b}).card : ℝ) :=
  log_prod fun w _ => (card_sdiff_pair_pos hk (hT w) a b).ne'

/-- Split `∑_{A × B}` into the five classes. -/
theorem sum_split (A B : Finset ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ a ∈ A, ∑ b ∈ B, F a b = ∑ a ∈ A ∩ B, F a a + ∑ p ∈ (A ∩ B).offDiag, F p.1 p.2 +
      ∑ a ∈ A ∩ B, ∑ b ∈ B \ A, F a b + ∑ a ∈ A \ B, ∑ b ∈ A ∩ B, F a b +
      ∑ a ∈ A \ B, ∑ b ∈ B \ A, F a b := by
  have hA : ∑ a ∈ A, ∑ b ∈ B, F a b =
      ∑ a ∈ A \ B, ∑ b ∈ B, F a b + ∑ a ∈ A ∩ B, ∑ b ∈ B, F a b := by
    conv_lhs => rw [← sdiff_union_inter A B]
    rw [sum_union (disjoint_sdiff_inter A B)]
  have hB : ∀ a, ∑ b ∈ B, F a b = ∑ b ∈ B \ A, F a b + ∑ b ∈ A ∩ B, F a b := by
    intro a
    conv_lhs => rw [← sdiff_union_inter B A]
    rw [sum_union (disjoint_sdiff_inter B A), inter_comm B A]
  have hII : ∑ a ∈ A ∩ B, ∑ b ∈ A ∩ B, F a b =
      ∑ a ∈ A ∩ B, F a a + ∑ p ∈ (A ∩ B).offDiag, F p.1 p.2 := by
    rw [← sum_product' (f := F), ← diag_union_offDiag, sum_union (disjoint_diag_offDiag _), diag,
      sum_map]
    rfl
  rw [hA, sum_congr rfl fun a _ => hB a, sum_congr rfl fun a _ => hB a, sum_add_distrib,
    sum_add_distrib, hII]
  ring

/-! ### Class bounds -/

section ClassBounds

variable {k n : ℕ} {T : Fin n → Finset ℕ}

/-- `∑_{X} ∑_{Y} log pf = ∑_w (per-list cross formula)`. -/
theorem sum_log_pf_cross (hk : 3 ≤ k) (hT : ∀ w, (T w).card = k) {X Y : Finset ℕ}
    (hXY : Disjoint X Y) :
    ∑ a ∈ X, ∑ b ∈ Y, log (pf T a b) = ∑ w, (X.card * Y.card * log k -
      ell k * ((X ∩ T w).card * Y.card + X.card * (Y ∩ T w).card) -
      del k * ((X ∩ T w).card * (Y ∩ T w).card)) := by
  simp_rw [log_pf hk hT]
  calc ∑ a ∈ X, ∑ b ∈ Y, ∑ w, log ((T w \ {a, b}).card : ℝ)
      = ∑ a ∈ X, ∑ w, ∑ b ∈ Y, log ((T w \ {a, b}).card : ℝ) :=
        sum_congr rfl fun a _ => sum_comm
    _ = ∑ w, ∑ a ∈ X, ∑ b ∈ Y, log ((T w \ {a, b}).card : ℝ) := sum_comm
    _ = _ := sum_congr rfl fun w _ => sum_log_cross (hT w) hXY

theorem sum_log_pf_diag (hk : 3 ≤ k) (hT : ∀ w, (T w).card = k) (X : Finset ℕ) :
    ∑ a ∈ X, log (pf T a a) = ∑ w, (X.card * log k - ell k * (X ∩ T w).card) := by
  simp_rw [log_pf hk hT]
  rw [sum_comm]
  exact sum_congr rfl fun w _ => sum_log_diag (hT w)

theorem sum_log_pf_offDiag (hk : 3 ≤ k) (hT : ∀ w, (T w).card = k) (X : Finset ℕ) :
    ∑ p ∈ X.offDiag, log (pf T p.1 p.2) = ∑ w, (X.card * (X.card - 1) * log k -
      2 * ell k * (X ∩ T w).card * (X.card - 1) -
      del k * ((X ∩ T w).card * ((X ∩ T w).card - 1))) := by
  simp_rw [log_pf hk hT]
  rw [sum_comm]
  exact sum_congr rfl fun w _ => sum_log_offDiag (hT w)

/-- AM–GM on a class, with any lower bound `L` for the summed logarithm. -/
theorem class_bound {α : Type*} (c : Finset α) (g : α → ℝ) (hg : ∀ p ∈ c, 0 < g p) {L m : ℝ}
    (hm : (c.card : ℝ) = m) (hL : L ≤ ∑ p ∈ c, log (g p)) :
    m * exp (L / m) ≤ ∑ p ∈ c, g p := by
  rcases eq_or_lt_of_le (Nat.cast_nonneg (α := ℝ) c.card) with h0 | hpos
  · rw [← hm, ← h0, zero_mul]
    exact sum_nonneg fun p hp => (hg p hp).le
  · rw [← hm]
    refine le_trans ?_ (card_mul_exp_mean_le c g hg)
    exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (div_le_div_of_nonneg_right hL hpos.le))
      hpos.le

end ClassBounds

/-! ### Assembly -/

theorem pow_eq_exp {k : ℕ} (hk : 3 ≤ k) (n : ℕ) :
    ((k : ℝ) - 1) ^ n = exp (n * log ((k : ℝ) - 1)) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  rw [← log_pow, exp_log (pow_pos (by linarith) n)]

theorem log_sub_one_eq (k : ℕ) : log ((k : ℝ) - 1) = log k - ell k := by simp only [ell]; ring

/-- The per-list exponent inequality for class `O`. -/
theorem expO_w {r i L ℓ d : ℝ} (hd : 0 ≤ d) (hi0 : 0 ≤ i) (hir : i ≤ r) :
    r * (r - 1) * L - (2 * ℓ + d) * (r - 1) * i ≤
      r * (r - 1) * L - 2 * ℓ * i * (r - 1) - d * (i * (i - 1)) := by
  have : 0 ≤ d * (i * (r - i)) := mul_nonneg hd (mul_nonneg hi0 (by linarith))
  nlinarith

/-- The per-list exponent inequality for class `M`. -/
theorem expM_w {r s i j l L ℓ d : ℝ} (hd : 0 ≤ d) (hi0 : 0 ≤ i) (hj0 : 0 ≤ j) (hl0 : 0 ≤ l)
    (hir : i ≤ r) (hjs : j ≤ s) (hls : l ≤ s) :
    2 * (r * s) * L - ℓ * (2 * s * i + r * (j + l)) - 2 * (r * s) * d ≤
      (r * s * L - ℓ * (i * s + r * l) - d * (i * l)) +
        (s * r * L - ℓ * (j * r + s * i) - d * (j * i)) := by
  have h1 : i * (j + l) ≤ r * (2 * s) :=
    mul_le_mul hir (by linarith) (by linarith) (by linarith)
  have h2 : 0 ≤ d * (2 * (r * s) - i * (j + l)) := mul_nonneg hd (by linarith)
  nlinarith

/-- The per-list exponent inequality for class `PQ`. -/
theorem expPQ_w {s j l L ℓ d : ℝ} (hd : 0 ≤ d) (hjs : j ≤ s) (hls : l ≤ s) (hjl : s ≤ j + l) :
    s ^ 2 * L - ℓ * s * (j + l) - d / 4 * (3 * s * (j + l) - 2 * s ^ 2) ≤
      s * s * L - ℓ * (j * s + s * l) - d * (j * l) := by
  have h1 : 4 * (j * l) ≤ 3 * s * (j + l) - 2 * s ^ 2 := by
    nlinarith [sq_nonneg (j - l)]
  have h2 : 0 ≤ d * (3 * s * (j + l) - 2 * s ^ 2 - 4 * (j * l)) := mul_nonneg hd (by linarith)
  have e : d / 4 * (3 * s * (j + l) - 2 * s ^ 2) = d * (j * l) +
      d * (3 * s * (j + l) - 2 * s ^ 2 - 4 * (j * l)) / 4 := by ring
  rw [e]
  have e2 : s * s * L - ℓ * (j * s + s * l) = s ^ 2 * L - ℓ * s * (j + l) := by ring
  rw [e2]
  linarith

section Assembly

variable {k n : ℕ} {A B : Finset ℕ} {T : Fin n → Finset ℕ}

theorem sum_const_fin (n : ℕ) (c : ℝ) : ∑ _w : Fin n, c = n * c := by
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem termD (hk : 3 ≤ k) (hT : ∀ w, (T w).card = k) {r : ℝ} (hr1 : 1 ≤ r)
    (hrdef : ((A ∩ B).card : ℝ) = r) :
    ((k : ℝ) - 1) ^ n * (r * exp (ell k * (n * r - ∑ w, ((A ∩ B ∩ T w).card : ℝ)) / r)) ≤
      ∑ a ∈ A ∩ B, pf T a a := by
  have h := class_bound (A ∩ B) (fun a => pf T a a) (fun a _ => pf_pos hk hT a a) hrdef
    (le_of_eq (sum_log_pf_diag hk hT (A ∩ B)).symm)
  refine le_of_eq_of_le ?_ h
  rw [pow_eq_exp hk, mul_left_comm, ← exp_add, sum_sub_distrib, sum_const_fin, ← mul_sum, hrdef,
    log_sub_one_eq]
  congr 2
  field_simp
  ring

theorem termO (hk : 3 ≤ k) (hT : ∀ w, (T w).card = k) {r : ℝ} (hr1 : 1 ≤ r)
    (hrdef : ((A ∩ B).card : ℝ) = r) (hir : ∀ w, ((A ∩ B ∩ T w).card : ℝ) ≤ r) :
    ((k : ℝ) - 1) ^ n * (r * (r - 1) * exp (-(n * ell k) - n * del k +
      (2 + del k / ell k) * (ell k * (n * r - ∑ w, ((A ∩ B ∩ T w).card : ℝ)) / r))) ≤
      ∑ p ∈ (A ∩ B).offDiag, pf T p.1 p.2 := by
  rcases eq_or_lt_of_le hr1 with h1 | h1
  · rw [← h1]; simp only [sub_self, mul_zero, zero_mul]
    exact sum_nonneg fun p _ => (pf_pos hk hT _ _).le
  have hℓ0 := ell_pos hk
  have hd0 := del_nonneg hk
  set N := ∑ w, ((A ∩ B ∩ T w).card : ℝ) with hN
  have hL : n * (r * (r - 1)) * log k - (2 * ell k + del k) * (r - 1) * N ≤
      ∑ p ∈ (A ∩ B).offDiag, log (pf T p.1 p.2) := by
    rw [sum_log_pf_offDiag hk hT, hrdef, hN, mul_sum, mul_assoc, ← sum_const_fin, ← sum_sub_distrib]
    exact sum_le_sum fun w _ => expO_w hd0 (Nat.cast_nonneg _) (hir w)
  have hcard : (((A ∩ B).offDiag.card : ℕ) : ℝ) = r * (r - 1) := by
    rw [offDiag_card, Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul, hrdef]; ring
  have h := class_bound _ (fun p : ℕ × ℕ => pf T p.1 p.2) (fun p _ => pf_pos hk hT _ _) hcard hL
  refine le_trans (le_of_eq ?_) h
  rw [pow_eq_exp hk, mul_left_comm, ← exp_add, log_sub_one_eq]
  congr 2
  have : r - 1 ≠ 0 := by linarith
  have : ell k ≠ 0 := hℓ0.ne'
  field_simp
  ring

theorem termM (hk : 3 ≤ k) (hT : ∀ w, (T w).card = k) {r s : ℝ} (hr1 : 1 ≤ r) (hs1 : 1 ≤ s)
    (hrdef : ((A ∩ B).card : ℝ) = r) (hPc : ((A \ B).card : ℝ) = s)
    (hQc : ((B \ A).card : ℝ) = s)
    (hsum3 : ∀ w, ((A ∩ B ∩ T w).card : ℝ) + ((A \ B ∩ T w).card : ℝ) +
      ((B \ A ∩ T w).card : ℝ) = k) (hks : (k : ℝ) = r + s)
    (hir : ∀ w, ((A ∩ B ∩ T w).card : ℝ) ≤ r) (hjs : ∀ w, ((A \ B ∩ T w).card : ℝ) ≤ s)
    (hls : ∀ w, ((B \ A ∩ T w).card : ℝ) ≤ s) :
    ((k : ℝ) - 1) ^ n * (2 * r * s * exp (-(n * ell k / 2) - n * del k +
      (1 - r / (2 * s)) * (ell k * (n * r - ∑ w, ((A ∩ B ∩ T w).card : ℝ)) / r))) ≤
      ∑ a ∈ A ∩ B, ∑ b ∈ B \ A, pf T a b + ∑ a ∈ A \ B, ∑ b ∈ A ∩ B, pf T a b := by
  have hd0 := del_nonneg hk
  have hIQ := sum_log_pf_cross hk hT (X := A ∩ B) (Y := B \ A)
    (disjoint_left.mpr fun x hx hx' => (mem_sdiff.mp hx').2 (mem_inter.mp hx).1)
  have hPI := sum_log_pf_cross hk hT (X := A \ B) (Y := A ∩ B)
    (disjoint_left.mpr fun x hx hx' => (mem_sdiff.mp hx).2 (mem_inter.mp hx').2)
  rw [hrdef, hQc] at hIQ
  rw [hrdef, hPc] at hPI
  have c1 : (((A ∩ B) ×ˢ (B \ A)).card : ℝ) = r * s := by
    rw [card_product, Nat.cast_mul, hQc, hrdef]
  have c2 : (((A \ B) ×ˢ (A ∩ B)).card : ℝ) = r * s := by
    rw [card_product, Nat.cast_mul, hPc, hrdef]; ring
  have b1 := class_bound _ (fun p : ℕ × ℕ => pf T p.1 p.2) (fun p _ => pf_pos hk hT _ _) c1
    (le_of_eq ((sum_product _ _ _).trans hIQ).symm)
  have b2 := class_bound _ (fun p : ℕ × ℕ => pf T p.1 p.2) (fun p _ => pf_pos hk hT _ _) c2
    (le_of_eq ((sum_product _ _ _).trans hPI).symm)
  rw [sum_product] at b1 b2
  set L1 := ∑ w : Fin n, (r * s * log k -
      ell k * (((A ∩ B ∩ T w).card : ℝ) * s + r * ((B \ A ∩ T w).card : ℝ)) -
      del k * (((A ∩ B ∩ T w).card : ℝ) * ((B \ A ∩ T w).card : ℝ))) with hL1
  set L2 := ∑ w : Fin n, (s * r * log k -
      ell k * (((A \ B ∩ T w).card : ℝ) * r + s * ((A ∩ B ∩ T w).card : ℝ)) -
      del k * (((A \ B ∩ T w).card : ℝ) * ((A ∩ B ∩ T w).card : ℝ))) with hL2
  set N := ∑ w, ((A ∩ B ∩ T w).card : ℝ) with hN
  have hrs : 0 < r * s := by positivity
  have hmid := two_mul_exp_mid_le (L1 / (r * s)) (L2 / (r * s))
  have hsum : 2 * r * s * exp ((L1 + L2) / (2 * (r * s))) ≤
      r * s * exp (L1 / (r * s)) + r * s * exp (L2 / (r * s)) := by
    have e : (L1 + L2) / (2 * (r * s)) = (L1 / (r * s) + L2 / (r * s)) / 2 := by field_simp
    rw [e]; nlinarith
  have hJL : ∑ w, (((A \ B ∩ T w).card : ℝ) + ((B \ A ∩ T w).card : ℝ)) = n * k - N := by
    have : ∀ w, ((A \ B ∩ T w).card : ℝ) + ((B \ A ∩ T w).card : ℝ) =
        k - ((A ∩ B ∩ T w).card : ℝ) := fun w => by linarith [hsum3 w]
    rw [sum_congr rfl fun w _ => this w, sum_sub_distrib, sum_const_fin]
  have hLsum : 2 * (r * s) * n * log k - ell k * (2 * s * N + r * (n * k - N)) -
      2 * (r * s) * n * del k ≤ L1 + L2 := by
    have h1 := sum_le_sum fun w (_ : w ∈ univ) => expM_w (L := log k) (ℓ := ell k) hd0
      (Nat.cast_nonneg ((A ∩ B ∩ T w).card)) (Nat.cast_nonneg ((A \ B ∩ T w).card))
      (Nat.cast_nonneg ((B \ A ∩ T w).card)) (hir w) (hjs w) (hls w)
    rw [sum_add_distrib] at h1
    refine le_trans (le_of_eq ?_) h1
    rw [sum_sub_distrib, sum_sub_distrib, sum_const_fin, sum_const_fin, ← mul_sum,
      sum_add_distrib, ← mul_sum, ← mul_sum, hJL, ← hN]
    ring
  have hexp : n * log ((k : ℝ) - 1) + (-(n * ell k / 2) - n * del k +
      (1 - r / (2 * s)) * (ell k * (n * r - N) / r)) ≤ (L1 + L2) / (2 * (r * s)) := by
    rw [le_div_iff₀ (by positivity), log_sub_one_eq]
    have e : (n * (log k - ell k) + (-(n * ell k / 2) - n * del k +
        (1 - r / (2 * s)) * (ell k * (n * r - N) / r))) * (2 * (r * s)) =
        2 * (r * s) * n * log k - ell k * (2 * s * N + r * (n * k - N)) -
        2 * (r * s) * n * del k := by
      have : r ≠ 0 := by linarith
      have : s ≠ 0 := by linarith
      have e1 : (1 - r / (2 * s)) * (ell k * (n * r - N) / r) * (2 * (r * s)) =
          2 * s * ell k * (n * r - N) - r * ell k * (n * r - N) := by field_simp
      rw [show (n * (log k - ell k) + (-(n * ell k / 2) - n * del k +
          (1 - r / (2 * s)) * (ell k * (n * r - N) / r))) * (2 * (r * s)) =
          n * (log k - ell k) * (2 * (r * s)) - n * ell k / 2 * (2 * (r * s)) -
          n * del k * (2 * (r * s)) +
          (1 - r / (2 * s)) * (ell k * (n * r - N) / r) * (2 * (r * s)) by ring, e1]
      linear_combination (r * n * ell k) * hks
    rw [e]; exact hLsum
  calc ((k : ℝ) - 1) ^ n * (2 * r * s * exp (-(n * ell k / 2) - n * del k +
        (1 - r / (2 * s)) * (ell k * (n * r - N) / r)))
      = 2 * r * s * exp (n * log ((k : ℝ) - 1) + (-(n * ell k / 2) - n * del k +
          (1 - r / (2 * s)) * (ell k * (n * r - N) / r))) := by
        rw [pow_eq_exp hk, exp_add (n * log ((k : ℝ) - 1))]; ring
    _ ≤ 2 * r * s * exp ((L1 + L2) / (2 * (r * s))) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr hexp) (by positivity)
    _ ≤ _ := by linarith

theorem termPQ (hk : 3 ≤ k) (hT : ∀ w, (T w).card = k) {r s : ℝ} (hs1 : 1 ≤ s)
    (hPc : ((A \ B).card : ℝ) = s) (hQc : ((B \ A).card : ℝ) = s)
    (hsum3 : ∀ w, ((A ∩ B ∩ T w).card : ℝ) + ((A \ B ∩ T w).card : ℝ) +
      ((B \ A ∩ T w).card : ℝ) = k)
    (hks : (k : ℝ) = r + s) (hir : ∀ w, ((A ∩ B ∩ T w).card : ℝ) ≤ r)
    (hjs : ∀ w, ((A \ B ∩ T w).card : ℝ) ≤ s) (hls : ∀ w, ((B \ A ∩ T w).card : ℝ) ≤ s) :
    ((k : ℝ) - 1) ^ n * (s ^ 2 * exp (-(n * del k / 4) - r / s * (1 + 3 * (del k / ell k) / 4) *
      (ell k * (n * r - ∑ w, ((A ∩ B ∩ T w).card : ℝ)) / r))) ≤
      ∑ a ∈ A \ B, ∑ b ∈ B \ A, pf T a b := by
  have hd0 := del_nonneg hk
  have hℓ0 := ell_pos hk
  have hPQ' := sum_log_pf_cross hk hT (X := A \ B) (Y := B \ A)
    (disjoint_left.mpr fun x hx hx' => (mem_sdiff.mp hx').2 (mem_sdiff.mp hx).1)
  rw [hPc, hQc] at hPQ'
  set N := ∑ w, ((A ∩ B ∩ T w).card : ℝ) with hN
  have hJL : ∑ w, (((A \ B ∩ T w).card : ℝ) + ((B \ A ∩ T w).card : ℝ)) = n * k - N := by
    have : ∀ w, ((A \ B ∩ T w).card : ℝ) + ((B \ A ∩ T w).card : ℝ) =
        k - ((A ∩ B ∩ T w).card : ℝ) := fun w => by linarith [hsum3 w]
    rw [sum_congr rfl fun w _ => this w, sum_sub_distrib, sum_const_fin]
  have c : (((A \ B) ×ˢ (B \ A)).card : ℝ) = s ^ 2 := by
    rw [card_product, Nat.cast_mul, hPc, hQc]; ring
  have hL : n * s ^ 2 * log k - ell k * s * (n * k - N) -
      del k / 4 * (3 * s * (n * k - N) - 2 * n * s ^ 2) ≤
      ∑ p ∈ (A \ B) ×ˢ (B \ A), log (pf T p.1 p.2) := by
    rw [sum_product, hPQ']
    have h1 := sum_le_sum fun w (_ : w ∈ univ) => expPQ_w (L := log k) (ℓ := ell k) hd0
      (hjs w) (hls w) (by linarith [hsum3 w, hir w] :
        s ≤ ((A \ B ∩ T w).card : ℝ) + ((B \ A ∩ T w).card : ℝ))
    refine le_trans (le_of_eq ?_) h1
    rw [sum_sub_distrib, sum_sub_distrib, sum_const_fin, ← mul_sum, ← mul_sum, sum_sub_distrib,
      ← mul_sum, sum_const_fin, hJL]
    ring
  have h := class_bound _ (fun p : ℕ × ℕ => pf T p.1 p.2) (fun p _ => pf_pos hk hT _ _) c hL
  rw [sum_product] at h
  refine le_trans (le_of_eq ?_) h
  rw [pow_eq_exp hk, mul_left_comm, ← exp_add, log_sub_one_eq]
  congr 2
  have hs0 : s ≠ 0 := by linarith
  have hℓne : ell k ≠ 0 := hℓ0.ne'
  have hs' : s = k - r := by linarith
  subst hs'
  rcases eq_or_ne r 0 with hr0 | hr0
  · have hN0 : N = 0 := by
      rw [hN]
      refine sum_eq_zero fun w _ => le_antisymm ?_ (Nat.cast_nonneg _)
      have := hir w; rw [hr0] at this; exact this
    rw [hr0, hN0]
    simp only [zero_div, zero_mul, sub_zero, mul_zero, div_zero, sub_self]
    rw [hr0, sub_zero] at hs0
    field_simp
    ring
  field_simp
  ring

/-- **Class AM–GM for `K₂,ₙ`.** For pushed lists with hub overlap `1 ≤ r ≤ k - 1`, the colouring
count is at least `(k - 1)ⁿ · lowerG` with `x = n ℓ`, `η = n δ`, `λ = δ / ℓ` and
`w = ℓ (n r - N) / r`, where `N = ∑_w |A ∩ B ∩ T w|`. -/
theorem lowerG_le_sum (hk : 3 ≤ k) (hA : A.card = k) (hB : B.card = k)
    (hTsub : ∀ w, T w ⊆ A ∪ B) (hT : ∀ w, (T w).card = k) (hr : 1 ≤ (A ∩ B).card)
    (hrk : (A ∩ B).card + 1 ≤ k) :
    ((k : ℝ) - 1) ^ n * lowerG k (A ∩ B).card (n * ell k) (n * del k) (del k / ell k)
      (ell k * (n * (A ∩ B).card - ∑ w, ((A ∩ B ∩ T w).card : ℝ)) / (A ∩ B).card) ≤
      ∑ a ∈ A, ∑ b ∈ B, pf T a b := by
  have hr1 : (1 : ℝ) ≤ (A ∩ B).card := by exact_mod_cast hr
  have hs1 : (1 : ℝ) ≤ k - (A ∩ B).card := by
    have : ((A ∩ B).card : ℝ) + 1 ≤ k := by exact_mod_cast hrk
    linarith
  have hPc : ((A \ B).card : ℝ) = k - (A ∩ B).card := by
    have := card_sdiff_add_card_inter A B
    rw [hA] at this
    have h2 : ((A \ B).card : ℝ) + (A ∩ B).card = k := by exact_mod_cast this
    linarith
  have hQc : ((B \ A).card : ℝ) = k - (A ∩ B).card := by
    have := card_sdiff_add_card_inter B A
    rw [hB, inter_comm] at this
    have h2 : ((B \ A).card : ℝ) + (A ∩ B).card = k := by exact_mod_cast this
    linarith
  have hsum3 : ∀ w, ((A ∩ B ∩ T w).card : ℝ) + ((A \ B ∩ T w).card : ℝ) +
      ((B \ A ∩ T w).card : ℝ) = k := fun w => by
    exact_mod_cast card_parts (hTsub w) (hT w)
  have hir : ∀ w, ((A ∩ B ∩ T w).card : ℝ) ≤ (A ∩ B).card := fun w => by
    exact_mod_cast card_le_card inter_subset_left
  have hjs : ∀ w, ((A \ B ∩ T w).card : ℝ) ≤ k - (A ∩ B).card := fun w => by
    rw [← hPc]; exact_mod_cast card_le_card inter_subset_left
  have hls : ∀ w, ((B \ A ∩ T w).card : ℝ) ≤ k - (A ∩ B).card := fun w => by
    rw [← hQc]; exact_mod_cast card_le_card inter_subset_left
  have hD := termD (n := n) (A := A) (B := B) hk hT hr1 rfl
  have hO := termO hk hT hr1 rfl hir
  have hM := termM hk hT hr1 hs1 rfl hPc hQc hsum3 (by ring) hir hjs hls
  have hPQ := termPQ hk hT hs1 hPc hQc hsum3 (by ring) hir hjs hls
  rw [sum_split A B (pf T)]
  simp only [lowerG]
  nlinarith [hD, hO, hM, hPQ]

end Assembly

end SimpleGraph.TwoDegenerate.K2nSqrt
