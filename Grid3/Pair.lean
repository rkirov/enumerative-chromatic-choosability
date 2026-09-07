/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.Pointwise

/-!
# The pair lemma for `(H1)`, `k ≥ 5`

Summing the pointwise bound `LB` over the states with a given middle colour `y` gives a lower
bound on `QH y`; after three cardinality inequalities it is bounded below by the simple
expression

  `Λ y = (k-2)²·[y ∉ M]·x·z + ((k-2)·z·(x-1) - 1)·uT + (k-2)·x·(z-1)·uB
          - ((k-2)·z + 1)·[y ∈ M \ T] - (k-2)·x·[y ∈ M \ B]`,

where `x = |X \ y|`, `z = |Z \ y|`, `uT = |(M \ y) \ T|`, `uB = |(M \ y) \ B|`. A colour is
*bad* only when it is the unique colour of `M` outside `T` (or `B`); then every other colour
sees `uT ≥ 1` and carries the surplus `(k-2)·z·(x-1) - 1`, which pays for it exactly when
`(k-2)(k-3) ≥ k + 1`, i.e. `k ≥ 5`.
-/

open Finset

namespace Grid3

/-! ### Indicator sums -/

theorem sum_ind_filter {S : Finset ℕ} (p : ℕ → Prop) [DecidablePred p] :
    ∑ a ∈ S, ind (p a) = ((S.filter p).card : ℤ) := by
  unfold ind; simp [Finset.sum_boole]

/-- The bonus sum of one colour, exactly. -/
theorem sum_dT_eq (T M : Finset ℕ) {y a : ℕ} (hay : a ≠ y) :
    ∑ m ∈ M.erase y, dT T a m
      = (((M.erase y).filter (· ∉ T)).card : ℤ) - ind (a ∈ M ∧ a ∉ T)
        + ((M.erase y).card : ℤ) * ind (a ∉ T) := by
  unfold dT
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have h : ∀ m ∈ M.erase y, ind (m ∉ T) * ind (a ≠ m) = ind (m ∉ T) - ind (a = m ∧ m ∉ T) := by
    intro m _
    unfold ind
    by_cases h1 : m ∈ T <;> by_cases h2 : a = m <;> simp [h1, h2]
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, sum_ind_filter]
  congr 1
  unfold ind
  have h3 : ∀ m ∈ M.erase y, (if a = m ∧ m ∉ T then (1 : ℤ) else 0)
      = if a = m then (if m ∉ T then 1 else 0) else 0 := by
    intro m _; by_cases h : a = m <;> simp [h]
  rw [Finset.sum_congr rfl h3, Finset.sum_ite_eq]
  by_cases hM : a ∈ M <;> by_cases hT : a ∈ T <;> simp [hM, hT, hay]

/-- The top-colour contribution to `LB`, in the form used for the sums. -/
def alpha (k : ℕ) (T M : Finset ℕ) (y a : ℕ) : ℤ :=
  ((k : ℤ) - 2) * ((M.erase y).filter (· ∉ T)).card - ((k : ℤ) - 2) * ind (a ∈ T ∧ a ∉ M)
    + ((k : ℤ) - 2) * (((M.erase y).card : ℤ) - 1) * ind (a ∉ T)

theorem alpha_eq (k : ℕ) (T M : Finset ℕ) {y a : ℕ} (hay : a ≠ y) :
    - ((k : ℤ) - 2) * ind (a ∉ M) + ((k : ℤ) - 2) * ∑ m ∈ M.erase y, dT T a m
      = alpha k T M y a := by
  rw [sum_dT_eq T M hay]
  unfold alpha ind
  by_cases hT : a ∈ T <;> by_cases hM : a ∈ M <;> simp [hT, hM] <;> ring

/-- `LB` of a state, decomposed by its top and bottom colours. -/
theorem LB_decomp (k : ℕ) (T M B : Finset ℕ) {y a c : ℕ} (hay : a ≠ y) (hcy : c ≠ y) :
    LB k T M B (a, y, c)
      = ((k : ℤ) - 2) ^ 2 * ind (y ∉ M) + alpha k T M y a + alpha k B M y c
        - ind (a = c) * ind (a ∉ M) := by
  rw [← alpha_eq k T M hay, ← alpha_eq k B M hcy]
  unfold LB
  simp only
  ring

/-! ### Summing over a colour -/

/-- The number of colours of `S` outside `M`, split by membership in `T`. -/
theorem card_notMem_le (S T M : Finset ℕ) :
    ((S.filter (· ∉ M)).card : ℤ)
      ≤ (S.filter (fun a => a ∈ T ∧ a ∉ M)).card + (S.filter (· ∉ T)).card := by
  have h : S.filter (· ∉ M) ⊆ S.filter (fun a => a ∈ T ∧ a ∉ M) ∪ S.filter (· ∉ T) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_union] at ha ⊢
    by_cases hT : a ∈ T
    · exact Or.inl ⟨ha.1, hT, ha.2⟩
    · exact Or.inr ⟨ha.1, hT⟩
  exact_mod_cast le_trans (Finset.card_le_card h) (Finset.card_union_le _ _)

theorem sum_alpha (k : ℕ) (T M : Finset ℕ) (y : ℕ) (S : Finset ℕ) :
    ∑ a ∈ S, alpha k T M y a
      = ((k : ℤ) - 2) * ((S.card : ℤ) * ((M.erase y).filter (· ∉ T)).card
          - (S.filter (fun a => a ∈ T ∧ a ∉ M)).card
          + (((M.erase y).card : ℤ) - 1) * (S.filter (· ∉ T)).card) := by
  unfold alpha
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_ind_filter, sum_ind_filter]
  ring

theorem sum_eq_notMem_le (X Z M : Finset ℕ) :
    ∑ a ∈ X, ∑ c ∈ Z, ind (a = c) * ind (a ∉ M) ≤ ((X.filter (· ∉ M)).card : ℤ) := by
  rw [← sum_ind_filter]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.sum_mul]
  have h : ∑ c ∈ Z, ind (a = c) ≤ 1 := by
    unfold ind
    rw [Finset.sum_ite_eq]
    split_ifs <;> norm_num
  have h0 : 0 ≤ ∑ c ∈ Z, ind (a = c) := Finset.sum_nonneg fun _ _ => ind_nonneg _
  nlinarith [ind_nonneg (a ∉ M), ind_le_one (a ∉ M)]

/-- The number of colours of `S` in `T \ M` is at most `|M \ T|`, which is `|(M \ y) \ T|` plus
the indicator of `y ∈ M \ T`. -/
theorem card_filter_TM_le {k : ℕ} (S : Finset ℕ) {T M : Finset ℕ} (hT : T.card = k)
    (hM : M.card = k) (y : ℕ) :
    ((S.filter (fun a => a ∈ T ∧ a ∉ M)).card : ℤ)
      ≤ ((M.erase y).filter (· ∉ T)).card + ind (y ∈ M ∧ y ∉ T) := by
  have h1 : S.filter (fun a => a ∈ T ∧ a ∉ M) ⊆ T \ M := by
    intro a ha; simp only [Finset.mem_filter, Finset.mem_sdiff] at ha ⊢; exact ha.2
  have h2 : (T \ M).card = (M \ T).card := by
    have a1 := Finset.card_sdiff_add_card_inter T M
    have a2 := Finset.card_sdiff_add_card_inter M T
    rw [Finset.inter_comm] at a2
    omega
  have h3 : (M \ T).card = ((M.erase y).filter (· ∉ T)).card + (if y ∈ M ∧ y ∉ T then 1 else 0) := by
    rw [Finset.filter_erase, ← Finset.sdiff_eq_filter]
    by_cases hy : y ∈ M \ T
    · rw [Finset.card_erase_of_mem hy, if_pos (Finset.mem_sdiff.mp hy)]
      have := Finset.card_pos.mpr ⟨y, hy⟩; omega
    · rw [Finset.erase_eq_of_notMem hy, if_neg (fun h => hy (Finset.mem_sdiff.mpr h))]; simp
  have h4 := Finset.card_le_card h1
  unfold ind
  rw [h2, h3] at h4
  split_ifs at h4 ⊢ <;> omega

/-- The simplified per-colour bound `Λ`. -/
def Lam (k : ℕ) (X Z T M B : Finset ℕ) (y : ℕ) : ℤ :=
  ((k : ℤ) - 2) ^ 2 * ind (y ∉ M) * (X.erase y).card * (Z.erase y).card
    + (((k : ℤ) - 2) * (Z.erase y).card * (((X.erase y).card : ℤ) - 1) - 1)
        * ((M.erase y).filter (· ∉ T)).card
    + ((k : ℤ) - 2) * (X.erase y).card * (((Z.erase y).card : ℤ) - 1)
        * ((M.erase y).filter (· ∉ B)).card
    - (((k : ℤ) - 2) * (Z.erase y).card + 1) * ind (y ∈ M ∧ y ∉ T)
    - ((k : ℤ) - 2) * (X.erase y).card * ind (y ∈ M ∧ y ∉ B)

/-- Cardinality facts about a punctured near-`k` list. -/
theorem card_erase_bounds {k : ℕ} {X : Finset ℕ} (hX : NearK k X) (y : ℕ) :
    (k : ℤ) - 2 ≤ (X.erase y).card ∧ ((X.erase y).card : ℤ) ≤ k := by
  have h1 := Finset.pred_card_le_card_erase (s := X) (a := y)
  have h2 := Finset.card_erase_le (s := X) (a := y)
  rcases hX with h | h <;> omega

/-- `Λ⁺`: `Λ` together with the two surplus terms it discards. -/
def LamP (k : ℕ) (X Z T M B : Finset ℕ) (y : ℕ) : ℤ :=
  Lam k X Z T M B y
    + (((k : ℤ) - 2) * (Z.erase y).card * (((M.erase y).card : ℤ) - 1) - 1)
        * ((X.erase y).filter (· ∉ T)).card
    + ((k : ℤ) - 2) * (X.erase y).card * (((M.erase y).card : ℤ) - 1)
        * ((Z.erase y).filter (· ∉ B)).card

/-- **The per-colour bound, with surplus.** `QH y ≥ Λ⁺ y` for `k ≥ 5`. -/
theorem LamP_le_QH {k : ℕ} (hk : 5 ≤ k) {X Z T M B : Finset ℕ} (hX : NearK k X) (hZ : NearK k Z)
    (hT : T.card = k) (hM : M.card = k) (hB : B.card = k) (y : ℕ) :
    LamP k X Z T M B y ≤ QH k X Z T M B y := by
  -- `QH ≥ ∑ LB`
  have hLB : ∑ a ∈ X.erase y, ∑ c ∈ Z.erase y, LB k T M B (a, y, c) ≤ QH k X Z T M B y := by
    unfold QH
    refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun c hc => ?_
    exact LB_le_dH (by omega) hT hM hB (Finset.ne_of_mem_erase ha)
      (Ne.symm (Finset.ne_of_mem_erase hc))
  refine le_trans ?_ hLB
  -- decompose and sum
  have hdec : ∑ a ∈ X.erase y, ∑ c ∈ Z.erase y, LB k T M B (a, y, c)
      = ((k : ℤ) - 2) ^ 2 * ind (y ∉ M) * (X.erase y).card * (Z.erase y).card
        + (Z.erase y).card * ∑ a ∈ X.erase y, alpha k T M y a
        + (X.erase y).card * ∑ c ∈ Z.erase y, alpha k B M y c
        - ∑ a ∈ X.erase y, ∑ c ∈ Z.erase y, ind (a = c) * ind (a ∉ M) := by
    rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun c hc =>
      LB_decomp k T M B (Finset.ne_of_mem_erase ha) (Finset.ne_of_mem_erase hc)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  rw [hdec, sum_alpha, sum_alpha]
  -- the cardinality inequalities
  have hw := sum_eq_notMem_le (X.erase y) (Z.erase y) M
  have hnX := card_notMem_le (X.erase y) T M
  have hrT := card_filter_TM_le (X.erase y) hT hM y
  have hrB := card_filter_TM_le (Z.erase y) hB hM y
  obtain ⟨hx1, hx2⟩ := card_erase_bounds hX y
  obtain ⟨hz1, hz2⟩ := card_erase_bounds hZ y
  have hμ : (k : ℤ) - 1 ≤ (M.erase y).card := by
    have := Finset.pred_card_le_card_erase (s := M) (a := y); omega
  have hqT : (0 : ℤ) ≤ ((X.erase y).filter (· ∉ T)).card := by positivity
  have hqB : (0 : ℤ) ≤ ((Z.erase y).filter (· ∉ B)).card := by positivity
  have huT : (0 : ℤ) ≤ ((M.erase y).filter (· ∉ T)).card := by positivity
  have huB : (0 : ℤ) ≤ ((M.erase y).filter (· ∉ B)).card := by positivity
  have hrT0 : (0 : ℤ) ≤ ((X.erase y).filter (fun a => a ∈ T ∧ a ∉ M)).card := by positivity
  have hrB0 : (0 : ℤ) ≤ ((Z.erase y).filter (fun a => a ∈ B ∧ a ∉ M)).card := by positivity
  have hyMT := ind_nonneg (y ∈ M ∧ y ∉ T)
  have hyMB := ind_nonneg (y ∈ M ∧ y ∉ B)
  have hyM := ind_nonneg (y ∉ M)
  unfold LamP Lam
  set x : ℤ := ((X.erase y).card : ℤ)
  set z : ℤ := ((Z.erase y).card : ℤ)
  set μ : ℤ := ((M.erase y).card : ℤ)
  set uT : ℤ := (((M.erase y).filter (· ∉ T)).card : ℤ)
  set uB : ℤ := (((M.erase y).filter (· ∉ B)).card : ℤ)
  set rT : ℤ := (((X.erase y).filter (fun a => a ∈ T ∧ a ∉ M)).card : ℤ)
  set rB : ℤ := (((Z.erase y).filter (fun a => a ∈ B ∧ a ∉ M)).card : ℤ)
  set qT : ℤ := (((X.erase y).filter (· ∉ T)).card : ℤ)
  set qB : ℤ := (((Z.erase y).filter (· ∉ B)).card : ℤ)
  set w : ℤ := ∑ a ∈ X.erase y, ∑ c ∈ Z.erase y, ind (a = c) * ind (a ∉ M)
  set nX : ℤ := (((X.erase y).filter (· ∉ M)).card : ℤ)
  set yMT : ℤ := ind (y ∈ M ∧ y ∉ T)
  set yMB : ℤ := ind (y ∈ M ∧ y ∉ B)
  have hk2 : (3 : ℤ) ≤ (k : ℤ) - 2 := by omega
  -- the top side: `z·(k-2)·(x·uT - rT + (μ-1)·qT) - w ≥ ((k-2)·z·(x-1) - 1)·uT - ((k-2)·z + 1)·yMT`
  have hz0 : (0 : ℤ) ≤ z := by linarith
  have hx0 : (0 : ℤ) ≤ x := by linarith
  have hμ1 : (0 : ℤ) ≤ μ - 1 := by linarith
  have P1 : z * ((k : ℤ) - 2) * rT ≤ z * ((k : ℤ) - 2) * (uT + yMT) :=
    mul_le_mul_of_nonneg_left hrT (by positivity)
  have P2 : x * ((k : ℤ) - 2) * rB ≤ x * ((k : ℤ) - 2) * (uB + yMB) :=
    mul_le_mul_of_nonneg_left hrB (by positivity)
  have P3 : (0 : ℤ) ≤ (z * ((k : ℤ) - 2) * (μ - 1) - 1) * qT := by
    apply mul_nonneg _ hqT
    nlinarith [mul_le_mul hz1 hk2 (by norm_num) hz0]
  have P4 : (0 : ℤ) ≤ x * ((k : ℤ) - 2) * (μ - 1) * qB := by positivity
  have P5 : w ≤ rT + qT := le_trans hw hnX
  nlinarith [P1, P2, P3, P4, P5]

theorem Lam_le_LamP {k : ℕ} (hk : 5 ≤ k) {X Z T M B : Finset ℕ} (hX : NearK k X) (hZ : NearK k Z)
    (hM : M.card = k) (y : ℕ) :
    Lam k X Z T M B y ≤ LamP k X Z T M B y := by
  unfold LamP
  obtain ⟨hx1, _⟩ := card_erase_bounds hX y
  obtain ⟨hz1, _⟩ := card_erase_bounds hZ y
  have hμ : (k : ℤ) - 1 ≤ (M.erase y).card := by
    have := Finset.pred_card_le_card_erase (s := M) (a := y); omega
  have hk2 : (3 : ℤ) ≤ (k : ℤ) - 2 := by omega
  have h1 : (0 : ℤ) ≤ ((k : ℤ) - 2) * (Z.erase y).card * (((M.erase y).card : ℤ) - 1) - 1 := by
    nlinarith [mul_le_mul hk2 hz1 (by linarith) (by linarith)]
  have h2 : (0 : ℤ) ≤ ((k : ℤ) - 2) * (X.erase y).card * (((M.erase y).card : ℤ) - 1) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  nlinarith [mul_nonneg h1 (by positivity : (0:ℤ) ≤ ((X.erase y).filter (· ∉ T)).card),
    mul_nonneg h2 (by positivity : (0:ℤ) ≤ ((Z.erase y).filter (· ∉ B)).card)]

/-- **The per-colour bound.** It is the weaker consequence of the surplus-preserving bound. -/
theorem Lam_le_QH {k : ℕ} (hk : 5 ≤ k) {X Z T M B : Finset ℕ} (hX : NearK k X) (hZ : NearK k Z)
    (hT : T.card = k) (hM : M.card = k) (hB : B.card = k) (y : ℕ) :
    Lam k X Z T M B y ≤ QH k X Z T M B y :=
  le_trans (Lam_le_LamP hk hX hZ hM y) (LamP_le_QH hk hX hZ hT hM hB y)

/-- **The pair inequality, arithmetic form.** Two colours with parameters
`(x, z, uT, uB, p, q, m)` — list sizes, the counts `|(M \ y) \ T|`, `|(M \ y) \ B|`, and the
indicators of `y ∈ M \ T`, `y ∈ M \ B`, `y ∉ M` — coupled by `uT₁ ≥ p₂`, `uT₂ ≥ p₁` (a bad colour
is counted by the other colour's `uT`) and likewise for `B`. -/
theorem pair_arith (k x₁ z₁ x₂ z₂ uT₁ uT₂ uB₁ uB₂ p₁ p₂ q₁ q₂ m₁ m₂ : ℤ) (hk : 5 ≤ k)
    (hx1 : k - 2 ≤ x₁) (hx1' : x₁ ≤ k) (hz1 : k - 2 ≤ z₁) (hz1' : z₁ ≤ k)
    (hx2 : k - 2 ≤ x₂) (hx2' : x₂ ≤ k) (hz2 : k - 2 ≤ z₂) (hz2' : z₂ ≤ k)
    (cT12 : p₁ ≤ uT₂) (cT21 : p₂ ≤ uT₁) (cB12 : q₁ ≤ uB₂) (cB21 : q₂ ≤ uB₁)
    (hp1 : 0 ≤ p₁) (hp2 : 0 ≤ p₂) (hq1 : 0 ≤ q₁) (hq2 : 0 ≤ q₂) (hm1 : 0 ≤ m₁) (hm2 : 0 ≤ m₂) :
    0 ≤ ((k - 2) ^ 2 * m₁ * x₁ * z₁ + ((k - 2) * z₁ * (x₁ - 1) - 1) * uT₁
          + (k - 2) * x₁ * (z₁ - 1) * uB₁ - ((k - 2) * z₁ + 1) * p₁ - (k - 2) * x₁ * q₁)
        + ((k - 2) ^ 2 * m₂ * x₂ * z₂ + ((k - 2) * z₂ * (x₂ - 1) - 1) * uT₂
          + (k - 2) * x₂ * (z₂ - 1) * uB₂ - ((k - 2) * z₂ + 1) * p₂ - (k - 2) * x₂ * q₂) := by
  have hk3 : (3 : ℤ) ≤ k - 2 := by omega
  have hkk : (1 : ℤ) ≤ (k - 2) * (k - 3) - k := by nlinarith
  have m1 : (k - 2) * (k - 3) ≤ z₁ * (x₁ - 1) := mul_le_mul hz1 (by linarith) (by linarith) (by linarith)
  have m2 : (k - 2) * (k - 3) ≤ z₂ * (x₂ - 1) := mul_le_mul hz2 (by linarith) (by linarith) (by linarith)
  have m3 : (k - 2) * (k - 3) ≤ x₁ * (z₁ - 1) := mul_le_mul hx1 (by linarith) (by linarith) (by linarith)
  have m4 : (k - 2) * (k - 3) ≤ x₂ * (z₂ - 1) := mul_le_mul hx2 (by linarith) (by linarith) (by linarith)
  have cT1 : (0 : ℤ) ≤ (k - 2) * z₁ * (x₁ - 1) - 1 := by nlinarith
  have cT2 : (0 : ℤ) ≤ (k - 2) * z₂ * (x₂ - 1) - 1 := by nlinarith
  have cB1 : (0 : ℤ) ≤ (k - 2) * x₁ * (z₁ - 1) := by nlinarith
  have cB2 : (0 : ℤ) ≤ (k - 2) * x₂ * (z₂ - 1) := by nlinarith
  have d1 : (0 : ℤ) ≤ (k - 2) * (z₂ * (x₂ - 1) - z₁) - 2 := by nlinarith
  have d2 : (0 : ℤ) ≤ (k - 2) * (z₁ * (x₁ - 1) - z₂) - 2 := by nlinarith
  have e1 : (0 : ℤ) ≤ (k - 2) * (x₂ * (z₂ - 1) - x₁) := by nlinarith
  have e2 : (0 : ℤ) ≤ (k - 2) * (x₁ * (z₁ - 1) - x₂) := by nlinarith
  have A1 : (0 : ℤ) ≤ (k - 2) ^ 2 * m₁ * x₁ * z₁ := by
    have : (0:ℤ) ≤ x₁ := by linarith
    have : (0:ℤ) ≤ z₁ := by linarith
    positivity
  have A2 : (0 : ℤ) ≤ (k - 2) ^ 2 * m₂ * x₂ * z₂ := by
    have : (0:ℤ) ≤ x₂ := by linarith
    have : (0:ℤ) ≤ z₂ := by linarith
    positivity
  have F1 := mul_le_mul_of_nonneg_left cT21 cT1
  have F2 := mul_le_mul_of_nonneg_left cT12 cT2
  have F3 := mul_le_mul_of_nonneg_left cB21 cB1
  have F4 := mul_le_mul_of_nonneg_left cB12 cB2
  have G1 := mul_nonneg hp1 d1
  have G2 := mul_nonneg hp2 d2
  have G3 := mul_nonneg hq1 e1
  have G4 := mul_nonneg hq2 e2
  linarith

/-- **The pair inequality for `Λ`.** -/
theorem Lam_pair {k : ℕ} (hk : 5 ≤ k) {X Z : Finset ℕ} (T M B : Finset ℕ) (hX : NearK k X)
    (hZ : NearK k Z) {y₁ y₂ : ℕ} (hne : y₁ ≠ y₂) :
    0 ≤ Lam k X Z T M B y₁ + Lam k X Z T M B y₂ := by
  obtain ⟨hx1, hx1'⟩ := card_erase_bounds hX y₁
  obtain ⟨hz1, hz1'⟩ := card_erase_bounds hZ y₁
  obtain ⟨hx2, hx2'⟩ := card_erase_bounds hX y₂
  obtain ⟨hz2, hz2'⟩ := card_erase_bounds hZ y₂
  -- coupling: if `y₁ ∈ M \ T` then `y₁` is counted in `(M \ y₂) \ T`
  have cpl : ∀ (P : Finset ℕ) {u v : ℕ}, u ≠ v →
      ind (u ∈ M ∧ u ∉ P) ≤ (((M.erase v).filter (· ∉ P)).card : ℤ) := by
    intro P u v huv
    unfold ind; split_ifs with h
    · exact_mod_cast Finset.card_pos.mpr
        ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨huv, h.1⟩, h.2⟩⟩
    · positivity
  unfold Lam
  exact pair_arith k _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by exact_mod_cast hk) hx1 hx1' hz1 hz1' hx2 hx2'
    hz2 hz2' (cpl T hne) (cpl T (Ne.symm hne)) (cpl B hne) (cpl B (Ne.symm hne))
    (ind_nonneg _) (ind_nonneg _) (ind_nonneg _) (ind_nonneg _) (ind_nonneg _) (ind_nonneg _)

/-- **The `(H1)` pair lemma for `k ≥ 5`.** -/
theorem pairH_of_five {k : ℕ} (hk : 5 ≤ k) {X Z T M B : Finset ℕ} (hX : NearK k X) (hZ : NearK k Z)
    (hT : T.card = k) (hM : M.card = k) (hB : B.card = k) : PairH k X Z T M B := by
  intro y₁ y₂ hne
  have h1 := Lam_le_QH hk hX hZ hT hM hB y₁
  have h2 := Lam_le_QH hk hX hZ hT hM hB y₂
  have h3 := Lam_pair hk T M B hX hZ hne
  linarith

end Grid3
