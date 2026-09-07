/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.Pair
import Grid3.ArithC

/-!
# The pair lemma for `(C1_r)`, `k ≥ 5`

`QC y = cc · QH y + R y`, where `R y` sums the `eq`-successor deficiencies
`eqSucc s - gam - del·[eq]`. The `eq` successors of `(a, y, c)` are the pairs `(x, m)` with
`x ∈ (T ∩ B) \ {a, c}` and `m ∈ (M \ y) \ x`, so `eqSucc = μ·|W'| - |W' ∩ M_y|` exactly, with
`W' = (T ∩ B) \ {a, c}`; a per-state lower bound `rl` exact at uniform follows, and summing it
over a colour gives `R y ≥ RL' y`, an expression in the same parameters as `Λ`. The pair
inequality `cc·(Λ⁺ y₁ + Λ⁺ y₂) + RL' y₁ + RL' y₂ ≥ 0` is then a polynomial inequality in the
parameters, linear in `t = |M \ T|` and `b = |M \ B|`.
-/

open Finset

namespace Grid3

/-! ### The `eq` successors of a state -/

/-- The `eq` successors, fibred over the common top-and-bottom colour. -/
theorem eqSucc_eq_sum (T M B : Finset ℕ) (a b c : ℕ) :
    eqSucc T M B (a, b, c)
      = ∑ x ∈ (T.erase a) ∩ (B.erase c), ((M.erase b).erase x).card := by
  rw [eqSucc_eq_card, card_eq_states']

theorem inter_erase_erase (T B : Finset ℕ) (a c : ℕ) :
    (T.erase a) ∩ (B.erase c) = ((T ∩ B).erase a).erase c := by
  ext x; simp only [Finset.mem_inter, Finset.mem_erase]; tauto

/-- The per-state deficiency of the `eq` count. -/
def rC (k : ℕ) (T M B : Finset ℕ) (s : State) : ℤ :=
  (eqSucc T M B s : ℤ) - gam k - del k * eqInd s

/-- The per-state lower bound on `rC`, exact at uniform. -/
def rl (k : ℕ) (T M B : Finset ℕ) (y a c : ℕ) : ℤ :=
  ((M.erase y).card : ℤ) * (((T ∩ B).card : ℤ) - ind (a ∈ T ∩ B) - ind (a ≠ c ∧ c ∈ T ∩ B))
    - (((M.erase y).card : ℤ) - ind (a ∈ T ∩ B ∧ a ∈ M) - ind (a ≠ c ∧ c ∈ T ∩ B ∧ c ∈ M))
    - gam k - del k * ind (a = c)

theorem card_filter_mem_erase_erase (W M : Finset ℕ) (y a c : ℕ) :
    ((((W.erase a).erase c).filter (· ∈ M.erase y)).card : ℤ)
      = ((W ∩ M.erase y).card : ℤ) - ind (a ∈ W ∩ M.erase y) - ind (a ≠ c ∧ c ∈ W ∩ M.erase y) := by
  rw [Finset.filter_erase, Finset.filter_erase, Finset.filter_mem_eq_inter, card_erase_erase_int]

theorem mem_inter_erase_iff {W M : Finset ℕ} {y a : ℕ} (hay : a ≠ y) :
    a ∈ W ∩ M.erase y ↔ a ∈ W ∧ a ∈ M := by
  simp [Finset.mem_inter, Finset.mem_erase, hay]

/-- **The per-state bound.** -/
theorem rl_le_rC {k : ℕ} (T M B : Finset ℕ) {y a c : ℕ} (hay : a ≠ y) (hcy : c ≠ y) :
    rl k T M B y a c ≤ rC k T M B (a, y, c) := by
  unfold rC
  rw [eqSucc_eq_sum, inter_erase_erase, eqInd_eq_ind]
  push_cast
  have hsum : ∑ x ∈ ((T ∩ B).erase a).erase c, (((M.erase y).erase x).card : ℤ)
      = ((M.erase y).card : ℤ) * (((T ∩ B).erase a).erase c).card
        - ((((T ∩ B).erase a).erase c).filter (· ∈ M.erase y)).card := by
    rw [Finset.sum_congr rfl fun x _ => card_erase_int (M.erase y) x, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, sum_ind_filter]
    ring
  rw [hsum, card_filter_mem_erase_erase, card_erase_erase_int]
  have hle : ((T ∩ B ∩ M.erase y).card : ℤ) ≤ (M.erase y).card := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have h1 : ind (a ∈ T ∩ B ∩ M.erase y) = ind (a ∈ T ∩ B ∧ a ∈ M) := by
    unfold ind; simp only [mem_inter_erase_iff hay]
  have h2 : ind (a ≠ c ∧ c ∈ T ∩ B ∩ M.erase y) = ind (a ≠ c ∧ c ∈ T ∩ B ∧ c ∈ M) := by
    unfold ind; simp only [mem_inter_erase_iff hcy]
  unfold rl
  rw [h1, h2]
  linarith



/-! ### Summing over a colour -/

/-- The per-colour eq-deficiency. -/
def RC (k : ℕ) (X Z T M B : Finset ℕ) (y : ℕ) : ℤ :=
  ∑ a ∈ X.erase y, ∑ c ∈ Z.erase y, rC k T M B (a, y, c)

theorem QC_eq (k : ℕ) (X Z T M B : Finset ℕ) (y : ℕ) :
    QC k X Z T M B y = cc k * QH k X Z T M B y + RC k X Z T M B y := by
  unfold QC QH RC dC rC
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]

/-- `|T ∩ B| ≥ k - |M \ T| - |M \ B|`. -/
theorem card_inter_ge {k : ℕ} {T M B : Finset ℕ} (hT : T.card = k) (hM : M.card = k)
    (hB : B.card = k) :
    (k : ℤ) - (M.filter (· ∉ T)).card - (M.filter (· ∉ B)).card ≤ ((T ∩ B).card : ℤ) := by
  have h1 : T ⊆ (T ∩ B) ∪ (T.filter (· ∉ M)) ∪ (M.filter (· ∉ B)) := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_filter]
    by_cases hB' : x ∈ B
    · exact Or.inl (Or.inl ⟨hx, hB'⟩)
    · by_cases hM' : x ∈ M
      · exact Or.inr ⟨hM', hB'⟩
      · exact Or.inl (Or.inr ⟨hx, hM'⟩)
  have h2 : (T.filter (· ∉ M)).card = (M.filter (· ∉ T)).card := by
    rw [← Finset.sdiff_eq_filter, ← Finset.sdiff_eq_filter]
    have a1 := Finset.card_sdiff_add_card_inter T M
    have a2 := Finset.card_sdiff_add_card_inter M T
    rw [Finset.inter_comm] at a2
    omega
  have h3 := Finset.card_le_card h1
  have h4 := Finset.card_union_le ((T ∩ B) ∪ (T.filter (· ∉ M))) (M.filter (· ∉ B))
  have h5 := Finset.card_union_le (T ∩ B) (T.filter (· ∉ M))
  rw [hT] at h3
  omega

/-- The colours of `S` in `T \ M` are at most `|M \ T|`. -/
theorem card_filter_TM_le' {k : ℕ} (S : Finset ℕ) {T M : Finset ℕ} (hT : T.card = k)
    (hM : M.card = k) :
    ((S.filter (fun a => a ∈ T ∧ a ∉ M)).card : ℤ) ≤ (M.filter (· ∉ T)).card := by
  have h1 : S.filter (fun a => a ∈ T ∧ a ∉ M) ⊆ T.filter (· ∉ M) := by
    intro a ha; simp only [Finset.mem_filter] at ha ⊢; exact ha.2
  have h2 : (T.filter (· ∉ M)).card = (M.filter (· ∉ T)).card := by
    rw [← Finset.sdiff_eq_filter, ← Finset.sdiff_eq_filter]
    have a1 := Finset.card_sdiff_add_card_inter T M
    have a2 := Finset.card_sdiff_add_card_inter M T
    rw [Finset.inter_comm] at a2
    omega
  have := Finset.card_le_card h1
  omega

/-- The lower bound on the per-colour eq-deficiency. -/
def RLp (k : ℕ) (X Z T M B : Finset ℕ) (y : ℕ) : ℤ :=
  ((X.erase y).card : ℤ) * (Z.erase y).card
      * (((k : ℤ) - 3) * (1 - ind (y ∈ M))
          - ((M.erase y).card : ℤ) * ((M.filter (· ∉ T)).card + (M.filter (· ∉ B)).card))
    - ((Z.erase y).card : ℤ) * ((M.filter (· ∉ T)).card + ((X.erase y).filter (· ∉ T)).card)
    - ((X.erase y).card : ℤ) * ((M.filter (· ∉ B)).card + ((Z.erase y).filter (· ∉ B)).card)

/-- Termwise facts used in the sum. -/
theorem ind_mem_ge (W M : Finset ℕ) (a : ℕ) : ind (a ∈ W) - ind (a ∉ M) ≤ ind (a ∈ W ∧ a ∈ M) := by
  unfold ind; by_cases h1 : a ∈ W <;> by_cases h2 : a ∈ M <;> simp [h1, h2]

theorem ind_ne_and (a c : ℕ) (p : Prop) [Decidable p] :
    ind (a ≠ c ∧ p) = ind p - ind (a = c) * ind p := by
  unfold ind; by_cases h1 : a = c <;> by_cases h2 : p <;> simp [h1, h2]

set_option maxHeartbeats 1000000 in
/-- **The per-colour bound on the eq-deficiency.** -/
theorem RLp_le_RC {k : ℕ} (hk : 5 ≤ k) {X Z T M B : Finset ℕ} (hX : NearK k X) (hZ : NearK k Z)
    (hT : T.card = k) (hM : M.card = k) (hB : B.card = k) (y : ℕ) :
    RLp k X Z T M B y ≤ RC k X Z T M B y := by
  -- `RC ≥ ∑ rl`
  have hrl : ∑ a ∈ X.erase y, ∑ c ∈ Z.erase y, rl k T M B y a c ≤ RC k X Z T M B y := by
    unfold RC
    exact Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun c hc =>
      rl_le_rC T M B (Finset.ne_of_mem_erase ha) (Finset.ne_of_mem_erase hc)
  refine le_trans ?_ hrl
  -- rewrite `rl` termwise into a sum of indicator products
  have hpt : ∀ a ∈ X.erase y, ∀ c ∈ Z.erase y, rl k T M B y a c
      = ((M.erase y).card : ℤ) * ((T ∩ B).card : ℤ) - (M.erase y).card - gam k
        - ((M.erase y).card : ℤ) * ind (a ∈ T ∩ B)
        - ((M.erase y).card : ℤ) * (ind (c ∈ T ∩ B) - ind (a = c) * ind (c ∈ T ∩ B))
        + ind (a ∈ T ∩ B ∧ a ∈ M)
        + (ind (c ∈ T ∩ B ∧ c ∈ M) - ind (a = c) * ind (c ∈ T ∩ B ∧ c ∈ M))
        - del k * ind (a = c) := by
    intro a _ c _
    unfold rl
    rw [ind_ne_and a c (c ∈ T ∩ B), ind_ne_and a c (c ∈ T ∩ B ∧ c ∈ M)]
    ring
  rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun c hc => hpt a ha c hc]
  -- collapse everything with `sum_add_distrib` etc.
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum]
  -- the diagonal sums: `∑_a ∑_c ind (a = c) * f c = ∑_c ind (c ∈ X \ y) * f c`
  have diag : ∀ f : ℕ → ℤ, ∑ a ∈ X.erase y, ∑ c ∈ Z.erase y, ind (a = c) * f c
      = ∑ c ∈ Z.erase y, ind (c ∈ X.erase y) * f c := by
    intro f
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    unfold ind
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq']
  have diag1 : ∑ a ∈ X.erase y, ∑ c ∈ Z.erase y, ind (a = c)
      = ∑ c ∈ Z.erase y, ind (c ∈ X.erase y) * 1 := by
    rw [← diag]; simp
  rw [diag, diag, diag1]
  set x : ℤ := ((X.erase y).card : ℤ) with hx
  set z : ℤ := ((Z.erase y).card : ℤ) with hz
  set μ : ℤ := ((M.erase y).card : ℤ) with hμ
  set w : ℤ := ((T ∩ B).card : ℤ) with hw
  have eXW : ∑ a ∈ X.erase y, ind (a ∈ T ∩ B) = x - ∑ a ∈ X.erase y, ind (a ∉ T ∩ B) := by
    have : ∀ a ∈ X.erase y, ind (a ∈ T ∩ B) = 1 - ind (a ∉ T ∩ B) := fun a _ => by
      unfold ind; by_cases h : a ∈ T ∩ B <;> simp [h]
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have eZW : ∑ c ∈ Z.erase y, ind (c ∈ T ∩ B) = z - ∑ c ∈ Z.erase y, ind (c ∉ T ∩ B) := by
    have : ∀ c ∈ Z.erase y, ind (c ∈ T ∩ B) = 1 - ind (c ∉ T ∩ B) := fun c _ => by
      unfold ind; by_cases h : c ∈ T ∩ B <;> simp [h]
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have eXM : ∑ a ∈ X.erase y, ind (a ∈ T ∩ B) - ∑ a ∈ X.erase y, ind (a ∉ M)
      ≤ ∑ a ∈ X.erase y, ind (a ∈ T ∩ B ∧ a ∈ M) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_le_sum fun a _ => ind_mem_ge _ _ a
  have eZM : ∑ c ∈ Z.erase y, ind (c ∈ T ∩ B) - ∑ c ∈ Z.erase y, ind (c ∉ M)
      ≤ ∑ c ∈ Z.erase y, ind (c ∈ T ∩ B ∧ c ∈ M) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_le_sum fun c _ => ind_mem_ge _ _ c
  set XW : ℤ := ∑ a ∈ X.erase y, ind (a ∈ T ∩ B) with hXW
  set ZW : ℤ := ∑ c ∈ Z.erase y, ind (c ∈ T ∩ B) with hZW
  set XMW : ℤ := ∑ a ∈ X.erase y, ind (a ∈ T ∩ B ∧ a ∈ M) with hXMW
  set ZMW : ℤ := ∑ c ∈ Z.erase y, ind (c ∈ T ∩ B ∧ c ∈ M) with hZMW
  set qW : ℤ := ∑ a ∈ X.erase y, ind (a ∉ T ∩ B) with hqW
  set qW' : ℤ := ∑ c ∈ Z.erase y, ind (c ∉ T ∩ B) with hqW'
  set nX : ℤ := ∑ a ∈ X.erase y, ind (a ∉ M) with hnX
  set nZ : ℤ := ∑ c ∈ Z.erase y, ind (c ∉ M) with hnZ
  set D1 : ℤ := ∑ c ∈ Z.erase y, ind (c ∈ X.erase y) * ind (c ∈ T ∩ B) with hD1
  set D2 : ℤ := ∑ c ∈ Z.erase y, ind (c ∈ X.erase y) * ind (c ∈ T ∩ B ∧ c ∈ M) with hD2
  set XZ : ℤ := ∑ c ∈ Z.erase y, ind (c ∈ X.erase y) * 1 with hXZ
  -- pointwise facts about the diagonal sums
  have hD21 : D2 ≤ D1 := Finset.sum_le_sum fun c _ => by
    unfold ind; by_cases h1 : c ∈ X.erase y <;> by_cases h2 : c ∈ T ∩ B <;> by_cases h3 : c ∈ M <;>
      simp [h1, h2, h3]
  have hXZ1 : XZ ≤ D1 + qW' := by
    rw [hXZ, hD1, hqW', ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun c _ => by
      unfold ind; by_cases h1 : c ∈ X.erase y <;> by_cases h2 : c ∈ T ∩ B <;> simp [h1, h2]
  have hD10 : 0 ≤ D1 := Finset.sum_nonneg fun c _ => mul_nonneg (ind_nonneg _) (ind_nonneg _)
  -- the global cardinality facts
  obtain ⟨hx1, hx2⟩ := card_erase_bounds hX y
  obtain ⟨hz1, hz2⟩ := card_erase_bounds hZ y
  have hμ' : μ = (k : ℤ) - ind (y ∈ M) := by rw [hμ, card_erase_int, hM]
  have hμ1 : (k : ℤ) - 1 ≤ μ := by
    have := ind_le_one (y ∈ M); linarith
  have hw' := card_inter_ge hT hM hB
  have hnX' : nX ≤ (M.filter (· ∉ T)).card + ((X.erase y).filter (· ∉ T)).card := by
    rw [hnX, sum_ind_filter]
    have := card_notMem_le (X.erase y) T M
    have := card_filter_TM_le' (X.erase y) hT hM
    linarith
  have hnZ' : nZ ≤ (M.filter (· ∉ B)).card + ((Z.erase y).filter (· ∉ B)).card := by
    rw [hnZ, sum_ind_filter]
    have := card_notMem_le (Z.erase y) B M
    have := card_filter_TM_le' (Z.erase y) hB hM
    linarith
  have hqW0 : 0 ≤ qW := Finset.sum_nonneg fun _ _ => ind_nonneg _
  have hqW0' : 0 ≤ qW' := Finset.sum_nonneg fun _ _ => ind_nonneg _
  have hgam : ((gam k : ℕ) : ℤ) = ((k : ℤ) - 2) ^ 2 + 1 := by
    unfold gam; push_cast [Nat.cast_sub (by omega : 2 ≤ k)]; ring
  have hdel : ((del k : ℕ) : ℤ) = (k : ℤ) - 2 := by
    unfold del; push_cast [Nat.cast_sub (by omega : 2 ≤ k)]; ring
  have hk2 : (3 : ℤ) ≤ (k : ℤ) - 2 := by omega
  -- the products that carry the inequality
  have P1 : 0 ≤ z * (XMW - XW + nX) := mul_nonneg (by linarith) (by linarith)
  have P2 : 0 ≤ x * (ZMW - ZW + nZ) := mul_nonneg (by linarith) (by linarith)
  have P3 : 0 ≤ (μ - 1 - ((k : ℤ) - 2)) * D1 := mul_nonneg (by linarith) hD10
  have P4 : 0 ≤ (μ - 1) * z * qW := mul_nonneg (mul_nonneg (by linarith) (by linarith)) hqW0
  have P5 : 0 ≤ ((μ - 1) * x - ((k : ℤ) - 2)) * qW' := by
    apply mul_nonneg _ hqW0'
    nlinarith [mul_le_mul (show (k:ℤ) - 2 ≤ μ - 1 by linarith) hx1 (by linarith) (by linarith)]
  have P6 : 0 ≤ μ * x * z * (w - ((k : ℤ) - (M.filter (· ∉ T)).card - (M.filter (· ∉ B)).card)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) (by linarith)
  have P7 : 0 ≤ z * ((M.filter (· ∉ T)).card + ((X.erase y).filter (· ∉ T)).card - nX) :=
    mul_nonneg (by linarith) (by linarith)
  have P8 : 0 ≤ x * ((M.filter (· ∉ B)).card + ((Z.erase y).filter (· ∉ B)).card - nZ) :=
    mul_nonneg (by linarith) (by linarith)
  have P9 : 0 ≤ ((k : ℤ) - 2) * (D1 + qW' - XZ) := mul_nonneg (by linarith) (by linarith)
  have key : x * z * (μ * ((k : ℤ) - 3)) = x * z * (((k : ℤ) - ind (y ∈ M)) * ((k : ℤ) - 3)) := by
    rw [hμ']
  have e1 : z * (μ * XW) = z * (μ * (x - qW)) := by rw [eXW]
  have e2 : μ * (x * ZW) = μ * (x * (z - qW')) := by rw [eZW]
  have e3 : z * XW = z * (x - qW) := by rw [eXW]
  have e4 : x * ZW = x * (z - qW') := by rw [eZW]
  unfold RLp
  rw [← hx, ← hz, ← hμ, hgam, hdel]
  linarith [P1, P2, P3, P4, P5, P6, P7, P8, P9, hD21, key, e1, e2, e3, e4]

/-! ### The pair lemma -/

theorem card_filter_erase_eq (M T : Finset ℕ) (y : ℕ) :
    (((M.erase y).filter (· ∉ T)).card : ℤ) = (M.filter (· ∉ T)).card - ind (y ∈ M ∧ y ∉ T) := by
  rw [Finset.filter_erase, card_erase_int]
  congr 1
  unfold ind; simp only [Finset.mem_filter]

theorem two_ind_le_card (M T : Finset ℕ) {y₁ y₂ : ℕ} (hne : y₁ ≠ y₂) :
    ind (y₁ ∈ M ∧ y₁ ∉ T) + ind (y₂ ∈ M ∧ y₂ ∉ T) ≤ ((M.filter (· ∉ T)).card : ℤ) := by
  have key : ∀ u, ind (u ∈ M ∧ u ∉ T) = ind (u ∈ M.filter (· ∉ T)) := fun u => by
    unfold ind; simp only [Finset.mem_filter]
  rw [key, key]
  unfold ind
  by_cases h1 : y₁ ∈ M.filter (· ∉ T) <;> by_cases h2 : y₂ ∈ M.filter (· ∉ T) <;>
    simp only [h1, h2, if_true, if_false]
  · have hsub : ({y₁, y₂} : Finset ℕ) ⊆ M.filter (· ∉ T) := by
      intro a ha
      rw [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> assumption
    have := Finset.card_le_card hsub
    rw [Finset.card_pair hne] at this
    push_cast; omega
  · have := Finset.card_pos.mpr ⟨y₁, h1⟩; push_cast; omega
  · have := Finset.card_pos.mpr ⟨y₂, h2⟩; push_cast; omega
  · positivity

theorem card_erase_coupling {X : Finset ℕ} (y₁ y₂ : ℕ) :
    ((X.erase y₂).card : ℤ) ≤ (X.erase y₁).card + 1 := by
  have h1 := Finset.card_erase_le (s := X) (a := y₂)
  have h2 := Finset.pred_card_le_card_erase (s := X) (a := y₁)
  omega

set_option maxHeartbeats 1000000 in
/-- **The `(C1_r)` pair lemma for `k ≥ 5`.** -/
theorem pairC_of_five {k : ℕ} (hk : 5 ≤ k) {X Z T M B : Finset ℕ} (hX : NearK k X) (hZ : NearK k Z)
    (hT : T.card = k) (hM : M.card = k) (hB : B.card = k) : PairC k X Z T M B := by
  intro y₁ y₂ hne
  rw [QC_eq, QC_eq]
  have hQ1 := LamP_le_QH hk hX hZ hT hM hB y₁
  have hQ2 := LamP_le_QH hk hX hZ hT hM hB y₂
  have hR1 := RLp_le_RC hk hX hZ hT hM hB y₁
  have hR2 := RLp_le_RC hk hX hZ hT hM hB y₂
  have hcc : (0 : ℤ) ≤ cc k := by positivity
  -- reduce to the arithmetic lemma
  suffices h : 0 ≤ cc k * (LamP k X Z T M B y₁ + LamP k X Z T M B y₂)
      + RLp k X Z T M B y₁ + RLp k X Z T M B y₂ by
    linarith [mul_le_mul_of_nonneg_left hQ1 hcc, mul_le_mul_of_nonneg_left hQ2 hcc]
  unfold LamP Lam RLp
  rw [card_filter_erase_eq M T y₁, card_filter_erase_eq M T y₂, card_filter_erase_eq M B y₁,
    card_filter_erase_eq M B y₂, card_erase_int M y₁, card_erase_int M y₂, hM]
  obtain ⟨hx1, hx1'⟩ := card_erase_bounds hX y₁
  obtain ⟨hz1, hz1'⟩ := card_erase_bounds hZ y₁
  obtain ⟨hx2, hx2'⟩ := card_erase_bounds hX y₂
  obtain ⟨hz2, hz2'⟩ := card_erase_bounds hZ y₂
  have cx1 := card_erase_coupling (X := X) y₁ y₂
  have cx2 := card_erase_coupling (X := X) y₂ y₁
  have cz1 := card_erase_coupling (X := Z) y₁ y₂
  have cz2 := card_erase_coupling (X := Z) y₂ y₁
  have ht := two_ind_le_card M T hne
  have hb := two_ind_le_card M B hne
  have hpM1 : ind (y₁ ∈ M ∧ y₁ ∉ T) ≤ ind (y₁ ∈ M) := by unfold ind; split_ifs <;> simp_all
  have hpM2 : ind (y₂ ∈ M ∧ y₂ ∉ T) ≤ ind (y₂ ∈ M) := by unfold ind; split_ifs <;> simp_all
  have hqM1 : ind (y₁ ∈ M ∧ y₁ ∉ B) ≤ ind (y₁ ∈ M) := by unfold ind; split_ifs <;> simp_all
  have hqM2 : ind (y₂ ∈ M ∧ y₂ ∉ B) ≤ ind (y₂ ∈ M) := by unfold ind; split_ifs <;> simp_all
  have hk' : (5 : ℤ) ≤ k := by exact_mod_cast hk
  have hk2 : (3 : ℤ) ≤ (k : ℤ) - 2 := by omega
  -- the surplus terms have nonnegative coefficients
  have hqT1 : (0 : ℤ) ≤ ((X.erase y₁).filter (· ∉ T)).card := by positivity
  have hqT2 : (0 : ℤ) ≤ ((X.erase y₂).filter (· ∉ T)).card := by positivity
  have hqB1 : (0 : ℤ) ≤ ((Z.erase y₁).filter (· ∉ B)).card := by positivity
  have hqB2 : (0 : ℤ) ≤ ((Z.erase y₂).filter (· ∉ B)).card := by positivity
  have hcc13 : (13 : ℤ) ≤ cc k := by
    have h : 13 ≤ cc k := by
      unfold cc
      have h1 : 3 ≤ k - 2 := by omega
      have h2 : 13 ≤ (k - 1) * (k - 2) + 1 := by
        have : 4 ≤ k - 1 := by omega
        nlinarith
      calc 13 = 1 * 13 := by norm_num
        _ ≤ (k - 2) * ((k - 1) * (k - 2) + 1) := Nat.mul_le_mul (by omega) h2
    exact_mod_cast h
  have hcT : ∀ (z μ : ℤ), (k : ℤ) - 2 ≤ z → (k : ℤ) - 1 ≤ μ →
      z ≤ cc k * (((k : ℤ) - 2) * z * (μ - 1) - 1) := by
    intro z μ hz hμ
    have h1 : 9 * z - 1 ≤ ((k : ℤ) - 2) * z * (μ - 1) - 1 := by
      have := mul_le_mul (mul_le_mul hk2 (le_refl z) (by linarith) (by linarith))
        (show (3 : ℤ) ≤ μ - 1 by linarith) (by norm_num) (mul_nonneg (by linarith) (by linarith))
      linarith
    have h2 : z ≤ 13 * (9 * z - 1) := by linarith
    calc z ≤ 13 * (9 * z - 1) := h2
      _ ≤ cc k * (9 * z - 1) := mul_le_mul_of_nonneg_right hcc13 (by linarith)
      _ ≤ cc k * (((k : ℤ) - 2) * z * (μ - 1) - 1) := mul_le_mul_of_nonneg_left h1 (by linarith)
  have hcB : ∀ (x μ : ℤ), (k : ℤ) - 2 ≤ x → (k : ℤ) - 1 ≤ μ →
      x ≤ cc k * (((k : ℤ) - 2) * x * (μ - 1)) := by
    intro x μ hx hμ
    have h1 : 9 * x ≤ ((k : ℤ) - 2) * x * (μ - 1) := by
      have := mul_le_mul (mul_le_mul hk2 (le_refl x) (by linarith) (by linarith))
        (show (3 : ℤ) ≤ μ - 1 by linarith) (by norm_num) (mul_nonneg (by linarith) (by linarith))
      linarith
    calc x ≤ 13 * (9 * x) := by linarith
      _ ≤ cc k * (9 * x) := mul_le_mul_of_nonneg_right hcc13 (by linarith)
      _ ≤ cc k * (((k : ℤ) - 2) * x * (μ - 1)) := mul_le_mul_of_nonneg_left h1 (by linarith)
  have hμ1 : (k : ℤ) - 1 ≤ (k : ℤ) - ind (y₁ ∈ M) := by have := ind_le_one (y₁ ∈ M); linarith
  have hμ2 : (k : ℤ) - 1 ≤ (k : ℤ) - ind (y₂ ∈ M) := by have := ind_le_one (y₂ ∈ M); linarith
  have s1 := mul_le_mul_of_nonneg_right (hcT _ _ hz1 hμ1) hqT1
  have s2 := mul_le_mul_of_nonneg_right (hcT _ _ hz2 hμ2) hqT2
  have s3 := mul_le_mul_of_nonneg_right (hcB _ _ hx1 hμ1) hqB1
  have s4 := mul_le_mul_of_nonneg_right (hcB _ _ hx2 hμ2) hqB2
  have hcc' : ((cc k : ℕ) : ℤ) = ((k : ℤ) - 2) * (((k : ℤ) - 1) * ((k : ℤ) - 2) + 1) := by
    unfold cc; push_cast [Nat.cast_sub (by omega : 2 ≤ k), Nat.cast_sub (by omega : 1 ≤ k)]; ring
  have core := pairC_arith' (cc k : ℤ) (k : ℤ) ((M.filter (· ∉ T)).card : ℤ)
    ((M.filter (· ∉ B)).card : ℤ)
    ((X.erase y₁).card : ℤ) ((Z.erase y₁).card : ℤ) ((X.erase y₂).card : ℤ) ((Z.erase y₂).card : ℤ)
    (ind (y₁ ∈ M)) (ind (y₂ ∈ M)) (ind (y₁ ∈ M ∧ y₁ ∉ T)) (ind (y₂ ∈ M ∧ y₂ ∉ T))
    (ind (y₁ ∈ M ∧ y₁ ∉ B)) (ind (y₂ ∈ M ∧ y₂ ∉ B)) hcc' hk' hx1 hx1' hz1 hz1' hx2 hx2' hz2 hz2'
    cx2 cx1 cz2 cz1 (ind_nonneg _) (ind_le_one _) (ind_nonneg _) (ind_le_one _)
    (ind_nonneg _) (ind_nonneg _) (ind_nonneg _) (ind_nonneg _) ht hb
  rw [ind_not (y₁ ∈ M), ind_not (y₂ ∈ M)]
  linarith [core, s1, s2, s3, s4]

/-- **Both pair lemmas hold for `k ≥ 5`.** -/
theorem pairOK_of_five {k : ℕ} (hk : 5 ≤ k) : PairOK k :=
  fun _ _ _ _ _ hX hZ hT hM hB => ⟨pairH_of_five hk hX hZ hT hM hB, pairC_of_five hk hX hZ hT hM hB⟩

/-- **`P_3 □ P_{n+1}` is `k`-ECC for every `k ≥ 5`.** -/
theorem ecc_grid3_of_five {k : ℕ} (hk : 5 ≤ k) (n : ℕ) :
    (ListColoring.pathG 2 □ ListColoring.pathG n).ECCAt k :=
  ecc_of_pairOK (by omega) (pairOK_of_five hk) n

end Grid3
