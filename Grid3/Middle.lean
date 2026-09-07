/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.Column

/-!
# Fibring over the middle colour, and the pair lemmas

The column inequalities of `Grid3.Column` are sums over the states `(a, y, c)` of a column; here
they are rewritten as sums over the middle colour `y` of per-colour terms `QH y`, `QC y` which do
not depend on the middle list `Y` at all. A **pair lemma** — `QH y₁ + QH y₂ ≥ 0` for any two
distinct colours — then gives the column inequality for every `Y` with at least two colours.
-/

open Finset

namespace Grid3

/-! ### Sums over a column -/

/-- A sum over the states of a column, fibred over the middle colour. -/
theorem sum_states {β : Type*} [AddCommMonoid β] (X Y Z : Finset ℕ) (f : State → β) :
    ∑ s ∈ states X Y Z, f s = ∑ y ∈ Y, ∑ a ∈ X.erase y, ∑ c ∈ Z.erase y, f (a, y, c) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := states X Y Z) (t := Y) (g := fun s : State => s.2.1)
    (fun s hs => (mem_states.mp hs).2.1)]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [filter_mid_eq_image X Y Z hy, Finset.sum_image, Finset.sum_product]
  intro p _ q _ h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext h.1 h.2.2

theorem sum_eqInd (S : Finset State) : ∑ s ∈ S, eqInd s = (S.filter IsEq).card := by
  unfold eqInd
  rw [Finset.sum_boole]
  simp

/-! ### The per-state and per-colour terms -/

/-- The deficiency of a state against the uniform successor count. -/
def dH (k : ℕ) (T M B : Finset ℕ) (s : State) : ℤ := (succ T M B s : ℤ) - ene k - eqInd s

/-- The `(C1_r)` deficiency of a state. -/
def dC (k : ℕ) (T M B : Finset ℕ) (s : State) : ℤ :=
  cc k * dH k T M B s + ((eqSucc T M B s : ℤ) - gam k - del k * eqInd s)

/-- The per-middle-colour term of `(H1)`. -/
def QH (k : ℕ) (X Z T M B : Finset ℕ) (y : ℕ) : ℤ :=
  ∑ a ∈ X.erase y, ∑ c ∈ Z.erase y, dH k T M B (a, y, c)

/-- The per-middle-colour term of `(C1_r)`. -/
def QC (k : ℕ) (X Z T M B : Finset ℕ) (y : ℕ) : ℤ :=
  ∑ a ∈ X.erase y, ∑ c ∈ Z.erase y, dC k T M B (a, y, c)

theorem sum_dH (k : ℕ) (X Y Z T M B : Finset ℕ) :
    ∑ s ∈ states X Y Z, dH k T M B s
      = (∑ s ∈ states X Y Z, succ T M B s : ℕ) - ene k * (states X Y Z).card
          - ((states X Y Z).filter IsEq).card := by
  unfold dH
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, ← sum_eqInd]
  push_cast
  ring

theorem colH1_of_sum {k : ℕ} {X Y Z T M B : Finset ℕ}
    (h : 0 ≤ ∑ y ∈ Y, QH k X Z T M B y) : ColH1 k X Y Z T M B := by
  unfold ColH1
  unfold QH at h
  rw [← sum_states X Y Z (dH k T M B), sum_dH] at h
  zify
  push_cast at h ⊢
  linarith

theorem sum_dC (k : ℕ) (X Y Z T M B : Finset ℕ) :
    ∑ s ∈ states X Y Z, dC k T M B s
      = cc k * ((∑ s ∈ states X Y Z, succ T M B s : ℕ) - ene k * (states X Y Z).card
          - ((states X Y Z).filter IsEq).card)
        + ((∑ s ∈ states X Y Z, eqSucc T M B s : ℕ) - gam k * (states X Y Z).card
          - del k * ((states X Y Z).filter IsEq).card) := by
  unfold dC
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_dH, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum, ← sum_eqInd]
  push_cast
  ring

theorem colC1r_of_sum {k : ℕ} {X Y Z T M B : Finset ℕ}
    (h : 0 ≤ ∑ y ∈ Y, QC k X Z T M B y) : ColC1r k X Y Z T M B := by
  unfold ColC1r
  unfold QC at h
  rw [← sum_states X Y Z (dC k T M B), sum_dC] at h
  zify
  push_cast at h ⊢
  linarith

/-! ### From pairs to sums -/

/-- If every pair of distinct colours has a nonnegative sum, so does any set of at least two. -/
theorem sum_nonneg_of_pair {Y : Finset ℕ} (hY : 2 ≤ Y.card) (Q : ℕ → ℤ)
    (h : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ ≠ y₂ → 0 ≤ Q y₁ + Q y₂) : 0 ≤ ∑ y ∈ Y, Q y := by
  have hdouble : ∑ y₁ ∈ Y, ∑ y₂ ∈ Y.erase y₁, (Q y₁ + Q y₂)
      = 2 * ((Y.card : ℤ) - 1) * ∑ y ∈ Y, Q y := by
    have h1 : ∀ y₁ ∈ Y, ∑ y₂ ∈ Y.erase y₁, (Q y₁ + Q y₂)
        = ((Y.card : ℤ) - 1) * Q y₁ + (∑ y ∈ Y, Q y - Q y₁) := by
      intro y₁ hy₁
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem hy₁,
        Finset.sum_erase_eq_sub hy₁]
      have : 1 ≤ Y.card := Finset.card_pos.mpr ⟨y₁, hy₁⟩
      simp only [nsmul_eq_mul]
      push_cast [Nat.cast_sub this]
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul]
    ring
  have hnn : 0 ≤ ∑ y₁ ∈ Y, ∑ y₂ ∈ Y.erase y₁, (Q y₁ + Q y₂) :=
    Finset.sum_nonneg fun y₁ hy₁ => Finset.sum_nonneg fun y₂ hy₂ =>
      h y₁ hy₁ y₂ (Finset.mem_of_mem_erase hy₂) (Ne.symm (Finset.ne_of_mem_erase hy₂))
  rw [hdouble] at hnn
  have hc : (0 : ℤ) < 2 * ((Y.card : ℤ) - 1) := by
    have : (2 : ℤ) ≤ Y.card := by exact_mod_cast hY
    linarith
  exact (mul_nonneg_iff_of_pos_left hc).mp hnn

/-- **The pair lemmas.** -/
def PairH (k : ℕ) (X Z T M B : Finset ℕ) : Prop :=
  ∀ y₁ y₂ : ℕ, y₁ ≠ y₂ → 0 ≤ QH k X Z T M B y₁ + QH k X Z T M B y₂

def PairC (k : ℕ) (X Z T M B : Finset ℕ) : Prop :=
  ∀ y₁ y₂ : ℕ, y₁ ≠ y₂ → 0 ≤ QC k X Z T M B y₁ + QC k X Z T M B y₂

/-- **The pair condition** at list size `k`. -/
def PairOK (k : ℕ) : Prop :=
  ∀ X Z T M B : Finset ℕ, NearK k X → NearK k Z → T.card = k → M.card = k → B.card = k →
    PairH k X Z T M B ∧ PairC k X Z T M B

theorem two_le_card_of_nearK {k : ℕ} (hk : 3 ≤ k) {Y : Finset ℕ} (hY : NearK k Y) : 2 ≤ Y.card := by
  rcases hY with h | h <;> omega

/-- **Pairs suffice for the column condition.** -/
theorem colOK_of_pairOK {k : ℕ} (hk : 3 ≤ k) (h : PairOK k) : ColOK k := by
  intro X Y Z T M B hX hY hZ hT hM hB
  obtain ⟨hH, hC⟩ := h X Z T M B hX hZ hT hM hB
  have hY2 := two_le_card_of_nearK hk hY
  exact ⟨colH1_of_sum (sum_nonneg_of_pair hY2 _ fun y₁ _ y₂ _ hne => hH y₁ y₂ hne),
    colC1r_of_sum (sum_nonneg_of_pair hY2 _ fun y₁ _ y₂ _ hne => hC y₁ y₂ hne)⟩

/-- **The theorem, from the pair lemmas.** -/
theorem ecc_of_pairOK {k : ℕ} (hk : 3 ≤ k) (h : PairOK k) (n : ℕ) :
    (ListColoring.pathG 2 □ ListColoring.pathG n).ECCAt k :=
  ecc_of_colOK hk (colOK_of_pairOK hk h) n

end Grid3
