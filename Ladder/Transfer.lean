/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring

/-!
# The ladder transfer, and the invariant that certifies it

The mathematical core of "every ladder `P₂ □ Pₙ` is `k`-ECC for every `k ≥ 3'', with no graph in
sight. A rung carries a pair of distinct colours drawn from its two lists; `step` is the transfer
that extends a state vector across one rung; and everything rests on one invariant.

> **(I)** For every state `(a,b)`: `rowMass a + colMass b ≤ total`.

In words: no row plus column exceeds the total mass. Equivalently — and this is how it is used —
the mass sitting off a state's row *and* column is at least the mass at that state.

The uniform per-rung factor is `lam k = (k-1)(k-2) + 1 = k² - 3k + 3`, written that way because
`ℕ` subtraction is only well behaved here for `k ≥ 2`. The four lemmas of
`ai_research_notes/GRID_LADDER_ALL_K_2026-08-24.md` are, in order, `lam_le_ext_succ`,
`lam_mul_total_le`, `inv_ones` and `inv_step`; `total_vec_ge` assembles them.

Nothing in this file mentions a graph. `Ladder/Graph.lean` supplies the bridge.
-/

open Finset

namespace Ladder

/-! ### States and masses -/

/-- The states of a rung whose top vertex has list `A` and bottom vertex has list `B`: the ordered
pairs of distinct colours, one from each list. -/
def states (A B : Finset ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ B).filter fun p => p.1 ≠ p.2

theorem mem_states {A B : Finset ℕ} {p : ℕ × ℕ} :
    p ∈ states A B ↔ p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 ≠ p.2 := by
  simp [states, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- Total mass of a state vector. -/
def total (S : Finset (ℕ × ℕ)) (N : ℕ × ℕ → ℕ) : ℕ := ∑ p ∈ S, N p

/-- Mass in the row `a`. -/
def rowMass (S : Finset (ℕ × ℕ)) (N : ℕ × ℕ → ℕ) (a : ℕ) : ℕ :=
  ∑ p ∈ S.filter fun p => p.1 = a, N p

/-- Mass in the column `b`. -/
def colMass (S : Finset (ℕ × ℕ)) (N : ℕ × ℕ → ℕ) (b : ℕ) : ℕ :=
  ∑ p ∈ S.filter fun p => p.2 = b, N p

/-- **The invariant (I).** No row plus column exceeds the total. -/
def Inv (S : Finset (ℕ × ℕ)) (N : ℕ × ℕ → ℕ) : Prop :=
  ∀ p ∈ S, rowMass S N p.1 + colMass S N p.2 ≤ total S N

/-! ### The transfer -/

/-- The number of ways to colour the next rung `(c,d)` from lists `T`, `B` given that the current
rung is `(a,b)`: the successors avoid each other and each avoids its own predecessor. -/
def ext (T B : Finset ℕ) (a b : ℕ) : ℕ :=
  ((T ×ˢ B).filter fun q => q.1 ≠ q.2 ∧ q.1 ≠ a ∧ q.2 ≠ b).card

/-- One rung of transfer. -/
def step (S : Finset (ℕ × ℕ)) (N : ℕ × ℕ → ℕ) : ℕ × ℕ → ℕ :=
  fun q => ∑ p ∈ S.filter fun p => p.1 ≠ q.1 ∧ p.2 ≠ q.2, N p

/-- The uniform per-rung expansion factor `k² - 3k + 3`, written so that `ℕ` subtraction behaves
for `k ≥ 2`. -/
def lam (k : ℕ) : ℕ := (k - 1) * (k - 2) + 1

theorem lam_eq {k : ℕ} (hk : 2 ≤ k) : lam k + 3 * k = k * k + 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  show (m + 2 - 1) * (m + 2 - 2) + 1 + 3 * (m + 2) = (m + 2) * (m + 2) + 3
  have h1 : m + 2 - 1 = m + 1 := by omega
  have h2 : m + 2 - 2 = m := by omega
  rw [h1, h2]; ring

/-! ### The state vector along a ladder -/

/-- `rungs L j` is the state set of rung `j`, whose top list is `(L j).1` and bottom `(L j).2`. -/
def rungs (L : ℕ → Finset ℕ × Finset ℕ) (j : ℕ) : Finset (ℕ × ℕ) :=
  states (L j).1 (L j).2

/-- The state vector after `j` transfers, started from the all-ones vector on rung `0`. -/
def vec (L : ℕ → Finset ℕ × Finset ℕ) : ℕ → (ℕ × ℕ → ℕ)
  | 0 => fun _ => 1
  | j + 1 => step (rungs L j) (vec L j)

@[simp] theorem vec_zero (L : ℕ → Finset ℕ × Finset ℕ) : vec L 0 = fun _ => 1 := rfl

@[simp] theorem vec_succ (L : ℕ → Finset ℕ × Finset ℕ) (j : ℕ) :
    vec L (j + 1) = step (rungs L j) (vec L j) := rfl

/-! ### Counting the states -/

/-- **The state count.** The product misses exactly the diagonal, a copy of `A ∩ B`. -/
theorem card_states_add (A B : Finset ℕ) :
    (states A B).card + (A ∩ B).card = A.card * B.card := by
  classical
  have hdiag : (A ×ˢ B).filter (fun p => ¬ p.1 ≠ p.2) = (A ∩ B).image (fun c => (c, c)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Finset.mem_inter,
      not_ne_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, heq⟩
      exact ⟨p.1, ⟨h1, heq ▸ h2⟩, Prod.ext rfl heq⟩
    · rintro ⟨c, ⟨hc1, hc2⟩, rfl⟩
      exact ⟨⟨hc1, hc2⟩, rfl⟩
  have hinj : Function.Injective (fun c : ℕ => ((c, c) : ℕ × ℕ)) := fun x y h => congrArg Prod.fst h
  have h := Finset.card_filter_add_card_filter_not (s := A ×ˢ B) (p := fun p : ℕ × ℕ => p.1 ≠ p.2)
  rw [hdiag, Finset.card_image_of_injective _ hinj, Finset.card_product] at h
  exact h

theorem card_states_ge (A B : Finset ℕ) :
    A.card * B.card ≤ (states A B).card + (A ∩ B).card :=
  le_of_eq (card_states_add A B).symm

/-- A row of the state set injects into the bottom list. -/
theorem rowMass_ones_le {A B : Finset ℕ} (a : ℕ) :
    rowMass (states A B) (fun _ => 1) a ≤ B.card := by
  classical
  simp only [rowMass, Finset.sum_const, smul_eq_mul, mul_one]
  refine Finset.card_le_card_of_injOn (fun p => p.2) (fun p hp => ?_) (fun p hp q hq h => ?_)
  · have hp' := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
    exact Finset.mem_coe.mpr (mem_states.mp hp'.1).2.1
  · have hp' := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
    have hq' := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
    exact Prod.ext (hp'.2.trans hq'.2.symm) h

/-- A column of the state set injects into the top list. -/
theorem colMass_ones_le {A B : Finset ℕ} (b : ℕ) :
    colMass (states A B) (fun _ => 1) b ≤ A.card := by
  classical
  simp only [colMass, Finset.sum_const, smul_eq_mul, mul_one]
  refine Finset.card_le_card_of_injOn (fun p => p.1) (fun p hp => ?_) (fun p hp q hq h => ?_)
  · have hp' := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
    exact Finset.mem_coe.mpr (mem_states.mp hp'.1).1
  · have hp' := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
    have hq' := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
    exact Prod.ext h (hp'.2.trans hq'.2.symm)

/-- The successors of `(a,b)` are exactly the states of the two erased lists. -/
theorem ext_eq_card_states (T B : Finset ℕ) (a b : ℕ) :
    ext T B a b = (states (T.erase a) (B.erase b)).card := by
  classical
  unfold ext states
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_erase]
  tauto

/-! ### The four lemmas

The names match `ai_research_notes/GRID_LADDER_ALL_K_2026-08-24.md`. -/

/-- **Lemma 1′.** A rung never offers fewer than `lam k - 1 = (k-1)(k-2)` successors.

Erasing one colour from each list leaves at least `k-1` in each; the only pairs lost are diagonal,
and there are at most `min` of the two sizes of those. -/
theorem lam_le_ext_succ {k : ℕ} (hk : 3 ≤ k) {T B : Finset ℕ} (hT : T.card = k) (hB : B.card = k)
    (a b : ℕ) : lam k ≤ ext T B a b + 1 := by
  classical
  have hTc : k - 1 ≤ (T.erase a).card := by
    have := Finset.pred_card_le_card_erase (s := T) (a := a); omega
  have hBc : k - 1 ≤ (B.erase b).card := by
    have := Finset.pred_card_le_card_erase (s := B) (a := b); omega
  have hadd := card_states_add (T.erase a) (B.erase b)
  have hi : ((T.erase a) ∩ (B.erase b)).card ≤ (T.erase a).card :=
    Finset.card_le_card Finset.inter_subset_left
  have hsplit : (T.erase a).card * (B.erase b).card
      = (T.erase a).card * ((B.erase b).card - 1) + (T.erase a).card := by
    obtain ⟨m, hm⟩ : ∃ m, (B.erase b).card = m + 1 := ⟨(B.erase b).card - 1, by omega⟩
    rw [hm]; simp only [Nat.add_sub_cancel]; ring
  have hprod : (k - 1) * (k - 2) ≤ (T.erase a).card * ((B.erase b).card - 1) :=
    Nat.mul_le_mul hTc (by omega)
  rw [ext_eq_card_states, lam]
  omega

/-- **Lemma 2′.** Under the invariant, one rung multiplies the total by at least `lam k`. -/
theorem lam_mul_total_le {k : ℕ} (hk : 3 ≤ k) {S : Finset (ℕ × ℕ)} {N : ℕ × ℕ → ℕ}
    {T B : Finset ℕ} (hT : T.card = k) (hB : B.card = k) (hI : Inv S N) :
    lam k * total S N ≤ ∑ p ∈ S, N p * ext T B p.1 p.2 := by
  sorry

/-- **Lemma 3′.** The all-ones vector on a rung satisfies the invariant, exactly when `k ≥ 3`:
the two masses are at most `k` each, the total is at least `k² - k`, and `2k ≤ k² - k` iff
`k ≥ 3`. -/
theorem inv_ones {k : ℕ} (hk : 3 ≤ k) {A B : Finset ℕ} (hA : A.card = k) (hB : B.card = k) :
    Inv (states A B) (fun _ => 1) := by
  classical
  intro p _
  have htot : total (states A B) (fun _ => 1) = (states A B).card := by simp [total]
  have hrow : rowMass (states A B) (fun _ => 1) p.1 ≤ k := by
    rw [← hB]; exact rowMass_ones_le p.1
  have hcol : colMass (states A B) (fun _ => 1) p.2 ≤ k := by
    rw [← hA]; exact colMass_ones_le p.2
  have hcard : k * k ≤ (states A B).card + (A ∩ B).card := by
    have h := card_states_ge A B; rw [hA, hB] at h; exact h
  have hint : (A ∩ B).card ≤ k := by
    rw [← hA]; exact Finset.card_le_card Finset.inter_subset_left
  rw [htot]
  nlinarith [hrow, hcol, hcard, hint, hk]

/-- **Lemma 4′.** The transfer preserves the invariant. For `k ≥ 4` this needs no hypothesis on
`N` at all; at `k = 3` it is where (I) is spent. -/
theorem inv_step {k : ℕ} (hk : 3 ≤ k) {S : Finset (ℕ × ℕ)} {N : ℕ × ℕ → ℕ}
    {T B : Finset ℕ} (hT : T.card = k) (hB : B.card = k) (hI : Inv S N) :
    Inv (states T B) (step S N) := by
  sorry

/-- The transfer's total is the `ext`-weighted sum of the old one: double counting the pairs
(old state, compatible new state). -/
theorem total_step {S : Finset (ℕ × ℕ)} {N : ℕ × ℕ → ℕ} (T B : Finset ℕ) :
    total (states T B) (step S N) = ∑ p ∈ S, N p * ext T B p.1 p.2 := by
  classical
  have hext : ∀ p : ℕ × ℕ, ext T B p.1 p.2
      = ((states T B).filter fun q => p.1 ≠ q.1 ∧ p.2 ≠ q.2).card := by
    intro p
    unfold ext states
    congr 1
    ext q
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨hq1, hq2⟩, hne, ha, hb⟩
      exact ⟨⟨⟨hq1, hq2⟩, hne⟩, Ne.symm ha, Ne.symm hb⟩
    · rintro ⟨⟨⟨hq1, hq2⟩, hne⟩, ha, hb⟩
      exact ⟨⟨hq1, hq2⟩, hne, Ne.symm ha, Ne.symm hb⟩
  have h2 : ∀ p : ℕ × ℕ,
      (∑ q ∈ states T B, (if p.1 ≠ q.1 ∧ p.2 ≠ q.2 then N p else 0))
        = N p * ext T B p.1 p.2 := by
    intro p
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, ← hext p, mul_comm]
  have h1 : total (states T B) (step S N)
      = ∑ q ∈ states T B, ∑ p ∈ S, (if p.1 ≠ q.1 ∧ p.2 ≠ q.2 then N p else 0) := by
    simp only [total, step, Finset.sum_filter]
  rw [h1, Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => h2 p

/-! ### The theorem -/

/-- The invariant holds at every rung. -/
theorem inv_vec {k : ℕ} (hk : 3 ≤ k) {L : ℕ → Finset ℕ × Finset ℕ}
    (hL : ∀ j, (L j).1.card = k ∧ (L j).2.card = k) :
    ∀ j, Inv (rungs L j) (vec L j) := by
  intro j
  induction j with
  | zero => exact inv_ones hk (hL 0).1 (hL 0).2
  | succ j ih => exact inv_step hk (hL (j + 1)).1 (hL (j + 1)).2 ih

/-- **The transfer theorem.** After `n` rungs the total mass is at least `k(k-1)·lam k ^ n`, which
is exactly the uniform count. -/
theorem total_vec_ge {k : ℕ} (hk : 3 ≤ k) {L : ℕ → Finset ℕ × Finset ℕ}
    (hL : ∀ j, (L j).1.card = k ∧ (L j).2.card = k) (n : ℕ) :
    k * (k - 1) * lam k ^ n ≤ total (rungs L n) (vec L n) := by
  induction n with
  | zero =>
      -- the first rung already has `k² - |A ∩ B| ≥ k(k-1)` states
      have htot : total (rungs L 0) (vec L 0) = (rungs L 0).card := by simp [total, rungs]
      have hcard : k * k ≤ (rungs L 0).card + ((L 0).1 ∩ (L 0).2).card := by
        have h := card_states_ge (L 0).1 (L 0).2
        rw [(hL 0).1, (hL 0).2] at h
        exact h
      have hint : ((L 0).1 ∩ (L 0).2).card ≤ k := by
        rw [← (hL 0).1]; exact Finset.card_le_card Finset.inter_subset_left
      have hkk : k * (k - 1) + k = k * k := by
        obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring
      rw [pow_zero, mul_one, htot]
      omega
  | succ n ih =>
      have hstep : total (rungs L (n + 1)) (vec L (n + 1))
          = ∑ p ∈ rungs L n, vec L n p * ext (L (n + 1)).1 (L (n + 1)).2 p.1 p.2 :=
        total_step _ _
      have hlam : lam k * total (rungs L n) (vec L n)
          ≤ ∑ p ∈ rungs L n, vec L n p * ext (L (n + 1)).1 (L (n + 1)).2 p.1 p.2 :=
        lam_mul_total_le hk (hL (n + 1)).1 (hL (n + 1)).2 (inv_vec hk hL n)
      calc k * (k - 1) * lam k ^ (n + 1)
          = lam k * (k * (k - 1) * lam k ^ n) := by ring
        _ ≤ lam k * total (rungs L n) (vec L n) := Nat.mul_le_mul_left _ ih
        _ ≤ _ := by rw [hstep]; exact hlam

end Ladder
