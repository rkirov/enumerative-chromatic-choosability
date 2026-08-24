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

theorem states_ne {A B : Finset ℕ} {p : ℕ × ℕ} (hp : p ∈ states A B) : p.1 ≠ p.2 :=
  (mem_states.mp hp).2.2

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

/-! ### An exact formula for `ext`

Everything both remaining lemmas need is the observation that
`(T.erase a) ∩ (B.erase b) = (T ∩ B) \ {a, b}`, which turns `ext` into arithmetic in
`|T ∩ B|` and four membership indicators. -/

theorem inter_erase (T B : Finset ℕ) (a b : ℕ) :
    (T.erase a) ∩ (B.erase b) = ((T ∩ B).erase a).erase b := by
  classical
  ext c
  simp only [Finset.mem_inter, Finset.mem_erase]
  tauto

/-- `ext` in closed form: `ext + |T ∩ B| = |T \ a| · |B \ b| + [a ∈ T ∩ B] + [b ∈ T ∩ B]`. -/
theorem ext_add_card_inter {T B : Finset ℕ} {a b : ℕ} (hab : a ≠ b) :
    ext T B a b + (T ∩ B).card
      = (T.erase a).card * (B.erase b).card
        + (if a ∈ T ∩ B then 1 else 0) + (if b ∈ T ∩ B then 1 else 0) := by
  classical
  have h1 := card_states_add (T.erase a) (B.erase b)
  rw [← ext_eq_card_states] at h1
  rw [inter_erase] at h1
  -- peel the two erasures off `T ∩ B`
  have hb : (((T ∩ B).erase a).erase b).card + (if b ∈ (T ∩ B).erase a then 1 else 0)
      = ((T ∩ B).erase a).card := by
    by_cases h : b ∈ (T ∩ B).erase a
    · rw [if_pos h, Finset.card_erase_of_mem h]
      have : 0 < ((T ∩ B).erase a).card := Finset.card_pos.mpr ⟨b, h⟩
      omega
    · rw [if_neg h, Finset.erase_eq_of_notMem h]
      omega
  have ha : ((T ∩ B).erase a).card + (if a ∈ T ∩ B then 1 else 0) = (T ∩ B).card := by
    by_cases h : a ∈ T ∩ B
    · rw [if_pos h, Finset.card_erase_of_mem h]
      have : 0 < (T ∩ B).card := Finset.card_pos.mpr ⟨a, h⟩
      omega
    · rw [if_neg h, Finset.erase_eq_of_notMem h]
      omega
  have hbeq : (if b ∈ (T ∩ B).erase a then 1 else 0) = (if b ∈ T ∩ B then 1 else 0) := by
    by_cases h : b ∈ T ∩ B
    · rw [if_pos h, if_pos (Finset.mem_erase.mpr ⟨fun hc => hab hc.symm, h⟩)]
    · rw [if_neg h, if_neg (fun hc => h (Finset.mem_of_mem_erase hc))]
  rw [hbeq] at hb
  omega

theorem card_erase_add {T : Finset ℕ} {a : ℕ} :
    (T.erase a).card + (if a ∈ T then 1 else 0) = T.card := by
  classical
  by_cases h : a ∈ T
  · rw [if_pos h, Finset.card_erase_of_mem h]
    have : 0 < T.card := Finset.card_pos.mpr ⟨a, h⟩
    omega
  · rw [if_neg h, Finset.erase_eq_of_notMem h]
    omega

/-! ### The deficient state is unique, and everything off its row and column has slack

`lam_le_ext_succ` says `ext ≥ lam k - 1`. A state attaining that bound pins down `T` and `B`
completely: `T \ B = {x}`, `B \ T = {y}`, and `|T ∩ B| = k - 1`. -/

/-- The shape forced by a deficient state: the two lists differ in exactly one element each,
namely `x` and `y`, and share the remaining `k - 1`. -/
theorem deficient_structure {k : ℕ} (hk : 3 ≤ k) {T B : Finset ℕ} (hT : T.card = k)
    (hB : B.card = k) {x y : ℕ} (hxy : x ≠ y) (hdef : ext T B x y + 1 = lam k) :
    x ∈ T ∧ x ∉ B ∧ y ∈ B ∧ y ∉ T ∧ (T ∩ B).card = k - 1 := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  have hform := ext_add_card_inter (T := T) (B := B) hxy
  have hTe := card_erase_add (T := T) (a := x)
  have hBe := card_erase_add (T := B) (a := y)
  rw [hT] at hTe
  rw [hB] at hBe
  have hmT : (T ∩ B).card ≤ m + 3 := by
    rw [← hT]; exact Finset.card_le_card Finset.inter_subset_left
  have hlam : lam (m + 3) = (m + 2) * (m + 1) + 1 := by simp [lam]
  have hdef' : ext T B x y = (m + 2) * (m + 1) := by omega
  -- the four possible products, linearised against the atom `(m+2)*(m+1)`
  have hp1 : (m + 2) * (m + 2) = (m + 2) * (m + 1) + (m + 2) := by ring
  have hp2 : (m + 2) * (m + 3) = (m + 2) * (m + 1) + 2 * (m + 2) := by ring
  have hp3 : (m + 3) * (m + 2) = (m + 2) * (m + 1) + 2 * (m + 2) := by ring
  have hp4 : (m + 3) * (m + 3) = (m + 2) * (m + 1) + (3 * m + 7) := by ring
  -- Step 1: both erasures must drop an element, i.e. `x ∈ T` and `y ∈ B`.
  have hxT : x ∈ T := by
    by_contra hxT
    rw [if_neg hxT] at hTe
    have hTc : (T.erase x).card = m + 3 := by omega
    by_cases hyB : y ∈ B
    · rw [if_pos hyB] at hBe
      have hBc : (B.erase y).card = m + 2 := by omega
      rw [hTc, hBc, hdef', hp3] at hform
      have hix : (if x ∈ T ∩ B then 1 else 0) = 0 :=
        if_neg fun h => hxT (Finset.mem_inter.mp h).1
      rw [hix] at hform
      have : (if y ∈ T ∩ B then 1 else 0) ≤ 1 := by split <;> omega
      omega
    · rw [if_neg hyB] at hBe
      have hBc : (B.erase y).card = m + 3 := by omega
      rw [hTc, hBc, hdef', hp4] at hform
      have h1 : (if x ∈ T ∩ B then 1 else 0) ≤ 1 := by split <;> omega
      have h2 : (if y ∈ T ∩ B then 1 else 0) ≤ 1 := by split <;> omega
      omega
  have hyB : y ∈ B := by
    by_contra hyB
    rw [if_neg hyB] at hBe
    have hBc : (B.erase y).card = m + 3 := by omega
    rw [if_pos hxT] at hTe
    have hTc : (T.erase x).card = m + 2 := by omega
    rw [hTc, hBc, hdef', hp2] at hform
    have hiy : (if y ∈ T ∩ B then 1 else 0) = 0 :=
      if_neg fun h => hyB (Finset.mem_inter.mp h).2
    rw [hiy] at hform
    have : (if x ∈ T ∩ B then 1 else 0) ≤ 1 := by split <;> omega
    omega
  -- Step 2: with both erasures dropping, the intersection is pinned.
  rw [if_pos hxT] at hTe
  rw [if_pos hyB] at hBe
  have hTc : (T.erase x).card = m + 2 := by omega
  have hBc : (B.erase y).card = m + 2 := by omega
  rw [hTc, hBc, hdef', hp1] at hform
  -- Step 3: neither `x ∈ B` nor `y ∈ T`, else the intersection is everything and `T = B`.
  have hTB_of_full : (T ∩ B).card = m + 3 → T = B := by
    intro hfull
    have h1 : T ∩ B = T := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have h2 : T ∩ B = B := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact h1.symm.trans h2
  have hxB : x ∉ B := by
    intro hxB
    have hix : (if x ∈ T ∩ B then 1 else 0) = 1 := if_pos (Finset.mem_inter.mpr ⟨hxT, hxB⟩)
    have hiy1 : (if y ∈ T ∩ B then 1 else 0) ≤ 1 := by split <;> omega
    rw [hix] at hform
    have hfull : (T ∩ B).card = m + 3 := by omega
    have hyT : y ∈ T := by rw [hTB_of_full hfull]; exact hyB
    have hiy : (if y ∈ T ∩ B then 1 else 0) = 1 := if_pos (Finset.mem_inter.mpr ⟨hyT, hyB⟩)
    rw [hiy] at hform
    omega
  have hyT : y ∉ T := by
    intro hyT
    have hiy : (if y ∈ T ∩ B then 1 else 0) = 1 := if_pos (Finset.mem_inter.mpr ⟨hyT, hyB⟩)
    have hix : (if x ∈ T ∩ B then 1 else 0) = 0 :=
      if_neg fun h => hxB (Finset.mem_inter.mp h).2
    rw [hix, hiy] at hform
    have hfull : (T ∩ B).card = m + 3 := by omega
    exact hxB (by rw [← hTB_of_full hfull]; exact hxT)
  have hix : (if x ∈ T ∩ B then 1 else 0) = 0 := if_neg fun h => hxB (Finset.mem_inter.mp h).2
  have hiy : (if y ∈ T ∩ B then 1 else 0) = 0 := if_neg fun h => hyT (Finset.mem_inter.mp h).1
  rw [hix, hiy] at hform
  exact ⟨hxT, hxB, hyB, hyT, by omega⟩

/-- With the deficient shape in hand, every element of `T` other than `x` lies in `B`. -/
theorem mem_of_ne_of_card {k : ℕ} {T B : Finset ℕ} (hT : T.card = k) {x : ℕ} (hxT : x ∈ T)
    (hxB : x ∉ B) (hm : (T ∩ B).card = k - 1) (hk : 1 ≤ k) {c : ℕ} (hc : c ∈ T) (hcx : c ≠ x) :
    c ∈ B := by
  classical
  by_contra hcB
  have hsplit : (T \ B).card + (T ∩ B).card = T.card := Finset.card_sdiff_add_card_inter T B
  have hpair : ({x, c} : Finset ℕ) ⊆ T \ B := by
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact Finset.mem_sdiff.mpr ⟨hxT, hxB⟩
    · rw [Finset.mem_singleton] at hd
      subst hd
      exact Finset.mem_sdiff.mpr ⟨hc, hcB⟩
  have h2 : 2 ≤ (T \ B).card := by
    have := Finset.card_le_card hpair
    rwa [Finset.card_insert_of_notMem (by simpa using fun h => hcx h.symm),
      Finset.card_singleton] at this
  omega

/-- **The slack off the deficient row and column.** -/
theorem lam_succ_le_ext {k : ℕ} (hk : 3 ≤ k) {T B : Finset ℕ} (hT : T.card = k) (hB : B.card = k)
    {x y : ℕ} (hxT : x ∈ T) (hxB : x ∉ B) (hyB : y ∈ B) (hyT : y ∉ T)
    (hm : (T ∩ B).card = k - 1) {a b : ℕ} (hab : a ≠ b) (hax : a ≠ x) (hby : b ≠ y) :
    lam k + 1 ≤ ext T B a b := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  have hform := ext_add_card_inter (T := T) (B := B) hab
  have hTe := card_erase_add (T := T) (a := a)
  have hBe := card_erase_add (T := B) (a := b)
  rw [hT] at hTe
  rw [hB] at hBe
  have hlam : lam (m + 3) = (m + 2) * (m + 1) + 1 := by simp [lam]
  have hp1 : (m + 2) * (m + 2) = (m + 2) * (m + 1) + (m + 2) := by ring
  have hp2 : (m + 3) * (m + 2) = (m + 2) * (m + 1) + 2 * (m + 2) := by ring
  have hp3 : (m + 2) * (m + 3) = (m + 2) * (m + 1) + 2 * (m + 2) := by ring
  have hp4 : (m + 3) * (m + 3) = (m + 2) * (m + 1) + (3 * m + 7) := by ring
  by_cases haT : a ∈ T <;> by_cases hbB : b ∈ B
  · -- both present: both indicators fire, and the bound is met with equality
    have haB : a ∈ B := mem_of_ne_of_card hT hxT hxB hm (by omega) haT hax
    have hbT : b ∈ T := by
      refine mem_of_ne_of_card hB hyB hyT ?_ (by omega) hbB hby
      rwa [Finset.inter_comm]
    rw [if_pos haT] at hTe
    rw [if_pos hbB] at hBe
    have hTc : (T.erase a).card = m + 2 := by omega
    have hBc : (B.erase b).card = m + 2 := by omega
    rw [hTc, hBc, hp1, if_pos (Finset.mem_inter.mpr ⟨haT, haB⟩),
      if_pos (Finset.mem_inter.mpr ⟨hbT, hbB⟩)] at hform
    omega
  · have haB : a ∈ B := mem_of_ne_of_card hT hxT hxB hm (by omega) haT hax
    rw [if_pos haT] at hTe
    rw [if_neg hbB] at hBe
    have hTc : (T.erase a).card = m + 2 := by omega
    have hBc : (B.erase b).card = m + 3 := by omega
    rw [hTc, hBc, hp3, if_pos (Finset.mem_inter.mpr ⟨haT, haB⟩),
      if_neg (fun h => hbB (Finset.mem_inter.mp h).2)] at hform
    omega
  · have hbT : b ∈ T := by
      refine mem_of_ne_of_card hB hyB hyT ?_ (by omega) hbB hby
      rwa [Finset.inter_comm]
    rw [if_neg haT] at hTe
    rw [if_pos hbB] at hBe
    have hTc : (T.erase a).card = m + 3 := by omega
    have hBc : (B.erase b).card = m + 2 := by omega
    rw [hTc, hBc, hp2, if_neg (fun h => haT (Finset.mem_inter.mp h).1),
      if_pos (Finset.mem_inter.mpr ⟨hbT, hbB⟩)] at hform
    omega
  · rw [if_neg haT] at hTe
    rw [if_neg hbB] at hBe
    have hTc : (T.erase a).card = m + 3 := by omega
    have hBc : (B.erase b).card = m + 3 := by omega
    rw [hTc, hBc, hp4, if_neg (fun h => haT (Finset.mem_inter.mp h).1),
      if_neg (fun h => hbB (Finset.mem_inter.mp h).2)] at hform
    omega

/-- Every state other than the deficient one already reaches `lam k`. -/
theorem lam_le_ext_of_ne {k : ℕ} (hk : 3 ≤ k) {T B : Finset ℕ} (hT : T.card = k) (hB : B.card = k)
    {x y : ℕ} (hxT : x ∈ T) (hxB : x ∉ B) (hyB : y ∈ B) (hyT : y ∉ T)
    (hm : (T ∩ B).card = k - 1) {a b : ℕ} (hab : a ≠ b) (hne : ¬ (a = x ∧ b = y)) :
    lam k ≤ ext T B a b := by
  classical
  by_cases hax : a = x
  · -- then `b ≠ y`; the `x` row still has no slack lost, because `x ∉ B`
    have hby : b ≠ y := fun h => hne ⟨hax, h⟩
    subst hax
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    have hform := ext_add_card_inter (T := T) (B := B) hab
    have hTe := card_erase_add (T := T) (a := a)
    have hBe := card_erase_add (T := B) (a := b)
    rw [hT] at hTe
    rw [hB] at hBe
    have hlam : lam (m + 3) = (m + 2) * (m + 1) + 1 := by simp [lam]
    have hp1 : (m + 2) * (m + 2) = (m + 2) * (m + 1) + (m + 2) := by ring
    have hp3 : (m + 2) * (m + 3) = (m + 2) * (m + 1) + 2 * (m + 2) := by ring
    have hia : (if a ∈ T ∩ B then 1 else 0) = 0 :=
      if_neg fun h => hxB (Finset.mem_inter.mp h).2
    rw [if_pos hxT] at hTe
    have hTc : (T.erase a).card = m + 2 := by omega
    by_cases hbB : b ∈ B
    · have hbT : b ∈ T := by
        refine mem_of_ne_of_card hB hyB hyT ?_ (by omega) hbB hby
        rwa [Finset.inter_comm]
      rw [if_pos hbB] at hBe
      have hBc : (B.erase b).card = m + 2 := by omega
      rw [hTc, hBc, hp1, hia, if_pos (Finset.mem_inter.mpr ⟨hbT, hbB⟩)] at hform
      omega
    · rw [if_neg hbB] at hBe
      have hBc : (B.erase b).card = m + 3 := by omega
      rw [hTc, hBc, hp3, hia, if_neg (fun h => hbB (Finset.mem_inter.mp h).2)] at hform
      omega
  · by_cases hby : b = y
    · -- symmetric, using `y ∉ T`
      subst hby
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
      have hform := ext_add_card_inter (T := T) (B := B) hab
      have hTe := card_erase_add (T := T) (a := a)
      have hBe := card_erase_add (T := B) (a := b)
      rw [hT] at hTe
      rw [hB] at hBe
      have hlam : lam (m + 3) = (m + 2) * (m + 1) + 1 := by simp [lam]
      have hp1 : (m + 2) * (m + 2) = (m + 2) * (m + 1) + (m + 2) := by ring
      have hp2 : (m + 3) * (m + 2) = (m + 2) * (m + 1) + 2 * (m + 2) := by ring
      have hib : (if b ∈ T ∩ B then 1 else 0) = 0 :=
        if_neg fun h => hyT (Finset.mem_inter.mp h).1
      rw [if_pos hyB] at hBe
      have hBc : (B.erase b).card = m + 2 := by omega
      by_cases haT : a ∈ T
      · have haB : a ∈ B := mem_of_ne_of_card hT hxT hxB hm (by omega) haT hax
        rw [if_pos haT] at hTe
        have hTc : (T.erase a).card = m + 2 := by omega
        rw [hTc, hBc, hp1, hib, if_pos (Finset.mem_inter.mpr ⟨haT, haB⟩)] at hform
        omega
      · rw [if_neg haT] at hTe
        have hTc : (T.erase a).card = m + 3 := by omega
        rw [hTc, hBc, hp2, hib, if_neg (fun h => haT (Finset.mem_inter.mp h).1)] at hform
        omega
    · exact le_trans (Nat.le_succ _) (lam_succ_le_ext hk hT hB hxT hxB hyB hyT hm hab hax hby)

/-- The mass off a state's row and column, by inclusion-exclusion. -/
theorem sum_off_add {S : Finset (ℕ × ℕ)} {N : ℕ × ℕ → ℕ} {x y : ℕ} (hxy : (x, y) ∈ S) :
    (∑ p ∈ S.filter fun p => ¬ p.1 = x ∧ ¬ p.2 = y, N p) + rowMass S N x + colMass S N y
      = total S N + N (x, y) := by
  classical
  have h1 : rowMass S N x + (∑ p ∈ S.filter fun p => ¬ p.1 = x, N p) = total S N :=
    Finset.sum_filter_add_sum_filter_not S (fun p : ℕ × ℕ => p.1 = x) N
  have h2 : (∑ p ∈ S.filter fun p => ¬ p.1 = x ∧ p.2 = y, N p)
      + (∑ p ∈ S.filter fun p => ¬ p.1 = x ∧ ¬ p.2 = y, N p)
      = ∑ p ∈ S.filter fun p => ¬ p.1 = x, N p := by
    rw [← Finset.filter_filter, ← Finset.filter_filter]
    exact Finset.sum_filter_add_sum_filter_not _ (fun p : ℕ × ℕ => p.2 = y) N
  have hsingle : S.filter (fun p => p.1 = x ∧ p.2 = y) = {(x, y)} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h1', h2'⟩; exact Prod.ext h1' h2'
    · rintro rfl; exact ⟨hxy, rfl, rfl⟩
  have h3 : colMass S N y
      = N (x, y) + ∑ p ∈ S.filter fun p => ¬ p.1 = x ∧ p.2 = y, N p := by
    have := Finset.sum_filter_add_sum_filter_not (S.filter fun p : ℕ × ℕ => p.2 = y)
      (fun p : ℕ × ℕ => p.1 = x) N
    rw [Finset.filter_filter, Finset.filter_filter] at this
    have hcomm : S.filter (fun p : ℕ × ℕ => p.2 = y ∧ p.1 = x)
        = S.filter (fun p : ℕ × ℕ => p.1 = x ∧ p.2 = y) := by
      apply Finset.filter_congr; intro p _; exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    have hcomm2 : S.filter (fun p : ℕ × ℕ => p.2 = y ∧ ¬ p.1 = x)
        = S.filter (fun p : ℕ × ℕ => ¬ p.1 = x ∧ p.2 = y) := by
      apply Finset.filter_congr; intro p _; exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [hcomm, hcomm2, hsingle, Finset.sum_singleton] at this
    rw [colMass, ← this]
  omega

/-- **Lemma 2′.** Under the invariant, one rung multiplies the total by at least `lam k`.

If no state is deficient the bound is pointwise. Otherwise the unique deficient state `(x,y)` is
short by exactly one, and by `deficient_structure` every state off its row and column is long by
at least one; the invariant says there is at least as much mass off the row and column as at
`(x,y)` itself. -/
theorem lam_mul_total_le {k : ℕ} (hk : 3 ≤ k) {S : Finset (ℕ × ℕ)} {N : ℕ × ℕ → ℕ}
    {T B : Finset ℕ} (hT : T.card = k) (hB : B.card = k) (hSsub : ∀ p ∈ S, p.1 ≠ p.2)
    (hI : Inv S N) :
    lam k * total S N ≤ ∑ p ∈ S, N p * ext T B p.1 p.2 := by
  classical
  by_cases hall : ∀ p ∈ S, lam k ≤ ext T B p.1 p.2
  · calc lam k * total S N = ∑ p ∈ S, lam k * N p := by rw [total, Finset.mul_sum]
      _ ≤ ∑ p ∈ S, N p * ext T B p.1 p.2 := by
          refine Finset.sum_le_sum fun p hp => ?_
          rw [mul_comm]
          exact Nat.mul_le_mul_left _ (hall p hp)
  · push_neg at hall
    obtain ⟨q, hqS, hq⟩ := hall
    have hdef : ext T B q.1 q.2 + 1 = lam k := by
      have := lam_le_ext_succ hk hT hB q.1 q.2
      omega
    obtain ⟨hxT, hxB, hyB, hyT, hm⟩ :=
      deficient_structure hk hT hB (hSsub q hqS) hdef
    -- pointwise: the deficit at `q` is charged against the surplus off its row and column
    have hpoint : ∀ p ∈ S, lam k * N p + (if ¬ p.1 = q.1 ∧ ¬ p.2 = q.2 then N p else 0)
        ≤ N p * ext T B p.1 p.2 + (if p = q then N p else 0) := by
      intro p hp
      by_cases hoff : ¬ p.1 = q.1 ∧ ¬ p.2 = q.2
      · have hpq : p ≠ q := fun h => hoff.1 (by rw [h])
        rw [if_pos hoff, if_neg hpq]
        have hge := lam_succ_le_ext hk hT hB hxT hxB hyB hyT hm (hSsub p hp) hoff.1 hoff.2
        have hmul := Nat.mul_le_mul_left (N p) hge
        nlinarith [hmul]
      · rw [if_neg hoff, Nat.add_zero]
        by_cases hpq : p = q
        · subst hpq
          rw [if_pos rfl, ← hdef]
          nlinarith []
        · rw [if_neg hpq]
          have hnp : ¬ (p.1 = q.1 ∧ p.2 = q.2) := fun h => hpq (Prod.ext h.1 h.2)
          have hge := lam_le_ext_of_ne hk hT hB hxT hxB hyB hyT hm (hSsub p hp) hnp
          have hmul := Nat.mul_le_mul_left (N p) hge
          nlinarith [hmul]
    have hsum := Finset.sum_le_sum hpoint
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← total,
      ← Finset.sum_filter, Finset.sum_ite_eq' S q N, if_pos hqS] at hsum
    -- the invariant says there is at least `N q` of mass off `q`'s row and column
    have hq' : (q.1, q.2) ∈ S := by simpa using hqS
    have hoffsum := sum_off_add (N := N) hq'
    have hinv := hI q hqS
    have hNq : N q ≤ ∑ p ∈ S.filter fun p => ¬ p.1 = q.1 ∧ ¬ p.2 = q.2, N p := by
      have : N (q.1, q.2) = N q := by simp
      omega
    omega



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
        lam_mul_total_le hk (hL (n + 1)).1 (hL (n + 1)).2
          (fun p hp => states_ne hp) (inv_vec hk hL n)
      calc k * (k - 1) * lam k ^ (n + 1)
          = lam k * (k * (k - 1) * lam k ^ n) := by ring
        _ ≤ lam k * total (rungs L n) (vec L n) := Nat.mul_le_mul_left _ ih
        _ ≤ _ := by rw [hstep]; exact hlam

end Ladder
