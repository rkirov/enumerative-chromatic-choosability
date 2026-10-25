/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Cone

/-!
# Height five: fibre bounds and the chain lemma

`GridGen/Four/Fibre.lean` and `Fibre6.lean` with five rows, plus the chain lemma of
`ai_research_notes/H5_K6_ANALYTIC_2026-10-23.md` (Lemma 7).

* **The sharp one-row fibre bound** (`fibre_sharp`), for any type of states: if a predicate `P`
  pins one row to a value `φ` read off the other rows, every pinned state has at least `m` values
  for that row, and weights differ by at most the factor `R`, then
  `(R + m - 1) · Σ_P w ≤ R · Σ w`.
* **Rows of a five-row column** (`fibre_row1` … `fibre_row5`): the instances inside
  `(sts A₁ … A₅).filter Q`, for an event `Q` that does not read the changed row. An end row has
  its list minus one neighbour as values, a middle row its list minus two.
* **The chain lemma** (`chain_row1` … `chain_row5`): with all weights one,
  `m · #{t : Q t ∧ tᵣ = φ t} ≤ #{t : Q t}`.
* **Fourteen events** (`ev p`), one for each equality pattern of a proper column other than
  `01234`: all the equalities of the pattern. Peeling one row of an equality class at a time
  bounds the share of each event by a product of reciprocals of row option counts
  (`chain_bound`): for lists of at least `L` colours, an end row has `L - 1` options and a middle
  row `L - 2`, so e.g. `01010` has share at most `1/((L-1)²(L-2))`.
-/

namespace GridGen.Five

open Finset

/-! ### The abstract fibre bound -/

/-- **The sharp one-row fibre bound**, for states of any type. -/
theorem fibre_sharp {α : Type*} [DecidableEq α] {Ω : Finset α} (w : α → ℝ) (hw : ∀ t, 0 ≤ w t)
    (P : α → Prop) [DecidablePred P] (get : α → ℕ) (set : α → ℕ → α) (φ : α → ℕ)
    (opts : α → Finset ℕ) (m : ℕ) (hm : 1 ≤ m) (hopts : ∀ t ∈ Ω, m ≤ (opts t).card)
    (hcur : ∀ t ∈ Ω, get t ∈ opts t)
    (hmem : ∀ t ∈ Ω, ∀ x ∈ opts t, set t x ∈ Ω)
    (hget : ∀ t x, get (set t x) = x)
    (hset : ∀ t₁ t₂ x₁ x₂, set t₁ x₁ = set t₂ x₂ → get t₁ = get t₂ → t₁ = t₂)
    (hφ : ∀ t x, φ (set t x) = φ t)
    (hP : ∀ t, P t → get t = φ t)
    {R : ℝ} (hR0 : 0 < R) (hR : ∀ t ∈ Ω, ∀ t' ∈ Ω, w t ≤ R * w t') :
    (R + ((m : ℝ) - 1)) * ∑ t ∈ Ω.filter P, w t ≤ R * ∑ t ∈ Ω, w t := by
  classical
  set S := (Ω.filter P).sigma (fun t => (opts t).erase (get t)) with hS
  have h1 : ((m : ℝ) - 1) * ∑ t ∈ Ω.filter P, w t ≤ ∑ p ∈ S, w p.1 := by
    rw [hS, Finset.sum_sigma, Finset.mul_sum]
    refine Finset.sum_le_sum fun t ht => ?_
    obtain ⟨htΩ, -⟩ := Finset.mem_filter.mp ht
    show ((m : ℝ) - 1) * w t ≤ ∑ _x ∈ (opts t).erase (get t), w t
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : (m : ℝ) - 1 ≤ ((opts t).erase (get t)).card := by
      rw [Finset.card_erase_of_mem (hcur t htΩ)]
      have := hopts t htΩ
      have h1 : 1 ≤ (opts t).card := le_trans hm this
      rw [Nat.cast_sub h1]; push_cast
      have : (m : ℝ) ≤ (opts t).card := by exact_mod_cast this
      linarith
    exact mul_le_mul_of_nonneg_right hc (hw t)
  have h2 : ∑ p ∈ S, w p.1 ≤ ∑ p ∈ S, R * w (set p.1 p.2) := by
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨ht, hx⟩ := Finset.mem_sigma.mp hp
    obtain ⟨htΩ, -⟩ := Finset.mem_filter.mp ht
    exact hR p.1 htΩ _ (hmem p.1 htΩ p.2 (Finset.mem_of_mem_erase hx))
  have hinjS : Set.InjOn (fun p : (_ : α) × ℕ => set p.1 p.2) S := by
    intro p hp q hq hpq
    obtain ⟨hpt, hpx⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hqt, hqx⟩ := Finset.mem_sigma.mp hq
    obtain ⟨-, hpP⟩ := Finset.mem_filter.mp hpt
    obtain ⟨-, hqP⟩ := Finset.mem_filter.mp hqt
    have hx : p.2 = q.2 := by
      have := congrArg get hpq; simp only [hget] at this; exact this
    have hg : get p.1 = get q.1 := by
      rw [hP _ hpP, hP _ hqP, ← hφ p.1 p.2, ← hφ q.1 q.2]
      exact congrArg φ hpq
    exact Sigma.ext (hset _ _ _ _ hpq hg) (heq_of_eq hx)
  have h3 : ∑ p ∈ S, w (set p.1 p.2) ≤ ∑ t ∈ Ω.filter (fun t => ¬ P t), w t := by
    rw [← Finset.sum_image (f := w) hinjS]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun t _ _ => hw t)
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hpt, hpx⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hpΩ, hpP⟩ := Finset.mem_filter.mp hpt
    refine Finset.mem_filter.mpr ⟨hmem p.1 hpΩ p.2 (Finset.mem_of_mem_erase hpx), fun hP' => ?_⟩
    have e1 := hP _ hP'
    rw [hget, hφ, ← hP _ hpP] at e1
    exact (Finset.ne_of_mem_erase hpx) e1
  have h4 : ∑ t ∈ Ω, w t = ∑ t ∈ Ω.filter P, w t + ∑ t ∈ Ω.filter (fun t => ¬ P t), w t :=
    (Finset.sum_filter_add_sum_filter_not Ω P w).symm
  have h5 : ∑ p ∈ S, R * w (set p.1 p.2) = R * ∑ p ∈ S, w (set p.1 p.2) := by
    rw [Finset.mul_sum]
  have h6 := mul_le_mul_of_nonneg_left h3 hR0.le
  nlinarith

/-! ### Changing one row of a five-row column -/

/-- Overwrite one row. -/
def set1 (t : T5) (x : ℕ) : T5 := (x, t.2)
def set2 (t : T5) (x : ℕ) : T5 := (t.1, x, t.2.2)
def set3 (t : T5) (x : ℕ) : T5 := (t.1, t.2.1, x, t.2.2.2)
def set4 (t : T5) (x : ℕ) : T5 := (t.1, t.2.1, t.2.2.1, x, t.2.2.2.2)
def set5 (t : T5) (x : ℕ) : T5 := (t.1, t.2.1, t.2.2.1, t.2.2.2.1, x)

theorem card_erase1_ge (A : Finset ℕ) (a : ℕ) {m : ℕ} (hA : m + 1 ≤ A.card) :
    m ≤ (A.erase a).card := by
  have h1 := Finset.pred_card_le_card_erase (s := A) (a := a)
  omega

theorem card_erase2_ge (A : Finset ℕ) (a b : ℕ) {m : ℕ} (hA : m + 2 ≤ A.card) :
    m ≤ ((A.erase a).erase b).card := by
  have h1 := Finset.pred_card_le_card_erase (s := A) (a := a)
  have h2 := Finset.pred_card_le_card_erase (s := A.erase a) (a := b)
  omega

variable {A₁ A₂ A₃ A₄ A₅ : Finset ℕ}

/-- **Fibre bound on row 1** (an end row), inside an event `Q` that does not read row 1. -/
theorem fibre_row1 (w : T5 → ℝ) (hw : ∀ t, 0 ≤ w t) (Q : T5 → Prop) [DecidablePred Q]
    (hQ : ∀ t x, Q (set1 t x) ↔ Q t) (P : T5 → Prop) [DecidablePred P] (φ : T5 → ℕ)
    (hφ : ∀ t x, φ (set1 t x) = φ t) (hP : ∀ t, P t → r1 t = φ t) {m : ℕ} (hm : 1 ≤ m)
    (hA : m + 1 ≤ A₁.card) {R : ℝ} (hR0 : 0 < R)
    (hR : ∀ t ∈ (sts A₁ A₂ A₃ A₄ A₅).filter Q, ∀ t' ∈ (sts A₁ A₂ A₃ A₄ A₅).filter Q,
      w t ≤ R * w t') :
    (R + ((m : ℝ) - 1)) * ∑ t ∈ ((sts A₁ A₂ A₃ A₄ A₅).filter Q).filter P, w t
      ≤ R * ∑ t ∈ (sts A₁ A₂ A₃ A₄ A₅).filter Q, w t := by
  refine fibre_sharp w hw P r1 set1 φ (fun t => A₁.erase (r2 t)) m hm
    (fun t _ => card_erase1_ge _ _ hA) ?_ ?_ (fun _ _ => rfl) ?_ hφ hP hR0 hR
  · intro t ht
    obtain ⟨ht, -⟩ := Finset.mem_filter.mp ht
    rw [mem_sts] at ht
    exact Finset.mem_erase.mpr ⟨ht.2.2.2.2.2.1, ht.1⟩
  · intro t ht x hx
    obtain ⟨ht, hq⟩ := Finset.mem_filter.mp ht
    simp only [Finset.mem_erase] at hx
    refine Finset.mem_filter.mpr ⟨?_, (hQ t x).mpr hq⟩
    rw [mem_sts] at ht ⊢
    exact ⟨hx.2, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, hx.1, ht.2.2.2.2.2.2⟩
  · intro t₁ t₂ x₁ x₂ he hg
    obtain ⟨a, b, c, d, e⟩ := t₁
    obtain ⟨a', b', c', d', e'⟩ := t₂
    simp only [set1, Prod.mk.injEq] at he
    simp only [r1] at hg
    obtain ⟨-, rfl, rfl, rfl, rfl⟩ := he; rw [hg]

/-- **Fibre bound on row 2** (a middle row). -/
theorem fibre_row2 (w : T5 → ℝ) (hw : ∀ t, 0 ≤ w t) (Q : T5 → Prop) [DecidablePred Q]
    (hQ : ∀ t x, Q (set2 t x) ↔ Q t) (P : T5 → Prop) [DecidablePred P] (φ : T5 → ℕ)
    (hφ : ∀ t x, φ (set2 t x) = φ t) (hP : ∀ t, P t → r2 t = φ t) {m : ℕ} (hm : 1 ≤ m)
    (hA : m + 2 ≤ A₂.card) {R : ℝ} (hR0 : 0 < R)
    (hR : ∀ t ∈ (sts A₁ A₂ A₃ A₄ A₅).filter Q, ∀ t' ∈ (sts A₁ A₂ A₃ A₄ A₅).filter Q,
      w t ≤ R * w t') :
    (R + ((m : ℝ) - 1)) * ∑ t ∈ ((sts A₁ A₂ A₃ A₄ A₅).filter Q).filter P, w t
      ≤ R * ∑ t ∈ (sts A₁ A₂ A₃ A₄ A₅).filter Q, w t := by
  refine fibre_sharp w hw P r2 set2 φ (fun t => (A₂.erase (r1 t)).erase (r3 t)) m hm
    (fun t _ => card_erase2_ge _ _ _ hA) ?_ ?_ (fun _ _ => rfl) ?_ hφ hP hR0 hR
  · intro t ht
    obtain ⟨ht, -⟩ := Finset.mem_filter.mp ht
    rw [mem_sts] at ht
    exact Finset.mem_erase.mpr ⟨ht.2.2.2.2.2.2.1,
      Finset.mem_erase.mpr ⟨Ne.symm ht.2.2.2.2.2.1, ht.2.1⟩⟩
  · intro t ht x hx
    obtain ⟨ht, hq⟩ := Finset.mem_filter.mp ht
    simp only [Finset.mem_erase] at hx
    refine Finset.mem_filter.mpr ⟨?_, (hQ t x).mpr hq⟩
    rw [mem_sts] at ht ⊢
    exact ⟨ht.1, hx.2.2, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, Ne.symm hx.2.1, hx.1,
      ht.2.2.2.2.2.2.2⟩
  · intro t₁ t₂ x₁ x₂ he hg
    obtain ⟨a, b, c, d, e⟩ := t₁
    obtain ⟨a', b', c', d', e'⟩ := t₂
    simp only [set2, Prod.mk.injEq] at he
    simp only [r2] at hg
    obtain ⟨rfl, -, rfl, rfl, rfl⟩ := he; rw [hg]

/-- **Fibre bound on row 3** (a middle row). -/
theorem fibre_row3 (w : T5 → ℝ) (hw : ∀ t, 0 ≤ w t) (Q : T5 → Prop) [DecidablePred Q]
    (hQ : ∀ t x, Q (set3 t x) ↔ Q t) (P : T5 → Prop) [DecidablePred P] (φ : T5 → ℕ)
    (hφ : ∀ t x, φ (set3 t x) = φ t) (hP : ∀ t, P t → r3 t = φ t) {m : ℕ} (hm : 1 ≤ m)
    (hA : m + 2 ≤ A₃.card) {R : ℝ} (hR0 : 0 < R)
    (hR : ∀ t ∈ (sts A₁ A₂ A₃ A₄ A₅).filter Q, ∀ t' ∈ (sts A₁ A₂ A₃ A₄ A₅).filter Q,
      w t ≤ R * w t') :
    (R + ((m : ℝ) - 1)) * ∑ t ∈ ((sts A₁ A₂ A₃ A₄ A₅).filter Q).filter P, w t
      ≤ R * ∑ t ∈ (sts A₁ A₂ A₃ A₄ A₅).filter Q, w t := by
  refine fibre_sharp w hw P r3 set3 φ (fun t => (A₃.erase (r2 t)).erase (r4 t)) m hm
    (fun t _ => card_erase2_ge _ _ _ hA) ?_ ?_ (fun _ _ => rfl) ?_ hφ hP hR0 hR
  · intro t ht
    obtain ⟨ht, -⟩ := Finset.mem_filter.mp ht
    rw [mem_sts] at ht
    exact Finset.mem_erase.mpr ⟨ht.2.2.2.2.2.2.2.1,
      Finset.mem_erase.mpr ⟨Ne.symm ht.2.2.2.2.2.2.1, ht.2.2.1⟩⟩
  · intro t ht x hx
    obtain ⟨ht, hq⟩ := Finset.mem_filter.mp ht
    simp only [Finset.mem_erase] at hx
    refine Finset.mem_filter.mpr ⟨?_, (hQ t x).mpr hq⟩
    rw [mem_sts] at ht ⊢
    exact ⟨ht.1, ht.2.1, hx.2.2, ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2.1, Ne.symm hx.2.1, hx.1,
      ht.2.2.2.2.2.2.2.2⟩
  · intro t₁ t₂ x₁ x₂ he hg
    obtain ⟨a, b, c, d, e⟩ := t₁
    obtain ⟨a', b', c', d', e'⟩ := t₂
    simp only [set3, Prod.mk.injEq] at he
    simp only [r3] at hg
    obtain ⟨rfl, rfl, -, rfl, rfl⟩ := he; rw [hg]

/-- **Fibre bound on row 4** (a middle row). -/
theorem fibre_row4 (w : T5 → ℝ) (hw : ∀ t, 0 ≤ w t) (Q : T5 → Prop) [DecidablePred Q]
    (hQ : ∀ t x, Q (set4 t x) ↔ Q t) (P : T5 → Prop) [DecidablePred P] (φ : T5 → ℕ)
    (hφ : ∀ t x, φ (set4 t x) = φ t) (hP : ∀ t, P t → r4 t = φ t) {m : ℕ} (hm : 1 ≤ m)
    (hA : m + 2 ≤ A₄.card) {R : ℝ} (hR0 : 0 < R)
    (hR : ∀ t ∈ (sts A₁ A₂ A₃ A₄ A₅).filter Q, ∀ t' ∈ (sts A₁ A₂ A₃ A₄ A₅).filter Q,
      w t ≤ R * w t') :
    (R + ((m : ℝ) - 1)) * ∑ t ∈ ((sts A₁ A₂ A₃ A₄ A₅).filter Q).filter P, w t
      ≤ R * ∑ t ∈ (sts A₁ A₂ A₃ A₄ A₅).filter Q, w t := by
  refine fibre_sharp w hw P r4 set4 φ (fun t => (A₄.erase (r3 t)).erase (r5 t)) m hm
    (fun t _ => card_erase2_ge _ _ _ hA) ?_ ?_ (fun _ _ => rfl) ?_ hφ hP hR0 hR
  · intro t ht
    obtain ⟨ht, -⟩ := Finset.mem_filter.mp ht
    rw [mem_sts] at ht
    exact Finset.mem_erase.mpr ⟨ht.2.2.2.2.2.2.2.2,
      Finset.mem_erase.mpr ⟨Ne.symm ht.2.2.2.2.2.2.2.1, ht.2.2.2.1⟩⟩
  · intro t ht x hx
    obtain ⟨ht, hq⟩ := Finset.mem_filter.mp ht
    simp only [Finset.mem_erase] at hx
    refine Finset.mem_filter.mpr ⟨?_, (hQ t x).mpr hq⟩
    rw [mem_sts] at ht ⊢
    exact ⟨ht.1, ht.2.1, ht.2.2.1, hx.2.2, ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1,
      Ne.symm hx.2.1, hx.1⟩
  · intro t₁ t₂ x₁ x₂ he hg
    obtain ⟨a, b, c, d, e⟩ := t₁
    obtain ⟨a', b', c', d', e'⟩ := t₂
    simp only [set4, Prod.mk.injEq] at he
    simp only [r4] at hg
    obtain ⟨rfl, rfl, rfl, -, rfl⟩ := he; rw [hg]

/-- **Fibre bound on row 5** (an end row). -/
theorem fibre_row5 (w : T5 → ℝ) (hw : ∀ t, 0 ≤ w t) (Q : T5 → Prop) [DecidablePred Q]
    (hQ : ∀ t x, Q (set5 t x) ↔ Q t) (P : T5 → Prop) [DecidablePred P] (φ : T5 → ℕ)
    (hφ : ∀ t x, φ (set5 t x) = φ t) (hP : ∀ t, P t → r5 t = φ t) {m : ℕ} (hm : 1 ≤ m)
    (hA : m + 1 ≤ A₅.card) {R : ℝ} (hR0 : 0 < R)
    (hR : ∀ t ∈ (sts A₁ A₂ A₃ A₄ A₅).filter Q, ∀ t' ∈ (sts A₁ A₂ A₃ A₄ A₅).filter Q,
      w t ≤ R * w t') :
    (R + ((m : ℝ) - 1)) * ∑ t ∈ ((sts A₁ A₂ A₃ A₄ A₅).filter Q).filter P, w t
      ≤ R * ∑ t ∈ (sts A₁ A₂ A₃ A₄ A₅).filter Q, w t := by
  refine fibre_sharp w hw P r5 set5 φ (fun t => A₅.erase (r4 t)) m hm
    (fun t _ => card_erase1_ge _ _ hA) ?_ ?_ (fun _ _ => rfl) ?_ hφ hP hR0 hR
  · intro t ht
    obtain ⟨ht, -⟩ := Finset.mem_filter.mp ht
    rw [mem_sts] at ht
    exact Finset.mem_erase.mpr ⟨Ne.symm ht.2.2.2.2.2.2.2.2, ht.2.2.2.2.1⟩
  · intro t ht x hx
    obtain ⟨ht, hq⟩ := Finset.mem_filter.mp ht
    simp only [Finset.mem_erase] at hx
    refine Finset.mem_filter.mpr ⟨?_, (hQ t x).mpr hq⟩
    rw [mem_sts] at ht ⊢
    exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, hx.2, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1,
      ht.2.2.2.2.2.2.2.1, Ne.symm hx.1⟩
  · intro t₁ t₂ x₁ x₂ he hg
    obtain ⟨a, b, c, d, e⟩ := t₁
    obtain ⟨a', b', c', d', e'⟩ := t₂
    simp only [set5, Prod.mk.injEq] at he
    simp only [r5] at hg
    obtain ⟨rfl, rfl, rfl, rfl, -⟩ := he; rw [hg]

/-! ### The chain lemma: counts -/

/-- The unweighted fibre bound: `(1 + m - 1) · #P ≤ #Ω` gives `m · #P ≤ #Ω`. -/
theorem count_of_fibre {Ω : Finset T5} (P : T5 → Prop) [DecidablePred P] {m : ℕ}
    (h : ((1 : ℝ) + ((m : ℝ) - 1)) * ∑ t ∈ Ω.filter P, (fun _ => (1 : ℝ)) t
      ≤ 1 * ∑ t ∈ Ω, (fun _ => (1 : ℝ)) t) :
    m * (Ω.filter P).card ≤ Ω.card := by
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, one_mul, add_sub_cancel] at h
  exact_mod_cast h

/-- A filter of a filter, as one filter. -/
theorem filter_filter_and (Ω : Finset T5) (Q P : T5 → Prop) [DecidablePred Q] [DecidablePred P] :
    (Ω.filter Q).filter P = Ω.filter (fun t => Q t ∧ P t) := Finset.filter_filter _ _ _

section chain
variable (Q : T5 → Prop) [DecidablePred Q] (φ : T5 → ℕ) {m : ℕ}

theorem chain_row1 (hQ : ∀ t x, Q (set1 t x) ↔ Q t) (hφ : ∀ t x, φ (set1 t x) = φ t)
    (hm : 1 ≤ m) (hA : m + 1 ≤ A₁.card) :
    m * ((sts A₁ A₂ A₃ A₄ A₅).filter (fun t => Q t ∧ r1 t = φ t)).card
      ≤ ((sts A₁ A₂ A₃ A₄ A₅).filter Q).card := by
  rw [← filter_filter_and]
  exact count_of_fibre _ (fibre_row1 (fun _ => 1) (fun _ => zero_le_one) Q hQ _ φ hφ
    (fun _ h => h) hm hA one_pos (fun _ _ _ _ => by norm_num))

theorem chain_row2 (hQ : ∀ t x, Q (set2 t x) ↔ Q t) (hφ : ∀ t x, φ (set2 t x) = φ t)
    (hm : 1 ≤ m) (hA : m + 2 ≤ A₂.card) :
    m * ((sts A₁ A₂ A₃ A₄ A₅).filter (fun t => Q t ∧ r2 t = φ t)).card
      ≤ ((sts A₁ A₂ A₃ A₄ A₅).filter Q).card := by
  rw [← filter_filter_and]
  exact count_of_fibre _ (fibre_row2 (fun _ => 1) (fun _ => zero_le_one) Q hQ _ φ hφ
    (fun _ h => h) hm hA one_pos (fun _ _ _ _ => by norm_num))

theorem chain_row5 (hQ : ∀ t x, Q (set5 t x) ↔ Q t) (hφ : ∀ t x, φ (set5 t x) = φ t)
    (hm : 1 ≤ m) (hA : m + 1 ≤ A₅.card) :
    m * ((sts A₁ A₂ A₃ A₄ A₅).filter (fun t => Q t ∧ r5 t = φ t)).card
      ≤ ((sts A₁ A₂ A₃ A₄ A₅).filter Q).card := by
  rw [← filter_filter_and]
  exact count_of_fibre _ (fibre_row5 (fun _ => 1) (fun _ => zero_le_one) Q hQ _ φ hφ
    (fun _ h => h) hm hA one_pos (fun _ _ _ _ => by norm_num))

end chain

/-! ### The fourteen events and their chain bounds -/

/-- The event of a non-discrete equality pattern: all its equalities (patterns in the order of
`canons`, without `01234`). -/
def evb (p : ℕ) (t : T5) : Bool :=
  match p with
  | 0 => decide (r1 t = r3 t) && decide (r3 t = r5 t) && decide (r2 t = r4 t)
  | 1 => decide (r1 t = r3 t) && decide (r2 t = r4 t)
  | 2 => decide (r1 t = r3 t) && decide (r3 t = r5 t)
  | 3 => decide (r1 t = r3 t) && decide (r2 t = r5 t)
  | 4 => decide (r1 t = r3 t)
  | 5 => decide (r1 t = r4 t) && decide (r2 t = r5 t)
  | 6 => decide (r1 t = r4 t) && decide (r3 t = r5 t)
  | 7 => decide (r1 t = r4 t)
  | 8 => decide (r1 t = r5 t) && decide (r2 t = r4 t)
  | 9 => decide (r2 t = r4 t) && decide (r3 t = r5 t)
  | 10 => decide (r2 t = r4 t)
  | 11 => decide (r1 t = r5 t)
  | 12 => decide (r2 t = r5 t)
  | 13 => decide (r3 t = r5 t)
  | _ => false

/-- The chain bound of each event, for lists of at least `L` colours: the reciprocal of the
product of the option counts of the peeled rows (`L - 1` for an end row, `L - 2` for a middle
row). -/
def chainB (L : ℕ) (p : ℕ) : ℕ :=
  match p with
  | 0 => (L - 1) * (L - 1) * (L - 2)
  | 1 => (L - 1) * (L - 2)
  | 2 => (L - 1) * (L - 1)
  | 3 => (L - 1) * (L - 1)
  | 4 => L - 1
  | 5 => (L - 1) * (L - 1)
  | 6 => (L - 1) * (L - 1)
  | 7 => L - 1
  | 8 => (L - 1) * (L - 2)
  | 9 => (L - 1) * (L - 2)
  | 10 => L - 2
  | 11 => L - 1
  | 12 => L - 1
  | 13 => L - 1
  | _ => 1

/-- One peeling step, as a bound on the counts of the events. -/
theorem peel {N a b m c : ℕ} (h : m * a ≤ b) (hb : c * b ≤ N) : (c * m) * a ≤ N := by
  calc c * m * a = c * (m * a) := by ring
    _ ≤ c * b := Nat.mul_le_mul_left c h
    _ ≤ N := hb

/-- Filters by equivalent predicates have the same card. -/
theorem card_filter_congr' {Ω : Finset T5} {P Q : T5 → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ t, P t ↔ Q t) : (Ω.filter P).card = (Ω.filter Q).card := by
  rw [Finset.filter_congr (fun t _ => h t)]

theorem evb_0 (t : T5) : evb 0 t = true ↔ (r2 t = r4 t ∧ r1 t = r3 t) ∧ r5 t = r3 t := by
  simp only [evb, Bool.and_eq_true, decide_eq_true_eq]; omega

theorem evb_1 (t : T5) : evb 1 t = true ↔ r2 t = r4 t ∧ r1 t = r3 t := by
  simp only [evb, Bool.and_eq_true, decide_eq_true_eq]; omega

theorem evb_2 (t : T5) : evb 2 t = true ↔ r5 t = r3 t ∧ r1 t = r3 t := by
  simp only [evb, Bool.and_eq_true, decide_eq_true_eq]; omega

theorem evb_3 (t : T5) : evb 3 t = true ↔ r5 t = r2 t ∧ r1 t = r3 t := by
  simp only [evb, Bool.and_eq_true, decide_eq_true_eq]; omega

theorem evb_4 (t : T5) : evb 4 t = true ↔ r1 t = r3 t := by
  simp only [evb, decide_eq_true_eq]

theorem evb_5 (t : T5) : evb 5 t = true ↔ r5 t = r2 t ∧ r1 t = r4 t := by
  simp only [evb, Bool.and_eq_true, decide_eq_true_eq]; omega

theorem evb_6 (t : T5) : evb 6 t = true ↔ r5 t = r3 t ∧ r1 t = r4 t := by
  simp only [evb, Bool.and_eq_true, decide_eq_true_eq]; omega

theorem evb_7 (t : T5) : evb 7 t = true ↔ r1 t = r4 t := by
  simp only [evb, decide_eq_true_eq]

theorem evb_8 (t : T5) : evb 8 t = true ↔ r2 t = r4 t ∧ r1 t = r5 t := by
  simp only [evb, Bool.and_eq_true, decide_eq_true_eq]; omega

theorem evb_9 (t : T5) : evb 9 t = true ↔ r2 t = r4 t ∧ r5 t = r3 t := by
  simp only [evb, Bool.and_eq_true, decide_eq_true_eq]; omega

theorem evb_10 (t : T5) : evb 10 t = true ↔ r2 t = r4 t := by
  simp only [evb, decide_eq_true_eq]

theorem evb_11 (t : T5) : evb 11 t = true ↔ r1 t = r5 t := by
  simp only [evb, decide_eq_true_eq]

theorem evb_12 (t : T5) : evb 12 t = true ↔ r5 t = r2 t := by
  simp only [evb, decide_eq_true_eq]; omega

theorem evb_13 (t : T5) : evb 13 t = true ↔ r5 t = r3 t := by
  simp only [evb, decide_eq_true_eq]; omega

/-- **The chain bounds**: for lists of at least `L ≥ 3` colours, the event of pattern `p` holds
on at most a `1/chainB L p` share of the proper columns. -/
theorem chain_bound {L : ℕ} (hL : 3 ≤ L) (h₁ : L ≤ A₁.card) (h₂ : L ≤ A₂.card) (h₃ : L ≤ A₃.card)
    (h₄ : L ≤ A₄.card) (h₅ : L ≤ A₅.card) (p : ℕ) :
    chainB L p * ((sts A₁ A₂ A₃ A₄ A₅).filter (fun t => evb p t = true)).card
      ≤ (sts A₁ A₂ A₃ A₄ A₅).card := by
  have e1 : 1 ≤ L - 1 := by omega
  have e2 : 1 ≤ L - 2 := by omega
  have a1 : L - 1 + 1 ≤ A₁.card := by omega
  have a2 : L - 2 + 2 ≤ A₂.card := by omega
  have a3 : L - 2 + 2 ≤ A₃.card := by omega
  have a4 : L - 2 + 2 ≤ A₄.card := by omega
  have a5 : L - 1 + 1 ≤ A₅.card := by omega
  set Ω := sts A₁ A₂ A₃ A₄ A₅ with hΩ
  have top : 1 * (Ω.filter (fun _ => True)).card ≤ Ω.card := by simp
  -- the single equalities, peeled through one row
  have s13 : (L - 1) * (Ω.filter (fun t => r1 t = r3 t)).card ≤ Ω.card := by
    have h := chain_row1 (A₂ := A₂) (A₃ := A₃) (A₄ := A₄) (A₅ := A₅) (fun _ => True) r3
      (fun _ _ => Iff.rfl) (fun _ _ => rfl) e1 a1
    rw [card_filter_congr' (fun t => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩)] at h
    simpa using h
  have s14 : (L - 1) * (Ω.filter (fun t => r1 t = r4 t)).card ≤ Ω.card := by
    have h := chain_row1 (A₂ := A₂) (A₃ := A₃) (A₄ := A₄) (A₅ := A₅) (fun _ => True) r4
      (fun _ _ => Iff.rfl) (fun _ _ => rfl) e1 a1
    rw [card_filter_congr' (fun t => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩)] at h
    simpa using h
  have s15 : (L - 1) * (Ω.filter (fun t => r1 t = r5 t)).card ≤ Ω.card := by
    have h := chain_row1 (A₂ := A₂) (A₃ := A₃) (A₄ := A₄) (A₅ := A₅) (fun _ => True) r5
      (fun _ _ => Iff.rfl) (fun _ _ => rfl) e1 a1
    rw [card_filter_congr' (fun t => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩)] at h
    simpa using h
  have s25 : (L - 1) * (Ω.filter (fun t => r5 t = r2 t)).card ≤ Ω.card := by
    have h := chain_row5 (A₁ := A₁) (A₂ := A₂) (A₃ := A₃) (A₄ := A₄) (fun _ => True) r2
      (fun _ _ => Iff.rfl) (fun _ _ => rfl) e1 a5
    rw [card_filter_congr' (fun t => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩)] at h
    simpa using h
  have s35 : (L - 1) * (Ω.filter (fun t => r5 t = r3 t)).card ≤ Ω.card := by
    have h := chain_row5 (A₁ := A₁) (A₂ := A₂) (A₃ := A₃) (A₄ := A₄) (fun _ => True) r3
      (fun _ _ => Iff.rfl) (fun _ _ => rfl) e1 a5
    rw [card_filter_congr' (fun t => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩)] at h
    simpa using h
  have s24 : (L - 2) * (Ω.filter (fun t => r2 t = r4 t)).card ≤ Ω.card := by
    have h := chain_row2 (A₁ := A₁) (A₃ := A₃) (A₄ := A₄) (A₅ := A₅) (fun _ => True) r4
      (fun _ _ => Iff.rfl) (fun _ _ => rfl) e2 a2
    rw [card_filter_congr' (fun t => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩)] at h
    simpa using h
  -- two equalities: peel an end row off a single equality
  have d13_24 : ((L - 1) * (L - 2)) * (Ω.filter (fun t => r2 t = r4 t ∧ r1 t = r3 t)).card
      ≤ Ω.card := by
    have := peel (c := L - 2) (m := L - 1) (chain_row1 (fun t => r2 t = r4 t) r3
      (fun _ _ => Iff.rfl) (fun _ _ => rfl) e1 a1) s24
    rwa [Nat.mul_comm (L - 2)] at this
  have d15_24 : ((L - 1) * (L - 2)) * (Ω.filter (fun t => r2 t = r4 t ∧ r1 t = r5 t)).card
      ≤ Ω.card := by
    have := peel (c := L - 2) (m := L - 1) (chain_row1 (fun t => r2 t = r4 t) r5
      (fun _ _ => Iff.rfl) (fun _ _ => rfl) e1 a1) s24
    rwa [Nat.mul_comm (L - 2)] at this
  have d35_24 : ((L - 1) * (L - 2)) * (Ω.filter (fun t => r2 t = r4 t ∧ r5 t = r3 t)).card
      ≤ Ω.card := by
    have := peel (c := L - 2) (m := L - 1) (chain_row5 (fun t => r2 t = r4 t) r3
      (fun _ _ => Iff.rfl) (fun _ _ => rfl) e1 a5) s24
    rwa [Nat.mul_comm (L - 2)] at this
  have d13_35 : ((L - 1) * (L - 1)) * (Ω.filter (fun t => r5 t = r3 t ∧ r1 t = r3 t)).card
      ≤ Ω.card :=
    peel (chain_row1 (fun t => r5 t = r3 t) r3 (fun _ _ => Iff.rfl) (fun _ _ => rfl) e1 a1) s35
  have d13_25 : ((L - 1) * (L - 1)) * (Ω.filter (fun t => r5 t = r2 t ∧ r1 t = r3 t)).card
      ≤ Ω.card :=
    peel (chain_row1 (fun t => r5 t = r2 t) r3 (fun _ _ => Iff.rfl) (fun _ _ => rfl) e1 a1) s25
  have d14_25 : ((L - 1) * (L - 1)) * (Ω.filter (fun t => r5 t = r2 t ∧ r1 t = r4 t)).card
      ≤ Ω.card :=
    peel (chain_row1 (fun t => r5 t = r2 t) r4 (fun _ _ => Iff.rfl) (fun _ _ => rfl) e1 a1) s25
  have d14_35 : ((L - 1) * (L - 1)) * (Ω.filter (fun t => r5 t = r3 t ∧ r1 t = r4 t)).card
      ≤ Ω.card :=
    peel (chain_row1 (fun t => r5 t = r3 t) r4 (fun _ _ => Iff.rfl) (fun _ _ => rfl) e1 a1) s35
  -- three equalities
  have d0 : ((L - 1) * (L - 1) * (L - 2))
      * (Ω.filter (fun t => (r2 t = r4 t ∧ r1 t = r3 t) ∧ r5 t = r3 t)).card ≤ Ω.card := by
    have := peel (chain_row5 (fun t => r2 t = r4 t ∧ r1 t = r3 t) r3 (fun _ _ => Iff.rfl)
      (fun _ _ => rfl) e1 a5) d13_24
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  have ev : ∀ (Q : T5 → Prop) [DecidablePred Q], (∀ t, evb p t = true ↔ Q t) →
      (chainB L p * (Ω.filter Q).card ≤ Ω.card) →
      chainB L p * (Ω.filter (fun t => evb p t = true)).card ≤ Ω.card := by
    intro Q _ hQ h; rwa [card_filter_congr' hQ]
  match p with
  | 0 => exact ev _ evb_0 d0
  | 1 => exact ev _ evb_1 d13_24
  | 2 => exact ev _ evb_2 d13_35
  | 3 => exact ev _ evb_3 d13_25
  | 4 => exact ev _ evb_4 s13
  | 5 => exact ev _ evb_5 d14_25
  | 6 => exact ev _ evb_6 d14_35
  | 7 => exact ev _ evb_7 s14
  | 8 => exact ev _ evb_8 d15_24
  | 9 => exact ev _ evb_9 d35_24
  | 10 => exact ev _ evb_10 s24
  | 11 => exact ev _ evb_11 s15
  | 12 => exact ev _ evb_12 s25
  | 13 => exact ev _ evb_13 s35
  | _ + 14 => simpa [chainB] using Finset.card_filter_le Ω _

end GridGen.Five
