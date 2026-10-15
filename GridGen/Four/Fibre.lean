/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Defs

/-!
# Height four: fibre bounds

A proper column of the four-row path from lists of at least `k - 1` colours can change any one row
to at least `k - 3` other admissible colours (its list minus the two neighbouring colours). So any
property that pins one row — a fixed colour, or equality with another row — holds on at most a
`R/(k-3)` share of the weighted columns, when the weights change by at most the factor `R` under
such a change. `fibre_core` is the abstract double-counting argument; `setRow` and the row
instances follow.
-/

namespace GridGen.Four

open Finset

/-- **Double counting.** If every column with property `P` has at least `m` options, each option
gives a column of `Ω` with weight at least `w t / R`, and distinct (column, option) pairs give
distinct columns, then `m · Σ_{P} w ≤ R · Σ_Ω w`. -/
theorem fibre_core {Ω : Finset T4} (w : T4 → ℝ) (hw : ∀ t, 0 ≤ w t) (P : T4 → Prop)
    [DecidablePred P] (upd : T4 → ℕ → T4) (opts : T4 → Finset ℕ) (m : ℕ)
    (hopts : ∀ t ∈ Ω, P t → m ≤ (opts t).card)
    (hmem : ∀ t ∈ Ω, P t → ∀ x ∈ opts t, upd t x ∈ Ω)
    (hinj : ∀ t₁ ∈ Ω, P t₁ → ∀ t₂ ∈ Ω, P t₂ → ∀ x₁ ∈ opts t₁, ∀ x₂ ∈ opts t₂,
      upd t₁ x₁ = upd t₂ x₂ → t₁ = t₂ ∧ x₁ = x₂)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ t ∈ Ω, P t → ∀ x ∈ opts t, w t ≤ R * w (upd t x)) :
    (m : ℝ) * ∑ t ∈ Ω.filter P, w t ≤ R * ∑ t ∈ Ω, w t := by
  classical
  set S := (Ω.filter P).sigma opts with hS
  -- left side ≤ Σ over pairs of w t
  have h1 : (m : ℝ) * ∑ t ∈ Ω.filter P, w t ≤ ∑ p ∈ S, w p.1 := by
    rw [hS, Finset.sum_sigma, Finset.mul_sum]
    refine Finset.sum_le_sum fun t ht => ?_
    obtain ⟨htΩ, hPt⟩ := Finset.mem_filter.mp ht
    show (m : ℝ) * w t ≤ ∑ _x ∈ opts t, w t
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hopts t htΩ hPt) (hw t)
  -- each pair is dominated by its image
  have h2 : ∑ p ∈ S, w p.1 ≤ ∑ p ∈ S, R * w (upd p.1 p.2) := by
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨ht, hx⟩ := Finset.mem_sigma.mp hp
    obtain ⟨htΩ, hPt⟩ := Finset.mem_filter.mp ht
    exact hR p.1 htΩ hPt p.2 hx
  -- the images are distinct columns of `Ω`
  have hinjS : Set.InjOn (fun p : (_ : T4) × ℕ => upd p.1 p.2) S := by
    intro p hp q hq hpq
    obtain ⟨hpt, hpx⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hqt, hqx⟩ := Finset.mem_sigma.mp hq
    obtain ⟨hpΩ, hpP⟩ := Finset.mem_filter.mp hpt
    obtain ⟨hqΩ, hqP⟩ := Finset.mem_filter.mp hqt
    obtain ⟨e1, e2⟩ := hinj p.1 hpΩ hpP q.1 hqΩ hqP p.2 hpx q.2 hqx hpq
    exact Sigma.ext e1 (heq_of_eq e2)
  have h3 : ∑ p ∈ S, w (upd p.1 p.2) ≤ ∑ t ∈ Ω, w t := by
    rw [← Finset.sum_image (f := w) hinjS]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun t _ _ => hw t)
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hpt, hpx⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hpΩ, hpP⟩ := Finset.mem_filter.mp hpt
    exact hmem p.1 hpΩ hpP p.2 hpx
  calc (m : ℝ) * ∑ t ∈ Ω.filter P, w t ≤ ∑ p ∈ S, w p.1 := h1
    _ ≤ ∑ p ∈ S, R * w (upd p.1 p.2) := h2
    _ = R * ∑ p ∈ S, w (upd p.1 p.2) := by rw [Finset.mul_sum]
    _ ≤ R * ∑ t ∈ Ω, w t := mul_le_mul_of_nonneg_left h3 hR0

/-! ### Changing one row -/

/-- **One-row fibres, abstractly.** `get`/`set` read and overwrite one row; `opts t` are the
admissible new values (at least `m` of them). If `P t` forces the row to a value `φ t` that does
not depend on the row itself, and weights on `Ω` differ by at most the factor `R`, then
`m · Σ_{P} w ≤ R · Σ_Ω w`. -/
theorem fibre_row {Ω : Finset T4} (w : T4 → ℝ) (hw : ∀ t, 0 ≤ w t) (P : T4 → Prop)
    [DecidablePred P] (get : T4 → ℕ) (set : T4 → ℕ → T4) (φ : T4 → ℕ) (opts : T4 → Finset ℕ)
    (m : ℕ) (hopts : ∀ t ∈ Ω, m ≤ (opts t).card)
    (hmem : ∀ t ∈ Ω, ∀ x ∈ opts t, set t x ∈ Ω)
    (hget : ∀ t x, get (set t x) = x)
    (hset : ∀ t₁ t₂ x₁ x₂, set t₁ x₁ = set t₂ x₂ → get t₁ = get t₂ → t₁ = t₂)
    (hφ : ∀ t₁ t₂ x₁ x₂, set t₁ x₁ = set t₂ x₂ → φ t₁ = φ t₂)
    (hP : ∀ t, P t → get t = φ t)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ t ∈ Ω, ∀ t' ∈ Ω, w t ≤ R * w t') :
    (m : ℝ) * ∑ t ∈ Ω.filter P, w t ≤ R * ∑ t ∈ Ω, w t := by
  refine fibre_core w hw P set opts m (fun t ht _ => hopts t ht) (fun t ht _ x hx => hmem t ht x hx)
    ?_ hR0 (fun t ht _ x hx => hR t ht _ (hmem t ht x hx))
  intro t₁ _ hP₁ t₂ _ hP₂ x₁ _ x₂ _ he
  have hx : x₁ = x₂ := by rw [← hget t₁ x₁, ← hget t₂ x₂, he]
  have hg : get t₁ = get t₂ := by rw [hP t₁ hP₁, hP t₂ hP₂]; exact hφ t₁ t₂ x₁ x₂ he
  exact ⟨hset t₁ t₂ x₁ x₂ he hg, hx⟩

/-- Overwrite row 1, 2, 3 or 4. -/
def set1 (t : T4) (x : ℕ) : T4 := (x, t.2)
def set2 (t : T4) (x : ℕ) : T4 := (t.1, x, t.2.2)
def set3 (t : T4) (x : ℕ) : T4 := (t.1, t.2.1, x, t.2.2.2)
def set4 (t : T4) (x : ℕ) : T4 := (t.1, t.2.1, t.2.2.1, x)

variable {A₁ A₂ A₃ A₄ : Finset ℕ} {k : ℕ}

/-- Admissible new values of each row: its list minus the neighbouring colours. -/
def opts1 (A₁ : Finset ℕ) (t : T4) : Finset ℕ := A₁.erase (r2 t)
def opts2 (A₂ : Finset ℕ) (t : T4) : Finset ℕ := (A₂.erase (r1 t)).erase (r3 t)
def opts3 (A₃ : Finset ℕ) (t : T4) : Finset ℕ := (A₃.erase (r2 t)).erase (r4 t)
def opts4 (A₄ : Finset ℕ) (t : T4) : Finset ℕ := A₄.erase (r3 t)

theorem card_opts_ge (A : Finset ℕ) (a b : ℕ) {k : ℕ} (hA : k - 1 ≤ A.card) :
    k - 3 ≤ ((A.erase a).erase b).card := by
  have h1 := Finset.pred_card_le_card_erase (s := A) (a := a)
  have h2 := Finset.pred_card_le_card_erase (s := A.erase a) (a := b)
  omega

theorem card_opts_ge1 (A : Finset ℕ) (a : ℕ) {k : ℕ} (hA : k - 1 ≤ A.card) :
    k - 3 ≤ (A.erase a).card := by
  have h1 := Finset.pred_card_le_card_erase (s := A) (a := a)
  omega

/-- **Fibre bound on row 1.** The predicate `P` pins row 1 to `φ`, a function of the other
rows. -/
theorem fibre_sts1 (w : T4 → ℝ) (hw : ∀ t, 0 ≤ w t) (P : T4 → Prop) [DecidablePred P]
    (hA₁ : k - 1 ≤ A₁.card) (hA₂ : k - 1 ≤ A₂.card) (hA₃ : k - 1 ≤ A₃.card)
    (hA₄ : k - 1 ≤ A₄.card) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ t ∈ sts A₁ A₂ A₃ A₄, ∀ t' ∈ sts A₁ A₂ A₃ A₄, w t ≤ R * w t') (φ : T4 → ℕ)
    (hφ : ∀ t x, φ (set1 t x) = φ t) (hP : ∀ t, P t → r1 t = φ t) :
    ((k - 3 : ℕ) : ℝ) * ∑ t ∈ (sts A₁ A₂ A₃ A₄).filter P, w t
      ≤ R * ∑ t ∈ sts A₁ A₂ A₃ A₄, w t := by
  refine fibre_row w hw P r1 set1 φ (opts1 A₁) (k - 3)
    (fun t _ => card_opts_ge1 _ _ hA₁) ?_ (fun _ _ => rfl) ?_
    (fun t₁ t₂ x₁ x₂ he => by rw [← hφ t₁ x₁, he, hφ]) hP hR0 hR
  · intro t ht x hx
    simp only [opts1, Finset.mem_erase] at hx
    rw [mem_sts] at ht ⊢
    exact ⟨hx.2, ht.2.1, ht.2.2.1, ht.2.2.2.1, hx.1, ht.2.2.2.2.2⟩
  · intro t₁ t₂ x₁ x₂ he hg
    obtain ⟨a, b, c, d⟩ := t₁
    obtain ⟨a', b', c', d'⟩ := t₂
    simp only [set1, Prod.mk.injEq] at he
    simp only [r1] at hg
    obtain ⟨-, rfl, rfl, rfl⟩ := he; rw [hg]

/-- **Fibre bound on row 2.** The predicate `P` pins row 2 to `φ`, a function of the other
rows. -/
theorem fibre_sts2 (w : T4 → ℝ) (hw : ∀ t, 0 ≤ w t) (P : T4 → Prop) [DecidablePred P]
    (hA₁ : k - 1 ≤ A₁.card) (hA₂ : k - 1 ≤ A₂.card) (hA₃ : k - 1 ≤ A₃.card)
    (hA₄ : k - 1 ≤ A₄.card) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ t ∈ sts A₁ A₂ A₃ A₄, ∀ t' ∈ sts A₁ A₂ A₃ A₄, w t ≤ R * w t') (φ : T4 → ℕ)
    (hφ : ∀ t x, φ (set2 t x) = φ t) (hP : ∀ t, P t → r2 t = φ t) :
    ((k - 3 : ℕ) : ℝ) * ∑ t ∈ (sts A₁ A₂ A₃ A₄).filter P, w t
      ≤ R * ∑ t ∈ sts A₁ A₂ A₃ A₄, w t := by
  refine fibre_row w hw P r2 set2 φ (opts2 A₂) (k - 3)
    (fun t _ => card_opts_ge _ _ _ hA₂) ?_ (fun _ _ => rfl) ?_
    (fun t₁ t₂ x₁ x₂ he => by rw [← hφ t₁ x₁, he, hφ]) hP hR0 hR
  · intro t ht x hx
    simp only [opts2, Finset.mem_erase] at hx
    rw [mem_sts] at ht ⊢
    exact ⟨ht.1, hx.2.2, ht.2.2.1, ht.2.2.2.1, Ne.symm hx.2.1, hx.1, ht.2.2.2.2.2.2⟩
  · intro t₁ t₂ x₁ x₂ he hg
    obtain ⟨a, b, c, d⟩ := t₁
    obtain ⟨a', b', c', d'⟩ := t₂
    simp only [set2, Prod.mk.injEq] at he
    simp only [r2] at hg
    obtain ⟨rfl, -, rfl, rfl⟩ := he; rw [hg]

/-- **Fibre bound on row 3.** The predicate `P` pins row 3 to `φ`, a function of the other
rows. -/
theorem fibre_sts3 (w : T4 → ℝ) (hw : ∀ t, 0 ≤ w t) (P : T4 → Prop) [DecidablePred P]
    (hA₁ : k - 1 ≤ A₁.card) (hA₂ : k - 1 ≤ A₂.card) (hA₃ : k - 1 ≤ A₃.card)
    (hA₄ : k - 1 ≤ A₄.card) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ t ∈ sts A₁ A₂ A₃ A₄, ∀ t' ∈ sts A₁ A₂ A₃ A₄, w t ≤ R * w t') (φ : T4 → ℕ)
    (hφ : ∀ t x, φ (set3 t x) = φ t) (hP : ∀ t, P t → r3 t = φ t) :
    ((k - 3 : ℕ) : ℝ) * ∑ t ∈ (sts A₁ A₂ A₃ A₄).filter P, w t
      ≤ R * ∑ t ∈ sts A₁ A₂ A₃ A₄, w t := by
  refine fibre_row w hw P r3 set3 φ (opts3 A₃) (k - 3)
    (fun t _ => card_opts_ge _ _ _ hA₃) ?_ (fun _ _ => rfl) ?_
    (fun t₁ t₂ x₁ x₂ he => by rw [← hφ t₁ x₁, he, hφ]) hP hR0 hR
  · intro t ht x hx
    simp only [opts3, Finset.mem_erase] at hx
    rw [mem_sts] at ht ⊢
    exact ⟨ht.1, ht.2.1, hx.2.2, ht.2.2.2.1, ht.2.2.2.2.1, Ne.symm hx.2.1, hx.1⟩
  · intro t₁ t₂ x₁ x₂ he hg
    obtain ⟨a, b, c, d⟩ := t₁
    obtain ⟨a', b', c', d'⟩ := t₂
    simp only [set3, Prod.mk.injEq] at he
    simp only [r3] at hg
    obtain ⟨rfl, rfl, -, rfl⟩ := he; rw [hg]

/-- **Fibre bound on row 4.** The predicate `P` pins row 4 to `φ`, a function of the other
rows. -/
theorem fibre_sts4 (w : T4 → ℝ) (hw : ∀ t, 0 ≤ w t) (P : T4 → Prop) [DecidablePred P]
    (hA₁ : k - 1 ≤ A₁.card) (hA₂ : k - 1 ≤ A₂.card) (hA₃ : k - 1 ≤ A₃.card)
    (hA₄ : k - 1 ≤ A₄.card) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ t ∈ sts A₁ A₂ A₃ A₄, ∀ t' ∈ sts A₁ A₂ A₃ A₄, w t ≤ R * w t') (φ : T4 → ℕ)
    (hφ : ∀ t x, φ (set4 t x) = φ t) (hP : ∀ t, P t → r4 t = φ t) :
    ((k - 3 : ℕ) : ℝ) * ∑ t ∈ (sts A₁ A₂ A₃ A₄).filter P, w t
      ≤ R * ∑ t ∈ sts A₁ A₂ A₃ A₄, w t := by
  refine fibre_row w hw P r4 set4 φ (opts4 A₄) (k - 3)
    (fun t _ => card_opts_ge1 _ _ hA₄) ?_ (fun _ _ => rfl) ?_
    (fun t₁ t₂ x₁ x₂ he => by rw [← hφ t₁ x₁, he, hφ]) hP hR0 hR
  · intro t ht x hx
    simp only [opts4, Finset.mem_erase] at hx
    rw [mem_sts] at ht ⊢
    exact ⟨ht.1, ht.2.1, ht.2.2.1, hx.2, ht.2.2.2.2.1, ht.2.2.2.2.2.1, Ne.symm hx.1⟩
  · intro t₁ t₂ x₁ x₂ he hg
    obtain ⟨a, b, c, d⟩ := t₁
    obtain ⟨a', b', c', d'⟩ := t₂
    simp only [set4, Prod.mk.injEq] at he
    simp only [r4] at hg
    obtain ⟨rfl, rfl, rfl, -⟩ := he; rw [hg]

end GridGen.Four
