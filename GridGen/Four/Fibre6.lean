/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Fibre

/-!
# Height four: sharp fibre bounds

`Fibre.lean` compares the pinned columns with their `m` images and gets `m · Σ_P w ≤ R · Σ w`.
The images under the `m - 1` values other than the current one leave the pin, so they are
disjoint from it, and so `(R + m - 1) · Σ_P w ≤ R · Σ w`. With `R = 1/ρ` this is
`Σ_P ≤ Σ/(1 + (m-1)ρ)` in place of `Σ/(mρ)`. End rows have one neighbour in the column, hence
`k - 2` admissible values instead of `k - 3` (`fibre_sts1_sharp`, `fibre_sts4_sharp`).
-/

namespace GridGen.Four

open Finset

/-- **The sharp one-row fibre bound.** -/
theorem fibre_row_sharp {Ω : Finset T4} (w : T4 → ℝ) (hw : ∀ t, 0 ≤ w t) (P : T4 → Prop)
    [DecidablePred P] (get : T4 → ℕ) (set : T4 → ℕ → T4) (φ : T4 → ℕ) (opts : T4 → Finset ℕ)
    (m : ℕ) (hm : 1 ≤ m) (hopts : ∀ t ∈ Ω, m ≤ (opts t).card)
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
  -- every pinned column has at least `m - 1` other values
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
  -- each is dominated by its image
  have h2 : ∑ p ∈ S, w p.1 ≤ ∑ p ∈ S, R * w (set p.1 p.2) := by
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨ht, hx⟩ := Finset.mem_sigma.mp hp
    obtain ⟨htΩ, -⟩ := Finset.mem_filter.mp ht
    exact hR p.1 htΩ _ (hmem p.1 htΩ p.2 (Finset.mem_of_mem_erase hx))
  -- the images are distinct unpinned columns
  have hinjS : Set.InjOn (fun p : (_ : T4) × ℕ => set p.1 p.2) S := by
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

variable {A₁ A₂ A₃ A₄ : Finset ℕ} {k : ℕ}

theorem card_opts1_ge (A : Finset ℕ) (a : ℕ) {k : ℕ} (hA : k - 1 ≤ A.card) :
    k - 2 ≤ (A.erase a).card := by
  have h1 := Finset.pred_card_le_card_erase (s := A) (a := a)
  omega

/-- **Sharp fibre bound on row 1** (an end row: `k - 2` values). -/
theorem fibre_sts1_sharp (w : T4 → ℝ) (hw : ∀ t, 0 ≤ w t) (P : T4 → Prop) [DecidablePred P]
    (hk : 3 ≤ k) (hA₁ : k - 1 ≤ A₁.card) {R : ℝ} (hR0 : 0 < R)
    (hR : ∀ t ∈ sts A₁ A₂ A₃ A₄, ∀ t' ∈ sts A₁ A₂ A₃ A₄, w t ≤ R * w t') (φ : T4 → ℕ)
    (hφ : ∀ t x, φ (set1 t x) = φ t) (hP : ∀ t, P t → r1 t = φ t) :
    (R + (((k - 2 : ℕ) : ℝ) - 1)) * ∑ t ∈ (sts A₁ A₂ A₃ A₄).filter P, w t
      ≤ R * ∑ t ∈ sts A₁ A₂ A₃ A₄, w t := by
  refine fibre_row_sharp w hw P r1 set1 φ (opts1 A₁) (k - 2) (by omega)
    (fun t _ => card_opts1_ge _ _ hA₁) ?_ ?_ (fun _ _ => rfl) ?_ hφ hP hR0 hR
  · intro t ht
    rw [mem_sts] at ht
    exact Finset.mem_erase.mpr ⟨ht.2.2.2.2.1, ht.1⟩
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

/-- **Sharp fibre bound on row 2** (`k - 3` values). -/
theorem fibre_sts2_sharp (w : T4 → ℝ) (hw : ∀ t, 0 ≤ w t) (P : T4 → Prop) [DecidablePred P]
    (hk : 4 ≤ k) (hA₂ : k - 1 ≤ A₂.card) {R : ℝ} (hR0 : 0 < R)
    (hR : ∀ t ∈ sts A₁ A₂ A₃ A₄, ∀ t' ∈ sts A₁ A₂ A₃ A₄, w t ≤ R * w t') (φ : T4 → ℕ)
    (hφ : ∀ t x, φ (set2 t x) = φ t) (hP : ∀ t, P t → r2 t = φ t) :
    (R + (((k - 3 : ℕ) : ℝ) - 1)) * ∑ t ∈ (sts A₁ A₂ A₃ A₄).filter P, w t
      ≤ R * ∑ t ∈ sts A₁ A₂ A₃ A₄, w t := by
  refine fibre_row_sharp w hw P r2 set2 φ (opts2 A₂) (k - 3) (by omega)
    (fun t _ => card_opts_ge _ _ _ hA₂) ?_ ?_ (fun _ _ => rfl) ?_ hφ hP hR0 hR
  · intro t ht
    rw [mem_sts] at ht
    exact Finset.mem_erase.mpr ⟨ht.2.2.2.2.2.1,
      Finset.mem_erase.mpr ⟨Ne.symm ht.2.2.2.2.1, ht.2.1⟩⟩
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

/-- **Sharp fibre bound on row 3** (`k - 3` values). -/
theorem fibre_sts3_sharp (w : T4 → ℝ) (hw : ∀ t, 0 ≤ w t) (P : T4 → Prop) [DecidablePred P]
    (hk : 4 ≤ k) (hA₃ : k - 1 ≤ A₃.card) {R : ℝ} (hR0 : 0 < R)
    (hR : ∀ t ∈ sts A₁ A₂ A₃ A₄, ∀ t' ∈ sts A₁ A₂ A₃ A₄, w t ≤ R * w t') (φ : T4 → ℕ)
    (hφ : ∀ t x, φ (set3 t x) = φ t) (hP : ∀ t, P t → r3 t = φ t) :
    (R + (((k - 3 : ℕ) : ℝ) - 1)) * ∑ t ∈ (sts A₁ A₂ A₃ A₄).filter P, w t
      ≤ R * ∑ t ∈ sts A₁ A₂ A₃ A₄, w t := by
  refine fibre_row_sharp w hw P r3 set3 φ (opts3 A₃) (k - 3) (by omega)
    (fun t _ => card_opts_ge _ _ _ hA₃) ?_ ?_ (fun _ _ => rfl) ?_ hφ hP hR0 hR
  · intro t ht
    rw [mem_sts] at ht
    exact Finset.mem_erase.mpr ⟨ht.2.2.2.2.2.2,
      Finset.mem_erase.mpr ⟨Ne.symm ht.2.2.2.2.2.1, ht.2.2.1⟩⟩
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

/-- **Sharp fibre bound on row 4** (an end row: `k - 2` values). -/
theorem fibre_sts4_sharp (w : T4 → ℝ) (hw : ∀ t, 0 ≤ w t) (P : T4 → Prop) [DecidablePred P]
    (hk : 3 ≤ k) (hA₄ : k - 1 ≤ A₄.card) {R : ℝ} (hR0 : 0 < R)
    (hR : ∀ t ∈ sts A₁ A₂ A₃ A₄, ∀ t' ∈ sts A₁ A₂ A₃ A₄, w t ≤ R * w t') (φ : T4 → ℕ)
    (hφ : ∀ t x, φ (set4 t x) = φ t) (hP : ∀ t, P t → r4 t = φ t) :
    (R + (((k - 2 : ℕ) : ℝ) - 1)) * ∑ t ∈ (sts A₁ A₂ A₃ A₄).filter P, w t
      ≤ R * ∑ t ∈ sts A₁ A₂ A₃ A₄, w t := by
  refine fibre_row_sharp w hw P r4 set4 φ (opts4 A₄) (k - 2) (by omega)
    (fun t _ => card_opts1_ge _ _ hA₄) ?_ ?_ (fun _ _ => rfl) ?_ hφ hP hR0 hR
  · intro t ht
    rw [mem_sts] at ht
    exact Finset.mem_erase.mpr ⟨Ne.symm ht.2.2.2.2.2.2, ht.2.2.2.1⟩
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
