/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Exact
import GridGen.Four.Fibre6

/-!
# Height four, `k = 5`: pins from the fibre and from the path marginals

`ai_research_notes/H4_K5_REVIEW_2026-10-24.md` §2. Previous columns `s ∈ sts X` (all `|Xᵢ| ≥ 4`)
are weighted by `u = GU 5 w`; any two weights are within the factor `125/118`, and all of them
lie in `[ρ g, g]` with `g = vA 3 w`, `ρ = 118/125`.

* **Lemma F, the event-conditioned fibre** (`peel_fac`). For a row `r` and an event `E` that does
  not read row `r`, the states of `E` with `sᵣ ∈ D` carry at most `min (qᵣ |D|, 1)` of the weight
  of `E`, and those with `sᵣ = sⱼ` (`j ≠ r`) at most `qᵣ`; `qᵣ = 1/(1 + (mᵣ - 1)ρ)` with `mᵣ = 3`
  free values on an end row and `2` on a middle row: `125/361` and `125/243`.
* **Lemma B, the marginal block** (`blk_bound`). For a block `R` of one row or two adjacent rows,
  the number of states with `s_R = τ` is between `ℓ_R c` and `c` for every proper `τ` (prepending
  rows, `card_sts`); with at least `M_R` such `τ` (`4` colours, `12` proper pairs), the states with
  `s_R` in a set of at most `m` tuples carry at most `m/(m + ρ ℓ_R (M_R - m))` of the weight
  (`block_core`). Here `ℓ_R = 2/3` for an end row or a pair at an end, `1/2` for a middle row,
  `9/16` for the middle pair.
* **Products** (`pin_bound`): a block event times factors, peeled in an order in which each
  peeled row is read neither by a later factor nor by the block, carries at most the product of
  the bounds.
-/

namespace GridGen.Four

open Finset GridGen.Lookback

/-! ### Rows by index -/

/-- Replace the colour of a row. -/
def setRow : Fin 4 → T4 → ℕ → T4
  | 0 => set1
  | 1 => set2
  | 2 => set3
  | 3 => set4

theorem rowfun_setRow (r : Fin 4) (t : T4) (x : ℕ) : rowfun r (setRow r t x) = x := by
  fin_cases r <;> rfl

theorem rowfun_setRow_ne {r j : Fin 4} (h : j ≠ r) (t : T4) (x : ℕ) :
    rowfun j (setRow r t x) = rowfun j t := by
  fin_cases r <;> fin_cases j <;> first | rfl | exact absurd rfl h

/-- The free values of a row: its list minus the colours of its neighbours. -/
def optsRow (X₁ X₂ X₃ X₄ : Finset ℕ) : Fin 4 → T4 → Finset ℕ
  | 0 => opts1 X₁
  | 1 => opts2 X₂
  | 2 => opts3 X₃
  | 3 => opts4 X₄

/-- The number of free values with lists of at least four colours. -/
def mrow (r : Fin 4) : ℕ := if r = 0 ∨ r = 3 then 3 else 2

/-- The fibre share of one colour on a row: `1/(1 + (mᵣ - 1)·118/125)`. -/
def qrow (r : Fin 4) : ℚ := if r = 0 ∨ r = 3 then 125 / 361 else 125 / 243

section rows

variable {X₁ X₂ X₃ X₄ : Finset ℕ}

theorem row_facts (h₁ : 4 ≤ X₁.card) (h₂ : 4 ≤ X₂.card) (h₃ : 4 ≤ X₃.card) (h₄ : 4 ≤ X₄.card)
    (r : Fin 4) {t : T4} (ht : t ∈ sts X₁ X₂ X₃ X₄) :
    mrow r ≤ (optsRow X₁ X₂ X₃ X₄ r t).card ∧ rowfun r t ∈ optsRow X₁ X₂ X₃ X₄ r t ∧
      ∀ x ∈ optsRow X₁ X₂ X₃ X₄ r t, setRow r t x ∈ sts X₁ X₂ X₃ X₄ := by
  rw [mem_sts] at ht
  fin_cases r
  · refine ⟨card_opts1_ge (k := 5) _ _ h₁, Finset.mem_erase.mpr ⟨ht.2.2.2.2.1, ht.1⟩, ?_⟩
    intro x hx
    simp only [optsRow, opts1, Finset.mem_erase] at hx
    simp only [setRow]
    rw [mem_sts]
    exact ⟨hx.2, ht.2.1, ht.2.2.1, ht.2.2.2.1, hx.1, ht.2.2.2.2.2⟩
  · refine ⟨card_opts_ge (k := 5) _ _ _ h₂, Finset.mem_erase.mpr ⟨ht.2.2.2.2.2.1,
      Finset.mem_erase.mpr ⟨Ne.symm ht.2.2.2.2.1, ht.2.1⟩⟩, ?_⟩
    intro x hx
    simp only [optsRow, opts2, Finset.mem_erase] at hx
    simp only [setRow]
    rw [mem_sts]
    exact ⟨ht.1, hx.2.2, ht.2.2.1, ht.2.2.2.1, Ne.symm hx.2.1, hx.1, ht.2.2.2.2.2.2⟩
  · refine ⟨card_opts_ge (k := 5) _ _ _ h₃, Finset.mem_erase.mpr ⟨ht.2.2.2.2.2.2,
      Finset.mem_erase.mpr ⟨Ne.symm ht.2.2.2.2.2.1, ht.2.2.1⟩⟩, ?_⟩
    intro x hx
    simp only [optsRow, opts3, Finset.mem_erase] at hx
    simp only [setRow]
    rw [mem_sts]
    exact ⟨ht.1, ht.2.1, hx.2.2, ht.2.2.2.1, ht.2.2.2.2.1, Ne.symm hx.2.1, hx.1⟩
  · refine ⟨card_opts1_ge (k := 5) _ _ h₄, Finset.mem_erase.mpr ⟨Ne.symm ht.2.2.2.2.2.2,
      ht.2.2.2.1⟩, ?_⟩
    intro x hx
    simp only [optsRow, opts4, Finset.mem_erase] at hx
    simp only [setRow]
    rw [mem_sts]
    exact ⟨ht.1, ht.2.1, ht.2.2.1, hx.2, ht.2.2.2.2.1, ht.2.2.2.2.2.1, Ne.symm hx.1⟩

theorem setRow_inj (r : Fin 4) (t₁ t₂ : T4) (x₁ x₂ : ℕ) (he : setRow r t₁ x₁ = setRow r t₂ x₂)
    (hg : rowfun r t₁ = rowfun r t₂) : t₁ = t₂ := by
  obtain ⟨a, b, c, d⟩ := t₁
  obtain ⟨a', b', c', d'⟩ := t₂
  fin_cases r <;> simp only [setRow, set1, set2, set3, set4, Prod.mk.injEq] at he <;>
    simp only [rowfun, r1, r2, r3, r4] at hg
  · obtain ⟨-, rfl, rfl, rfl⟩ := he; rw [hg]
  · obtain ⟨rfl, -, rfl, rfl⟩ := he; rw [hg]
  · obtain ⟨rfl, rfl, -, rfl⟩ := he; rw [hg]
  · obtain ⟨rfl, rfl, rfl, -⟩ := he; rw [hg]

/-! ### Lemma F: the event-conditioned fibre -/

/-- **The fibre bound inside an event** that does not read the row. -/
theorem fib_event (u : T4 → ℝ) (hu : ∀ t, 0 ≤ u t) {R : ℝ} (hR0 : 0 < R)
    (hR : ∀ t ∈ sts X₁ X₂ X₃ X₄, ∀ t' ∈ sts X₁ X₂ X₃ X₄, u t ≤ R * u t')
    (h₁ : 4 ≤ X₁.card) (h₂ : 4 ≤ X₂.card) (h₃ : 4 ≤ X₃.card) (h₄ : 4 ≤ X₄.card)
    (r : Fin 4) (E : T4 → Bool) (hE : ∀ t x, E (setRow r t x) = E t) (φ : T4 → ℕ)
    (hφ : ∀ t x, φ (setRow r t x) = φ t) :
    (R + ((mrow r : ℕ) : ℝ) - 1) * ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter
        (fun t => rowfun r t = φ t ∧ E t = true), u t
      ≤ R * ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => E t = true), u t := by
  set Ω := (sts X₁ X₂ X₃ X₄).filter (fun t => E t = true) with hΩ
  have e : (sts X₁ X₂ X₃ X₄).filter (fun t => rowfun r t = φ t ∧ E t = true)
      = Ω.filter (fun t => rowfun r t = φ t) := by
    rw [hΩ, Finset.filter_filter]
    exact Finset.filter_congr (fun t _ => and_comm)
  rw [e]
  have hm : 1 ≤ mrow r := by unfold mrow; split_ifs <;> norm_num
  have h := fibre_row_sharp u hu (fun t => rowfun r t = φ t) (Ω := Ω) (rowfun r) (setRow r) φ
    (optsRow X₁ X₂ X₃ X₄ r) (mrow r) hm
    (fun t ht => (row_facts h₁ h₂ h₃ h₄ r (Finset.mem_filter.mp ht).1).1)
    (fun t ht => (row_facts h₁ h₂ h₃ h₄ r (Finset.mem_filter.mp ht).1).2.1)
    (fun t ht x hx => Finset.mem_filter.mpr ⟨(row_facts h₁ h₂ h₃ h₄ r
      (Finset.mem_filter.mp ht).1).2.2 x hx, by rw [hE]; exact (Finset.mem_filter.mp ht).2⟩)
    (rowfun_setRow r) (setRow_inj r) hφ (fun _ h => h) hR0
    (fun t ht t' ht' => hR t (Finset.mem_filter.mp ht).1 t' (Finset.mem_filter.mp ht').1)
  linarith

/-- The fibre share in the form `Σ_P ≤ q Σ` at `R = 125/118`. -/
theorem q_of_fib (r : Fin 4) {P S : ℝ}
    (h : (125 / 118 + ((mrow r : ℕ) : ℝ) - 1) * P ≤ 125 / 118 * S) : P ≤ (qrow r : ℝ) * S := by
  unfold mrow at h; unfold qrow
  split_ifs at h ⊢ <;> push_cast at h ⊢ <;> linarith

/-- **A colour-set peel**: `Σ_{E, sᵣ ∈ D} u ≤ min (qᵣ d, 1) Σ_E u` for `|D| ≤ d`. -/
theorem peel_mem (u : T4 → ℝ) (hu : ∀ t, 0 ≤ u t)
    (hR : ∀ t ∈ sts X₁ X₂ X₃ X₄, ∀ t' ∈ sts X₁ X₂ X₃ X₄, u t ≤ 125 / 118 * u t')
    (h₁ : 4 ≤ X₁.card) (h₂ : 4 ≤ X₂.card) (h₃ : 4 ≤ X₃.card) (h₄ : 4 ≤ X₄.card)
    (r : Fin 4) (E : T4 → Bool) (hE : ∀ t x, E (setRow r t x) = E t) (D : Finset ℕ) {d : ℕ}
    (hd : D.card ≤ d) :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => rowfun r t ∈ D ∧ E t = true), u t
      ≤ ((min (qrow r * d) 1 : ℚ) : ℝ)
        * ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => E t = true), u t := by
  set S := ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => E t = true), u t with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun t _ => hu t
  have hq0 : (0 : ℝ) ≤ qrow r := by unfold qrow; split_ifs <;> norm_num
  -- per colour
  have hc : ∀ c, ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => rowfun r t = c ∧ E t = true), u t
      ≤ (qrow r : ℝ) * S := fun c =>
    q_of_fib r (fib_event u hu (by norm_num) hR h₁ h₂ h₃ h₄ r E hE (fun _ => c) (fun _ _ => rfl))
  -- summed over the colours of `D`
  have h1 : ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => rowfun r t ∈ D ∧ E t = true), u t
      ≤ (qrow r : ℝ) * d * S := by
    have e : ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => rowfun r t ∈ D ∧ E t = true), u t
        = ∑ c ∈ D, ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => rowfun r t = c ∧ E t = true), u t := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := rowfun r) (t := D)
        (fun x hx => by simp only [Finset.mem_filter] at hx; exact hx.2.1)]
      refine Finset.sum_congr rfl (fun c hc => ?_)
      rw [Finset.filter_filter]
      congr 1
      ext t; simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h1, ⟨-, h3⟩, h4⟩; exact ⟨h1, h4, h3⟩
      · rintro ⟨h1, h4, h3⟩; exact ⟨h1, ⟨h4 ▸ hc, h3⟩, h4⟩
    rw [e]
    calc ∑ c ∈ D, ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => rowfun r t = c ∧ E t = true), u t
        ≤ ∑ c ∈ D, (qrow r : ℝ) * S := Finset.sum_le_sum (fun c _ => hc c)
      _ = (qrow r : ℝ) * D.card * S := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ (qrow r : ℝ) * d * S := by
          have : (D.card : ℝ) ≤ d := by exact_mod_cast hd
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hq0) hS0
  have h2 : ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => rowfun r t ∈ D ∧ E t = true), u t ≤ S := by
    rw [hS]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun t ht => ?_) (fun t _ _ => hu t)
    simp only [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, ht.2.2⟩
  push_cast
  rcases le_total ((qrow r : ℝ) * d) 1 with h | h
  · rw [min_eq_left h]; exact h1
  · rw [min_eq_right h, one_mul]; exact h2

/-- **An equality peel**: `Σ_{E, sᵣ = sⱼ} u ≤ qᵣ Σ_E u` for `j ≠ r`. -/
theorem peel_eq (u : T4 → ℝ) (hu : ∀ t, 0 ≤ u t)
    (hR : ∀ t ∈ sts X₁ X₂ X₃ X₄, ∀ t' ∈ sts X₁ X₂ X₃ X₄, u t ≤ 125 / 118 * u t')
    (h₁ : 4 ≤ X₁.card) (h₂ : 4 ≤ X₂.card) (h₃ : 4 ≤ X₃.card) (h₄ : 4 ≤ X₄.card)
    (r j : Fin 4) (hj : j ≠ r) (E : T4 → Bool) (hE : ∀ t x, E (setRow r t x) = E t) :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => rowfun r t = rowfun j t ∧ E t = true), u t
      ≤ (qrow r : ℝ) * ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => E t = true), u t :=
  q_of_fib r (fib_event u hu (by norm_num) hR h₁ h₂ h₃ h₄ r E hE (rowfun j)
    (fun t x => rowfun_setRow_ne hj t x))

end rows

/-! ### Factors and peeling chains -/

/-- A factor of a pin: row `r` in the colour set `D` (declared size `d`), or row `r` equal to
row `j`. -/
inductive Fac
  | mem (r : Fin 4) (D : Finset ℕ) (d : ℕ)
  | eqr (r j : Fin 4)

namespace Fac

/-- The peeled row. -/
def row : Fac → Fin 4
  | mem r _ _ => r
  | eqr r _ => r

/-- The rows a factor reads. -/
def reads : Fac → Fin 4 → Bool
  | mem r _ _, i => decide (r = i)
  | eqr r j, i => decide (r = i) || decide (j = i)

/-- The event of a factor. -/
def ev : Fac → T4 → Bool
  | mem r D _, t => decide (rowfun r t ∈ D)
  | eqr r j, t => decide (rowfun r t = rowfun j t)

/-- The side condition: the declared size, or two different rows. -/
def ok : Fac → Prop
  | mem _ D d => D.card ≤ d
  | eqr r j => j ≠ r

/-- The bound of a factor. -/
def bnd : Fac → ℚ
  | mem r _ d => min (qrow r * d) 1
  | eqr r _ => qrow r

theorem ev_setRow {f : Fac} {i : Fin 4} (h : f.reads i = false) (t : T4) (x : ℕ) :
    f.ev (setRow i t x) = f.ev t := by
  cases f with
  | mem r D d =>
    simp only [reads, decide_eq_false_iff_not] at h
    simp only [ev, rowfun_setRow_ne h]
  | eqr r j =>
    simp only [reads, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    simp only [ev, rowfun_setRow_ne h.1, rowfun_setRow_ne h.2]

theorem bnd_nonneg (f : Fac) : (0 : ℚ) ≤ f.bnd := by
  have hq : ∀ r, (0 : ℚ) ≤ qrow r := fun r => by unfold qrow; split_ifs <;> norm_num
  cases f with
  | mem r D d => exact le_min (mul_nonneg (hq r) (Nat.cast_nonneg d)) zero_le_one
  | eqr r j => exact hq r

end Fac

/-- All factors hold. -/
def allEv (fs : List Fac) (t : T4) : Bool := fs.all fun f => f.ev t

/-- **The peel order**: each factor's row is read by no later factor and not by the base event,
and each factor's side condition holds. -/
def PeelOK (base : Fin 4 → Bool) : List Fac → Prop
  | [] => True
  | f :: fs => base f.row = false ∧ (∀ g ∈ fs, g.reads f.row = false) ∧ f.ok ∧ PeelOK base fs

theorem allEv_setRow {fs : List Fac} {i : Fin 4} (h : ∀ g ∈ fs, g.reads i = false) (t : T4)
    (x : ℕ) : allEv fs (setRow i t x) = allEv fs t := by
  unfold allEv
  induction fs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.all_cons]
    rw [Fac.ev_setRow (h g List.mem_cons_self),
      ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))]

section chain

variable {X₁ X₂ X₃ X₄ : Finset ℕ}

/-- One peel of a factor. -/
theorem peel_fac (u : T4 → ℝ) (hu : ∀ t, 0 ≤ u t)
    (hR : ∀ t ∈ sts X₁ X₂ X₃ X₄, ∀ t' ∈ sts X₁ X₂ X₃ X₄, u t ≤ 125 / 118 * u t')
    (h₁ : 4 ≤ X₁.card) (h₂ : 4 ≤ X₂.card) (h₃ : 4 ≤ X₃.card) (h₄ : 4 ≤ X₄.card)
    (f : Fac) (hf : f.ok) (E : T4 → Bool) (hE : ∀ t x, E (setRow f.row t x) = E t) :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => (f.ev t && E t) = true), u t
      ≤ (f.bnd : ℝ) * ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => E t = true), u t := by
  cases f with
  | mem r D d =>
    have h := peel_mem u hu hR h₁ h₂ h₃ h₄ r E hE D (d := d) hf
    have e : (sts X₁ X₂ X₃ X₄).filter (fun t => ((Fac.mem r D d).ev t && E t) = true)
        = (sts X₁ X₂ X₃ X₄).filter (fun t => rowfun r t ∈ D ∧ E t = true) :=
      Finset.filter_congr (fun t _ => by simp [Fac.ev])
    rw [e]; exact h
  | eqr r j =>
    have h := peel_eq u hu hR h₁ h₂ h₃ h₄ r j hf E hE
    have e : (sts X₁ X₂ X₃ X₄).filter (fun t => ((Fac.eqr r j).ev t && E t) = true)
        = (sts X₁ X₂ X₃ X₄).filter (fun t => rowfun r t = rowfun j t ∧ E t = true) :=
      Finset.filter_congr (fun t _ => by simp [Fac.ev])
    rw [e]; exact h

/-- **A peeling chain.** -/
theorem peel_chain (u : T4 → ℝ) (hu : ∀ t, 0 ≤ u t)
    (hR : ∀ t ∈ sts X₁ X₂ X₃ X₄, ∀ t' ∈ sts X₁ X₂ X₃ X₄, u t ≤ 125 / 118 * u t')
    (h₁ : 4 ≤ X₁.card) (h₂ : 4 ≤ X₂.card) (h₃ : 4 ≤ X₃.card) (h₄ : 4 ≤ X₄.card)
    (base : Fin 4 → Bool) (E : T4 → Bool)
    (hE : ∀ i, base i = false → ∀ t x, E (setRow i t x) = E t) :
    ∀ fs : List Fac, PeelOK base fs →
      ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => (allEv fs t && E t) = true), u t
        ≤ (((fs.map Fac.bnd).prod : ℚ) : ℝ)
          * ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => E t = true), u t
  | [], _ => by simp [allEv]
  | f :: fs, ⟨hb, hr, hok, hrest⟩ => by
    have ih := peel_chain u hu hR h₁ h₂ h₃ h₄ base E hE fs hrest
    have hE' : ∀ t x, (allEv fs (setRow f.row t x) && E (setRow f.row t x))
        = (allEv fs t && E t) := fun t x => by
      rw [allEv_setRow hr, hE _ hb]
    have h := peel_fac u hu hR h₁ h₂ h₃ h₄ f hok (fun t => allEv fs t && E t) hE'
    have e : (sts X₁ X₂ X₃ X₄).filter (fun t => (allEv (f :: fs) t && E t) = true)
        = (sts X₁ X₂ X₃ X₄).filter (fun t => (f.ev t && (allEv fs t && E t)) = true) :=
      Finset.filter_congr (fun t _ => by simp only [allEv, List.all_cons, Bool.and_assoc])
    rw [e]
    have hb0 : (0 : ℝ) ≤ f.bnd := by exact_mod_cast f.bnd_nonneg
    calc _ ≤ (f.bnd : ℝ) * ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter
            (fun t => (allEv fs t && E t) = true), u t := h
      _ ≤ (f.bnd : ℝ) * ((((fs.map Fac.bnd).prod : ℚ) : ℝ)
            * ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => E t = true), u t) :=
          mul_le_mul_of_nonneg_left ih hb0
      _ = _ := by simp only [List.map_cons, List.prod_cons]; push_cast; ring

end chain

/-! ### Lemma B: the marginal block -/

/-- **The block inequality, abstractly.** States fibre over `π` into `F`; every fibre has between
`ℓ c` and `c` states, the weights lie in `[ρ g, g]`, at most `m` values of `F` lie in `T`, and
`F` has at least `M` values. -/
theorem block_core {α : Type*} [DecidableEq α] (Ω : Finset T4) (u : T4 → ℝ) (π : T4 → α)
    (F T : Finset α) (hF : ∀ t ∈ Ω, π t ∈ F) {g c ℓ ρ : ℝ} (hρ : 0 ≤ ρ) (hℓ : 0 ≤ ℓ)
    (hc : 0 ≤ c) (hg : 0 ≤ g) (hu : ∀ t ∈ Ω, ρ * g ≤ u t ∧ u t ≤ g)
    (hN : ∀ τ ∈ F, ℓ * c ≤ ((Ω.filter (fun t => π t = τ)).card : ℝ) ∧
      ((Ω.filter (fun t => π t = τ)).card : ℝ) ≤ c)
    {m M : ℕ} (hm : (F ∩ T).card ≤ m) (hM : M ≤ F.card) :
    ((m : ℝ) + ρ * ℓ * ((M : ℝ) - m)) * ∑ t ∈ Ω.filter (fun t => π t ∈ T), u t
      ≤ m * ∑ t ∈ Ω, u t := by
  have hu0 : ∀ t ∈ Ω, 0 ≤ u t := fun t ht => le_trans (mul_nonneg hρ hg) (hu t ht).1
  set SE := ∑ t ∈ Ω.filter (fun t => π t ∈ T), u t with hSE
  set SC := ∑ t ∈ Ω.filter (fun t => ¬ π t ∈ T), u t with hSC
  have hW : ∑ t ∈ Ω, u t = SE + SC := (Finset.sum_filter_add_sum_filter_not Ω _ u).symm
  have hSE0 : 0 ≤ SE := Finset.sum_nonneg fun t ht => hu0 t (Finset.mem_filter.mp ht).1
  have hSC0 : 0 ≤ SC := Finset.sum_nonneg fun t ht => hu0 t (Finset.mem_filter.mp ht).1
  -- the fibre counts
  have cE : ((Ω.filter (fun t => π t ∈ T)).card : ℝ)
      = ∑ τ ∈ F ∩ T, ((Ω.filter (fun t => π t = τ)).card : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := π) (t := F ∩ T) (fun t ht => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_inter.mpr ⟨hF t h1, h2⟩)]
    push_cast
    refine Finset.sum_congr rfl (fun τ hτ => ?_)
    rw [Finset.filter_filter]
    congr 2
    ext t; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, h3 ▸ (Finset.mem_inter.mp hτ).2, h3⟩
  have cC : ((Ω.filter (fun t => ¬ π t ∈ T)).card : ℝ)
      = ∑ τ ∈ F \ T, ((Ω.filter (fun t => π t = τ)).card : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := π) (t := F \ T) (fun t ht => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_sdiff.mpr ⟨hF t h1, h2⟩)]
    push_cast
    refine Finset.sum_congr rfl (fun τ hτ => ?_)
    rw [Finset.filter_filter]
    congr 2
    ext t; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, h3 ▸ (Finset.mem_sdiff.mp hτ).2, h3⟩
  have hNE : ((Ω.filter (fun t => π t ∈ T)).card : ℝ) ≤ (F ∩ T).card * c := by
    rw [cE]
    calc ∑ τ ∈ F ∩ T, ((Ω.filter (fun t => π t = τ)).card : ℝ)
        ≤ ∑ τ ∈ F ∩ T, c := Finset.sum_le_sum (fun τ hτ =>
          (hN τ (Finset.mem_inter.mp hτ).1).2)
      _ = (F ∩ T).card * c := by rw [Finset.sum_const, nsmul_eq_mul]
  have hNC : ((F \ T).card : ℝ) * (ℓ * c) ≤ ((Ω.filter (fun t => ¬ π t ∈ T)).card : ℝ) := by
    rw [cC]
    calc ((F \ T).card : ℝ) * (ℓ * c) = ∑ τ ∈ F \ T, ℓ * c := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun τ hτ => (hN τ (Finset.mem_sdiff.mp hτ).1).1)
  -- the weights
  have bE : SE ≤ g * (Ω.filter (fun t => π t ∈ T)).card := by
    rw [hSE, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun t ht => by
      have := (hu t (Finset.mem_filter.mp ht).1).2; push_cast; linarith)
  have bC : ρ * g * (Ω.filter (fun t => ¬ π t ∈ T)).card ≤ SC := by
    rw [hSC, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun t ht => by
      have := (hu t (Finset.mem_filter.mp ht).1).1; push_cast; linarith)
  have hFT : ((F \ T).card : ℝ) = F.card - (F ∩ T).card := by
    have := Finset.card_sdiff_add_card_inter F T
    have : ((F \ T).card : ℝ) + (F ∩ T).card = F.card := by exact_mod_cast this
    linarith
  have hm' : ((F ∩ T).card : ℝ) ≤ m := by exact_mod_cast hm
  have hM' : (M : ℝ) ≤ F.card := by exact_mod_cast hM
  rw [hW]
  rcases le_or_gt (M : ℝ) m with hMm | hMm
  · have : ρ * ℓ * ((M : ℝ) - m) * SE ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hρ hℓ)
        (by linarith)) hSE0
    have : 0 ≤ (m : ℝ) * SC := mul_nonneg (Nat.cast_nonneg m) hSC0
    nlinarith
  · set t' : ℝ := ((F ∩ T).card : ℝ)
    have hK : 0 ≤ ρ * ℓ * g * c := mul_nonneg (mul_nonneg (mul_nonneg hρ hℓ) hg) hc
    have i1 : ρ * ℓ * ((M : ℝ) - m) * SE ≤ ρ * ℓ * ((M : ℝ) - m) * (g * (t' * c)) := by
      have : SE ≤ g * (t' * c) := bE.trans (mul_le_mul_of_nonneg_left hNE hg)
      exact mul_le_mul_of_nonneg_left this (mul_nonneg (mul_nonneg hρ hℓ) (by linarith))
    have i2 : ρ * g * (((F.card : ℝ) - t') * (ℓ * c)) ≤ SC := by
      have : ((F.card : ℝ) - t') * (ℓ * c) ≤ ((Ω.filter (fun t => ¬ π t ∈ T)).card : ℝ) := by
        rw [← hFT]; exact hNC
      exact le_trans (mul_le_mul_of_nonneg_left this (mul_nonneg hρ hg)) bC
    have i3 : ((M : ℝ) - m) * t' ≤ m * ((F.card : ℝ) - t') := by nlinarith
    have i4 : ρ * ℓ * ((M : ℝ) - m) * (g * (t' * c)) ≤ m * (ρ * g * (((F.card : ℝ) - t') * (ℓ * c))) := by
      have := mul_le_mul_of_nonneg_left i3 hK
      nlinarith
    have i5 : (m : ℝ) * (ρ * g * (((F.card : ℝ) - t') * (ℓ * c))) ≤ m * SC :=
      mul_le_mul_of_nonneg_left i2 (Nat.cast_nonneg m)
    nlinarith

end GridGen.Four
