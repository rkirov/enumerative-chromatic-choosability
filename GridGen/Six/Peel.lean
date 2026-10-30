/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.Count

/-!
# Height six: event-conditioned fibres and peeling chains

`GridGen/Five/K5/Peel.lean` with six rows.

* **The fibre property** (`FibOK Ω u q`): inside any event `E` that does not read row `r`, the
  states whose row `r` is pinned to a function `φ` of the other rows carry at most `q r` of the
  weight of `E`. For the proper columns of lists of at least `nᵣ` colours and weights within the
  factor `R` of each other it holds with `q r = R/(R + mᵣ - 1)`, `mᵣ = nᵣ - 1` on an end row and
  `nᵣ - 2` on a middle row (`fibOK_sts`, from `Lookback.fibre_row_sharp`).
* **Factors** (`Fac6`): row `r` in a colour set `D` of at most `d` colours (bound
  `min (q r · d) 1`), or row `r` equal to row `j` (bound `q r`).
* **Peeling chains** (`peel_chain6`): a list of factors in an order in which each peeled row is
  read neither by a later factor nor by the base event carries at most the product of the bounds
  times the weight of the base event.
-/

namespace GridGen.Six

open Finset

/-! ### The fibre property -/

/-- **Fibres inside events**: pinning row `r` inside an event that does not read it costs the
factor `q r`. -/
def FibOK (Ω : Finset T6) (u : T6 → ℝ) (q : ℕ → ℚ) : Prop :=
  ∀ r < 6, ∀ E : T6 → Bool, (∀ t x, E (setAt r t x) = E t) → ∀ φ : T6 → ℕ,
    (∀ t x, φ (setAt r t x) = φ t) →
    ∑ t ∈ Ω.filter (fun t => rowAt r t = φ t ∧ E t = true), u t
      ≤ (q r : ℝ) * ∑ t ∈ Ω.filter (fun t => E t = true), u t

/-- The number of free colours of row `r` with lists of at least `n` colours. -/
def frc (n r : ℕ) : ℕ := if r = 0 ∨ 5 ≤ r then n - 1 else n - 2

theorem optsAt_frc {X₁ X₂ X₃ X₄ X₅ X₆ : Finset ℕ} {n : ℕ → ℕ}
    (hX : ∀ i < 6, n i ≤ (bl X₁ X₂ X₃ X₄ X₅ X₆ i).card) {r : ℕ} (hr : r < 6) (t : T6) :
    frc (n r) r ≤ (optsAt X₁ X₂ X₃ X₄ X₅ X₆ r t).card := by
  interval_cases r <;> simp only [frc, optsAt] <;> norm_num
  · have := card_erase_ge X₁ (r2 t); have := hX 0 (by norm_num); simp only [bl] at this; omega
  · have := card_erase_ge X₂ (r1 t); have := card_erase_ge (X₂.erase (r1 t)) (r3 t)
    have := hX 1 (by norm_num); simp only [bl] at this; omega
  · have := card_erase_ge X₃ (r2 t); have := card_erase_ge (X₃.erase (r2 t)) (r4 t)
    have := hX 2 (by norm_num); simp only [bl] at this; omega
  · have := card_erase_ge X₄ (r3 t); have := card_erase_ge (X₄.erase (r3 t)) (r5 t)
    have := hX 3 (by norm_num); simp only [bl] at this; omega
  · have := card_erase_ge X₅ (r4 t); have := card_erase_ge (X₅.erase (r4 t)) (r6 t)
    have := hX 4 (by norm_num); simp only [bl] at this; omega
  · have := card_erase_ge X₆ (r5 t); have := hX 5 (by norm_num); simp only [bl] at this; omega

/-- **The fibre property of proper columns**, for weights within the factor `R`. -/
theorem fibOK_sts {X₁ X₂ X₃ X₄ X₅ X₆ : Finset ℕ} (n : ℕ → ℕ)
    (hX : ∀ i < 6, n i ≤ (bl X₁ X₂ X₃ X₄ X₅ X₆ i).card) (hn : ∀ i < 6, 1 ≤ frc (n i) i)
    (u : T6 → ℝ) (hu : ∀ t, 0 ≤ u t) {R : ℚ} (hR0 : 0 < R)
    (hR : ∀ t ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, ∀ t' ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, u t ≤ R * u t')
    (q : ℕ → ℚ) (hq : ∀ i < 6, q i = R / (R + frc (n i) i - 1)) :
    FibOK (sts X₁ X₂ X₃ X₄ X₅ X₆) u q := by
  intro r hr E hE φ hφ
  set Ω := (sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => E t = true) with hΩ
  have e : (sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => rowAt r t = φ t ∧ E t = true)
      = Ω.filter (fun t => rowAt r t = φ t) := by
    rw [hΩ, Finset.filter_filter]
    exact Finset.filter_congr (fun t _ => and_comm)
  rw [e]
  have h := Lookback.fibre_row_sharp (Ω := Ω) u hu (fun t => rowAt r t = φ t) (rowAt r) (setAt r) φ
    (optsAt X₁ X₂ X₃ X₄ X₅ X₆ r) (frc (n r) r) (hn r hr)
    (fun t _ => optsAt_frc hX hr t)
    (fun t ht => optsAt_cur hr (Finset.mem_filter.mp ht).1)
    (fun t ht x hx => Finset.mem_filter.mpr ⟨optsAt_mem hr (Finset.mem_filter.mp ht).1 hx,
      by rw [hE]; exact (Finset.mem_filter.mp ht).2⟩)
    (getAt_setAt r) (fun t₁ t₂ x₁ x₂ he hg => setAt_inj r t₁ t₂ x₁ x₂ he hg) hφ (fun _ h => h)
    (R := (R : ℝ)) (by exact_mod_cast hR0)
    (fun t ht t' ht' => hR t (Finset.mem_filter.mp ht).1 t' (Finset.mem_filter.mp ht').1)
  rw [hq r hr]
  have hm : (1 : ℝ) ≤ (frc (n r) r : ℝ) := by exact_mod_cast hn r hr
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR0
  have hpos : (0 : ℝ) < (R : ℝ) + (frc (n r) r : ℝ) - 1 := by linarith
  push_cast
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  linarith

/-! ### Factors and peeling chains -/

/-- A factor of a pin: row `r` in the colour set `D` (declared size `d`), or row `r` equal to
row `j`. -/
inductive Fac6
  | mem (r : ℕ) (D : Finset ℕ) (d : ℕ)
  | eqr (r j : ℕ)

namespace Fac6

/-- The peeled row. -/
def row : Fac6 → ℕ
  | mem r _ _ => r
  | eqr r _ => r

/-- The rows a factor reads. -/
def reads : Fac6 → ℕ → Bool
  | mem r _ _, i => decide (r = i)
  | eqr r j, i => decide (r = i) || decide (j = i)

/-- The event of a factor. -/
def ev : Fac6 → T6 → Bool
  | mem r D _, t => decide (rowAt r t ∈ D)
  | eqr r j, t => decide (rowAt r t = rowAt j t)

/-- The side condition. -/
def ok : Fac6 → Prop
  | mem r D d => r < 6 ∧ D.card ≤ d
  | eqr r j => r < 6 ∧ j < 6 ∧ j ≠ r

/-- The bound of a factor. -/
def bnd (q : ℕ → ℚ) : Fac6 → ℚ
  | mem r _ d => min (q r * d) 1
  | eqr r _ => q r

theorem ev_setAt {f : Fac6} {i : ℕ} (hi : i < 6) (hf : f.ok) (h : f.reads i = false) (t : T6)
    (x : ℕ) : f.ev (setAt i t x) = f.ev t := by
  cases f with
  | mem r D d =>
    simp only [reads, decide_eq_false_iff_not] at h
    simp only [ev, rowAt_setAt_ne (Ne.symm h) hi hf.1]
  | eqr r j =>
    simp only [reads, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    simp only [ev, rowAt_setAt_ne (Ne.symm h.1) hi hf.1, rowAt_setAt_ne (Ne.symm h.2) hi hf.2.1]

theorem bnd_nonneg {q : ℕ → ℚ} (hq : ∀ i, 0 ≤ q i) (f : Fac6) : (0 : ℚ) ≤ f.bnd q := by
  cases f with
  | mem r D d => exact le_min (mul_nonneg (hq r) (Nat.cast_nonneg d)) zero_le_one
  | eqr r j => exact hq r

theorem row_lt {f : Fac6} (hf : f.ok) : f.row < 6 := by
  cases f with
  | mem r D d => exact hf.1
  | eqr r j => exact hf.1

end Fac6

/-- All factors hold. -/
def allEv6 (fs : List Fac6) (t : T6) : Bool := fs.all fun f => f.ev t

/-- **The peel order**: each factor's row is read by no later factor and not by the base. -/
def PeelOK6 (base : ℕ → Bool) : List Fac6 → Prop
  | [] => True
  | f :: fs => base f.row = false ∧ (∀ g ∈ fs, g.reads f.row = false) ∧ f.ok ∧ PeelOK6 base fs

theorem allEv6_setAt {fs : List Fac6} {i : ℕ} (hi : i < 6) (hok : ∀ g ∈ fs, g.ok)
    (h : ∀ g ∈ fs, g.reads i = false) (t : T6) (x : ℕ) :
    allEv6 fs (setAt i t x) = allEv6 fs t := by
  unfold allEv6
  induction fs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.all_cons]
    rw [Fac6.ev_setAt hi (hok g List.mem_cons_self) (h g List.mem_cons_self),
      ih (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))]

theorem PeelOK6.oks {base : ℕ → Bool} : ∀ {fs : List Fac6}, PeelOK6 base fs → ∀ g ∈ fs, g.ok
  | [], _, g, hg => absurd hg List.not_mem_nil
  | _ :: _, ⟨_, _, hf, hr⟩, g, hg => by
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hf
    · exact PeelOK6.oks hr g hg

section chain

variable {Ω : Finset T6} {u : T6 → ℝ} {q : ℕ → ℚ}

/-- One peel. -/
theorem peel_fac6 (hF : FibOK Ω u q) (hu : ∀ t, 0 ≤ u t) (hq : ∀ i, 0 ≤ q i) (f : Fac6)
    (hf : f.ok) (E : T6 → Bool) (hE : ∀ t x, E (setAt f.row t x) = E t) :
    ∑ t ∈ Ω.filter (fun t => (f.ev t && E t) = true), u t
      ≤ (f.bnd q : ℝ) * ∑ t ∈ Ω.filter (fun t => E t = true), u t := by
  set S := ∑ t ∈ Ω.filter (fun t => E t = true), u t with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun t _ => hu t
  cases f with
  | eqr r j =>
    have e : Ω.filter (fun t => ((Fac6.eqr r j).ev t && E t) = true)
        = Ω.filter (fun t => rowAt r t = rowAt j t ∧ E t = true) :=
      Finset.filter_congr (fun t _ => by simp [Fac6.ev])
    rw [e]
    exact hF r hf.1 E hE (rowAt j) (fun t x => rowAt_setAt_ne (Ne.symm hf.2.2) hf.1 hf.2.1 t x)
  | mem r D d =>
    have e : Ω.filter (fun t => ((Fac6.mem r D d).ev t && E t) = true)
        = Ω.filter (fun t => rowAt r t ∈ D ∧ E t = true) :=
      Finset.filter_congr (fun t _ => by simp [Fac6.ev])
    rw [e]
    have hc : ∀ c, ∑ t ∈ Ω.filter (fun t => rowAt r t = c ∧ E t = true), u t ≤ (q r : ℝ) * S :=
      fun c => hF r hf.1 E hE (fun _ => c) (fun _ _ => rfl)
    have h1 : ∑ t ∈ Ω.filter (fun t => rowAt r t ∈ D ∧ E t = true), u t ≤ (q r : ℝ) * d * S := by
      have e2 : ∑ t ∈ Ω.filter (fun t => rowAt r t ∈ D ∧ E t = true), u t
          = ∑ c ∈ D, ∑ t ∈ Ω.filter (fun t => rowAt r t = c ∧ E t = true), u t := by
        rw [← Finset.sum_fiberwise_of_maps_to (g := rowAt r) (t := D)
          (fun x hx => by simp only [Finset.mem_filter] at hx; exact hx.2.1)]
        refine Finset.sum_congr rfl (fun c hc => ?_)
        rw [Finset.filter_filter]
        congr 1
        ext t; simp only [Finset.mem_filter]
        constructor
        · rintro ⟨h1, ⟨-, h3⟩, h4⟩; exact ⟨h1, h4, h3⟩
        · rintro ⟨h1, h4, h3⟩; exact ⟨h1, ⟨h4 ▸ hc, h3⟩, h4⟩
      rw [e2]
      calc ∑ c ∈ D, ∑ t ∈ Ω.filter (fun t => rowAt r t = c ∧ E t = true), u t
          ≤ ∑ _c ∈ D, (q r : ℝ) * S := Finset.sum_le_sum (fun c _ => hc c)
        _ = (q r : ℝ) * D.card * S := by rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ (q r : ℝ) * d * S := by
            have : (D.card : ℝ) ≤ d := by exact_mod_cast hf.2
            have hq' : (0 : ℝ) ≤ q r := by exact_mod_cast hq r
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hq') hS0
    have h2 : ∑ t ∈ Ω.filter (fun t => rowAt r t ∈ D ∧ E t = true), u t ≤ S := by
      rw [hS]
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun t ht => ?_) (fun t _ _ => hu t)
      simp only [Finset.mem_filter] at ht ⊢
      exact ⟨ht.1, ht.2.2⟩
    simp only [Fac6.bnd]
    push_cast
    rcases le_total ((q r : ℝ) * d) 1 with h | h
    · rw [min_eq_left h]; exact h1
    · rw [min_eq_right h, one_mul]; exact h2

/-- **A peeling chain.** -/
theorem peel_chain6 (hF : FibOK Ω u q) (hu : ∀ t, 0 ≤ u t) (hq : ∀ i, 0 ≤ q i)
    (base : ℕ → Bool) (E : T6 → Bool)
    (hE : ∀ i < 6, base i = false → ∀ t x, E (setAt i t x) = E t) :
    ∀ fs : List Fac6, PeelOK6 base fs →
      ∑ t ∈ Ω.filter (fun t => (allEv6 fs t && E t) = true), u t
        ≤ (((fs.map (Fac6.bnd q)).prod : ℚ) : ℝ)
          * ∑ t ∈ Ω.filter (fun t => E t = true), u t
  | [], _ => by simp [allEv6]
  | f :: fs, ⟨hb, hr, hok, hrest⟩ => by
    have ih := peel_chain6 hF hu hq base E hE fs hrest
    have hlt := Fac6.row_lt hok
    have hE' : ∀ t x, (allEv6 fs (setAt f.row t x) && E (setAt f.row t x))
        = (allEv6 fs t && E t) := fun t x => by
      rw [allEv6_setAt hlt hrest.oks hr, hE _ hlt hb]
    have h := peel_fac6 hF hu hq f hok (fun t => allEv6 fs t && E t) hE'
    have e : Ω.filter (fun t => (allEv6 (f :: fs) t && E t) = true)
        = Ω.filter (fun t => (f.ev t && (allEv6 fs t && E t)) = true) :=
      Finset.filter_congr (fun t _ => by simp only [allEv6, List.all_cons, Bool.and_assoc])
    rw [e]
    have hb0 : (0 : ℝ) ≤ f.bnd q := by exact_mod_cast f.bnd_nonneg hq
    calc _ ≤ (f.bnd q : ℝ) * ∑ t ∈ Ω.filter (fun t => (allEv6 fs t && E t) = true), u t := h
      _ ≤ (f.bnd q : ℝ) * ((((fs.map (Fac6.bnd q)).prod : ℚ) : ℝ)
            * ∑ t ∈ Ω.filter (fun t => E t = true), u t) :=
          mul_le_mul_of_nonneg_left ih hb0
      _ = _ := by simp only [List.map_cons, List.prod_cons]; push_cast; ring

end chain

end GridGen.Six
