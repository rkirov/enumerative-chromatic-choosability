/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Chain5

/-!
# Height five: corner certificates for the pattern linear programme

The pattern lemmas of `ai_research_notes/H5_K6_ANALYTIC_2026-10-23.md` (Lemmas 8 and 11) bound
the average pattern weight of the proper columns of a list system from below. For a weight at a
corner of the box, the pattern shares `f` of the columns satisfy the chain bounds of
`GridGen/Five/Chain5.lean` (`f(E_p) ≤ 1/B_p` for the fourteen events), and the least possible
average is a linear programme over `f`. A feasible point of its dual — multipliers `y_p ≥ 0` and a
level `λ` with `λ ≤ σ(o(c)) + Σ_{c ∈ E_p} y_p` for each of the fifteen canonical patterns `c` —
gives `Σ_t σ(o(t)) ≥ (λ - Σ_p y_p/B_p) · #columns` (`lp_count`).

Everything is scaled to natural numbers: the corner weights by `2000` (`sigN`), the multipliers
as `y_p = B_p Z_p/(2000 D)` and the level as `Λ/(2000 D)`, so a certificate is checked by a
Boolean function (`ptOK`) and `decide`.

**Corners.** A corner is a list `β` of ten bits, bit `o - 1` set when orbit `o` sits at its lower
edge (`sigR`); `allBits 10` lists all of them. A linear form `Σ aₒ wₒ` on the box is at least its
value at the corner chosen by the signs of its coefficients (`corner_pick`).
-/

namespace GridGen.Five

open Finset

/-! ### The events read only the pattern -/

theorem evb_congr {s t : T5} (h : SamePat s t) (p : ℕ) : evb p s = evb p t := by
  obtain ⟨h13, h24, h35, h14, h25, h15⟩ := h
  unfold evb
  split <;> simp only [h13, h24, h35, h14, h25, h15]

/-! ### Corners -/

/-- All bit lists of length `n` (the first bit varies fastest). -/
def allBits : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBits n).flatMap (fun l => [false :: l, true :: l])

theorem mem_allBits : ∀ (l : List Bool), l ∈ allBits l.length
  | [] => by simp [allBits]
  | b :: l => by
    simp only [List.length_cons, allBits, List.mem_flatMap]
    refine ⟨l, mem_allBits l, ?_⟩
    cases b <;> simp

theorem length_allBits : ∀ n, (allBits n).length = 2 ^ n
  | 0 => rfl
  | n + 1 => by
    simp only [allBits, List.length_flatMap, List.length_cons, List.length_nil]
    rw [List.map_const', List.sum_replicate, length_allBits n]
    ring

/-- A partner in a zipped list. -/
theorem exists_mem_zip {α β : Type*} {l₁ : List α} {l₂ : List β} (h : l₁.length = l₂.length)
    {x : α} (hx : x ∈ l₁) : ∃ y, (x, y) ∈ l₁.zip l₂ := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  refine ⟨l₂[i]'(h ▸ hi), ?_⟩
  have hz : i < (l₁.zip l₂).length := by rw [List.length_zip]; omega
  have := List.getElem_mem hz
  rwa [List.getElem_zip] at this

/-- The lower edges of the box, times `2000`. -/
def loL : List ℕ := [2000, 1974, 1977, 1947, 1953, 1918, 1924, 1954, 1951, 1933, 1931]

theorem loL_eq : ∀ o : Fin 11, ((loL.getD o 0 : ℕ) : ℚ) = 2000 * lo5 o := by decide +kernel

/-- The corner weight of orbit `o`, times `2000`. -/
def sigN (β : List Bool) (o : Fin 11) : ℕ :=
  if o.val = 0 then 2000 else if β.getD (o.val - 1) false then loL.getD o.val 0 else 2000

/-- The corner weight of orbit `o`. -/
noncomputable def sigR (β : List Bool) (o : Fin 11) : ℝ :=
  if o.val = 0 then 1 else if β.getD (o.val - 1) false then (lo5 o : ℝ) else 1

theorem sigN_eq (β : List Bool) (o : Fin 11) : (sigN β o : ℝ) = 2000 * sigR β o := by
  unfold sigN sigR
  split_ifs
  · norm_num
  · have := loL_eq o
    have h : ((loL.getD o 0 : ℕ) : ℝ) = 2000 * (lo5 o : ℝ) := by exact_mod_cast this
    exact h
  · norm_num

/-- **The corner of a linear form.** -/
theorem corner_pick {w : Wt5} (hw : InBox5 w) (a : Fin 11 → ℝ) :
    ∃ β ∈ allBits 10, ∑ o, a o * sigR β o ≤ ∑ o, a o * w o := by
  set a' : ℕ → ℝ := fun j => if h : j < 11 then a ⟨j, h⟩ else 0 with ha'
  set β : List Bool := (List.range 10).map (fun j => decide (0 ≤ a' (j + 1))) with hβ
  have hlen : β.length = 10 := by simp [hβ]
  refine ⟨β, hlen ▸ mem_allBits β, Finset.sum_le_sum fun o _ => ?_⟩
  obtain ⟨hl, hu⟩ := hw o
  unfold sigR
  by_cases h0 : o.val = 0
  · have ho : o = 0 := Fin.ext h0
    subst ho
    have : w 0 = 1 := le_antisymm hu (by simpa [lo5] using hl)
    simp [this]
  · have hb : β.getD (o.val - 1) false = decide (0 ≤ a o) := by
      have ho : o.val - 1 < 10 := by omega
      rw [hβ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ho]
      simp only [Option.map_some, Option.getD_some, ha']
      have e : o.val - 1 + 1 = o.val := by omega
      simp only [e, o.isLt, dite_true]
    simp only [h0, ↓reduceIte, hb]
    by_cases ha : 0 ≤ a o
    · simp only [ha, decide_true, ↓reduceIte]
      exact mul_le_mul_of_nonneg_left hl ha
    · simp only [ha, decide_false, Bool.false_eq_true, ↓reduceIte]
      have ha' : a o < 0 := lt_of_not_ge ha
      nlinarith

/-! ### The dual certificate -/

/-- The multiplier sum of the events containing a column, scaled. -/
def ptSum (Z : List ℕ) (B : ℕ → ℕ) (c : T5) : ℕ → ℕ
  | 0 => 0
  | p + 1 => ptSum Z B c p + (if evb p c then B p * Z.getD p 0 else 0)

theorem ptSum_eq (Z : List ℕ) (B : ℕ → ℕ) (c : T5) (n : ℕ) :
    ptSum Z B c n = ∑ p ∈ range n, (if evb p c then B p * Z.getD p 0 else 0) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ptSum, ih, Finset.sum_range_succ]

theorem ptSum_congr (Z : List ℕ) (B : ℕ → ℕ) {s t : T5} (h : SamePat s t) (n : ℕ) :
    ptSum Z B s n = ptSum Z B t n := by
  rw [ptSum_eq, ptSum_eq]
  exact Finset.sum_congr rfl fun p _ => by rw [evb_congr h p]

/-- **The pointwise dual check**: at every canonical pattern, the level is at most the corner
weight plus the multipliers of the events containing it. -/
def ptOK (D : ℕ) (B : ℕ → ℕ) (β : List Bool) (Λ : ℕ) (Z : List ℕ) : Bool :=
  canons.all fun c => decide (Λ ≤ D * sigN β (orb c) + ptSum Z B c 14)

/-- **Weak duality, in counts.** -/
theorem lp_count {Ω : Finset T5} (hΩ : ∀ t ∈ Ω, Proper t) (B : ℕ → ℕ)
    (hB : ∀ p < 14, B p * (Ω.filter (fun t => evb p t = true)).card ≤ Ω.card)
    {D : ℕ} {β : List Bool} {Λ : ℕ} {Z : List ℕ} (hpt : ptOK D B β Λ Z = true) :
    Λ * Ω.card ≤ D * ∑ t ∈ Ω, sigN β (orb t) + (∑ p ∈ range 14, Z.getD p 0) * Ω.card := by
  have hpt' : ∀ t ∈ Ω, Λ ≤ D * sigN β (orb t) + ptSum Z B t 14 := by
    intro t ht
    have hs := hΩ t ht
    have hc := List.all_eq_true.mp hpt (canon t) (canon_mem hs)
    rw [decide_eq_true_eq] at hc
    rw [orb_congr (samePat_canon hs), ptSum_congr Z B (samePat_canon hs)]
    exact hc
  have h1 : Λ * Ω.card ≤ ∑ t ∈ Ω, (D * sigN β (orb t) + ptSum Z B t 14) := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hpt'
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h1
  have h2 : ∑ t ∈ Ω, ptSum Z B t 14
      = ∑ p ∈ range 14, B p * Z.getD p 0 * (Ω.filter (fun t => evb p t = true)).card := by
    simp only [ptSum_eq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
  have h3 : ∑ p ∈ range 14, B p * Z.getD p 0 * (Ω.filter (fun t => evb p t = true)).card
      ≤ (∑ p ∈ range 14, Z.getD p 0) * Ω.card := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun p hp => ?_
    have := hB p (Finset.mem_range.mp hp)
    calc B p * Z.getD p 0 * (Ω.filter (fun t => evb p t = true)).card
        = Z.getD p 0 * (B p * (Ω.filter (fun t => evb p t = true)).card) := by ring
      _ ≤ Z.getD p 0 * Ω.card := Nat.mul_le_mul_left _ this
  omega

/-- The weighted sum of a column system by orbits. -/
theorem sum_gw_orb (w : Wt5) (Ω : Finset T5) :
    ∑ t ∈ Ω, gw w t = ∑ o, ((Ω.filter (fun t => orb t = o)).card : ℝ) * w o := by
  unfold gw
  rw [← Finset.sum_fiberwise Ω orb (fun t => w (orb t))]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.mp ht).2]), Finset.sum_const,
    nsmul_eq_mul]

theorem sum_sigN_orb (β : List Bool) (Ω : Finset T5) :
    ((∑ t ∈ Ω, sigN β (orb t) : ℕ) : ℝ)
      = 2000 * ∑ o, ((Ω.filter (fun t => orb t = o)).card : ℝ) * sigR β o := by
  push_cast
  rw [← Finset.sum_fiberwise Ω orb (fun t => (sigN β (orb t) : ℝ)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.mp ht).2]), Finset.sum_const,
    nsmul_eq_mul, sigN_eq]
  ring

end GridGen.Five
