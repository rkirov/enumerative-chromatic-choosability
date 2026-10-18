/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Nine.Box9

/-!
# The refined box bound at `k = 8`

The scheme of `Nine/Box9.lean` with the constants of `k = 8`:

* `y₁`: the factors sum to at most `1 + 7 · 5/4 = 39/4`;
* `y₆`: `α₆ - 1` when `b` is available at `y₆` (ratio `1`), `α₆` otherwise (ratio `5/4`);
* a domino: ratio `25/18` when `b` is available at its future cell, `5/3` otherwise.

At most `3, 2, 2` labels are unavailable at `y₆` and at the two dominoes, so the label sum is at
most `24625/1296`. Hence a `5184/960375` fraction of the solutions is hit (`box_bound_eight`).
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m k : ℕ} {P A : Fin m → Finset ℕ} {N : Fin m → ℕ → ℕ}

section Eight

theorem dom_in_arith8 {α₂ α₃ τ u s : ℕ} (h2 : 6 ≤ α₂) (h3 : 6 ≤ α₃) (hτ : α₂ * (α₃ - 1) ≤ τ)
    (hu : u + α₂ ≤ τ + 1) (hs : τ ≤ s + α₃ + α₂) : 18 * u ≤ 25 * s := by
  obtain ⟨p, rfl⟩ : ∃ p, α₂ = 6 + p := ⟨α₂ - 6, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, α₃ = 6 + q := ⟨α₃ - 6, by omega⟩
  have e : (6 + p) * (6 + q - 1) = 30 + 5 * p + 6 * q + p * q := by
    rw [show 6 + q - 1 = 5 + q by omega]; ring
  rw [e] at hτ
  nlinarith

theorem dom_out_arith8 {α₂ α₃ τ u s : ℕ} (h2 : 6 ≤ α₂) (h3 : 6 ≤ α₃) (hτ : α₂ * (α₃ - 1) ≤ τ)
    (hu : u ≤ τ) (hs : τ ≤ s + α₃ + α₂) : 3 * u ≤ 5 * s := by
  obtain ⟨p, rfl⟩ : ∃ p, α₂ = 6 + p := ⟨α₂ - 6, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, α₃ = 6 + q := ⟨α₃ - 6, by omega⟩
  have e : (6 + p) * (6 + q - 1) = 30 + 5 * p + 6 * q + p * q := by
    rw [show 6 + q - 1 = 5 + q by omega]; ring
  rw [e] at hτ
  nlinarith

/-- The nested outsider sum. -/
theorem nested_sum8 (o6 oU oD : ℕ → Prop) [DecidablePred o6] [DecidablePred oU]
    [DecidablePred oD] (h6 : ((range 8).filter o6).card ≤ 3) (hU : ((range 8).filter oU).card ≤ 2)
    (hD : ((range 8).filter oD).card ≤ 2) :
    ∑ b ∈ range 8, (if o6 b then (5 / 4 : ℚ) else 1) * (if oU b then (5 / 3 : ℚ) else 25 / 18) *
      (if oD b then (5 / 3 : ℚ) else 25 / 18) ≤ 24625 / 1296 := by
  set I6 : ℕ → ℚ := fun b => if o6 b then 1 else 0
  set IU : ℕ → ℚ := fun b => if oU b then 1 else 0
  set ID : ℕ → ℚ := fun b => if oD b then 1 else 0
  have e : ∀ b, (if o6 b then (5 / 4 : ℚ) else 1) * (if oU b then (5 / 3 : ℚ) else 25 / 18) *
      (if oD b then (5 / 3 : ℚ) else 25 / 18) = 625 / 324 + 625 / 1296 * I6 b + 125 / 324 * IU b +
        125 / 324 * ID b + 125 / 1296 * (I6 b * IU b) + 125 / 1296 * (I6 b * ID b) +
          25 / 324 * (IU b * ID b) + 25 / 1296 * (I6 b * (IU b * ID b)) := by
    intro b; simp only [I6, IU, ID]; split_ifs <;> norm_num
  have hI : ∀ (o : ℕ → Prop) [DecidablePred o], ∑ b ∈ range 8, (if o b then (1 : ℚ) else 0) =
      ((range 8).filter o).card := by
    intro o _; rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
  have s6 : ∑ b ∈ range 8, I6 b ≤ 3 := by rw [hI o6]; exact_mod_cast h6
  have sU : ∑ b ∈ range 8, IU b ≤ 2 := by rw [hI oU]; exact_mod_cast hU
  have sD : ∑ b ∈ range 8, ID b ≤ 2 := by rw [hI oD]; exact_mod_cast hD
  have b01 : ∀ (I : ℕ → ℚ), (∀ b, I b = 0 ∨ I b = 1) → ∀ b, 0 ≤ I b ∧ I b ≤ 1 := by
    intro I h b; rcases h b with h | h <;> rw [h] <;> norm_num
  have i6 := b01 I6 (fun b => by simp only [I6]; split_ifs <;> simp)
  have iU := b01 IU (fun b => by simp only [IU]; split_ifs <;> simp)
  have iD := b01 ID (fun b => by simp only [ID]; split_ifs <;> simp)
  have p1 : ∑ b ∈ range 8, I6 b * IU b ≤ 2 := le_trans (sum_le_sum fun b _ =>
    mul_le_of_le_one_left (iU b).1 (i6 b).2) sU
  have p2 : ∑ b ∈ range 8, I6 b * ID b ≤ 2 := le_trans (sum_le_sum fun b _ =>
    mul_le_of_le_one_left (iD b).1 (i6 b).2) sD
  have p3 : ∑ b ∈ range 8, IU b * ID b ≤ 2 := le_trans (sum_le_sum fun b _ =>
    mul_le_of_le_one_left (iD b).1 (iU b).2) sD
  have p4 : ∑ b ∈ range 8, I6 b * (IU b * ID b) ≤ 2 := le_trans (sum_le_sum fun b _ =>
    mul_le_of_le_one_left (mul_nonneg (iU b).1 (iD b).1) (i6 b).2) p3
  rw [sum_congr rfl fun b _ => e b]
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  push_cast
  linarith


/-- Labels unavailable at `y₆`. -/
def o6e (v : Fin m) (g : Cell c m → ℕ) (b : ℕ) : Prop :=
  if h : 2 ≤ c then b ∉ (slab c m 8 P A N).avail (boxB c v) g (y₆ h v) else False

/-- Labels unavailable at the future cell of the upper domino. -/
def oUe (hc : 1 ≤ c) (v : Fin m) (g : Cell c m → ℕ) (b : ℕ) : Prop :=
  if h : 1 ≤ v.val then b ∉ (slab c m 8 P A N).avail (boxB c v) g (yU₂ hc h) else False

/-- Labels unavailable at the future cell of the lower domino. -/
def oDe (hc : 1 ≤ c) (v : Fin m) (g : Cell c m → ℕ) (b : ℕ) : Prop :=
  if h : v.val + 1 < m then b ∉ (slab c m 8 P A N).avail (boxB c v) g (yD₂ hc h) else False

/-- Few labels are unavailable at a future cell of the box. -/
theorem card_unavail_le8 (hK : KeyInj 8 A N) {v : Fin m} {g : Cell c m → ℕ}
    (hg : (slab c m 8 P A N).Valid g) {y : Cell c m} (hy : inB v y) (hy2 : 2 ≤ y.1.val) {r : ℕ}
    (hr : ((slab c m 8 P A N).nbrsOut y (boxB c v)).card ≤ r) :
    ((range 8).filter (fun b => b ∉ (slab c m 8 P A N).avail (boxB c v) g y)).card ≤ r := by
  have hav := card_avail_fut_ge hK hg hy hy2
  have hsub : (slab c m 8 P A N).avail (boxB c v) g y ⊆ range 8 := by
    intro a ha; have := ((slab c m 8 P A N).mem_avail.mp ha).1; rwa [slab_D_fut hy2] at this
  have e : (range 8).filter (fun b => b ∉ (slab c m 8 P A N).avail (boxB c v) g y) =
      range 8 \ (slab c m 8 P A N).avail (boxB c v) g y := by
    ext b; simp [mem_sdiff]
  rw [e, card_sdiff_of_subset hsub, card_range]
  omega

/-- The `y₁` factor at `k = 8`. -/
theorem y1_eight (hK : KeyInj 8 A N) (v : Fin m) {a₀ : ℕ} (hPv : 7 ≤ (P v).card ∨ a₀ ∉ P v)
    {g : Cell c m → ℕ} (hg : (slab c m 8 P A N).Valid g) :
    4 * ((slab c m 8 P A N).avail (boxB c v) g (y₁ v)).card ≤
      5 * (((slab c m 8 P A N).avail (boxB c v) g (y₁ v)).erase a₀).card := by
  have hM := slab_match (c := c) (P := P) hK
  have hI : (slab c m 8 P A N : CSP (Cell c m)).Irrefl := slab_irrefl
  by_cases hm : a₀ ∈ (slab c m 8 P A N).avail (boxB c v) g (y₁ v)
  · have hP : a₀ ∈ P v := by
      have := ((slab c m 8 P A N).mem_avail.mp hm).1; rwa [slab_D_zero rfl] at this
    have hPc : 7 ≤ (P v).card := hPv.resolve_right (not_not.mpr hP)
    have hav := (slab c m 8 P A N).card_avail_ge hM hI (mem_boxB.mpr (y₁_inY (c := c) v).1)
      (fun x _ => hg.1 x)
    rw [slab_D_zero rfl] at hav
    change (P v).card - _ ≤ _ at hav
    have hn := nbrsOut_y₁ (c := c) (k := 8) (P := P) (A := A) (N := N) v
    rw [card_erase_of_mem hm]
    omega
  · rw [erase_eq_of_notMem hm]; omega

/-- The `y₆` factor at `k = 8`. -/
theorem y6_eight (hK : KeyInj 8 A N) (v : Fin m) {x₀ : ℕ} {g : Cell c m → ℕ}
    (hg : (slab c m 8 P A N).Valid g) (b : ℕ) :
    ((opt6b c 8 P A N v g b).card : ℚ) ≤
      (if o6e (P := P) (A := A) (N := N) v g b then (5 / 4 : ℚ) else 1) *
        (opt6' c 8 P A N v x₀ g).card := by
  by_cases h : 2 ≤ c
  · have ho : o6e (P := P) (A := A) (N := N) v g b ↔
        b ∉ (slab c m 8 P A N).avail (boxB c v) g (y₆ h v) := by simp [o6e, h]
    simp only [opt6b, opt6', dite_eq_left h, card_map]
    have hav := card_avail_fut_ge hK hg (y₆_inY h v).1 (show 2 ≤ (y₆ h v).1.val by
      show 2 ≤ 3; omega)
    have hn := nbrsOut_y₆ (k := 8) (P := P) (A := A) (N := N) h v
    have hlow := pred_card_le_card_erase (s := (slab c m 8 P A N).avail (boxB c v) g (y₆ h v))
      (a := x₀)
    by_cases hb : b ∈ (slab c m 8 P A N).avail (boxB c v) g (y₆ h v)
    · rw [ite_eq_right (by rw [ho]; exact not_not.mpr hb), one_mul, card_erase_of_mem hb]
      exact_mod_cast hlow
    · rw [ite_eq_left (by rw [ho]; exact hb), erase_eq_of_notMem hb]
      have h3 : 4 * ((slab c m 8 P A N).avail (boxB c v) g (y₆ h v)).card ≤
          5 * (((slab c m 8 P A N).avail (boxB c v) g (y₆ h v)).erase x₀).card := by omega
      have := (Nat.cast_le (α := ℚ)).mpr h3
      push_cast at this
      linarith
  · simp only [opt6b, opt6', o6e, dite_eq_right h, card_singleton, Nat.cast_one]; norm_num

/-- A domino factor at `k = 8`. -/
theorem dom_eight (hK : KeyInj 8 A N) {v : Fin m} {g : Cell c m → ℕ} {y y' : Cell c m} {a₀ x₀ : ℕ}
    (h2 : 6 ≤ ((slab c m 8 P A N).avail (boxB c v) g y).card)
    (h3 : 6 ≤ ((slab c m 8 P A N).avail (boxB c v) g y').card) (b : ℕ) :
    (((dom c 8 P A N (boxB c v) g y y').filter (fun pq => pq.2 ≠ b)).card : ℚ) ≤
      (if b ∉ (slab c m 8 P A N).avail (boxB c v) g y' then (5 / 3 : ℚ) else 25 / 18) *
        ((dom c 8 P A N (boxB c v) g y y').filter (fun pq => pq.1 ≠ a₀ ∧ pq.2 ≠ x₀)).card := by
  have hτ := card_dom_ge (c := c) (P := P) (A := A) (N := N) (U := boxB c v) (g := g)
    (y := y) (y' := y') hK
  have hs := card_dom_filter_ge (c := c) (k := 8) (P := P) (A := A) (N := N)
    (U := boxB c v) (g := g) (y := y) (y' := y') a₀ x₀
  have hle : ((dom c 8 P A N (boxB c v) g y y').filter (fun pq => pq.2 ≠ b)).card ≤
      (dom c 8 P A N (boxB c v) g y y').card := card_le_card (filter_subset _ _)
  by_cases hb : b ∈ (slab c m 8 P A N).avail (boxB c v) g y'
  · rw [ite_eq_right (not_not.mpr hb)]
    have hge := card_dom_eq_ge hK hb (y := y)
    have := dom_in_arith8 (u := ((dom c 8 P A N (boxB c v) g y y').filter
      (fun pq => pq.2 ≠ b)).card) h2 h3 hτ (by omega) hs
    have := (Nat.cast_le (α := ℚ)).mpr this
    push_cast at this
    linarith
  · rw [ite_eq_left hb]
    have := dom_out_arith8 (u := ((dom c 8 P A N (boxB c v) g y y').filter
      (fun pq => pq.2 ≠ b)).card) h2 h3 hτ hle hs
    have := (Nat.cast_le (α := ℚ)).mpr this
    push_cast at this
    linarith

theorem dom_avail_U8 (hK : KeyInj 8 A N) (hA : ∀ v, (A v).card = 8) (hc : 1 ≤ c) {v : Fin m}
    (h : 1 ≤ v.val) {g : Cell c m → ℕ} (hg : (slab c m 8 P A N).Valid g) :
    6 ≤ ((slab c m 8 P A N).avail (boxB c v) g (yU₁ h)).card ∧
      6 ≤ ((slab c m 8 P A N).avail (boxB c v) g (yU₂ hc h)).card := by
  have hM := slab_match (c := c) (P := P) hK
  have hI : (slab c m 8 P A N : CSP (Cell c m)).Irrefl := slab_irrefl
  constructor
  · have hav := (slab c m 8 P A N).card_avail_ge hM hI (mem_boxB.mpr (yU₁_inY (c := c) h).1)
      (fun x _ => hg.1 x)
    rw [slab_D_one (show (yU₁ (c := c) h).1.val = 1 from Fin.val_one _), hA] at hav
    have hn := nbrsOut_yU₁ (c := c) (k := 8) (P := P) (A := A) (N := N) h
    omega
  · have hav := card_avail_fut_ge hK hg (yU₂_inY hc h).1 (show 2 ≤ (yU₂ hc h).1.val from le_rfl)
    have hn := nbrsOut_yU₂ (k := 8) (P := P) (A := A) (N := N) hc h
    omega

theorem dom_avail_D8 (hK : KeyInj 8 A N) (hA : ∀ v, (A v).card = 8) (hc : 1 ≤ c) {v : Fin m}
    (h : v.val + 1 < m) {g : Cell c m → ℕ} (hg : (slab c m 8 P A N).Valid g) :
    6 ≤ ((slab c m 8 P A N).avail (boxB c v) g (yD₁ h)).card ∧
      6 ≤ ((slab c m 8 P A N).avail (boxB c v) g (yD₂ hc h)).card := by
  have hM := slab_match (c := c) (P := P) hK
  have hI : (slab c m 8 P A N : CSP (Cell c m)).Irrefl := slab_irrefl
  constructor
  · have hav := (slab c m 8 P A N).card_avail_ge hM hI (mem_boxB.mpr (yD₁_inY (c := c) h).1)
      (fun x _ => hg.1 x)
    rw [slab_D_one (show (yD₁ (c := c) h).1.val = 1 from Fin.val_one _), hA] at hav
    have hn := nbrsOut_yD₁ (c := c) (k := 8) (P := P) (A := A) (N := N) h
    omega
  · have hav := card_avail_fut_ge hK hg (yD₂_inY hc h).1 (show 2 ≤ (yD₂ hc h).1.val from le_rfl)
    have hn := nbrsOut_yD₂ (k := 8) (P := P) (A := A) (N := N) hc h
    omega

theorem U_eight (hK : KeyInj 8 A N) (hA : ∀ v, (A v).card = 8) (hc : 1 ≤ c) (v : Fin m)
    {a₀ x₀ : ℕ} {g : Cell c m → ℕ} (hg : (slab c m 8 P A N).Valid g) (b : ℕ) :
    ((optUb c 8 P A N hc v g b).card : ℚ) ≤
      (if oUe (P := P) (A := A) (N := N) hc v g b then (5 / 3 : ℚ) else 25 / 18) *
        (optU' c 8 P A N hc v a₀ x₀ g).card := by
  by_cases h : 1 ≤ v.val
  · have ho : oUe (P := P) (A := A) (N := N) hc v g b ↔
        b ∉ (slab c m 8 P A N).avail (boxB c v) g (yU₂ hc h) := by simp [oUe, h]
    simp only [optUb, optU', dite_eq_left h, card_map]
    obtain ⟨h2, h3⟩ := dom_avail_U8 hK hA hc h hg
    have := dom_eight (a₀ := a₀) (x₀ := x₀) hK h2 h3 b
    by_cases hb : oUe (P := P) (A := A) (N := N) hc v g b
    · rw [ite_eq_left hb]; rw [ite_eq_left (ho.mp hb)] at this; exact this
    · rw [ite_eq_right hb]; rw [ite_eq_right (fun h' => hb (ho.mpr h'))] at this; exact this
  · simp only [optUb, optU', oUe, dite_eq_right h, card_singleton, Nat.cast_one]; norm_num

theorem D_eight (hK : KeyInj 8 A N) (hA : ∀ v, (A v).card = 8) (hc : 1 ≤ c) (v : Fin m)
    {a₀ x₀ : ℕ} {g : Cell c m → ℕ} (hg : (slab c m 8 P A N).Valid g) (b : ℕ) :
    ((optDb c 8 P A N hc v g b).card : ℚ) ≤
      (if oDe (P := P) (A := A) (N := N) hc v g b then (5 / 3 : ℚ) else 25 / 18) *
        (optD' c 8 P A N hc v a₀ x₀ g).card := by
  by_cases h : v.val + 1 < m
  · have ho : oDe (P := P) (A := A) (N := N) hc v g b ↔
        b ∉ (slab c m 8 P A N).avail (boxB c v) g (yD₂ hc h) := by simp [oDe, h]
    simp only [optDb, optD', dite_eq_left h, card_map]
    obtain ⟨h2, h3⟩ := dom_avail_D8 hK hA hc h hg
    have := dom_eight (a₀ := a₀) (x₀ := x₀) hK h2 h3 b
    by_cases hb : oDe (P := P) (A := A) (N := N) hc v g b
    · rw [ite_eq_left hb]; rw [ite_eq_left (ho.mp hb)] at this; exact this
    · rw [ite_eq_right hb]; rw [ite_eq_right (fun h' => hb (ho.mpr h'))] at this; exact this
  · simp only [optDb, optD', oDe, dite_eq_right h, card_singleton, Nat.cast_one]; norm_num

/-- **The refined box inequality on one fibre** (`k = 8`). -/
theorem box_fibre_eight (hK : KeyInj 8 A N) (hA : ∀ v, (A v).card = 8) (hc : 1 ≤ c)
    (v : Fin m) {a₀ x₀ : ℕ} (ha : a₀ ∈ A v) (hx : x₀ < 8) (hN : 8 ≤ N v a₀)
    (hPv : 7 ≤ (P v).card ∨ a₀ ∉ P v) {g : Cell c m → ℕ}
    (hg : (slab c m 8 P A N).Valid g) :
    (((slab c m 8 P A N).cls (boxB c v) g).card : ℚ) * 5184 ≤
      ((((slab c m 8 P A N).cls (boxB c v) g).filter (Hit hc v a₀ x₀)).card : ℚ) * 960375 := by
  set C := slab c m 8 P A N
  have h₁ := y1_eight (P := P) hK v hPv hg
  have hsum₁ : ∑ a ∈ A v, ((C.avail (boxB c v) g (y₁ v)).erase a).card ≤
      ((C.avail (boxB c v) g (y₁ v)).erase a₀).card + 7 * (C.avail (boxB c v) g (y₁ v)).card := by
    rw [← add_sum_erase _ _ ha]
    refine Nat.add_le_add_left ?_ _
    calc ∑ a ∈ (A v).erase a₀, ((C.avail (boxB c v) g (y₁ v)).erase a).card
        ≤ ∑ _a ∈ (A v).erase a₀, (C.avail (boxB c v) g (y₁ v)).card :=
          sum_le_sum fun a _ => card_erase_le
      _ = 7 * (C.avail (boxB c v) g (y₁ v)).card := by
          rw [sum_const, card_erase_of_mem ha, hA, smul_eq_mul]
  set s₁ := ((C.avail (boxB c v) g (y₁ v)).erase a₀).card
  set s₆ := (opt6' c 8 P A N v x₀ g).card
  set sU := (optU' c 8 P A N hc v a₀ x₀ g).card
  set sD := (optD' c 8 P A N hc v a₀ x₀ g).card
  have h₆ := y6_eight (P := P) hK v (x₀ := x₀) hg
  have hU := U_eight (P := P) hK hA hc v (a₀ := a₀) (x₀ := x₀) hg
  have hD := D_eight (P := P) hK hA hc v (a₀ := a₀) (x₀ := x₀) hg
  -- outsider counts
  have c6 : ((range 8).filter (o6e (P := P) (A := A) (N := N) v g)).card ≤ 3 := by
    by_cases h : 2 ≤ c
    · have e : (range 8).filter (o6e (P := P) (A := A) (N := N) v g) =
          (range 8).filter (fun b => b ∉ C.avail (boxB c v) g (y₆ h v)) := by
        ext b; simp only [mem_filter, o6e, dite_eq_left h]; rfl
      rw [e]
      exact card_unavail_le8 hK hg (y₆_inY h v).1 (show 2 ≤ (y₆ h v).1.val by show 2 ≤ 3; omega)
        (nbrsOut_y₆ h v)
    · have e : (range 8).filter (o6e (P := P) (A := A) (N := N) v g) = ∅ := by
        ext b; simp [o6e, h]
      rw [e]; simp
  have cU : ((range 8).filter (oUe (P := P) (A := A) (N := N) hc v g)).card ≤ 2 := by
    by_cases h : 1 ≤ v.val
    · have e : (range 8).filter (oUe (P := P) (A := A) (N := N) hc v g) =
          (range 8).filter (fun b => b ∉ C.avail (boxB c v) g (yU₂ hc h)) := by
        ext b; simp only [mem_filter, oUe, dite_eq_left h]; rfl
      rw [e]
      exact card_unavail_le8 hK hg (yU₂_inY hc h).1 le_rfl (nbrsOut_yU₂ hc h)
    · have e : (range 8).filter (oUe (P := P) (A := A) (N := N) hc v g) = ∅ := by
        ext b; simp [oUe, h]
      rw [e]; simp
  have cD : ((range 8).filter (oDe (P := P) (A := A) (N := N) hc v g)).card ≤ 2 := by
    by_cases h : v.val + 1 < m
    · have e : (range 8).filter (oDe (P := P) (A := A) (N := N) hc v g) =
          (range 8).filter (fun b => b ∉ C.avail (boxB c v) g (yD₂ hc h)) := by
        ext b; simp only [mem_filter, oDe, dite_eq_left h]; rfl
      rw [e]
      exact card_unavail_le8 hK hg (yD₂_inY hc h).1 le_rfl (nbrsOut_yD₂ hc h)
    · have e : (range 8).filter (oDe (P := P) (A := A) (N := N) hc v g) = ∅ := by
        ext b; simp [oDe, h]
      rw [e]; simp
  have hnest := nested_sum8 _ _ _ c6 cU cD
  -- assemble
  have hup := card_cls_le_sum (k := 8) (P := P) (A := A) (N := N) hc v g
  have hlo := card_hit_ge (P := P) hc v hg ha hx hN
  have hs6 : (0 : ℚ) ≤ s₆ := by positivity
  have hsU : (0 : ℚ) ≤ sU := by positivity
  have hsD : (0 : ℚ) ≤ sD := by positivity
  have hb : ∀ b, ((opt6b c 8 P A N v g b).card : ℚ) * (optUb c 8 P A N hc v g b).card *
      (optDb c 8 P A N hc v g b).card ≤ ((if o6e (P := P) (A := A) (N := N) v g b then (5 / 4 : ℚ)
        else 1) * (if oUe (P := P) (A := A) (N := N) hc v g b then (5 / 3 : ℚ) else 25 / 18) *
        (if oDe (P := P) (A := A) (N := N) hc v g b then (5 / 3 : ℚ) else 25 / 18)) * (s₆ * sU * sD) := by
    intro b
    have e1 := h₆ b
    have e2 := hU b
    have e3 := hD b
    calc ((opt6b c 8 P A N v g b).card : ℚ) * (optUb c 8 P A N hc v g b).card *
          (optDb c 8 P A N hc v g b).card
        ≤ ((if o6e (P := P) (A := A) (N := N) v g b then (5 / 4 : ℚ) else 1) * s₆) *
            ((if oUe (P := P) (A := A) (N := N) hc v g b then (5 / 3 : ℚ) else 25 / 18) * sU) *
              ((if oDe (P := P) (A := A) (N := N) hc v g b then (5 / 3 : ℚ) else 25 / 18) * sD) := by
          gcongr
      _ = _ := by ring
  have hsumb : (∑ b ∈ range 8, ((opt6b c 8 P A N v g b).card : ℚ) * (optUb c 8 P A N hc v g b).card *
      (optDb c 8 P A N hc v g b).card) ≤ 24625 / 1296 * (s₆ * sU * sD) := by
    calc _ ≤ ∑ b ∈ range 8, ((if o6e (P := P) (A := A) (N := N) v g b then (5 / 4 : ℚ) else 1) *
          (if oUe (P := P) (A := A) (N := N) hc v g b then (5 / 3 : ℚ) else 25 / 18) *
          (if oDe (P := P) (A := A) (N := N) hc v g b then (5 / 3 : ℚ) else 25 / 18)) *
            (s₆ * sU * sD) := sum_le_sum fun b _ => hb b
      _ = (∑ b ∈ range 8, (if o6e (P := P) (A := A) (N := N) v g b then (5 / 4 : ℚ) else 1) *
          (if oUe (P := P) (A := A) (N := N) hc v g b then (5 / 3 : ℚ) else 25 / 18) *
          (if oDe (P := P) (A := A) (N := N) hc v g b then (5 / 3 : ℚ) else 25 / 18)) *
            (s₆ * sU * sD) := by rw [sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hnest (by positivity)
  have hcls : (((slab c m 8 P A N).cls (boxB c v) g).card : ℚ) ≤
      (∑ a ∈ A v, (((C.avail (boxB c v) g (y₁ v)).erase a).card : ℚ)) *
        ∑ b ∈ range 8, ((opt6b c 8 P A N v g b).card : ℚ) * (optUb c 8 P A N hc v g b).card *
          (optDb c 8 P A N hc v g b).card := by
    rw [sum_mul_sum]
    have := (Nat.cast_le (α := ℚ)).mpr hup
    push_cast at this
    refine le_trans this (le_of_eq (sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring))
  have ha1 : (∑ a ∈ A v, (((C.avail (boxB c v) g (y₁ v)).erase a).card : ℚ)) ≤ 39 / 4 * s₁ := by
    have := (Nat.cast_le (α := ℚ)).mpr hsum₁
    have h1q := (Nat.cast_le (α := ℚ)).mpr h₁
    push_cast at this h1q
    linarith
  have hlo' : (s₁ : ℚ) * s₆ * sU * sD ≤
      ((((slab c m 8 P A N).cls (boxB c v) g).filter (Hit hc v a₀ x₀)).card : ℚ) := by
    exact_mod_cast hlo
  have hs1 : (0 : ℚ) ≤ s₁ := by positivity
  calc (((slab c m 8 P A N).cls (boxB c v) g).card : ℚ) * 5184
      ≤ (39 / 4 * s₁) * (24625 / 1296 * (s₆ * sU * sD)) * 5184 := by
        have := mul_le_mul ha1 hsumb (sum_nonneg fun b _ => by positivity) (by positivity)
        nlinarith
    _ = (s₁ * s₆ * sU * sD) * 960375 := by ring
    _ ≤ _ := by nlinarith

/-- **The refined box bound** (`k = 8`). -/
theorem box_bound_eight (hK : KeyInj 8 A N) (hA : ∀ v, (A v).card = 8) (hc : 1 ≤ c)
    (v : Fin m) {a₀ x₀ : ℕ} (ha : a₀ ∈ A v) (hx : x₀ < 8) (hN : 8 ≤ N v a₀)
    (hPv : 7 ≤ (P v).card ∨ a₀ ∉ P v) :
    (slab c m 8 P A N).Ω.card * 5184 ≤
      ((slab c m 8 P A N).Ω.filter (Hit hc v a₀ x₀)).card * 960375 :=
  (slab c m 8 P A N).fibre_sum_ge (boxB c v) _ _ _ fun _ hg => by
    have := box_fibre_eight hK hA hc v ha hx hN hPv ((CSP.mem_Ω _).mp hg)
    exact_mod_cast this

end Eight

end GridGen.Gauge
