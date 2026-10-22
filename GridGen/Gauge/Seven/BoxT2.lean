/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Box
import GridGen.Gauge.Bad

/-!
# The 4-cycle against the star: `θ₂ ≤ 13/100` at `k = 7`

In row `r ≥ 1` the colour `a₀` is unpaired and `h` is the hole label. The 4-cycle event (`Event` on
the vertical path `(2, r), (2, r - 1)` with phase `h`) is compared with the hit event
`(1, r) = a₀, (2, r) = h` (`absorb_two`):
`100 · #Event ≤ 13 · #Hit`. The proved constant is `512/3969 ≈ 0.1290`
(`ai_research_notes/GRID_K7_BOX_SPEC_2026-10-22.md`, Lean report).

**The box `T`** (`inT`): the core `z₁ = (1, r)`, `z₂ = (2, r)`, `p = (1, r - 1)`, `q = (2, r - 1)`,
and the hanging cells `l₁ = (0, r)`, `l₂ = (0, r - 1)` (a domino on `z₁, p`), `u = (1, r + 1)` (on
`z₁`), `w = (3, r - 1)` and `d = (2, r - 2)` (both on `q`). The seam cell `(1, r - 2)` is left
outside. `u`, `w`, `d` may be missing (last row, `c = 1`, `r = 1`); they then count `1`.

**On a fibre.**
* `#Event ≤ |U \ f| · T(f) · ω(t)`, where `f` is the colour of row `r` keyed `t`, `T(a)` counts the
  domino pairs avoiding `a`, and `ω(q) = |W \ q| · |D \ q|` (`card_event_le`).
* `#Hit ≥ |U \ a₀| · ∑_p ∑_q L(p) · ω(q)` over `p ∈ avail(p) \ a₀` and labels `q ≠ h` not keyed by
  `p`, where `L(p)` counts the domino pairs avoiding `a₀` and `p` (`card_hit_ge_T`).

**The ratio lemmas.**
* `u`: `3 |U \ f| ≤ 4 |U \ a₀|`, because `|U| ≥ 4`.
* The domino: `3 T(f) ≤ 4 T(a₀)`, because `|S₁| ≥ 5` when `a₀ ∈ S₁` (`hP`).
* The pairing: `L(p) = T(a₀) − ν_p`, with `4 ν_p ≤ T(a₀)` (`|S₂| ≥ 5` when `p ∈ S₂`) and
  `∑ ν_p ≤ T(a₀)`.
* Five values of `p` with distinct keys:
  `∑ (T − ν_p) Ψ_p ≥ T (13 Ω + 3 lo − hi) / 4` (`pairing_bound`), where `Ψ_p = Ω − ω(key p)`.
* **The label lemma** (`label_bound`): `8 (13 Ω + 3 lo − hi) ≥ 441 ω(t)`.

Together `9 #Event ≤ 16 X` and `441 X ≤ 32 #Hit` with `X = T(a₀) |U \ a₀| ω(t)`, so
`#Event/#Hit ≤ 512/3969 < 13/100` (`fibre_T`), and `CSP.fibre_sum_two` sums the fibres.

The box value itself (the maximum of the ratio over all fibres) is about `0.1264`
(`ai_research_notes/k7_scripts/theta_climb2.c`, option `dmode = 1`); the spec box with the
seam domino `(1, r - 2), (2, r - 2)` hanging has the exact value `196/1613`.
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

/-! ### Fibre sums for two events -/

theorem CSP.fibre_sum_two {X : Type*} [Fintype X] [DecidableEq X] (C : CSP X) (U : Finset X)
    (Q R : (X → ℕ) → Prop) [DecidablePred Q] [DecidablePred R] (a b : ℕ)
    (h : ∀ g ∈ C.Ω, ((C.cls U g).filter Q).card * a ≤ ((C.cls U g).filter R).card * b) :
    (C.Ω.filter Q).card * a ≤ (C.Ω.filter R).card * b := by
  classical
  set T := C.Ω.image (CSP.restr U)
  have hQ : (C.Ω.filter Q).card = ∑ ω ∈ T, ((C.Ω.filter Q).filter (fun f => CSP.restr U f = ω)).card :=
    card_eq_sum_card_fiberwise (fun f hf => mem_image_of_mem _ (mem_filter.mp hf).1)
  have hR : (C.Ω.filter R).card = ∑ ω ∈ T, ((C.Ω.filter R).filter (fun f => CSP.restr U f = ω)).card :=
    card_eq_sum_card_fiberwise (fun f hf => mem_image_of_mem _ (mem_filter.mp hf).1)
  rw [hQ, hR, sum_mul, sum_mul]
  refine sum_le_sum fun ω hω => ?_
  obtain ⟨g, hg, rfl⟩ := mem_image.mp hω
  have h1 := h g hg
  rw [CSP.cls_eq_filter] at h1
  have e : ∀ (S : (X → ℕ) → Prop) [DecidablePred S],
      (C.Ω.filter S).filter (fun f => CSP.restr U f = CSP.restr U g)
        = (C.Ω.filter (fun f => CSP.restr U f = CSP.restr U g)).filter S := by
    intro S _; ext f; simp only [mem_filter]; tauto
  rw [e Q, e R]
  convert h1 using 3

/-! ### The box -/

variable {c m : ℕ} {P A : Fin m → Finset ℕ} {M : Fin m → ℕ → ℕ}

/-- Membership in the box around rows `r - 1, r`. -/
def inT (r : Fin m) (y : Cell c m) : Prop :=
  (y.2.val = r.val ∧ y.1.val ≤ 2) ∨ (y.2.val + 1 = r.val ∧ y.1.val ≤ 3) ∨
    (y.2.val = r.val + 1 ∧ y.1.val = 1) ∨ (y.2.val + 2 = r.val ∧ y.1.val = 2)

/-- The box. -/
noncomputable def boxT (c : ℕ) (r : Fin m) : Finset (Cell c m) := univ.filter (inT r)

theorem mem_boxT {r : Fin m} {y : Cell c m} : y ∈ boxT c r ↔ inT r y := by
  unfold boxT; simp

/-- The past cell of row `r - 1`. -/
def cL2 {r : Fin m} (hr : 1 ≤ r.val) : Cell c m := (0, ⟨r.val - 1, by omega⟩)

/-- The second future cell of row `r - 1`. -/
def cW (h : 2 ≤ c) {r : Fin m} (hr : 1 ≤ r.val) : Cell c m := (⟨3, by omega⟩, ⟨r.val - 1, by omega⟩)

/-- The first future cell of row `r - 2`. -/
def cD (hc : 1 ≤ c) {r : Fin m} (h : 2 ≤ r.val) : Cell c m := (fut0 hc, ⟨r.val - 2, by omega⟩)

theorem inT_cases (hc : 1 ≤ c) {r : Fin m} (hr : 1 ≤ r.val) {y : Cell c m} (hy : inT r y) :
    y = z₁ r ∨ y = z₂ hc r ∨ y = y₁ r ∨ y = yU₁ hr ∨ y = yU₂ hc hr ∨ y = cL2 hr ∨
      (∃ h : r.val + 1 < m, y = yD₁ h) ∨ (∃ h : 2 ≤ c, y = cW h hr) ∨
        (∃ h : 2 ≤ r.val, y = cD hc h) := by
  unfold inT at hy
  have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  rcases hy with ⟨hrow, hcol⟩ | ⟨hrow, hcol⟩ | ⟨hrow, hcol⟩ | ⟨hrow, hcol⟩
  · have : y.1.val = 0 ∨ y.1.val = 1 ∨ y.1.val = 2 := by omega
    rcases this with h0 | h0 | h0
    · right; right; left; exact cell_eq (by simp [y₁, h0]) hrow
    · left; exact cell_eq (by simp [z₁, h0]) hrow
    · right; left; exact cell_eq (by simp [z₂, fut0, h0]) hrow
  · have : y.1.val = 0 ∨ y.1.val = 1 ∨ y.1.val = 2 ∨ y.1.val = 3 := by omega
    rcases this with h0 | h0 | h0 | h0
    · right; right; right; right; right; left
      exact cell_eq (by simp [cL2, h0]) (by simp [cL2]; omega)
    · right; right; right; left; exact cell_eq (by simp [yU₁, h0]) (by simp [yU₁]; omega)
    · right; right; right; right; left
      exact cell_eq (by simp [yU₂, fut0, h0]) (by simp [yU₂]; omega)
    · right; right; right; right; right; right; right; left
      have h2 : 2 ≤ c := by have := y.1.isLt; omega
      exact ⟨h2, cell_eq (by simp [cW, h0]) (by simp [cW]; omega)⟩
  · right; right; right; right; right; right; left
    have h2 : r.val + 1 < m := by have := y.2.isLt; omega
    exact ⟨h2, cell_eq (by simp [yD₁, hcol]) (by simp [yD₁]; omega)⟩
  · right; right; right; right; right; right; right; right
    have h2 : 2 ≤ r.val := by omega
    exact ⟨h2, cell_eq (by simp [cD, fut0, hcol]) (by simp [cD]; omega)⟩

theorem z₁_inT (r : Fin m) : inT r (z₁ (c := c) r) := by
  have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  unfold inT z₁; dsimp only; rw [h1]; omega

theorem z₂_inT (hc : 1 ≤ c) (r : Fin m) : inT r (z₂ hc r) := by
  unfold inT z₂ fut0; dsimp only; omega

theorem y₁_inT (r : Fin m) : inT r (y₁ (c := c) r) := by
  unfold inT y₁; simp

theorem yU₁_inT {r : Fin m} (hr : 1 ≤ r.val) : inT r (yU₁ (c := c) hr) := by
  have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  unfold inT yU₁; dsimp only; rw [h1]; omega

theorem yU₂_inT (hc : 1 ≤ c) {r : Fin m} (hr : 1 ≤ r.val) : inT r (yU₂ hc hr) := by
  unfold inT yU₂ fut0; dsimp only; omega

theorem cL2_inT {r : Fin m} (hr : 1 ≤ r.val) : inT r (cL2 (c := c) hr) := by
  have e1 : (cL2 (c := c) (m := m) hr).1.val = 0 := rfl
  have e2 : (cL2 (c := c) hr).2.val = r.val - 1 := rfl
  unfold inT; rw [e1, e2]; omega

theorem yD₁_inT {r : Fin m} (h : r.val + 1 < m) : inT r (yD₁ (c := c) h) := by
  have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  unfold inT yD₁; dsimp only; rw [h1]; omega

theorem cW_inT (h : 2 ≤ c) {r : Fin m} (hr : 1 ≤ r.val) : inT r (cW h hr) := by
  have e1 : (cW (c := c) (m := m) h hr).1.val = 3 := rfl
  have e2 : (cW (c := c) h hr).2.val = r.val - 1 := rfl
  unfold inT; rw [e1, e2]; omega

theorem cD_inT (hc : 1 ≤ c) {r : Fin m} (h : 2 ≤ r.val) : inT r (cD hc h) := by
  have e1 : (cD (m := m) hc h).1.val = 2 := rfl
  have e2 : (cD (m := m) hc h).2.val = r.val - 2 := rfl
  unfold inT; rw [e1, e2]; omega

/-! ### Neighbours off the box -/

section Nbrs

variable {k : ℕ}

theorem nbrsOut_T_y₁ (r : Fin m) :
    ((slab c m k P A M).nbrsOut (y₁ r) (boxT c r)).card ≤ 1 := by
  refine card_le_of_coords _ [(0, r.val + 1)] fun w hw => ?_
  rw [CSP.mem_nbrsOut, mem_boxT] at hw
  have hc := adj_coords hw.1
  have hB := hw.2
  have hy1 : (y₁ (c := c) r).1.val = 0 := rfl
  have hy2 : (y₁ (c := c) r).2.val = r.val := rfl
  rw [hy1, hy2] at hc
  unfold inT at hB
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  omega

theorem nbrsOut_T_cL2 {r : Fin m} (hr : 1 ≤ r.val) :
    ((slab c m k P A M).nbrsOut (cL2 hr) (boxT c r)).card ≤ 1 := by
  refine card_le_of_coords _ [(0, r.val - 2)] fun w hw => ?_
  rw [CSP.mem_nbrsOut, mem_boxT] at hw
  have hc := adj_coords hw.1
  have hB := hw.2
  have hy1 : (cL2 (c := c) hr).1.val = 0 := rfl
  have hy2 : (cL2 (c := c) hr).2.val = r.val - 1 := rfl
  rw [hy1, hy2] at hc
  unfold inT at hB
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  omega

theorem nbrsOut_T_yU₁ {r : Fin m} (hr : 1 ≤ r.val) :
    ((slab c m k P A M).nbrsOut (yU₁ hr) (boxT c r)).card ≤ 1 := by
  have h1v : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  refine card_le_of_coords _ [(1, r.val - 2)] fun w hw => ?_
  rw [CSP.mem_nbrsOut, mem_boxT] at hw
  have hc := adj_coords hw.1
  have hB := hw.2
  have hy1 : (yU₁ (c := c) hr).1.val = 1 := h1v
  have hy2 : (yU₁ (c := c) hr).2.val = r.val - 1 := rfl
  rw [hy1, hy2] at hc
  unfold inT at hB
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  omega

theorem nbrsOut_T_yD₁ {r : Fin m} (h : r.val + 1 < m) :
    ((slab c m k P A M).nbrsOut (yD₁ h) (boxT c r)).card ≤ 3 := by
  have h1v : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  refine card_le_of_coords _ [(0, r.val + 1), (2, r.val + 1), (1, r.val + 2)] fun w hw => ?_
  rw [CSP.mem_nbrsOut, mem_boxT] at hw
  have hc := adj_coords hw.1
  have hB := hw.2
  have hy1 : (yD₁ (c := c) h).1.val = 1 := h1v
  have hy2 : (yD₁ (c := c) h).2.val = r.val + 1 := rfl
  rw [hy1, hy2] at hc
  unfold inT at hB
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  omega

theorem nbrsOut_T_cW (h : 2 ≤ c) {r : Fin m} (hr : 1 ≤ r.val) :
    ((slab c m k P A M).nbrsOut (cW h hr) (boxT c r)).card ≤ 3 := by
  refine card_le_of_coords _ [(4, r.val - 1), (3, r.val), (3, r.val - 2)] fun w hw => ?_
  rw [CSP.mem_nbrsOut, mem_boxT] at hw
  have hc := adj_coords hw.1
  have hB := hw.2
  have hy1 : (cW (c := c) (m := m) h hr).1.val = 3 := rfl
  have hy2 : (cW (c := c) h hr).2.val = r.val - 1 := rfl
  rw [hy1, hy2] at hc
  unfold inT at hB
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  omega

theorem nbrsOut_T_cD (hc : 1 ≤ c) {r : Fin m} (h : 2 ≤ r.val) :
    ((slab c m k P A M).nbrsOut (cD hc h) (boxT c r)).card ≤ 3 := by
  refine card_le_of_coords _ [(1, r.val - 2), (3, r.val - 2), (2, r.val - 3)] fun w hw => ?_
  rw [CSP.mem_nbrsOut, mem_boxT] at hw
  have hcd := adj_coords hw.1
  have hB := hw.2
  have hy1 : (cD (m := m) hc h).1.val = 2 := rfl
  have hy2 : (cD (m := m) hc h).2.val = r.val - 2 := rfl
  rw [hy1, hy2] at hcd
  unfold inT at hB
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  omega

/-- A cell whose neighbours all lie in the box keeps its whole domain. -/
theorem avail_eq_D {U : Finset (Cell c m)} {g : Cell c m → ℕ} {x : Cell c m}
    (h : ∀ y, ((slab c m k P A M).adj x y ∨ (slab c m k P A M).adj y x) → y ∈ U) :
    (slab c m k P A M).avail U g x = (slab c m k P A M).D x := by
  ext a
  rw [CSP.mem_avail]
  exact ⟨fun h' => h'.1, fun h' => ⟨h', fun y hy => ⟨fun hxy => absurd (h y (Or.inl hxy)) hy,
    fun hyx => absurd (h y (Or.inr hyx)) hy⟩⟩⟩

theorem avail_T_z₁ (r : Fin m) (g : Cell c m → ℕ) :
    (slab c m k P A M).avail (boxT c r) g (z₁ r) = A r := by
  have hD : ∀ y, ((slab c m k P A M).adj (z₁ r) y ∨ (slab c m k P A M).adj y (z₁ r)) →
      y ∈ boxT c r := by
    intro y hy
    have hc := adj_coords hy
    have hy1 : (z₁ (c := c) r).1.val = 1 := z₁_fst r
    have hy2 : (z₁ (c := c) r).2.val = r.val := rfl
    rw [hy1, hy2] at hc
    rw [mem_boxT]; unfold inT; omega
  rw [avail_eq_D hD, slab_D_one (z₁_fst r)]; rfl

theorem avail_T_yU₂ (hc : 1 ≤ c) {r : Fin m} (hr : 1 ≤ r.val) (g : Cell c m → ℕ) :
    (slab c m k P A M).avail (boxT c r) g (yU₂ hc hr) = range k := by
  have hD : ∀ y, ((slab c m k P A M).adj (yU₂ hc hr) y ∨ (slab c m k P A M).adj y (yU₂ hc hr)) →
      y ∈ boxT c r := by
    intro y hy
    have hcd := adj_coords hy
    have hy1 : (yU₂ (m := m) hc hr).1.val = 2 := rfl
    have hy2 : (yU₂ (m := m) hc hr).2.val = r.val - 1 := rfl
    rw [hy1, hy2] at hcd
    rw [mem_boxT]; unfold inT
    have := y.1.isLt
    omega
  rw [avail_eq_D hD, slab_D_fut (show 2 ≤ (yU₂ hc hr).1.val from le_rfl)]

end Nbrs

/-! ### Arithmetic: domino pairs, the pairing bound, the label lemma -/

section Arith

/-- The pairs of a past domino: the second colour differs from the first. -/
noncomputable def dpairs (X Y : Finset ℕ) : Finset (ℕ × ℕ) :=
  (X ×ˢ Y).filter (fun pr => pr.2 ≠ pr.1)

theorem dpairs_card_add (X Y : Finset ℕ) :
    (dpairs X Y).card + (X.filter (· ∈ Y)).card = X.card * Y.card := by
  have h1 : (dpairs X Y).card = ∑ x ∈ X, (Y.erase x).card := by
    unfold dpairs
    rw [card_filter, sum_product]
    refine sum_congr rfl fun x _ => ?_
    rw [← card_filter, filter_ne']
  have h2 : (X.filter (· ∈ Y)).card = ∑ x ∈ X, if x ∈ Y then 1 else 0 := card_filter _ _
  have h3 : X.card * Y.card = ∑ _x ∈ X, Y.card := by rw [sum_const, smul_eq_mul]
  rw [h1, h2, h3, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ Y
  · rw [ite_eq_left hx]; exact card_erase_add_one hx
  · rw [ite_eq_right hx, erase_eq_of_notMem hx, add_zero]

theorem dpairs_mono {X X' Y : Finset ℕ} (h : X' ⊆ X) : (dpairs X' Y).card ≤ (dpairs X Y).card :=
  card_le_card (filter_subset_filter _ (product_subset_product_left h))

/-- **The domino ratio**: `3 T(a) ≤ 4 T(a₀)`. -/
theorem dpairs_ratio {S1 S2 : Finset ℕ} {a₀ : ℕ} (h5 : a₀ ∈ S1 → 5 ≤ S1.card) (a : ℕ) :
    3 * (dpairs (S1.erase a) S2).card ≤ 4 * (dpairs (S1.erase a₀) S2).card := by
  have hmono := dpairs_mono (Y := S2) (erase_subset a S1)
  by_cases ha : a₀ ∈ S1
  · have hS1 := h5 ha
    have hsub : dpairs S1 S2 ⊆ dpairs (S1.erase a₀) S2 ∪ ({a₀} ×ˢ S2) := by
      intro pr hpr
      unfold dpairs at hpr ⊢
      rw [mem_filter, mem_product] at hpr
      rw [mem_union, mem_filter, mem_product, mem_product, mem_erase, mem_singleton]
      by_cases e : pr.1 = a₀
      · exact Or.inr ⟨e, hpr.1.2⟩
      · exact Or.inl ⟨⟨⟨e, hpr.1.1⟩, hpr.1.2⟩, hpr.2⟩
    have hle := le_trans (card_le_card hsub) (card_union_le _ _)
    rw [card_product, card_singleton, one_mul] at hle
    have e2 := dpairs_card_add (S1.erase a₀) S2
    have f1 : ((S1.erase a₀).filter (· ∈ S2)).card ≤ S2.card :=
      card_le_card fun x hx => (mem_filter.mp hx).2
    have hX : 4 ≤ (S1.erase a₀).card := by rw [card_erase_of_mem ha]; omega
    have : 4 * S2.card ≤ (S1.erase a₀).card * S2.card := Nat.mul_le_mul_right _ hX
    omega
  · rw [erase_eq_of_notMem ha]
    omega

/-- The pairs whose second colour is `p`. -/
theorem dpairs_split (X Y : Finset ℕ) (p : ℕ) :
    ((dpairs X Y).filter (fun pr => pr.2 ≠ p)).card +
      ((dpairs X Y).filter (fun pr => pr.2 = p)).card = (dpairs X Y).card := by
  rw [add_comm]
  have := card_filter_add_card_filter_not (s := dpairs X Y) (fun pr => pr.2 = p)
  simpa only [ne_eq] using this

theorem nu_le_left (X Y : Finset ℕ) (p : ℕ) :
    ((dpairs X Y).filter (fun pr => pr.2 = p)).card ≤ X.card := by
  refine card_le_card_of_injOn (fun pr => pr.1) (fun pr hpr => ?_) (fun pr hpr pr' hpr' e => ?_)
  · rw [mem_coe, mem_filter] at hpr; unfold dpairs at hpr
    rw [mem_filter, mem_product] at hpr; exact hpr.1.1.1
  · rw [mem_coe, mem_filter] at hpr hpr'
    exact Prod.ext e (hpr.2.trans hpr'.2.symm)

theorem nu_eq_zero (X Y : Finset ℕ) {p : ℕ} (hp : p ∉ Y) :
    ((dpairs X Y).filter (fun pr => pr.2 = p)).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro pr hpr e
  unfold dpairs at hpr
  rw [mem_filter, mem_product] at hpr
  exact hp (e ▸ hpr.1.2)

theorem four_nu_le (X Y : Finset ℕ) (hY : 5 ≤ Y.card) (p : ℕ) :
    4 * ((dpairs X Y).filter (fun pr => pr.2 = p)).card ≤ (dpairs X Y).card := by
  have e := dpairs_card_add X Y
  have f : (X.filter (· ∈ Y)).card ≤ X.card := card_filter_le _ _
  have hn := nu_le_left X Y p
  have : 5 * X.card ≤ X.card * Y.card := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hY
  omega

theorem sum_nu_le (X Y : Finset ℕ) (S : Finset ℕ) :
    ∑ p ∈ S, ((dpairs X Y).filter (fun pr => pr.2 = p)).card ≤ (dpairs X Y).card := by
  rw [sum_card_fiberwise_eq_card_filter]
  exact card_filter_le _ _

/-- **The pairing bound.** Five values `p` with `4 ν_p ≤ T`, `∑ ν_p ≤ T`, `Ψ_p = Ω − ρ_p`,
`ρ_p ≤ hi` and `∑ ρ_p ≤ Ω − lo`. -/
theorem pairing_bound (S : Finset ℕ) (hS : S.card = 5) (T Ω lo hi : ℚ) (ν Ψ ρ : ℕ → ℚ)
    (hT : 0 ≤ T) (_hν0 : ∀ p ∈ S, 0 ≤ ν p) (hν : ∀ p ∈ S, 4 * ν p ≤ T)
    (hSν : ∑ p ∈ S, ν p ≤ T) (hΨ : ∀ p ∈ S, Ψ p + ρ p = Ω) (hρ : ∀ p ∈ S, ρ p ≤ hi)
    (hSρ : ∑ p ∈ S, ρ p + lo ≤ Ω) (hhi : hi ≤ Ω) :
    T * (13 * Ω + 3 * lo - hi) ≤ 4 * ∑ p ∈ S, (T - ν p) * Ψ p := by
  have hnn : 0 ≤ ∑ p ∈ S, (T / 4 - ν p) * (hi - ρ p) :=
    sum_nonneg fun p hp => mul_nonneg (by linarith [hν p hp]) (by linarith [hρ p hp])
  have e1 : ∑ p ∈ S, (T - ν p) * Ψ p =
      ∑ p ∈ S, (T * Ω - T * ρ p - Ω * ν p + ν p * ρ p) := by
    refine sum_congr rfl fun p hp => ?_
    have := hΨ p hp
    have : Ψ p = Ω - ρ p := by linarith
    rw [this]; ring
  have e2 : ∑ p ∈ S, (T / 4 - ν p) * (hi - ρ p) =
      ∑ p ∈ S, (T / 4 * hi - T / 4 * ρ p - hi * ν p + ν p * ρ p) :=
    sum_congr rfl fun p _ => by ring
  have s1 : ∑ p ∈ S, (T * Ω - T * ρ p - Ω * ν p + ν p * ρ p) =
      5 * (T * Ω) - T * ∑ p ∈ S, ρ p - Ω * ∑ p ∈ S, ν p + ∑ p ∈ S, ν p * ρ p := by
    rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib, sum_const, hS, ← mul_sum, ← mul_sum,
      nsmul_eq_mul]
    push_cast; ring
  have s2 : ∑ p ∈ S, (T / 4 * hi - T / 4 * ρ p - hi * ν p + ν p * ρ p) =
      5 * (T / 4 * hi) - T / 4 * ∑ p ∈ S, ρ p - hi * ∑ p ∈ S, ν p + ∑ p ∈ S, ν p * ρ p := by
    rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib, sum_const, hS, ← mul_sum, ← mul_sum,
      nsmul_eq_mul]
    push_cast; ring
  rw [e1, s1]
  rw [e2, s2] at hnn
  have k1 : T * ∑ p ∈ S, ρ p ≤ T * (Ω - lo) := mul_le_mul_of_nonneg_left (by linarith) hT
  have k2 : (Ω - hi) * ∑ p ∈ S, ν p ≤ (Ω - hi) * T :=
    mul_le_mul_of_nonneg_left hSν (by linarith)
  nlinarith

/-- The counts of a label configuration. -/
theorem omega_sum {h x y : ℕ} {D W : Finset ℕ} :
    ∑ q ∈ (range 7).erase h, (((x : ℤ) - if q ∈ D then 1 else 0) * ((y : ℤ) - if q ∈ W then 1 else 0)) =
      ((range 7).erase h).card * (x * y) - x * (((range 7).erase h).filter (· ∈ W)).card -
        y * (((range 7).erase h).filter (· ∈ D)).card +
          (((range 7).erase h).filter (fun q => q ∈ D ∧ q ∈ W)).card := by
  have e : ∀ q, (((x : ℤ) - if q ∈ D then 1 else 0) * ((y : ℤ) - if q ∈ W then 1 else 0)) =
      x * y - x * (if q ∈ W then 1 else 0) - y * (if q ∈ D then 1 else 0) +
        (if q ∈ D ∧ q ∈ W then 1 else 0) := by
    intro q; by_cases h1 : q ∈ D <;> by_cases h2 : q ∈ W <;> simp [h1, h2] <;> ring
  rw [sum_congr rfl fun q _ => e q]
  simp only [sum_add_distrib, sum_sub_distrib, sum_const, ← mul_sum, nsmul_eq_mul, sum_boole]
  try push_cast
  try ring

/-- **The label lemma.** -/
theorem label_bound {h t x y : ℕ} {D W : Finset ℕ} (hh7 : h < 7) (hht : t ≠ h) (ht : t < 7)
    (hD : D ⊆ range 7) (hW : W ⊆ range 7)
    (hx : (x = D.card ∧ 4 ≤ x) ∨ (D = ∅ ∧ x = 1)) (hy : (y = W.card ∧ 4 ≤ y) ∨ (W = ∅ ∧ y = 1)) :
    441 * (((x : ℤ) - if t ∈ D then 1 else 0) * ((y : ℤ) - if t ∈ W then 1 else 0)) ≤
      8 * (13 * ∑ q ∈ (range 7).erase h,
        (((x : ℤ) - if q ∈ D then 1 else 0) * ((y : ℤ) - if q ∈ W then 1 else 0)) +
          3 * ((x : ℤ) - 1) * ((y : ℤ) - 1) - (x : ℤ) * y) ∧
    (x : ℤ) * y ≤ ∑ q ∈ (range 7).erase h,
        (((x : ℤ) - if q ∈ D then 1 else 0) * ((y : ℤ) - if q ∈ W then 1 else 0)) := by
  set N := (range 7).erase h with hN
  have htN : t ∈ N := by rw [hN, mem_erase, mem_range]; exact ⟨hht, ht⟩
  have hN6 : N.card = 6 := by rw [hN, card_erase_of_mem (mem_range.mpr hh7), card_range]
  rw [omega_sum, hN6]
  set A := (N.filter (· ∈ D)).card with hA
  set B := (N.filter (· ∈ W)).card with hB
  set C := (N.filter (fun q => q ∈ D ∧ q ∈ W)).card with hC
  have hAx : A ≤ D.card := card_le_card fun q hq => (mem_filter.mp hq).2
  have hBy : B ≤ W.card := card_le_card fun q hq => (mem_filter.mp hq).2
  have hD7 : D.card ≤ 7 := by simpa using card_le_card hD
  have hW7 : W.card ≤ 7 := by simpa using card_le_card hW
  have hCA : C ≤ A := card_le_card fun q hq => by
    rw [mem_filter] at hq ⊢; exact ⟨hq.1, hq.2.1⟩
  have hCB : C ≤ B := card_le_card fun q hq => by
    rw [mem_filter] at hq ⊢; exact ⟨hq.1, hq.2.2⟩
  have hunion : (N.filter (· ∈ D) ∪ N.filter (· ∈ W)).card + C = A + B := by
    have e := card_union_add_card_inter (N.filter (· ∈ D)) (N.filter (· ∈ W))
    have e' : N.filter (· ∈ D) ∩ N.filter (· ∈ W) = N.filter (fun q => q ∈ D ∧ q ∈ W) := by
      ext q; simp only [mem_inter, mem_filter]; tauto
    rw [e'] at e
    omega
  have hsubN : N.filter (· ∈ D) ∪ N.filter (· ∈ W) ⊆ N := by
    intro q hq
    rw [mem_union, mem_filter, mem_filter] at hq
    rcases hq with hq | hq <;> exact hq.1
  have hU6 : (N.filter (· ∈ D) ∪ N.filter (· ∈ W)).card ≤ 6 := hN6 ▸ card_le_card hsubN
  have hU5 : t ∉ D → t ∉ W → (N.filter (· ∈ D) ∪ N.filter (· ∈ W)).card ≤ 5 := by
    intro h1 h2
    have : N.filter (· ∈ D) ∪ N.filter (· ∈ W) ⊆ N.erase t := by
      intro q hq
      rw [mem_erase]
      refine ⟨fun e => ?_, hsubN hq⟩
      subst e
      rw [mem_union, mem_filter, mem_filter] at hq
      rcases hq with hq | hq
      · exact h1 hq.2
      · exact h2 hq.2
    have := card_le_card this
    rw [card_erase_of_mem htN, hN6] at this
    exact this
  have htA : t ∈ D → 1 ≤ A := fun h1 => card_pos.mpr ⟨t, mem_filter.mpr ⟨htN, h1⟩⟩
  have htB : t ∈ W → 1 ≤ B := fun h2 => card_pos.mpr ⟨t, mem_filter.mpr ⟨htN, h2⟩⟩
  have htC : t ∈ D → t ∈ W → 1 ≤ C := fun h1 h2 => card_pos.mpr ⟨t, mem_filter.mpr ⟨htN, h1, h2⟩⟩
  have hA0 : D = ∅ → A = 0 := fun e => by rw [hA, e]; simp
  have hB0 : W = ∅ → B = 0 := fun e => by rw [hB, e]; simp
  have hX : (4 ≤ x ∧ x ≤ 7 ∧ A ≤ x) ∨ (x = 1 ∧ A = 0 ∧ t ∉ D) := by
    rcases hx with ⟨hxD, hx4⟩ | ⟨hD0, hx1⟩
    · exact Or.inl ⟨hx4, hxD ▸ hD7, hxD ▸ hAx⟩
    · exact Or.inr ⟨hx1, hA0 hD0, by rw [hD0]; exact notMem_empty t⟩
  have hY : (4 ≤ y ∧ y ≤ 7 ∧ B ≤ y) ∨ (y = 1 ∧ B = 0 ∧ t ∉ W) := by
    rcases hy with ⟨hyW, hy4⟩ | ⟨hW0, hy1⟩
    · exact Or.inl ⟨hy4, hyW ▸ hW7, hyW ▸ hBy⟩
    · exact Or.inr ⟨hy1, hB0 hW0, by rw [hW0]; exact notMem_empty t⟩
  have hU6' : A + B ≤ 6 + C := by omega
  have hU5' : t ∉ D → t ∉ W → A + B ≤ 5 + C := fun a b => by have := hU5 a b; omega
  clear_value A B C
  by_cases h1 : t ∈ D <;> by_cases h2 : t ∈ W <;> simp only [h1, h2, ite_true, ite_false]
  all_goals
    rcases hX with ⟨hx4, hx7, hAx'⟩ | ⟨rfl, hA0', htD⟩ <;>
    rcases hY with ⟨hy4, hy7, hBy'⟩ | ⟨rfl, hB0', htW⟩
  all_goals first | exact absurd h1 htD | exact absurd h2 htW | skip
  all_goals first | have := htA h1 | skip
  all_goals first | have := htB h2 | skip
  all_goals first | have := htC h1 h2 | skip
  all_goals first | have := hU5' h1 h2 | skip
  all_goals (try interval_cases x) <;> (try interval_cases y) <;> constructor <;> push_cast <;> omega

end Arith

/-! ### Coordinates, edges and the event -/

section Cells

variable {r : Fin m}

theorem z₁_c1 : (z₁ (c := c) r).1.val = 1 := Fin.val_one _
theorem z₁_c2 : (z₁ (c := c) r).2.val = r.val := rfl
theorem z₂_c1 (hc : 1 ≤ c) : (z₂ hc r).1.val = 2 := rfl
theorem z₂_c2 (hc : 1 ≤ c) : (z₂ hc r).2.val = r.val := rfl
theorem y₁_c1 : (y₁ (c := c) r).1.val = 0 := rfl
theorem y₁_c2 : (y₁ (c := c) r).2.val = r.val := rfl
theorem yU₁_c1 (hr : 1 ≤ r.val) : (yU₁ (c := c) hr).1.val = 1 := Fin.val_one _
theorem yU₁_c2 (hr : 1 ≤ r.val) : (yU₁ (c := c) hr).2.val = r.val - 1 := rfl
theorem yU₂_c1 (hc : 1 ≤ c) (hr : 1 ≤ r.val) : (yU₂ hc hr).1.val = 2 := rfl
theorem yU₂_c2 (hc : 1 ≤ c) (hr : 1 ≤ r.val) : (yU₂ hc hr).2.val = r.val - 1 := rfl
theorem cL2_c1 (hr : 1 ≤ r.val) : (cL2 (c := c) hr).1.val = 0 := rfl
theorem cL2_c2 (hr : 1 ≤ r.val) : (cL2 (c := c) hr).2.val = r.val - 1 := rfl
theorem yD₁_c1 (h : r.val + 1 < m) : (yD₁ (c := c) h).1.val = 1 := Fin.val_one _
theorem yD₁_c2 (h : r.val + 1 < m) : (yD₁ (c := c) h).2.val = r.val + 1 := rfl
theorem cW_c1 (h : 2 ≤ c) (hr : 1 ≤ r.val) : (cW (m := m) h hr).1.val = 3 := rfl
theorem cW_c2 (h : 2 ≤ c) (hr : 1 ≤ r.val) : (cW (m := m) h hr).2.val = r.val - 1 := rfl
theorem cD_c1 (hc : 1 ≤ c) (h : 2 ≤ r.val) : (cD (m := m) hc h).1.val = 2 := rfl
theorem cD_c2 (hc : 1 ≤ c) (h : 2 ≤ r.val) : (cD (m := m) hc h).2.val = r.val - 2 := rfl

theorem slabAdj_iff {x y : Cell c m} : slabAdj x y ↔
    (x.1.val = y.1.val ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)) ∨
      (x.2.val = y.2.val ∧ (x.1.val + 1 = y.1.val ∨ y.1.val + 1 = x.1.val)) := by
  unfold slabAdj; rw [Fin.ext_iff, Fin.ext_iff]

theorem ne_of_adj_eq {k : ℕ} {f : Cell c m → ℕ} (hf : (slab c m k P A M).Valid f)
    {x y : Cell c m} (h : slabAdj x y) (h1 : ¬ (x.1.val = 1 ∧ y.1.val = 2))
    (h2 : ¬ (x.1.val = 2 ∧ y.1.val = 1)) : f x ≠ f y := by
  have := hf.2 x y h
  rwa [slab_conf_eq h1 h2] at this

/-- **The 4-cycle event, unpacked.** -/
theorem event_T {x y h : ℕ} (hxy : x ≠ y) (hh : h = x ∨ h = y) (hc : 1 ≤ c)
    (hr : 1 ≤ r.val) {f : Cell c m → ℕ}
    (hE : Event (A := A) M x y [(fut0 hc, r), (fut0 hc, ⟨r.val - 1, by omega⟩)] h f) :
    (f (z₁ r) ∈ A r ∧ M r (f (z₁ r)) = oth x y h) ∧ f (z₂ hc r) = h ∧
      f (yU₂ hc hr) = oth x y h ∧
        (f (yU₁ hr) ∈ A ⟨r.val - 1, by omega⟩ ∧ M ⟨r.val - 1, by omega⟩ (f (yU₁ hr)) = h) := by
  have hne : ((fut0 hc, ⟨r.val - 1, by omega⟩) : Cell c m) ≠ (fut0 hc, r) := by
    intro e; have := congrArg (fun z : Cell c m => z.2.val) e; simp at this; omega
  have hrr : (⟨r.val - 1, by omega⟩ : Fin m) ≠ r := by
    intro e; have := congrArg Fin.val e; simp at this; omega
  have h1 := hE (z₁ r) (by simp [chainOf, seamOf, z₁])
  have h2 := hE (z₂ hc r) (by simp [chainOf, z₂])
  have h3 := hE (yU₂ hc hr) (by simp [chainOf, yU₂])
  have h4 := hE (yU₁ hr) (by simp [chainOf, seamOf, yU₁])
  have hl1 : lab x y h 1 = oth x y h := by unfold lab; simp
  have hl0 : lab x y h 0 = h := by unfold lab; simp
  have hf0 : (fut0 hc).val = 2 := rfl
  have hlen : ([(fut0 hc, r), (fut0 hc, ⟨r.val - 1, by omega⟩)] : List (Cell c m)).length - 1 = 1 :=
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [presc, z₁, Fin.val_one, ite_true, List.head?_cons, Option.map_some] at h1
    exact mem_filter.mp h1
  · simp only [presc, z₂, hf0, List.idxOf_cons_self] at h2
    simp only [hl0, show (2 : ℕ) ≠ 1 by omega, ite_false, mem_singleton] at h2
    exact h2
  · simp only [presc, yU₂, hf0] at h3
    rw [List.idxOf_cons_ne _ hne.symm, List.idxOf_cons_self] at h3
    simp only [hl1, show (2 : ℕ) ≠ 1 by omega, ite_false, mem_singleton] at h3
    exact h3
  · simp only [presc, yU₁, Fin.val_one, ite_true, List.head?_cons, Option.map_some,
      Option.some.injEq, hrr, ite_false, hlen, hl1, oth_oth hxy hh, mem_filter] at h4
    exact h4

end Cells

/-! ### The options of the hanging cells -/

section Opts

variable (P A M)

/-- Options at `u = (1, r + 1)` avoiding `a`. -/
noncomputable def optUT (r : Fin m) (g : Cell c m → ℕ) (a : ℕ) : Finset (Option ℕ) :=
  if h : r.val + 1 < m then
    (((slab c m 7 P A M).avail (boxT c r) g (yD₁ h)).erase a).map Function.Embedding.some
  else {none}

/-- Options at `w = (3, r - 1)` avoiding `q`. -/
noncomputable def optWT {r : Fin m} (hr : 1 ≤ r.val) (g : Cell c m → ℕ) (q : ℕ) :
    Finset (Option ℕ) :=
  if h : 2 ≤ c then
    (((slab c m 7 P A M).avail (boxT c r) g (cW h hr)).erase q).map Function.Embedding.some
  else {none}

/-- Options at `d = (2, r - 2)` avoiding `q`. -/
noncomputable def optDT (hc : 1 ≤ c) (r : Fin m) (g : Cell c m → ℕ) (q : ℕ) :
    Finset (Option ℕ) :=
  if h : 2 ≤ r.val then
    (((slab c m 7 P A M).avail (boxT c r) g (cD hc h)).erase q).map Function.Embedding.some
  else {none}

end Opts

/-- The value at `u`, if present. -/
def uVal (r : Fin m) (f : Cell c m → ℕ) : Option ℕ :=
  if h : r.val + 1 < m then some (f (yD₁ h)) else none

/-- The value at `w`, if present. -/
def wVal {r : Fin m} (hr : 1 ≤ r.val) (f : Cell c m → ℕ) : Option ℕ :=
  if h : 2 ≤ c then some (f (cW h hr)) else none

/-- The value at `d`, if present. -/
def dVal (hc : 1 ≤ c) (r : Fin m) (f : Cell c m → ℕ) : Option ℕ :=
  if h : 2 ≤ r.val then some (f (cD hc h)) else none

/-! ### The upper bound on a fibre -/

section Upper

variable {r : Fin m}

theorem adj_y₁_z₁ : slabAdj (y₁ (c := c) r) (z₁ r) := by
  rw [slabAdj_iff, y₁_c1, y₁_c2, z₁_c1, z₁_c2]; omega

theorem adj_cL2_y₁ (hr : 1 ≤ r.val) : slabAdj (cL2 (c := c) hr) (y₁ r) := by
  rw [slabAdj_iff, cL2_c1, cL2_c2, y₁_c1, y₁_c2]; omega

theorem adj_cL2_yU₁ (hr : 1 ≤ r.val) : slabAdj (cL2 (c := c) hr) (yU₁ hr) := by
  rw [slabAdj_iff, cL2_c1, cL2_c2, yU₁_c1, yU₁_c2]; omega

theorem adj_yD₁_z₁ (h : r.val + 1 < m) : slabAdj (yD₁ (c := c) h) (z₁ r) := by
  rw [slabAdj_iff, yD₁_c1, yD₁_c2, z₁_c1, z₁_c2]; omega

theorem adj_cW_yU₂ (hc : 1 ≤ c) (h : 2 ≤ c) (hr : 1 ≤ r.val) : slabAdj (cW (m := m) h hr) (yU₂ hc hr) := by
  rw [slabAdj_iff, cW_c1, cW_c2, yU₂_c1, yU₂_c2]; omega

theorem adj_cD_yU₂ (hc : 1 ≤ c) (h : 2 ≤ r.val) (hr : 1 ≤ r.val) :
    slabAdj (cD (m := m) hc h) (yU₂ hc hr) := by
  rw [slabAdj_iff, cD_c1, cD_c2, yU₂_c1, yU₂_c2]; omega

/-- **The 4-cycle event on a fibre.** -/
theorem card_event_le (hc : 1 ≤ c) (hr : 1 ≤ r.val) {x y h : ℕ} (hxy : x ≠ y)
    (hh : h = x ∨ h = y) (g : Cell c m → ℕ) :
    (((slab c m 7 P A M).cls (boxT c r) g).filter
        (Event (A := A) M x y [(fut0 hc, r), (fut0 hc, ⟨r.val - 1, by omega⟩)] h)).card ≤
      ∑ a ∈ (A r).filter (fun a => M r a = oth x y h),
        ((A ⟨r.val - 1, by omega⟩).filter (fun a => M ⟨r.val - 1, by omega⟩ a = h)).card *
          ((dpairs (((slab c m 7 P A M).avail (boxT c r) g (y₁ r)).erase a)
              ((slab c m 7 P A M).avail (boxT c r) g (cL2 hr))).card *
            ((optUT P A M r g a).card *
              ((optWT P A M hr g (oth x y h)).card * (optDT P A M hc r g (oth x y h)).card))) := by
  set C := slab c m 7 P A M
  set S1 := C.avail (boxT c r) g (y₁ r)
  set S2 := C.avail (boxT c r) g (cL2 hr)
  set t := oth x y h
  set Ft := (A r).filter (fun a => M r a = t)
  set Fe := (A ⟨r.val - 1, by omega⟩).filter (fun a => M ⟨r.val - 1, by omega⟩ a = h)
  set Tg := Ft.sigma (fun a => Fe ×ˢ (dpairs (S1.erase a) S2 ×ˢ
    (optUT P A M r g a ×ˢ (optWT P A M hr g t ×ˢ optDT P A M hc r g t))))
  have hcard : Tg.card = ∑ a ∈ Ft, Fe.card * ((dpairs (S1.erase a) S2).card *
      ((optUT P A M r g a).card * ((optWT P A M hr g t).card * (optDT P A M hc r g t).card))) := by
    simp only [Tg, card_sigma, card_product]
  rw [← hcard]
  refine card_le_card_of_injOn (fun f => (⟨f (z₁ r), (f (yU₁ hr), ((f (y₁ r), f (cL2 hr)),
    (uVal r f, (wVal hr f, dVal hc r f))))⟩ : (_ : ℕ) × (ℕ × ((ℕ × ℕ) ×
      (Option ℕ × (Option ℕ × Option ℕ)))))) ?_ ?_
  · intro f hf
    rw [mem_coe, mem_filter] at hf
    obtain ⟨hfc, hE⟩ := hf
    have hv := ((CSP.mem_cls _).mp hfc).1
    obtain ⟨⟨hz1A, hz1M⟩, hz2, hq, hpA, hpM⟩ := event_T hxy hh hc hr hE
    rw [mem_coe, mem_sigma]
    refine ⟨mem_filter.mpr ⟨hz1A, hz1M⟩, ?_⟩
    simp only [mem_product]
    refine ⟨mem_filter.mpr ⟨hpA, hpM⟩, ?_, ?_, ?_, ?_⟩
    · unfold dpairs
      rw [mem_filter, mem_product, mem_erase]
      refine ⟨⟨⟨ne_of_adj_eq hv adj_y₁_z₁ (by rw [y₁_c1]; omega) (by rw [y₁_c1]; omega),
        CSP.mem_avail_of_mem_cls _ hfc (mem_boxT.mpr (y₁_inT r))⟩,
        CSP.mem_avail_of_mem_cls _ hfc (mem_boxT.mpr (cL2_inT hr))⟩,
        ne_of_adj_eq hv (adj_cL2_y₁ hr) (by rw [cL2_c1]; omega) (by rw [cL2_c1]; omega)⟩
    · unfold optUT uVal
      split_ifs with h1
      · refine mem_map_of_mem _ (mem_erase.mpr ⟨ne_of_adj_eq hv (adj_yD₁_z₁ h1)
          (by rw [yD₁_c1, z₁_c1]; omega) (by rw [yD₁_c1]; omega),
          CSP.mem_avail_of_mem_cls _ hfc (mem_boxT.mpr (yD₁_inT h1))⟩)
      · exact mem_singleton_self _
    · unfold optWT wVal
      split_ifs with h1
      · refine mem_map_of_mem _ (mem_erase.mpr ⟨?_,
          CSP.mem_avail_of_mem_cls _ hfc (mem_boxT.mpr (cW_inT h1 hr))⟩)
        rw [show t = f (yU₂ hc hr) from hq.symm]
        exact ne_of_adj_eq hv (adj_cW_yU₂ hc h1 hr) (by rw [cW_c1]; omega)
          (by rw [cW_c1]; omega)
      · exact mem_singleton_self _
    · unfold optDT dVal
      split_ifs with h1
      · refine mem_map_of_mem _ (mem_erase.mpr ⟨?_,
          CSP.mem_avail_of_mem_cls _ hfc (mem_boxT.mpr (cD_inT hc h1))⟩)
        rw [show t = f (yU₂ hc hr) from hq.symm]
        exact ne_of_adj_eq hv (adj_cD_yU₂ hc h1 hr) (by rw [cD_c1, yU₂_c1]; omega)
          (by rw [cD_c1, yU₂_c1]; omega)
      · exact mem_singleton_self _
  · intro f hf f' hf' he
    rw [mem_coe, mem_filter] at hf hf'
    obtain ⟨-, hz2, hq, -⟩ := event_T hxy hh hc hr hf.2
    obtain ⟨-, hz2', hq', -⟩ := event_T hxy hh hc hr hf'.2
    have hc1 := (CSP.mem_cls _).mp hf.1
    have hc1' := (CSP.mem_cls _).mp hf'.1
    simp only [Sigma.mk.inj_iff] at he
    obtain ⟨e1, he2⟩ := he
    have he2' := eq_of_heq he2
    simp only [Prod.mk.injEq] at he2'
    obtain ⟨e2, ⟨e3, e4⟩, e5, e6, e7⟩ := he2'
    funext z
    by_cases hz : z ∈ boxT c r
    · rcases inT_cases hc hr (mem_boxT.mp hz) with rfl | rfl | rfl | rfl | rfl | rfl |
        ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩
      · exact e1
      · rw [hz2, hz2']
      · exact e3
      · exact e2
      · rw [hq, hq']
      · exact e4
      · simpa [uVal, h1] using e5
      · simpa [wVal, h1] using e6
      · simpa [dVal, h1] using e7
    · rw [hc1.2 z hz, hc1'.2 z hz]

end Upper

/-! ### The lower bound on a fibre -/

section Lower

variable {r : Fin m}

/-- The tuples of box values: `p`, `q`, the past domino, `u`, `w`, `d`. -/
abbrev TupT := (_ : ℕ) × (_ : ℕ) × ((ℕ × ℕ) × (Option ℕ × (Option ℕ × Option ℕ)))

/-- Fill the box: `a₀` at `z₁`, `h` at `z₂`, the tuple on the other box cells, `g` off the box. -/
def fillT (r : Fin m) (a₀ h : ℕ) (g : Cell c m → ℕ) (τ : TupT) (y : Cell c m) : ℕ :=
  if y.2.val = r.val ∧ y.1.val = 0 then τ.2.2.1.1
  else if y.2.val = r.val ∧ y.1.val = 1 then a₀
  else if y.2.val = r.val ∧ y.1.val = 2 then h
  else if y.2.val + 1 = r.val ∧ y.1.val = 0 then τ.2.2.1.2
  else if y.2.val + 1 = r.val ∧ y.1.val = 1 then τ.1
  else if y.2.val + 1 = r.val ∧ y.1.val = 2 then τ.2.1
  else if y.2.val + 1 = r.val ∧ y.1.val = 3 then τ.2.2.2.2.1.getD 0
  else if y.2.val = r.val + 1 ∧ y.1.val = 1 then τ.2.2.2.1.getD 0
  else if y.2.val + 2 = r.val ∧ y.1.val = 2 then τ.2.2.2.2.2.getD 0
  else g y

variable {a₀ h : ℕ} {g : Cell c m → ℕ} {τ : TupT}

theorem fillT_z₁ : fillT r a₀ h g τ (z₁ r) = a₀ := by
  have := z₁_c1 (c := c) (r := r)
  have := z₁_c2 (c := c) (r := r)
  unfold fillT
  split_ifs <;> omega

theorem fillT_z₂ (hc : 1 ≤ c) : fillT r a₀ h g τ (z₂ hc r) = h := by
  have := z₂_c1 hc (r := r)
  have := z₂_c2 hc (r := r)
  unfold fillT
  split_ifs <;> omega

theorem fillT_y₁ : fillT r a₀ h g τ (y₁ r) = τ.2.2.1.1 := by
  have := y₁_c1 (c := c) (r := r)
  have := y₁_c2 (c := c) (r := r)
  unfold fillT
  split_ifs <;> omega

theorem fillT_cL2 (hr : 1 ≤ r.val) : fillT r a₀ h g τ (cL2 hr) = τ.2.2.1.2 := by
  have := cL2_c1 (c := c) hr
  have := cL2_c2 (c := c) hr
  unfold fillT
  split_ifs <;> omega

theorem fillT_yU₁ (hr : 1 ≤ r.val) : fillT r a₀ h g τ (yU₁ hr) = τ.1 := by
  have := yU₁_c1 (c := c) hr
  have := yU₁_c2 (c := c) hr
  unfold fillT
  split_ifs <;> omega

theorem fillT_yU₂ (hc : 1 ≤ c) (hr : 1 ≤ r.val) : fillT r a₀ h g τ (yU₂ hc hr) = τ.2.1 := by
  have := yU₂_c1 hc hr
  have := yU₂_c2 hc hr
  unfold fillT
  split_ifs <;> omega

theorem fillT_yD₁ (h1 : r.val + 1 < m) : fillT r a₀ h g τ (yD₁ h1) = τ.2.2.2.1.getD 0 := by
  have := yD₁_c1 (c := c) h1
  have := yD₁_c2 (c := c) h1
  unfold fillT
  split_ifs <;> omega

theorem fillT_cW (h1 : 2 ≤ c) (hr : 1 ≤ r.val) : fillT r a₀ h g τ (cW h1 hr) = τ.2.2.2.2.1.getD 0 := by
  have := cW_c1 (m := m) h1 hr
  have := cW_c2 (m := m) h1 hr
  unfold fillT
  split_ifs <;> omega

theorem fillT_cD (hc : 1 ≤ c) (h1 : 2 ≤ r.val) : fillT r a₀ h g τ (cD hc h1) = τ.2.2.2.2.2.getD 0 := by
  have := cD_c1 (m := m) hc h1
  have := cD_c2 (m := m) hc h1
  unfold fillT
  split_ifs <;> omega

theorem fillT_off {y : Cell c m} (hy : ¬ inT r y) : fillT r a₀ h g τ y = g y := by
  unfold inT at hy
  unfold fillT
  split_ifs <;> first | rfl | omega

theorem mem_optUT {a : ℕ} {o : Option ℕ} (ho : o ∈ optUT P A M r g a) :
    (∃ h1 : r.val + 1 < m, ∃ u, o = some u ∧
      u ∈ ((slab c m 7 P A M).avail (boxT c r) g (yD₁ h1)).erase a) ∨
      (¬ r.val + 1 < m ∧ o = none) := by
  unfold optUT at ho
  split_ifs at ho with h1
  · rw [mem_map] at ho; obtain ⟨u, hu, rfl⟩ := ho; exact Or.inl ⟨h1, u, rfl, hu⟩
  · rw [mem_singleton] at ho; exact Or.inr ⟨h1, ho⟩

theorem mem_optWT {hr : 1 ≤ r.val} {q : ℕ} {o : Option ℕ} (ho : o ∈ optWT P A M hr g q) :
    (∃ h1 : 2 ≤ c, ∃ w, o = some w ∧
      w ∈ ((slab c m 7 P A M).avail (boxT c r) g (cW h1 hr)).erase q) ∨ (¬ 2 ≤ c ∧ o = none) := by
  unfold optWT at ho
  split_ifs at ho with h1
  · rw [mem_map] at ho; obtain ⟨u, hu, rfl⟩ := ho; exact Or.inl ⟨h1, u, rfl, hu⟩
  · rw [mem_singleton] at ho; exact Or.inr ⟨h1, ho⟩

theorem mem_optDT {hc : 1 ≤ c} {q : ℕ} {o : Option ℕ} (ho : o ∈ optDT P A M hc r g q) :
    (∃ h1 : 2 ≤ r.val, ∃ w, o = some w ∧
      w ∈ ((slab c m 7 P A M).avail (boxT c r) g (cD hc h1)).erase q) ∨
      (¬ 2 ≤ r.val ∧ o = none) := by
  unfold optDT at ho
  split_ifs at ho with h1
  · rw [mem_map] at ho; obtain ⟨u, hu, rfl⟩ := ho; exact Or.inl ⟨h1, u, rfl, hu⟩
  · rw [mem_singleton] at ho; exact Or.inr ⟨h1, ho⟩

end Lower

section Lower2

variable {r : Fin m} {a₀ h : ℕ} {g : Cell c m → ℕ}

/-- The columns of the box cells. -/
local macro "colsimp" : tactic =>
  `(tactic| simp only [z₁_c1, z₂_c1, y₁_c1, yU₁_c1, yU₂_c1, cL2_c1, yD₁_c1, cW_c1, cD_c1])

theorem z₁_snd : (z₁ (c := c) r).2 = r := rfl
theorem yU₁_snd (hr : 1 ≤ r.val) : (yU₁ (c := c) hr).2 = ⟨r.val - 1, by omega⟩ := rfl

/-- **The hit event on a fibre.** -/
theorem card_hit_ge_T (hc : 1 ≤ c) (hr : 1 ≤ r.val) (hh7 : h < 7) (ha₀ : a₀ ∈ A r)
    (h7 : 7 ≤ M r a₀) (hg : (slab c m 7 P A M).Valid g)
    (hz : h ∈ (slab c m 7 P A M).avail (boxT c r) g (z₂ hc r)) :
    ∑ p ∈ ((slab c m 7 P A M).avail (boxT c r) g (yU₁ hr)).erase a₀,
      ∑ q ∈ ((range 7).erase h).filter (fun q => M ⟨r.val - 1, by omega⟩ p ≠ q),
        ((dpairs (((slab c m 7 P A M).avail (boxT c r) g (y₁ r)).erase a₀)
            ((slab c m 7 P A M).avail (boxT c r) g (cL2 hr))).filter (fun pr => pr.2 ≠ p)).card *
          ((optUT P A M r g a₀).card *
            ((optWT P A M hr g q).card * (optDT P A M hc r g q).card)) ≤
      (((slab c m 7 P A M).cls (boxT c r) g).filter (Hit hc r a₀ h)).card := by
  set C := slab c m 7 P A M
  set S1 := C.avail (boxT c r) g (y₁ r)
  set S2 := C.avail (boxT c r) g (cL2 hr)
  set Ap := (C.avail (boxT c r) g (yU₁ hr)).erase a₀
  set Tup : Finset TupT := Ap.sigma (fun p => (((range 7).erase h).filter
      (fun q => M ⟨r.val - 1, by omega⟩ p ≠ q)).sigma (fun q =>
        ((dpairs (S1.erase a₀) S2).filter (fun pr => pr.2 ≠ p)) ×ˢ
          (optUT P A M r g a₀ ×ˢ (optWT P A M hr g q ×ˢ optDT P A M hc r g q))))
  have hcard : Tup.card = ∑ p ∈ Ap, ∑ q ∈ ((range 7).erase h).filter
      (fun q => M ⟨r.val - 1, by omega⟩ p ≠ q),
        ((dpairs (S1.erase a₀) S2).filter (fun pr => pr.2 ≠ p)).card *
          ((optUT P A M r g a₀).card *
            ((optWT P A M hr g q).card * (optDT P A M hc r g q).card)) := by
    simp only [Tup, card_sigma, card_product]
  rw [← hcard]
  have hMa : M r a₀ ≠ h := by omega
  refine card_le_card_of_injOn (fillT r a₀ h g) ?_ ?_
  · intro τ hτ
    obtain ⟨p, q, ⟨l1, l2⟩, uo, wo, dd⟩ := τ
    simp only [Tup, mem_coe, mem_sigma, mem_product, mem_filter, mem_erase, mem_range] at hτ
    obtain ⟨hpAp, ⟨⟨hqh, hq7⟩, hMpq⟩, ⟨hpr, hl2p⟩, huo, hwo, hdo⟩ := hτ
    have hpAp' : p ∈ (C.avail (boxT c r) g (yU₁ hr)).erase a₀ := hpAp
    rw [mem_erase] at hpAp'
    obtain ⟨hpa, hpav⟩ := hpAp'
    unfold dpairs at hpr
    rw [mem_filter, mem_product, mem_erase] at hpr
    obtain ⟨⟨⟨hl1a, hl1S⟩, hl2S⟩, hl21⟩ := hpr
    dsimp only at hl2p hl21
    have hU : ∀ h1 : r.val + 1 < m, uo.getD 0 ≠ a₀ ∧
        uo.getD 0 ∈ C.avail (boxT c r) g (yD₁ h1) := by
      intro h1
      rcases mem_optUT huo with ⟨_, u, rfl, hu⟩ | ⟨hn, -⟩
      · rw [mem_erase] at hu; exact hu
      · exact absurd h1 hn
    have hW : ∀ h1 : 2 ≤ c, wo.getD 0 ≠ q ∧ wo.getD 0 ∈ C.avail (boxT c r) g (cW h1 hr) := by
      intro h1
      rcases mem_optWT hwo with ⟨_, u, rfl, hu⟩ | ⟨hn, -⟩
      · rw [mem_erase] at hu; exact hu
      · exact absurd h1 hn
    have hD : ∀ h1 : 2 ≤ r.val, dd.getD 0 ≠ q ∧ dd.getD 0 ∈ C.avail (boxT c r) g (cD hc h1) := by
      intro h1
      rcases mem_optDT hdo with ⟨_, u, rfl, hu⟩ | ⟨hn, -⟩
      · rw [mem_erase] at hu; exact hu
      · exact absurd h1 hn
    rw [mem_coe, mem_filter]
    refine ⟨C.mem_cls_of (C.validOff_of_valid hg)
      (fun y hy => fillT_off (by rwa [mem_boxT] at hy)) ?_ ?_, fillT_z₁, fillT_z₂ hc⟩
    · intro u hu
      rcases inT_cases hc hr (mem_boxT.mp hu) with rfl | rfl | rfl | rfl | rfl | rfl |
        ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩
      · rw [fillT_z₁, avail_T_z₁]; exact ha₀
      · rw [fillT_z₂]; exact hz
      · rw [fillT_y₁]; exact hl1S
      · rw [fillT_yU₁]; exact hpav
      · rw [fillT_yU₂, avail_T_yU₂]; exact mem_range.mpr hq7
      · rw [fillT_cL2]; exact hl2S
      · rw [fillT_yD₁]; exact (hU h1).2
      · rw [fillT_cW]; exact (hW h1).2
      · rw [fillT_cD]; exact (hD h1).2
    · intro u u' hu hu' hadj
      have hadj' := slabAdj_iff.mp hadj
      rcases inT_cases hc hr (mem_boxT.mp hu) with rfl | rfl | rfl | rfl | rfl | rfl |
          ⟨hu1, rfl⟩ | ⟨hu1, rfl⟩ | ⟨hu1, rfl⟩ <;>
        rcases inT_cases hc hr (mem_boxT.mp hu') with rfl | rfl | rfl | rfl | rfl | rfl |
          ⟨hu2, rfl⟩ | ⟨hu2, rfl⟩ | ⟨hu2, rfl⟩
      all_goals
        simp only [z₁_c1, z₁_c2, z₂_c1, z₂_c2, y₁_c1, y₁_c2, yU₁_c1, yU₁_c2, yU₂_c1, yU₂_c2,
          cL2_c1, cL2_c2, yD₁_c1, yD₁_c2, cW_c1, cW_c2, cD_c1, cD_c2] at hadj'
      all_goals first | (exfalso; omega) | skip
      all_goals
        simp only [fillT_z₁, fillT_z₂, fillT_y₁, fillT_cL2, fillT_yU₁, fillT_yU₂, fillT_yD₁,
          fillT_cW, fillT_cD]
      all_goals first | have := hU ‹_› | skip
      all_goals first | have := hW ‹_› | skip
      all_goals first | have := hD ‹_› | skip
      all_goals
        first
        | (rw [slab_conf_seam z₁_c1 (z₂_c1 hc), z₁_snd]; exact hMa)
        | (rw [slab_conf_seam' (z₂_c1 hc) z₁_c1, z₁_snd]; exact fun e => hMa e.symm)
        | (rw [slab_conf_seam (yU₁_c1 hr) (yU₂_c1 hc hr), yU₁_snd]; exact hMpq)
        | (rw [slab_conf_seam' (yU₂_c1 hc hr) (yU₁_c1 hr), yU₁_snd]; exact fun e => hMpq e.symm)
        | (rw [slab_conf_eq (by colsimp; omega) (by colsimp; omega)]; omega)
  · intro τ hτ τ' hτ' he
    obtain ⟨p, q, ⟨l1, l2⟩, uo, wo, dd⟩ := τ
    obtain ⟨p', q', ⟨l1', l2'⟩, uo', wo', dd'⟩ := τ'
    simp only [Tup, mem_coe, mem_sigma, mem_product] at hτ hτ'
    have e1 := congrFun he (yU₁ hr)
    have e2 := congrFun he (yU₂ hc hr)
    have e3 := congrFun he (y₁ r)
    have e4 := congrFun he (cL2 hr)
    rw [fillT_yU₁, fillT_yU₁] at e1
    rw [fillT_yU₂, fillT_yU₂] at e2
    rw [fillT_y₁, fillT_y₁] at e3
    rw [fillT_cL2, fillT_cL2] at e4
    have e5 : uo = uo' := by
      rcases mem_optUT hτ.2.2.2.1 with ⟨h1, u, rfl, -⟩ | ⟨hn, rfl⟩ <;>
        rcases mem_optUT hτ'.2.2.2.1 with ⟨h1', u', rfl, -⟩ | ⟨hn', rfl⟩
      · have := congrFun he (yD₁ h1); rw [fillT_yD₁, fillT_yD₁] at this; simpa using this
      · exact absurd h1 hn'
      · exact absurd h1' hn
      · rfl
    have e6 : wo = wo' := by
      rcases mem_optWT hτ.2.2.2.2.1 with ⟨h1, u, rfl, -⟩ | ⟨hn, rfl⟩ <;>
        rcases mem_optWT hτ'.2.2.2.2.1 with ⟨h1', u', rfl, -⟩ | ⟨hn', rfl⟩
      · have := congrFun he (cW h1 hr); rw [fillT_cW, fillT_cW] at this; simpa using this
      · exact absurd h1 hn'
      · exact absurd h1' hn
      · rfl
    have e7 : dd = dd' := by
      rcases mem_optDT hτ.2.2.2.2.2 with ⟨h1, u, rfl, -⟩ | ⟨hn, rfl⟩ <;>
        rcases mem_optDT hτ'.2.2.2.2.2 with ⟨h1', u', rfl, -⟩ | ⟨hn', rfl⟩
      · have := congrFun he (cD hc h1); rw [fillT_cD, fillT_cD] at this; simpa using this
      · exact absurd h1 hn'
      · exact absurd h1' hn
      · rfl
    dsimp only at e1 e2 e3 e4
    subst e1 e2 e3 e4 e5 e6 e7
    rfl

end Lower2

/-! ### Sizes of the available sets -/

section Sizes

variable {r : Fin m} {g : Cell c m → ℕ}

theorem card_erase_int (S : Finset ℕ) (q : ℕ) :
    ((S.erase q).card : ℤ) = S.card - if q ∈ S then 1 else 0 := by
  by_cases hq : q ∈ S
  · rw [ite_eq_left hq]
    have := card_erase_add_one hq
    omega
  · rw [ite_eq_right hq, erase_eq_of_notMem hq]; simp

variable (P A M)

/-- The labels available at `d` (empty when `d` is missing). -/
noncomputable def setD (hc : 1 ≤ c) (r : Fin m) (g : Cell c m → ℕ) : Finset ℕ :=
  if h1 : 2 ≤ r.val then (slab c m 7 P A M).avail (boxT c r) g (cD hc h1) else ∅

/-- The labels available at `w` (empty when `w` is missing). -/
noncomputable def setW {r : Fin m} (hr : 1 ≤ r.val) (g : Cell c m → ℕ) : Finset ℕ :=
  if h1 : 2 ≤ c then (slab c m 7 P A M).avail (boxT c r) g (cW h1 hr) else ∅

/-- The size at `d` (`1` when `d` is missing). -/
noncomputable def sizeD (hc : 1 ≤ c) (r : Fin m) (g : Cell c m → ℕ) : ℕ :=
  if 2 ≤ r.val then (setD P A M hc r g).card else 1

/-- The size at `w` (`1` when `w` is missing). -/
noncomputable def sizeW {r : Fin m} (hr : 1 ≤ r.val) (g : Cell c m → ℕ) : ℕ :=
  if 2 ≤ c then (setW P A M hr g).card else 1

variable {P A M}

theorem optDT_card (hc : 1 ≤ c) (q : ℕ) :
    ((optDT P A M hc r g q).card : ℤ) =
      sizeD P A M hc r g - if q ∈ setD P A M hc r g then 1 else 0 := by
  unfold optDT sizeD setD
  by_cases h1 : 2 ≤ r.val
  · rw [dite_eq_left h1, ite_eq_left h1, dite_eq_left h1, card_map, card_erase_int]
  · rw [dite_eq_right h1, ite_eq_right h1, dite_eq_right h1]; simp

theorem optWT_card (hr : 1 ≤ r.val) (q : ℕ) :
    ((optWT P A M hr g q).card : ℤ) =
      sizeW P A M hr g - if q ∈ setW P A M hr g then 1 else 0 := by
  unfold optWT sizeW setW
  by_cases h1 : 2 ≤ c
  · rw [dite_eq_left h1, ite_eq_left h1, dite_eq_left h1, card_map, card_erase_int]
  · rw [dite_eq_right h1, ite_eq_right h1, dite_eq_right h1]; simp

theorem setD_spec (hK : KeyInj 7 A M) (hc : 1 ≤ c) (hg : (slab c m 7 P A M).Valid g) :
    setD P A M hc r g ⊆ range 7 ∧
      ((sizeD P A M hc r g = (setD P A M hc r g).card ∧ 4 ≤ sizeD P A M hc r g) ∨
        (setD P A M hc r g = ∅ ∧ sizeD P A M hc r g = 1)) := by
  unfold sizeD setD
  split_ifs with h1
  · have hsub : (slab c m 7 P A M).avail (boxT c r) g (cD hc h1) ⊆ range 7 := by
      intro a ha
      have := ((slab c m 7 P A M).mem_avail.mp ha).1
      rwa [slab_D_fut (show 2 ≤ (cD (m := m) hc h1).1.val from le_rfl)] at this
    refine ⟨hsub, Or.inl ⟨rfl, ?_⟩⟩
    have hav := (slab c m 7 P A M).card_avail_ge (slab_match hK) slab_irrefl
      (mem_boxT.mpr (cD_inT hc h1)) (fun x _ => hg.1 x)
    rw [slab_D_fut (show 2 ≤ (cD (m := m) hc h1).1.val from le_rfl), card_range] at hav
    have hn := nbrsOut_T_cD (k := 7) (P := P) (A := A) (M := M) hc h1
    omega
  · exact ⟨empty_subset _, Or.inr ⟨rfl, rfl⟩⟩

theorem setW_spec (hK : KeyInj 7 A M) (hr : 1 ≤ r.val) (hg : (slab c m 7 P A M).Valid g) :
    setW P A M hr g ⊆ range 7 ∧
      ((sizeW P A M hr g = (setW P A M hr g).card ∧ 4 ≤ sizeW P A M hr g) ∨
        (setW P A M hr g = ∅ ∧ sizeW P A M hr g = 1)) := by
  unfold sizeW setW
  split_ifs with h1
  · have hsub : (slab c m 7 P A M).avail (boxT c r) g (cW h1 hr) ⊆ range 7 := by
      intro a ha
      have := ((slab c m 7 P A M).mem_avail.mp ha).1
      rwa [slab_D_fut (show 2 ≤ (cW (m := m) h1 hr).1.val by rw [cW_c1]; omega)] at this
    refine ⟨hsub, Or.inl ⟨rfl, ?_⟩⟩
    have hav := (slab c m 7 P A M).card_avail_ge (slab_match hK) slab_irrefl
      (mem_boxT.mpr (cW_inT h1 hr)) (fun x _ => hg.1 x)
    rw [slab_D_fut (show 2 ≤ (cW (m := m) h1 hr).1.val by rw [cW_c1]; omega), card_range] at hav
    have hn := nbrsOut_T_cW (k := 7) (P := P) (A := A) (M := M) h1 hr
    omega
  · exact ⟨empty_subset _, Or.inr ⟨rfl, rfl⟩⟩

/-- The `u` ratio: `3 |U \ a| ≤ 4 |U \ a₀|`. -/
theorem optUT_ratio (hK : KeyInj 7 A M) (hA : ∀ v, (A v).card = 7)
    (hg : (slab c m 7 P A M).Valid g) (a a₀ : ℕ) :
    3 * (optUT P A M r g a).card ≤ 4 * (optUT P A M r g a₀).card := by
  unfold optUT
  split_ifs with h1
  · rw [card_map, card_map]
    have hav := (slab c m 7 P A M).card_avail_ge (slab_match hK) slab_irrefl
      (mem_boxT.mpr (yD₁_inT h1)) (fun x _ => hg.1 x)
    rw [slab_D_one (yD₁_c1 h1), hA] at hav
    have hn := nbrsOut_T_yD₁ (k := 7) (P := P) (A := A) (M := M) (c := c) h1
    have e1 := card_erase_le (s := (slab c m 7 P A M).avail (boxT c r) g (yD₁ h1)) (a := a)
    have e2 := pred_card_le_card_erase (s := (slab c m 7 P A M).avail (boxT c r) g (yD₁ h1))
      (a := a₀)
    omega
  · simp

/-- `|S₁| ≥ 5` when `a₀ ∈ S₁`. -/
theorem S1_size (hK : KeyInj 7 A M) (hP : ∀ v a, a ∈ A v → 6 ≤ (P v).card ∨ a ∉ P v)
    (hg : (slab c m 7 P A M).Valid g) {a₀ : ℕ} (ha₀ : a₀ ∈ A r)
    (hm : a₀ ∈ (slab c m 7 P A M).avail (boxT c r) g (y₁ r)) :
    5 ≤ ((slab c m 7 P A M).avail (boxT c r) g (y₁ r)).card := by
  have hPm : a₀ ∈ P r := by
    have := ((slab c m 7 P A M).mem_avail.mp hm).1; rwa [slab_D_zero (y₁_c1 (r := r))] at this
  have hP6 := (hP r a₀ ha₀).resolve_right (not_not.mpr hPm)
  have hav := (slab c m 7 P A M).card_avail_ge (slab_match hK) slab_irrefl
    (mem_boxT.mpr (y₁_inT r)) (fun x _ => hg.1 x)
  rw [slab_D_zero (y₁_c1 (r := r))] at hav
  have hn := nbrsOut_T_y₁ (k := 7) (P := P) (A := A) (M := M) (c := c) r
  change (P r).card - _ ≤ _ at hav
  omega

/-- `|S₂| ≥ 5` when a colour of `A (r - 1)` lies in `S₂`. -/
theorem S2_size (hK : KeyInj 7 A M) (hP : ∀ v a, a ∈ A v → 6 ≤ (P v).card ∨ a ∉ P v)
    (hr : 1 ≤ r.val) (hg : (slab c m 7 P A M).Valid g) {p : ℕ}
    (hpA : p ∈ A ⟨r.val - 1, by omega⟩)
    (hm : p ∈ (slab c m 7 P A M).avail (boxT c r) g (cL2 hr)) :
    5 ≤ ((slab c m 7 P A M).avail (boxT c r) g (cL2 hr)).card := by
  have hPm : p ∈ P ⟨r.val - 1, by omega⟩ := by
    have := ((slab c m 7 P A M).mem_avail.mp hm).1; rwa [slab_D_zero (cL2_c1 hr)] at this
  have hP6 := (hP _ p hpA).resolve_right (not_not.mpr hPm)
  have hav := (slab c m 7 P A M).card_avail_ge (slab_match hK) slab_irrefl
    (mem_boxT.mpr (cL2_inT hr)) (fun x _ => hg.1 x)
  rw [slab_D_zero (cL2_c1 hr)] at hav
  have hn := nbrsOut_T_cL2 (k := 7) (P := P) (A := A) (M := M) (c := c) hr
  change (P ⟨r.val - 1, by omega⟩).card - _ ≤ _ at hav
  omega

/-- At least five values of `p`. -/
theorem Ap_size (hK : KeyInj 7 A M) (hA : ∀ v, (A v).card = 7) (hr : 1 ≤ r.val)
    (hg : (slab c m 7 P A M).Valid g) (a₀ : ℕ) :
    5 ≤ (((slab c m 7 P A M).avail (boxT c r) g (yU₁ hr)).erase a₀).card := by
  have hav := (slab c m 7 P A M).card_avail_ge (slab_match hK) slab_irrefl
    (mem_boxT.mpr (yU₁_inT hr)) (fun x _ => hg.1 x)
  rw [slab_D_one (yU₁_c1 hr), hA] at hav
  have hn := nbrsOut_T_yU₁ (k := 7) (P := P) (A := A) (M := M) (c := c) hr
  have := pred_card_le_card_erase (s := (slab c m 7 P A M).avail (boxT c r) g (yU₁ hr)) (a := a₀)
  omega

end Sizes

/-! ### The box inequality on a fibre, and `absorb_two` -/

section Final

/-- Five colours with distinct keys miss a label: `∑_p ω(key p) + lo ≤ Ω`. -/
theorem sum_key_le {N S : Finset ℕ} (hN : N.card = 6) (hS : S.card = 5) (ω : ℕ → ℕ) {lo : ℕ}
    (hlo : ∀ q ∈ N, lo ≤ ω q) (κ : ℕ → ℕ)
    (hinj : ∀ p ∈ S, ∀ p' ∈ S, κ p ∈ N → κ p = κ p' → p = p') :
    ∑ p ∈ S, ∑ q ∈ N.filter (fun q => ¬ κ p ≠ q), ω q + lo ≤ ∑ q ∈ N, ω q := by
  have e1 : ∑ p ∈ S, ∑ q ∈ N.filter (fun q => ¬ κ p ≠ q), ω q =
      ∑ q ∈ N, (S.filter (fun p => κ p = q)).card * ω q := by
    simp only [sum_filter, not_not]
    rw [sum_comm]
    refine sum_congr rfl fun q _ => ?_
    rw [card_filter, sum_mul]
    exact sum_congr rfl fun p _ => by split_ifs <;> simp
  have hc1 : ∀ q ∈ N, (S.filter (fun p => κ p = q)).card ≤ 1 := by
    intro q hq
    refine card_le_one.mpr fun p hp p' hp' => ?_
    rw [mem_filter] at hp hp'
    exact hinj p hp.1 p' hp'.1 (hp.2 ▸ hq) (hp.2.trans hp'.2.symm)
  have hsum : ∑ q ∈ N, (S.filter (fun p => κ p = q)).card ≤ 5 := by
    rw [sum_card_fiberwise_eq_card_filter]
    exact hS ▸ card_filter_le _ _
  obtain ⟨q0, hq0, hz⟩ : ∃ q0 ∈ N, (S.filter (fun p => κ p = q0)).card = 0 := by
    by_contra hne
    push Not at hne
    have : ∑ q ∈ N, (1 : ℕ) ≤ ∑ q ∈ N, (S.filter (fun p => κ p = q)).card :=
      sum_le_sum fun q hq => Nat.one_le_iff_ne_zero.mpr (hne q hq)
    rw [sum_const, hN, smul_eq_mul, mul_one] at this
    omega
  rw [e1]
  have h1 := add_sum_erase N (fun q => (S.filter (fun p => κ p = q)).card * ω q) hq0
  have h2 := add_sum_erase N ω hq0
  have h3 : ∑ q ∈ N.erase q0, (S.filter (fun p => κ p = q)).card * ω q ≤
      ∑ q ∈ N.erase q0, ω q :=
    sum_le_sum fun q hq => le_trans (Nat.mul_le_mul_right _ (hc1 q (mem_of_mem_erase hq)))
      (by rw [one_mul])
  have h4 := hlo q0 hq0
  simp only [hz, zero_mul, zero_add] at h1
  omega

theorem omega_bounds {x y : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) (d w : Prop) [Decidable d]
    [Decidable w] :
    ((x : ℚ) - 1) * ((y : ℚ) - 1) ≤ ((x : ℚ) - if d then 1 else 0) * ((y : ℚ) - if w then 1 else 0) ∧
      ((x : ℚ) - if d then 1 else 0) * ((y : ℚ) - if w then 1 else 0) ≤ (x : ℚ) * y := by
  have hx' : (1 : ℚ) ≤ x := by exact_mod_cast hx
  have hy' : (1 : ℚ) ≤ y := by exact_mod_cast hy
  split_ifs <;> constructor <;> nlinarith

/-- The upper bound, abstractly: `9 · #Event ≤ 16 · T₀ U₀ ω(t)`. -/
theorem upper_core (Ft : Finset ℕ) (hFt : Ft.card ≤ 1) (fe : ℕ) (hfe : fe ≤ 1)
    (Tf Uf : ℕ → ℕ) (T0 U0 w : ℕ) (hT : ∀ a, 3 * Tf a ≤ 4 * T0) (hU : ∀ a, 3 * Uf a ≤ 4 * U0) :
    9 * ∑ a ∈ Ft, fe * (Tf a * (Uf a * w)) ≤ 16 * (T0 * U0 * w) := by
  rw [mul_sum]
  calc ∑ a ∈ Ft, 9 * (fe * (Tf a * (Uf a * w))) ≤ ∑ _a ∈ Ft, 16 * (T0 * U0 * w) := by
        refine sum_le_sum fun a _ => ?_
        have h1 := hT a
        have h2 := hU a
        calc 9 * (fe * (Tf a * (Uf a * w))) ≤ 9 * (1 * (Tf a * (Uf a * w))) := by gcongr
          _ = (3 * Tf a) * (3 * Uf a) * w := by ring
          _ ≤ (4 * T0) * (4 * U0) * w := by gcongr
          _ = 16 * (T0 * U0 * w) := by ring
    _ = Ft.card * (16 * (T0 * U0 * w)) := by rw [sum_const, smul_eq_mul]
    _ ≤ 1 * (16 * (T0 * U0 * w)) := Nat.mul_le_mul_right _ hFt
    _ = _ := one_mul _

/-- The lower bound, abstractly: `441 · T₀ ω(t) ≤ 32 ∑_{p ∈ P₅} L_p Ψ_p`. -/
theorem lower_core (P5 N : Finset ℕ) (hP5 : P5.card = 5) (hN : N.card = 6) (T0 : ℕ)
    (ν L : ℕ → ℕ) (hLν : ∀ p, L p + ν p = T0) (hν : ∀ p ∈ P5, 4 * ν p ≤ T0)
    (hSν : ∑ p ∈ P5, ν p ≤ T0) (κ : ℕ → ℕ)
    (hinj : ∀ p ∈ P5, ∀ p' ∈ P5, κ p ∈ N → κ p = κ p' → p = p') (ω : ℕ → ℕ) (xD yW : ℕ)
    (hx1 : 1 ≤ xD) (hy1 : 1 ≤ yW) (Dset Wset : Finset ℕ)
    (hω : ∀ q, (ω q : ℚ) = ((xD : ℚ) - if q ∈ Dset then 1 else 0) *
      ((yW : ℚ) - if q ∈ Wset then 1 else 0)) (t : ℕ)
    (hlab1 : 441 * (ω t : ℚ) ≤ 8 * (13 * ∑ q ∈ N, (ω q : ℚ) + 3 * ((xD : ℚ) - 1) * ((yW : ℚ) - 1) -
      (xD : ℚ) * yW))
    (hlab2 : (xD : ℚ) * yW ≤ ∑ q ∈ N, (ω q : ℚ)) :
    441 * (T0 * ω t) ≤ 32 * ∑ p ∈ P5, L p * ∑ q ∈ N.filter (fun q => κ p ≠ q), ω q := by
  set Ωq : ℚ := ∑ q ∈ N, (ω q : ℚ) with hΩq
  have hΨsplit : ∀ p, (∑ q ∈ N.filter (fun q => κ p ≠ q), (ω q : ℚ)) +
      ∑ q ∈ N.filter (fun q => ¬ κ p ≠ q), (ω q : ℚ) = Ωq := fun p =>
    sum_filter_add_sum_filter_not N (fun q => κ p ≠ q) (fun q => (ω q : ℚ))
  have hlo : ∀ q, ((xD : ℚ) - 1) * ((yW : ℚ) - 1) ≤ ω q := fun q => by
    rw [hω]; exact (omega_bounds hx1 hy1 _ _).1
  have hhi : ∀ q, (ω q : ℚ) ≤ (xD : ℚ) * yW := fun q => by
    rw [hω]; exact (omega_bounds hx1 hy1 _ _).2
  have hpair := pairing_bound P5 hP5 (T0 : ℚ) Ωq (((xD : ℚ) - 1) * ((yW : ℚ) - 1))
    ((xD : ℚ) * yW) (fun p => (ν p : ℚ))
    (fun p => ∑ q ∈ N.filter (fun q => κ p ≠ q), (ω q : ℚ))
    (fun p => ∑ q ∈ N.filter (fun q => ¬ κ p ≠ q), (ω q : ℚ))
    (Nat.cast_nonneg _) (fun p _ => Nat.cast_nonneg _)
    (fun p hp => by exact_mod_cast hν p hp) (by exact_mod_cast hSν)
    (fun p _ => hΨsplit p)
    (fun p _ => by
      have hle1 : (N.filter (fun q => ¬ κ p ≠ q)).card ≤ 1 := by
        refine card_le_one.mpr fun q hq q' hq' => ?_
        rw [mem_filter, not_not] at hq hq'
        exact hq.2.symm.trans hq'.2
      calc ∑ q ∈ N.filter (fun q => ¬ κ p ≠ q), (ω q : ℚ)
          ≤ ∑ _q ∈ N.filter (fun q => ¬ κ p ≠ q), (xD : ℚ) * yW := sum_le_sum fun q _ => hhi q
        _ = (N.filter (fun q => ¬ κ p ≠ q)).card * ((xD : ℚ) * yW) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ 1 * ((xD : ℚ) * yW) := by
            have : ((N.filter (fun q => ¬ κ p ≠ q)).card : ℚ) ≤ 1 := by exact_mod_cast hle1
            have h0 : (0 : ℚ) ≤ (xD : ℚ) * yW := by positivity
            nlinarith
        _ = _ := one_mul _)
    (by
      -- the integer version: `∑_p ω(key p) + lo ≤ Ω`
      have hlo' : ∀ q ∈ N, (xD - 1) * (yW - 1) ≤ ω q := fun q _ => by
        have h := hlo q
        have e : (((xD - 1) * (yW - 1) : ℕ) : ℚ) = ((xD : ℚ) - 1) * ((yW : ℚ) - 1) := by
          rw [Nat.cast_mul, Nat.cast_sub hx1, Nat.cast_sub hy1]; simp
        rw [← e] at h
        exact_mod_cast h
      have hkey := sum_key_le hN hP5 ω hlo' κ hinj
      have hcast : ((∑ p ∈ P5, ∑ q ∈ N.filter (fun q => ¬ κ p ≠ q), ω q +
          (xD - 1) * (yW - 1) : ℕ) : ℚ) ≤ ((∑ q ∈ N, ω q : ℕ) : ℚ) := by exact_mod_cast hkey
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hx1, Nat.cast_sub hy1] at hcast
      push_cast at hcast
      rw [hΩq]
      simpa using hcast)
    hlab2
  have hL : ∀ p, (L p : ℚ) = (T0 : ℚ) - ν p := fun p => by
    have := hLν p
    have : ((L p : ℕ) : ℚ) + ν p = T0 := by exact_mod_cast this
    linarith
  have hsum : ∑ p ∈ P5, ((T0 : ℚ) - ν p) * ∑ q ∈ N.filter (fun q => κ p ≠ q), (ω q : ℚ) =
      ((∑ p ∈ P5, L p * ∑ q ∈ N.filter (fun q => κ p ≠ q), ω q : ℕ) : ℚ) := by
    push_cast
    exact sum_congr rfl fun p _ => by rw [hL]
  rw [hsum] at hpair
  have hX : (0 : ℚ) ≤ T0 := Nat.cast_nonneg _
  have k1 : (T0 : ℚ) * (441 * (ω t : ℚ)) ≤ T0 * (8 * (13 * Ωq + 3 * ((xD : ℚ) - 1) *
      ((yW : ℚ) - 1) - (xD : ℚ) * yW)) := mul_le_mul_of_nonneg_left hlab1 hX
  have : (441 * (T0 * ω t) : ℚ) ≤ 32 * ((∑ p ∈ P5, L p * ∑ q ∈ N.filter (fun q => κ p ≠ q),
      ω q : ℕ) : ℚ) := by nlinarith
  exact_mod_cast this

variable {r : Fin m} {g : Cell c m → ℕ}

/-- **The box inequality on one fibre.** -/
theorem fibre_T (hK : KeyInj 7 A M) (hA : ∀ v, (A v).card = 7)
    (hP : ∀ v a, a ∈ A v → 6 ≤ (P v).card ∨ a ∉ P v) (hc : 1 ≤ c) {x y h : ℕ} (hxy : x ≠ y)
    (hx : x < 7) (hy : y < 7) (hh : h = x ∨ h = y) (hr : 1 ≤ r.val) {a₀ : ℕ} (ha₀ : a₀ ∈ A r)
    (h7 : 7 ≤ M r a₀) (hg : (slab c m 7 P A M).Valid g) :
    (((slab c m 7 P A M).cls (boxT c r) g).filter
        (Event (A := A) M x y [(fut0 hc, r), (fut0 hc, ⟨r.val - 1, by omega⟩)] h)).card * 100 ≤
      (((slab c m 7 P A M).cls (boxT c r) g).filter (Hit hc r a₀ h)).card * 13 := by
  have hh7 : h < 7 := by rcases hh with rfl | rfl <;> assumption
  have ht7 : oth x y h < 7 := by rcases oth_mem hh with e | e <;> rw [e] <;> assumption
  have hth : oth x y h ≠ h := by
    unfold oth; split_ifs with e
    · rw [e]; exact fun e' => hxy e'.symm
    · exact fun e' => e (e'.symm)
  by_cases hz : h ∈ (slab c m 7 P A M).avail (boxT c r) g (z₂ hc r)
  swap
  · have : ((slab c m 7 P A M).cls (boxT c r) g).filter
        (Event (A := A) M x y [(fut0 hc, r), (fut0 hc, ⟨r.val - 1, by omega⟩)] h) = ∅ := by
      rw [filter_eq_empty_iff]
      intro f hf hE
      obtain ⟨-, hz2, -⟩ := event_T hxy hh hc hr hE
      exact hz (hz2 ▸ CSP.mem_avail_of_mem_cls _ hf (mem_boxT.mpr (z₂_inT hc r)))
    rw [this, card_empty, zero_mul]; exact Nat.zero_le _
  have hup := card_event_le (P := P) (A := A) (M := M) hc hr hxy hh g
  have hlo := card_hit_ge_T (P := P) (A := A) (M := M) (a₀ := a₀) hc hr hh7 ha₀ h7 hg hz
  -- the upper bound
  have hFt : ((A r).filter (fun a => M r a = oth x y h)).card ≤ 1 := by
    refine card_le_one.mpr fun a ha a' ha' => ?_
    rw [mem_filter] at ha ha'
    exact hK r a a' ha.1 ha'.1 (ha.2.trans ha'.2.symm) (ha.2 ▸ ht7)
  have hFe : ((A ⟨r.val - 1, by omega⟩).filter
      (fun a => M ⟨r.val - 1, by omega⟩ a = h)).card ≤ 1 := by
    refine card_le_one.mpr fun a ha a' ha' => ?_
    rw [mem_filter] at ha ha'
    exact hK _ a a' ha.1 ha'.1 (ha.2.trans ha'.2.symm) (ha.2 ▸ hh7)
  have hE9 := le_trans (Nat.mul_le_mul_left 9 hup) (upper_core _ hFt _ hFe
    (fun a => (dpairs (((slab c m 7 P A M).avail (boxT c r) g (y₁ r)).erase a)
      ((slab c m 7 P A M).avail (boxT c r) g (cL2 hr))).card)
    (fun a => (optUT P A M r g a).card) _ _ _
    (fun a => dpairs_ratio (fun hm => S1_size hK hP hg ha₀ hm) a)
    (fun a => optUT_ratio hK hA hg a a₀))
  -- the lower bound
  obtain ⟨P5, hP5, hP5c⟩ := exists_subset_card_eq (Ap_size hK hA hr hg a₀)
  have hA1 : ∀ p ∈ P5, p ∈ A ⟨r.val - 1, by omega⟩ := fun p hp => by
    have hpav := (mem_erase.mp (hP5 hp)).2
    have := ((slab c m 7 P A M).mem_avail.mp hpav).1
    rwa [slab_D_one (yU₁_c1 hr)] at this
  obtain ⟨hDsub, hDsz⟩ := setD_spec (P := P) (A := A) (M := M) (r := r) (g := g) hK hc hg
  obtain ⟨hWsub, hWsz⟩ := setW_spec (P := P) (A := A) (M := M) (g := g) hK hr hg
  have hx1 : 1 ≤ sizeD P A M hc r g := by rcases hDsz with ⟨_, h4⟩ | ⟨_, h1⟩ <;> omega
  have hy1 : 1 ≤ sizeW P A M hr g := by rcases hWsz with ⟨_, h4⟩ | ⟨_, h1⟩ <;> omega
  have hωz : ∀ q, (((optWT P A M hr g q).card * (optDT P A M hc r g q).card : ℕ) : ℤ) =
      ((sizeD P A M hc r g : ℤ) - if q ∈ setD P A M hc r g then 1 else 0) *
        ((sizeW P A M hr g : ℤ) - if q ∈ setW P A M hr g then 1 else 0) := by
    intro q
    rw [Nat.cast_mul, optDT_card hc q, optWT_card hr q]; ring
  have hωq : ∀ q, (((optWT P A M hr g q).card * (optDT P A M hc r g q).card : ℕ) : ℚ) =
      ((sizeD P A M hc r g : ℚ) - if q ∈ setD P A M hc r g then 1 else 0) *
        ((sizeW P A M hr g : ℚ) - if q ∈ setW P A M hr g then 1 else 0) := by
    intro q
    have := congrArg (fun z : ℤ => (z : ℚ)) (hωz q)
    push_cast at this ⊢
    rw [← this]
  have hlab := label_bound (h := h) (t := oth x y h) hh7 hth ht7 hDsub hWsub hDsz hWsz
  have hsumz : ∑ q ∈ (range 7).erase h, (((sizeD P A M hc r g : ℤ) -
      if q ∈ setD P A M hc r g then 1 else 0) *
        ((sizeW P A M hr g : ℤ) - if q ∈ setW P A M hr g then 1 else 0)) =
      ∑ q ∈ (range 7).erase h,
        (((optWT P A M hr g q).card * (optDT P A M hc r g q).card : ℕ) : ℤ) :=
    sum_congr rfl fun q _ => (hωz q).symm
  rw [hsumz, ← hωz] at hlab
  have hlab1 : 441 * (((optWT P A M hr g (oth x y h)).card *
      (optDT P A M hc r g (oth x y h)).card : ℕ) : ℚ) ≤
      8 * (13 * ∑ q ∈ (range 7).erase h,
        (((optWT P A M hr g q).card * (optDT P A M hc r g q).card : ℕ) : ℚ) +
          3 * ((sizeD P A M hc r g : ℚ) - 1) * ((sizeW P A M hr g : ℚ) - 1) -
            (sizeD P A M hc r g : ℚ) * sizeW P A M hr g) := by
    have := (Int.cast_le (R := ℚ)).mpr hlab.1
    push_cast at this ⊢
    exact this
  have hlab2 : (sizeD P A M hc r g : ℚ) * sizeW P A M hr g ≤ ∑ q ∈ (range 7).erase h,
      (((optWT P A M hr g q).card * (optDT P A M hc r g q).card : ℕ) : ℚ) := by
    have := (Int.cast_le (R := ℚ)).mpr hlab.2
    push_cast at this ⊢
    exact this
  have hcore := lower_core P5 ((range 7).erase h) hP5c
    (by rw [card_erase_of_mem (mem_range.mpr hh7), card_range])
    (dpairs (((slab c m 7 P A M).avail (boxT c r) g (y₁ r)).erase a₀)
      ((slab c m 7 P A M).avail (boxT c r) g (cL2 hr))).card
    (fun p => ((dpairs (((slab c m 7 P A M).avail (boxT c r) g (y₁ r)).erase a₀)
      ((slab c m 7 P A M).avail (boxT c r) g (cL2 hr))).filter (fun pr => pr.2 = p)).card)
    (fun p => ((dpairs (((slab c m 7 P A M).avail (boxT c r) g (y₁ r)).erase a₀)
      ((slab c m 7 P A M).avail (boxT c r) g (cL2 hr))).filter (fun pr => pr.2 ≠ p)).card)
    (fun p => dpairs_split _ _ p)
    (fun p hp => by
      by_cases hpS : p ∈ (slab c m 7 P A M).avail (boxT c r) g (cL2 hr)
      · exact four_nu_le _ _ (S2_size hK hP hr hg (hA1 p hp) hpS) p
      · rw [nu_eq_zero _ _ hpS]; omega)
    (sum_nu_le _ _ P5) (M ⟨r.val - 1, by omega⟩)
    (fun p hp p' hp' hpN e => hK _ p p' (hA1 p hp) (hA1 p' hp') e
      (mem_range.mp (mem_erase.mp hpN).2))
    (fun q => (optWT P A M hr g q).card * (optDT P A M hc r g q).card)
    (sizeD P A M hc r g) (sizeW P A M hr g) hx1 hy1 (setD P A M hc r g) (setW P A M hr g)
    hωq (oth x y h) hlab1 hlab2
  have hsub5 := sum_le_sum_of_subset_of_nonneg (f := fun p =>
    ((dpairs (((slab c m 7 P A M).avail (boxT c r) g (y₁ r)).erase a₀)
      ((slab c m 7 P A M).avail (boxT c r) g (cL2 hr))).filter (fun pr => pr.2 ≠ p)).card *
    ∑ q ∈ ((range 7).erase h).filter (fun q => M ⟨r.val - 1, by omega⟩ p ≠ q),
      (optWT P A M hr g q).card * (optDT P A M hc r g q).card) hP5 (fun _ _ _ => Nat.zero_le _)
  have hlo' : (optUT P A M r g a₀).card * ∑ p ∈ ((slab c m 7 P A M).avail (boxT c r) g
      (yU₁ hr)).erase a₀,
      ((dpairs (((slab c m 7 P A M).avail (boxT c r) g (y₁ r)).erase a₀)
        ((slab c m 7 P A M).avail (boxT c r) g (cL2 hr))).filter (fun pr => pr.2 ≠ p)).card *
      ∑ q ∈ ((range 7).erase h).filter (fun q => M ⟨r.val - 1, by omega⟩ p ≠ q),
        (optWT P A M hr g q).card * (optDT P A M hc r g q).card ≤
      (((slab c m 7 P A M).cls (boxT c r) g).filter (Hit hc r a₀ h)).card := by
    refine le_trans (le_of_eq ?_) hlo
    rw [mul_sum]
    refine sum_congr rfl fun p _ => ?_
    rw [mul_sum, mul_sum]
    exact sum_congr rfl fun q _ => by ring
  -- assemble
  set E := (((slab c m 7 P A M).cls (boxT c r) g).filter
    (Event (A := A) M x y [(fut0 hc, r), (fut0 hc, ⟨r.val - 1, by omega⟩)] h)).card
  set H := (((slab c m 7 P A M).cls (boxT c r) g).filter (Hit hc r a₀ h)).card
  set T0 := (dpairs (((slab c m 7 P A M).avail (boxT c r) g (y₁ r)).erase a₀)
      ((slab c m 7 P A M).avail (boxT c r) g (cL2 hr))).card
  set U0 := (optUT P A M r g a₀).card
  set w := (optWT P A M hr g (oth x y h)).card * (optDT P A M hc r g (oth x y h)).card
  set S5 := ∑ p ∈ P5, ((dpairs (((slab c m 7 P A M).avail (boxT c r) g (y₁ r)).erase a₀)
      ((slab c m 7 P A M).avail (boxT c r) g (cL2 hr))).filter (fun pr => pr.2 ≠ p)).card *
    ∑ q ∈ ((range 7).erase h).filter (fun q => M ⟨r.val - 1, by omega⟩ p ≠ q),
      (optWT P A M hr g q).card * (optDT P A M hc r g q).card
  have k1 : 441 * (T0 * U0 * w) ≤ 32 * H := by
    have e1 : 441 * (T0 * U0 * w) = U0 * (441 * (T0 * w)) := by ring
    have e2 : U0 * (32 * S5) ≤ 32 * H := by
      have := le_trans (Nat.mul_le_mul_left U0 hsub5) hlo'
      calc U0 * (32 * S5) = 32 * (U0 * S5) := by ring
        _ ≤ 32 * H := Nat.mul_le_mul_left 32 this
    rw [e1]
    exact le_trans (Nat.mul_le_mul_left U0 hcore) e2
  have k2 : 9 * E ≤ 16 * (T0 * U0 * w) := hE9
  omega

/-- **`θ₂ ≤ 13/100`** (H orientation): at most `13/100` of the hit event `(1, r) = a₀, (2, r) = h`
in solutions realizing the 4-cycle event on `(2, r), (2, r - 1)` with phase `h`. The proved
constant is `512/3969`. -/
theorem absorb_two (hK : KeyInj 7 A M) (hA : ∀ v, (A v).card = 7)
    (hP : ∀ v a, a ∈ A v → 6 ≤ (P v).card ∨ a ∉ P v) (hc : 1 ≤ c) {x y h : ℕ} (hxy : x ≠ y)
    (hx : x < 7) (hy : y < 7) (hh : h = x ∨ h = y) (r : Fin m) (hr : 1 ≤ r.val)
    (_hhole : ∀ a ∈ A r, M r a ≠ h) {a₀ : ℕ} (ha₀ : a₀ ∈ A r) (h7 : 7 ≤ M r a₀) :
    ((slab c m 7 P A M).Ω.filter (Event (A := A) M x y
        [(fut0 hc, r), (fut0 hc, ⟨r.val - 1, by omega⟩)] h)).card * 100 ≤
      13 * ((slab c m 7 P A M).Ω.filter (Hit hc r a₀ h)).card := by
  rw [mul_comm 13]
  exact (slab c m 7 P A M).fibre_sum_two (boxT c r) _ _ _ _ fun g hg =>
    fibre_T hK hA hP hc hxy hx hy hh hr ha₀ h7 ((CSP.mem_Ω _).mp hg)

/-- `absorb_two` with the star row written `v + 1` (the form of `AbsHBound`; the path is
`vert2 hc v hv`). -/
theorem absorb_two_vert (hK : KeyInj 7 A M) (hA : ∀ v, (A v).card = 7)
    (hP : ∀ v a, a ∈ A v → 6 ≤ (P v).card ∨ a ∉ P v) (hc : 1 ≤ c) {x y h : ℕ} (hxy : x ≠ y)
    (hx : x < 7) (hy : y < 7) (hh : h = x ∨ h = y) (v : ℕ) (hv : v + 1 < m)
    (hhole : ∀ a ∈ A ⟨v + 1, hv⟩, M ⟨v + 1, hv⟩ a ≠ h) {a₀ : ℕ} (ha₀ : a₀ ∈ A ⟨v + 1, hv⟩)
    (h7 : 7 ≤ M ⟨v + 1, hv⟩ a₀) :
    ((slab c m 7 P A M).Ω.filter (Event (A := A) M x y
        [(fut0 hc, ⟨v + 1, hv⟩), (fut0 hc, ⟨v, by omega⟩)] h)).card * 100 ≤
      13 * ((slab c m 7 P A M).Ω.filter (Hit hc ⟨v + 1, hv⟩ a₀ h)).card :=
  absorb_two hK hA hP hc hxy hx hy hh ⟨v + 1, hv⟩ (Nat.le_add_left 1 v) hhole ha₀ h7

end Final

end GridGen.Gauge
