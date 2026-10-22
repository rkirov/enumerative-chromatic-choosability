/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Seven.BoxT2
import GridGen.Gauge.Seven.Short7

/-!
# The vertical three-cell path against a star in its middle row (`k = 7`)

The path is `vert3 hc v hv = [(2, v + 2), (2, v + 1), (2, v)]` with phase `ℓ₀`. The star `a₀` sits in
the middle row `v + 1` (unpaired) and the hit event is `(1, v + 1) = a₀, (2, v + 1) = h`.
`joint_three`: `81 · #Event ≤ 7 · #Hit` for either phase, i.e. `7 · 16/(9 · 144)
= 7/81 ≈ 0.0864` per phase.

**The box `J`** (`inJ`): row `v + 1` from column `0` to `3` (`l, z₁, z₂, w`; `w` may be missing)
and the seam dominoes `(1, v + 2), (2, v + 2)` and `(1, v), (2, v)`. The cells `z₁` and `z₂` have
all their neighbours in the box.

**On a fibre.** The event pins `z₂`, the two path cells and the two end seam cells (keys are
injective), so `#Event ≤ |A (v + 1)| · |S_l| · |W \ mid| = 7 |S_l| |W \ mid|`
(`card_eventJ_le`). The hit event is at least `|S_l \ a₀| · |W \ h| · |Pu| · |Pd|`, where each
domino keeps at least `4 · 3 = 12` pairs (`card_hitJ_ge`). With `3 |S_l| ≤ 4 |S_l \ a₀|` and
`3 |W \ mid| ≤ 4 |W \ h|`, `9 · #Event ≤ 112 X ≤ (112/144) · #Hit`.
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m : ℕ} {P A : Fin m → Finset ℕ} {M : Fin m → ℕ → ℕ}

/-! ### The box -/

/-- Membership in the box around row `v + 1`. -/
def inJ (v : ℕ) (y : Cell c m) : Prop :=
  (y.2.val = v + 1 ∧ y.1.val ≤ 3) ∨
    ((y.2.val = v + 2 ∨ y.2.val = v) ∧ (y.1.val = 1 ∨ y.1.val = 2))

/-- The box. -/
noncomputable def boxJ (c m : ℕ) (v : ℕ) : Finset (Cell c m) := univ.filter (inJ v)

theorem mem_boxJ {v : ℕ} {y : Cell c m} : y ∈ boxJ c m v ↔ inJ v y := by
  unfold boxJ; simp

section Cells

variable {v : ℕ}

/-- `l = (0, v + 1)`. -/
def jL (hv : v + 2 < m) : Cell c m := (0, ⟨v + 1, by omega⟩)
/-- `z₁ = (1, v + 1)`. -/
def jZ1 (hv : v + 2 < m) : Cell c m := (1, ⟨v + 1, by omega⟩)
/-- `z₂ = (2, v + 1)`. -/
def jZ2 (hc : 1 ≤ c) (hv : v + 2 < m) : Cell c m := (fut0 hc, ⟨v + 1, by omega⟩)
/-- `w = (3, v + 1)`. -/
def jW (h : 2 ≤ c) (hv : v + 2 < m) : Cell c m := (⟨3, by omega⟩, ⟨v + 1, by omega⟩)
/-- `p⁺ = (1, v + 2)`. -/
def jPu (hv : v + 2 < m) : Cell c m := (1, ⟨v + 2, hv⟩)
/-- `q⁺ = (2, v + 2)`. -/
def jQu (hc : 1 ≤ c) (hv : v + 2 < m) : Cell c m := (fut0 hc, ⟨v + 2, hv⟩)
/-- `p⁻ = (1, v)`. -/
def jPd (hv : v + 2 < m) : Cell c m := (1, ⟨v, by omega⟩)
/-- `q⁻ = (2, v)`. -/
def jQd (hc : 1 ≤ c) (hv : v + 2 < m) : Cell c m := (fut0 hc, ⟨v, by omega⟩)

theorem jL_c (hv : v + 2 < m) : (jL (c := c) hv).1.val = 0 ∧ (jL (c := c) hv).2.val = v + 1 :=
  ⟨rfl, rfl⟩
theorem jZ1_c (hv : v + 2 < m) : (jZ1 (c := c) hv).1.val = 1 ∧ (jZ1 (c := c) hv).2.val = v + 1 :=
  ⟨Fin.val_one _, rfl⟩
theorem jZ2_c (hc : 1 ≤ c) (hv : v + 2 < m) : (jZ2 hc hv).1.val = 2 ∧ (jZ2 hc hv).2.val = v + 1 :=
  ⟨rfl, rfl⟩
theorem jW_c (h : 2 ≤ c) (hv : v + 2 < m) : (jW h hv).1.val = 3 ∧ (jW h hv).2.val = v + 1 :=
  ⟨rfl, rfl⟩
theorem jPu_c (hv : v + 2 < m) : (jPu (c := c) hv).1.val = 1 ∧ (jPu (c := c) hv).2.val = v + 2 :=
  ⟨Fin.val_one _, rfl⟩
theorem jQu_c (hc : 1 ≤ c) (hv : v + 2 < m) : (jQu hc hv).1.val = 2 ∧ (jQu hc hv).2.val = v + 2 :=
  ⟨rfl, rfl⟩
theorem jPd_c (hv : v + 2 < m) : (jPd (c := c) hv).1.val = 1 ∧ (jPd (c := c) hv).2.val = v :=
  ⟨Fin.val_one _, rfl⟩
theorem jQd_c (hc : 1 ≤ c) (hv : v + 2 < m) : (jQd hc hv).1.val = 2 ∧ (jQd hc hv).2.val = v :=
  ⟨rfl, rfl⟩

theorem inJ_of {y : Cell c m} (h : (y.2.val = v + 1 ∧ y.1.val ≤ 3) ∨
    ((y.2.val = v + 2 ∨ y.2.val = v) ∧ (y.1.val = 1 ∨ y.1.val = 2))) : inJ v y := h

theorem inJ_cases (hc : 1 ≤ c) (hv : v + 2 < m) {y : Cell c m} (hy : inJ v y) :
    y = jL hv ∨ y = jZ1 hv ∨ y = jZ2 hc hv ∨ (∃ h : 2 ≤ c, y = jW h hv) ∨
      y = jPu hv ∨ y = jQu hc hv ∨ y = jPd hv ∨ y = jQd hc hv := by
  unfold inJ at hy
  have hc1 := y.1.isLt
  rcases hy with ⟨hr, hcol⟩ | ⟨hr, hcol⟩
  · have : y.1.val = 0 ∨ y.1.val = 1 ∨ y.1.val = 2 ∨ y.1.val = 3 := by omega
    rcases this with h0 | h0 | h0 | h0
    · left; exact cell_eq (h0.trans (jL_c hv).1.symm) (hr.trans (jL_c hv).2.symm)
    · right; left; exact cell_eq (h0.trans (jZ1_c hv).1.symm) (hr.trans (jZ1_c hv).2.symm)
    · right; right; left
      exact cell_eq (h0.trans (jZ2_c hc hv).1.symm) (hr.trans (jZ2_c hc hv).2.symm)
    · right; right; right; left
      have h2 : 2 ≤ c := by omega
      exact ⟨h2, cell_eq (h0.trans (jW_c h2 hv).1.symm) (hr.trans (jW_c h2 hv).2.symm)⟩
  · right; right; right; right
    rcases hr with hr | hr <;> rcases hcol with h0 | h0
    · left; exact cell_eq (h0.trans (jPu_c hv).1.symm) (hr.trans (jPu_c hv).2.symm)
    · right; left; exact cell_eq (h0.trans (jQu_c hc hv).1.symm) (hr.trans (jQu_c hc hv).2.symm)
    · right; right; left; exact cell_eq (h0.trans (jPd_c hv).1.symm) (hr.trans (jPd_c hv).2.symm)
    · right; right; right
      exact cell_eq (h0.trans (jQd_c hc hv).1.symm) (hr.trans (jQd_c hc hv).2.symm)

end Cells

/-! ### Neighbours off the box -/

section NbrsJ

theorem nbrsOut_J {v : ℕ} (x : Cell c m) (L : List (ℕ × ℕ))
    (hL : ∀ w : Cell c m, (w.1.val = x.1.val ∧ (w.2.val + 1 = x.2.val ∨ w.2.val = x.2.val + 1)) ∨
      (w.2.val = x.2.val ∧ (w.1.val + 1 = x.1.val ∨ w.1.val = x.1.val + 1)) → ¬ inJ v w →
        (w.1.val, w.2.val) ∈ L) :
    ((slab c m 7 P A M).nbrsOut x (boxJ c m v)).card ≤ L.length := by
  refine card_le_of_coords _ L fun w hw => ?_
  rw [CSP.mem_nbrsOut, mem_boxJ] at hw
  exact hL w (adj_coords hw.1) hw.2

/-- A box cell keeps at least `|D| - n` values when at most `n` neighbours are off the box. -/
theorem card_avail_J (hK : KeyInj 7 A M) {g : Cell c m → ℕ}
    (hg : (slab c m 7 P A M).Valid g) {v : ℕ} {x : Cell c m} (hin : inJ v x) {n : ℕ}
    (hn : ((slab c m 7 P A M).nbrsOut x (boxJ c m v)).card ≤ n) :
    ((slab c m 7 P A M).D x).card - n ≤ ((slab c m 7 P A M).avail (boxJ c m v) g x).card := by
  have := (slab c m 7 P A M).card_avail_ge (slab_match hK) slab_irrefl (mem_boxJ.mpr hin)
    (fun x _ => hg.1 x)
  omega

end NbrsJ

/-! ### The event, unpacked -/

theorem event_J {x y ℓ₀ : ℕ} (hc : 1 ≤ c) {v : ℕ} (hv : v + 2 < m) {f : Cell c m → ℕ}
    (hE : Event (A := A) M x y (vert3 hc v hv) ℓ₀ f) :
    (f (jPu hv) ∈ A ⟨v + 2, hv⟩ ∧ M ⟨v + 2, hv⟩ (f (jPu hv)) = oth x y ℓ₀) ∧
      f (jQu hc hv) = ℓ₀ ∧ f (jZ2 hc hv) = oth x y ℓ₀ ∧ f (jQd hc hv) = ℓ₀ ∧
      (f (jPd hv) ∈ A ⟨v, by omega⟩ ∧ M ⟨v, by omega⟩ (f (jPd hv)) = oth x y ℓ₀) := by
  have hn1 : jZ2 hc hv ≠ (jQu hc hv : Cell c m) := by
    intro e; have := congrArg (fun z : Cell c m => z.2.val) e
    simp only [(jZ2_c hc hv).2, (jQu_c hc hv).2] at this; omega
  have hn2 : jQd hc hv ≠ (jQu hc hv : Cell c m) := by
    intro e; have := congrArg (fun z : Cell c m => z.2.val) e
    simp only [(jQd_c hc hv).2, (jQu_c hc hv).2] at this; omega
  have hn3 : jQd hc hv ≠ (jZ2 hc hv : Cell c m) := by
    intro e; have := congrArg (fun z : Cell c m => z.2.val) e
    simp only [(jQd_c hc hv).2, (jZ2_c hc hv).2] at this; omega
  have hrr : (⟨v, by omega⟩ : Fin m) ≠ ⟨v + 2, hv⟩ := by
    intro e; have := congrArg Fin.val e; simp only at this; omega
  have hl3 : vert3 hc v hv = [jQu hc hv, jZ2 hc hv, jQd hc hv] := rfl
  have s2 : (jPu hv : Cell c m) = seamOf (jQu hc hv) := rfl
  have s0 : (jPd hv : Cell c m) = seamOf (jQd hc hv) := rfl
  have h1 := hE (jPu hv) (by rw [hl3, s2]; simp [chainOf])
  have h2 := hE (jQu hc hv) (by rw [hl3]; simp [chainOf])
  have h3 := hE (jZ2 hc hv) (by rw [hl3]; simp [chainOf])
  have h4 := hE (jQd hc hv) (by rw [hl3]; simp [chainOf])
  have h5 := hE (jPd hv) (by rw [hl3, s0]; simp [chainOf])
  rw [hl3] at h1 h2 h3 h4 h5
  have hl1 : lab x y ℓ₀ 1 = oth x y ℓ₀ := by unfold lab; simp
  have hl0 : lab x y ℓ₀ 0 = ℓ₀ := by unfold lab; simp
  have hl2 : lab x y ℓ₀ 2 = ℓ₀ := by unfold lab; simp
  have c1 : ¬ (jQu hc hv : Cell c m).1.val = 1 := by rw [(jQu_c hc hv).1]; omega
  have c2 : ¬ (jZ2 hc hv : Cell c m).1.val = 1 := by rw [(jZ2_c hc hv).1]; omega
  have c3 : ¬ (jQd hc hv : Cell c m).1.val = 1 := by rw [(jQd_c hc hv).1]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [presc, (jPu_c (c := c) hv).1, ite_true, List.head?_cons, Option.map_some] at h1
    simp only [Option.some.injEq,
      show ((jPu (c := c) hv).2 = (jQu hc hv).2) ↔ True from iff_true_intro rfl, ite_true] at h1
    exact mem_filter.mp h1
  · simp only [presc, c1, ite_false, List.idxOf_cons_self, hl0, mem_singleton] at h2
    exact h2
  · simp only [presc, c2, ite_false] at h3
    rw [List.idxOf_cons_ne _ hn1.symm, List.idxOf_cons_self, hl1, mem_singleton] at h3
    exact h3
  · simp only [presc, c3, ite_false] at h4
    rw [List.idxOf_cons_ne _ hn2.symm, List.idxOf_cons_ne _ hn3.symm, List.idxOf_cons_self, hl2,
      mem_singleton] at h4
    exact h4
  · have hrow : (jPd (c := c) hv).2 = ⟨v, by omega⟩ := rfl
    have hne : ¬ (some (jPd (c := c) hv).2 = Option.map Prod.snd
        (([jQu hc hv, jZ2 hc hv, jQd hc hv] : List (Cell c m)).head?)) := by
      simp only [List.head?_cons, Option.map_some, Option.some.injEq]
      exact hrr
    simp only [presc, (jPd_c (c := c) hv).1, ite_true, hne, ite_false, List.length_cons,
      List.length_nil] at h5
    rw [show 0 + 1 + 1 + 1 - 1 = 2 from rfl, hl2, mem_filter] at h5
    exact h5

/-! ### Available sets -/

section Avail

variable {v : ℕ} {g : Cell c m → ℕ}

/-- Coordinates of the neighbours of a box cell that lie off the box. -/
local macro "nbr_tac" : tactic =>
  `(tactic| (intro w hw hnot; unfold inJ at hnot
             simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]; omega))

theorem nbrsOut_jL (hv : v + 2 < m) :
    ((slab c m 7 P A M).nbrsOut (jL hv) (boxJ c m v)).card ≤ 2 :=
  nbrsOut_J (P := P) (A := A) (M := M) _ [(0, v + 2), (0, v)]
    (by rw [(jL_c hv).1, (jL_c hv).2]; nbr_tac)

theorem nbrsOut_jW (h : 2 ≤ c) (hv : v + 2 < m) :
    ((slab c m 7 P A M).nbrsOut (jW h hv) (boxJ c m v)).card ≤ 3 :=
  nbrsOut_J (P := P) (A := A) (M := M) _ [(4, v + 1), (3, v + 2), (3, v)]
    (by rw [(jW_c h hv).1, (jW_c h hv).2]; nbr_tac)

theorem nbrsOut_jQu (hc : 1 ≤ c) (hv : v + 2 < m) :
    ((slab c m 7 P A M).nbrsOut (jQu hc hv) (boxJ c m v)).card ≤ 2 :=
  nbrsOut_J (P := P) (A := A) (M := M) _ [(3, v + 2), (2, v + 3)]
    (by rw [(jQu_c hc hv).1, (jQu_c hc hv).2]; nbr_tac)

theorem nbrsOut_jPu (hv : v + 2 < m) :
    ((slab c m 7 P A M).nbrsOut (jPu hv) (boxJ c m v)).card ≤ 2 :=
  nbrsOut_J (P := P) (A := A) (M := M) _ [(0, v + 2), (1, v + 3)]
    (by rw [(jPu_c hv).1, (jPu_c hv).2]; nbr_tac)

theorem nbrsOut_jQd (hc : 1 ≤ c) (hv : v + 2 < m) :
    ((slab c m 7 P A M).nbrsOut (jQd hc hv) (boxJ c m v)).card ≤ 2 :=
  nbrsOut_J (P := P) (A := A) (M := M) _ [(3, v), (2, v - 1)]
    (by rw [(jQd_c hc hv).1, (jQd_c hc hv).2]; nbr_tac)

theorem nbrsOut_jPd (hv : v + 2 < m) :
    ((slab c m 7 P A M).nbrsOut (jPd hv) (boxJ c m v)).card ≤ 2 :=
  nbrsOut_J (P := P) (A := A) (M := M) _ [(0, v), (1, v - 1)]
    (by rw [(jPd_c hv).1, (jPd_c hv).2]; nbr_tac)

theorem avail_jZ1 (hv : v + 2 < m) :
    (slab c m 7 P A M).avail (boxJ c m v) g (jZ1 hv) = A ⟨v + 1, by omega⟩ := by
  have hD : ∀ y, ((slab c m 7 P A M).adj (jZ1 hv) y ∨ (slab c m 7 P A M).adj y (jZ1 hv)) →
      y ∈ boxJ c m v := by
    intro y hy
    have hcd := adj_coords hy
    rw [(jZ1_c hv).1, (jZ1_c hv).2] at hcd
    rw [mem_boxJ]; unfold inJ; omega
  rw [avail_eq_D hD, slab_D_one (jZ1_c hv).1]; rfl

theorem avail_jZ2 (hc : 1 ≤ c) (hv : v + 2 < m) :
    (slab c m 7 P A M).avail (boxJ c m v) g (jZ2 hc hv) = range 7 := by
  have hD : ∀ y, ((slab c m 7 P A M).adj (jZ2 hc hv) y ∨ (slab c m 7 P A M).adj y (jZ2 hc hv)) →
      y ∈ boxJ c m v := by
    intro y hy
    have hcd := adj_coords hy
    rw [(jZ2_c hc hv).1, (jZ2_c hc hv).2] at hcd
    rw [mem_boxJ]; unfold inJ; omega
  rw [avail_eq_D hD, slab_D_fut (show 2 ≤ (jZ2 hc hv).1.val from le_rfl)]

end Avail

/-! ### Options at `w` -/

variable (P A M) in
/-- Options at `w = (3, v + 1)` avoiding `a`. -/
noncomputable def optWJ {v : ℕ} (hv : v + 2 < m) (g : Cell c m → ℕ) (a : ℕ) :
    Finset (Option ℕ) :=
  if h : 2 ≤ c then
    (((slab c m 7 P A M).avail (boxJ c m v) g (jW h hv)).erase a).map Function.Embedding.some
  else {none}

/-- The value at `w`, if present. -/
def wValJ {v : ℕ} (hv : v + 2 < m) (f : Cell c m → ℕ) : Option ℕ :=
  if h : 2 ≤ c then some (f (jW h hv)) else none

theorem mem_optWJ {v : ℕ} {hv : v + 2 < m} {g : Cell c m → ℕ} {a : ℕ} {o : Option ℕ}
    (ho : o ∈ optWJ P A M hv g a) :
    (∃ h1 : 2 ≤ c, ∃ w, o = some w ∧
      w ∈ ((slab c m 7 P A M).avail (boxJ c m v) g (jW h1 hv)).erase a) ∨ (¬ 2 ≤ c ∧ o = none) := by
  unfold optWJ at ho
  split_ifs at ho with h1
  · rw [mem_map] at ho; obtain ⟨u, hu, rfl⟩ := ho; exact Or.inl ⟨h1, u, rfl, hu⟩
  · rw [mem_singleton] at ho; exact Or.inr ⟨h1, ho⟩

/-! ### The upper bound -/

section UpperJ

variable {v : ℕ}

theorem adj_jW_jZ2 (hc : 1 ≤ c) (h : 2 ≤ c) (hv : v + 2 < m) : slabAdj (jW h hv) (jZ2 hc hv) := by
  rw [slabAdj_iff, (jW_c h hv).1, (jW_c h hv).2, (jZ2_c hc hv).1, (jZ2_c hc hv).2]; omega

/-- **The path event on a fibre.** -/
theorem card_eventJ_le (hA : ∀ v, (A v).card = 7) (hc : 1 ≤ c) (hv : v + 2 < m)
    {x y ℓ₀ : ℕ} (g : Cell c m → ℕ) :
    (((slab c m 7 P A M).cls (boxJ c m v) g).filter
        (Event (A := A) M x y (vert3 hc v hv) ℓ₀)).card ≤
      7 * (((slab c m 7 P A M).avail (boxJ c m v) g (jL hv)).card *
        ((optWJ P A M hv g (oth x y ℓ₀)).card *
          (((A ⟨v + 2, hv⟩).filter (fun a => M ⟨v + 2, hv⟩ a = oth x y ℓ₀)).card *
            ((A ⟨v, by omega⟩).filter (fun a => M ⟨v, by omega⟩ a = oth x y ℓ₀)).card))) := by
  set C := slab c m 7 P A M
  have hcard : (A ⟨v + 1, by omega⟩ ×ˢ (C.avail (boxJ c m v) g (jL hv) ×ˢ
      (optWJ P A M hv g (oth x y ℓ₀) ×ˢ
        ((A ⟨v + 2, hv⟩).filter (fun a => M ⟨v + 2, hv⟩ a = oth x y ℓ₀) ×ˢ
          (A ⟨v, by omega⟩).filter (fun a => M ⟨v, by omega⟩ a = oth x y ℓ₀))))).card =
      7 * ((C.avail (boxJ c m v) g (jL hv)).card * ((optWJ P A M hv g (oth x y ℓ₀)).card *
          (((A ⟨v + 2, hv⟩).filter (fun a => M ⟨v + 2, hv⟩ a = oth x y ℓ₀)).card *
            ((A ⟨v, by omega⟩).filter (fun a => M ⟨v, by omega⟩ a = oth x y ℓ₀)).card))) := by
    simp only [card_product, hA]
  rw [← hcard]
  refine card_le_card_of_injOn (fun f => (f (jZ1 hv), (f (jL hv), (wValJ hv f,
    (f (jPu hv), f (jPd hv)))))) ?_ ?_
  · intro f hf
    rw [mem_coe, mem_filter] at hf
    obtain ⟨hfc, hE⟩ := hf
    have hval := ((CSP.mem_cls _).mp hfc).1
    obtain ⟨hpu, -, hz2, -, hpd⟩ := event_J hc hv hE
    simp only [mem_coe, mem_product, mem_filter]
    refine ⟨?_, CSP.mem_avail_of_mem_cls _ hfc (mem_boxJ.mpr (Or.inl ⟨rfl, by
      rw [(jL_c hv).1]; omega⟩)), ?_, hpu, hpd⟩
    · have := hval.1 (jZ1 hv); rwa [slab_D_one (jZ1_c hv).1] at this
    · unfold optWJ wValJ
      split_ifs with h1
      · refine mem_map_of_mem _ (mem_erase.mpr ⟨?_, CSP.mem_avail_of_mem_cls _ hfc
          (mem_boxJ.mpr (Or.inl ⟨rfl, by rw [(jW_c h1 hv).1]⟩))⟩)
        rw [← hz2]
        exact ne_of_adj_eq hval (adj_jW_jZ2 hc h1 hv) (by rw [(jW_c h1 hv).1]; omega)
          (by rw [(jW_c h1 hv).1]; omega)
      · exact mem_singleton_self _
  · intro f hf f' hf' he
    rw [mem_coe, mem_filter] at hf hf'
    obtain ⟨-, hqu, hz2, hqd, -⟩ := event_J hc hv hf.2
    obtain ⟨-, hqu', hz2', hqd', -⟩ := event_J hc hv hf'.2
    have hc1 := (CSP.mem_cls _).mp hf.1
    have hc1' := (CSP.mem_cls _).mp hf'.1
    simp only [Prod.mk.injEq] at he
    obtain ⟨e1, e2, e3, e4, e5⟩ := he
    funext z
    by_cases hz : z ∈ boxJ c m v
    · rcases inJ_cases hc hv (mem_boxJ.mp hz) with rfl | rfl | rfl | ⟨h1, rfl⟩ | rfl | rfl |
        rfl | rfl
      · exact e2
      · exact e1
      · rw [hz2, hz2']
      · simpa [wValJ, h1] using e3
      · exact e4
      · rw [hqu, hqu']
      · exact e5
      · rw [hqd, hqd']
    · rw [hc1.2 z hz, hc1'.2 z hz]

end UpperJ

/-! ### The lower bound -/

section LowerJ

variable {v : ℕ}

/-- Fill the box: `l`, `w`, the upper and the lower domino from the tuple, `a₀` at `z₁`, `h` at
`z₂`, `g` off the box. -/
def fillJ (v : ℕ) (a₀ h : ℕ) (g : Cell c m → ℕ) (τ : ℕ × (Option ℕ × ((ℕ × ℕ) × (ℕ × ℕ))))
    (y : Cell c m) : ℕ :=
  if y.2.val = v + 1 ∧ y.1.val = 0 then τ.1
  else if y.2.val = v + 1 ∧ y.1.val = 1 then a₀
  else if y.2.val = v + 1 ∧ y.1.val = 2 then h
  else if y.2.val = v + 1 ∧ y.1.val = 3 then τ.2.1.getD 0
  else if y.2.val = v + 2 ∧ y.1.val = 2 then τ.2.2.1.1
  else if y.2.val = v + 2 ∧ y.1.val = 1 then τ.2.2.1.2
  else if y.2.val = v ∧ y.1.val = 2 then τ.2.2.2.1
  else if y.2.val = v ∧ y.1.val = 1 then τ.2.2.2.2
  else g y

variable {a₀ h : ℕ} {g : Cell c m → ℕ} {τ : ℕ × (Option ℕ × ((ℕ × ℕ) × (ℕ × ℕ)))}

theorem fillJ_L (hv : v + 2 < m) : fillJ v a₀ h g τ (jL hv) = τ.1 := by
  have := jL_c (c := c) hv; unfold fillJ; split_ifs <;> omega
theorem fillJ_Z1 (hv : v + 2 < m) : fillJ v a₀ h g τ (jZ1 hv) = a₀ := by
  have := jZ1_c (c := c) hv; unfold fillJ; split_ifs <;> omega
theorem fillJ_Z2 (hc : 1 ≤ c) (hv : v + 2 < m) : fillJ v a₀ h g τ (jZ2 hc hv) = h := by
  have := jZ2_c hc hv; unfold fillJ; split_ifs <;> omega
theorem fillJ_W (h1 : 2 ≤ c) (hv : v + 2 < m) : fillJ v a₀ h g τ (jW h1 hv) = τ.2.1.getD 0 := by
  have := jW_c h1 hv; unfold fillJ; split_ifs <;> omega
theorem fillJ_Qu (hc : 1 ≤ c) (hv : v + 2 < m) : fillJ v a₀ h g τ (jQu hc hv) = τ.2.2.1.1 := by
  have := jQu_c hc hv; unfold fillJ; split_ifs <;> omega
theorem fillJ_Pu (hv : v + 2 < m) : fillJ v a₀ h g τ (jPu hv) = τ.2.2.1.2 := by
  have := jPu_c (c := c) hv; unfold fillJ; split_ifs <;> omega
theorem fillJ_Qd (hc : 1 ≤ c) (hv : v + 2 < m) : fillJ v a₀ h g τ (jQd hc hv) = τ.2.2.2.1 := by
  have := jQd_c hc hv; unfold fillJ; split_ifs <;> omega
theorem fillJ_Pd (hv : v + 2 < m) : fillJ v a₀ h g τ (jPd hv) = τ.2.2.2.2 := by
  have := jPd_c (c := c) hv; unfold fillJ; split_ifs <;> omega

theorem fillJ_off {y : Cell c m} (hy : ¬ inJ v y) : fillJ v a₀ h g τ y = g y := by
  unfold inJ at hy
  unfold fillJ
  split_ifs <;> first | rfl | omega

/-- The colour columns of the box cells. -/
local macro "colJ" : tactic =>
  `(tactic| simp only [(jL_c _).1, (jZ1_c _).1, (jZ2_c _ _).1, (jW_c _ _).1, (jPu_c _).1,
    (jQu_c _ _).1, (jPd_c _).1, (jQd_c _ _).1])

/-- **The hit event on a fibre.** -/
theorem card_hitJ_ge (hc : 1 ≤ c) (hv : v + 2 < m) (hh7 : h < 7) (ha₀ : a₀ ∈ A ⟨v + 1, by omega⟩)
    (h7 : 7 ≤ M ⟨v + 1, by omega⟩ a₀) (hg : (slab c m 7 P A M).Valid g) :
    (((slab c m 7 P A M).avail (boxJ c m v) g (jL hv)).erase a₀).card *
        ((optWJ P A M hv g h).card *
          ((((((slab c m 7 P A M).avail (boxJ c m v) g (jQu hc hv)).erase h) ×ˢ
              (((slab c m 7 P A M).avail (boxJ c m v) g (jPu hv)).erase a₀)).filter
                (fun qp => M ⟨v + 2, hv⟩ qp.2 ≠ qp.1)).card *
            (((((slab c m 7 P A M).avail (boxJ c m v) g (jQd hc hv)).erase h) ×ˢ
              (((slab c m 7 P A M).avail (boxJ c m v) g (jPd hv)).erase a₀)).filter
                (fun qp => M ⟨v, by omega⟩ qp.2 ≠ qp.1)).card)) ≤
      (((slab c m 7 P A M).cls (boxJ c m v) g).filter (Hit hc ⟨v + 1, by omega⟩ a₀ h)).card := by
  set C := slab c m 7 P A M
  set Tup := ((C.avail (boxJ c m v) g (jL hv)).erase a₀) ×ˢ (optWJ P A M hv g h ×ˢ
    ((((C.avail (boxJ c m v) g (jQu hc hv)).erase h) ×ˢ
        ((C.avail (boxJ c m v) g (jPu hv)).erase a₀)).filter
          (fun qp => M ⟨v + 2, hv⟩ qp.2 ≠ qp.1) ×ˢ
      (((C.avail (boxJ c m v) g (jQd hc hv)).erase h) ×ˢ
        ((C.avail (boxJ c m v) g (jPd hv)).erase a₀)).filter
          (fun qp => M ⟨v, by omega⟩ qp.2 ≠ qp.1)))
  suffices hsuff : Tup.card ≤
      (((slab c m 7 P A M).cls (boxJ c m v) g).filter (Hit hc ⟨v + 1, by omega⟩ a₀ h)).card by
    simpa only [Tup, card_product] using hsuff
  have hMa : M ⟨v + 1, by omega⟩ a₀ ≠ h := by omega
  refine card_le_card_of_injOn (fillJ v a₀ h g) ?_ ?_
  · intro τ hτ
    obtain ⟨l, wo, ⟨qu, pu⟩, ⟨qd, pd⟩⟩ := τ
    simp only [Tup, mem_coe, mem_product, mem_filter, mem_erase] at hτ
    obtain ⟨⟨hla, hlS⟩, hwo, ⟨⟨⟨hquh, hquS⟩, hpua, hpuS⟩, hMu⟩, ⟨⟨hqdh, hqdS⟩, hpda, hpdS⟩, hMd⟩ := hτ
    try dsimp only at hMu hMd
    have hW : ∀ h1 : 2 ≤ c, wo.getD 0 ≠ h ∧ wo.getD 0 ∈ C.avail (boxJ c m v) g (jW h1 hv) := by
      intro h1
      rcases mem_optWJ hwo with ⟨_, u, rfl, hu⟩ | ⟨hn, -⟩
      · rw [mem_erase] at hu; exact hu
      · exact absurd h1 hn
    rw [mem_coe, mem_filter]
    refine ⟨C.mem_cls_of (C.validOff_of_valid hg)
      (fun y hy => fillJ_off (by rwa [mem_boxJ] at hy)) ?_ ?_, fillJ_Z1 hv, fillJ_Z2 hc hv⟩
    · intro u hu
      rcases inJ_cases hc hv (mem_boxJ.mp hu) with rfl | rfl | rfl | ⟨h1, rfl⟩ | rfl | rfl |
        rfl | rfl
      · rw [fillJ_L]; exact hlS
      · rw [fillJ_Z1, avail_jZ1]; exact ha₀
      · rw [fillJ_Z2, avail_jZ2]; exact mem_range.mpr hh7
      · rw [fillJ_W]; exact (hW h1).2
      · rw [fillJ_Pu]; exact hpuS
      · rw [fillJ_Qu]; exact hquS
      · rw [fillJ_Pd]; exact hpdS
      · rw [fillJ_Qd]; exact hqdS
    · intro u u' hu hu' hadj
      have hadj' := slabAdj_iff.mp hadj
      rcases inJ_cases hc hv (mem_boxJ.mp hu) with rfl | rfl | rfl | ⟨hu1, rfl⟩ | rfl | rfl |
          rfl | rfl <;>
        rcases inJ_cases hc hv (mem_boxJ.mp hu') with rfl | rfl | rfl | ⟨hu2, rfl⟩ | rfl | rfl |
          rfl | rfl
      all_goals
        simp only [(jL_c _).1, (jL_c _).2, (jZ1_c _).1, (jZ1_c _).2, (jZ2_c _ _).1, (jZ2_c _ _).2,
          (jW_c _ _).1, (jW_c _ _).2, (jPu_c _).1, (jPu_c _).2, (jQu_c _ _).1, (jQu_c _ _).2,
          (jPd_c _).1, (jPd_c _).2, (jQd_c _ _).1, (jQd_c _ _).2] at hadj'
      all_goals first | (exfalso; omega) | skip
      all_goals
        simp only [fillJ_L, fillJ_Z1, fillJ_Z2, fillJ_W, fillJ_Qu, fillJ_Pu, fillJ_Qd, fillJ_Pd]
      all_goals first | have := hW ‹_› | skip
      all_goals
        first
        | (rw [slab_conf_seam (jZ1_c hv).1 (jZ2_c hc hv).1]; exact hMa)
        | (rw [slab_conf_seam' (jZ2_c hc hv).1 (jZ1_c hv).1]; exact fun e => hMa e.symm)
        | (rw [slab_conf_seam (jPu_c hv).1 (jQu_c hc hv).1]; exact hMu)
        | (rw [slab_conf_seam' (jQu_c hc hv).1 (jPu_c hv).1]; exact fun e => hMu e.symm)
        | (rw [slab_conf_seam (jPd_c hv).1 (jQd_c hc hv).1]; exact hMd)
        | (rw [slab_conf_seam' (jQd_c hc hv).1 (jPd_c hv).1]; exact fun e => hMd e.symm)
        | (rw [slab_conf_eq (by colJ; omega) (by colJ; omega)]; omega)
  · intro τ hτ τ' hτ' he
    obtain ⟨l, wo, ⟨qu, pu⟩, ⟨qd, pd⟩⟩ := τ
    obtain ⟨l', wo', ⟨qu', pu'⟩, ⟨qd', pd'⟩⟩ := τ'
    simp only [Tup, mem_coe, mem_product] at hτ hτ'
    have e1 := congrFun he (jL hv)
    have e2 := congrFun he (jQu hc hv)
    have e3 := congrFun he (jPu hv)
    have e4 := congrFun he (jQd hc hv)
    have e5 := congrFun he (jPd hv)
    rw [fillJ_L, fillJ_L] at e1
    rw [fillJ_Qu, fillJ_Qu] at e2
    rw [fillJ_Pu, fillJ_Pu] at e3
    rw [fillJ_Qd, fillJ_Qd] at e4
    rw [fillJ_Pd, fillJ_Pd] at e5
    have e6 : wo = wo' := by
      rcases mem_optWJ hτ.2.1 with ⟨h1, u, rfl, -⟩ | ⟨hn, rfl⟩ <;>
        rcases mem_optWJ hτ'.2.1 with ⟨h1', u', rfl, -⟩ | ⟨hn', rfl⟩
      · have := congrFun he (jW h1 hv); rw [fillJ_W, fillJ_W] at this; simpa using this
      · exact absurd h1 hn'
      · exact absurd h1' hn
      · rfl
    dsimp only at e1 e2 e3 e4 e5
    subst e1 e2 e3 e4 e5 e6
    rfl

end LowerJ

/-! ### Sizes and the bound -/

section FinalJ

variable {v : ℕ} {g : Cell c m → ℕ}

/-- Pairs `(q, p)` with `κ p ≠ q`: at least `|Q| (|S| - 1)` when each label is hit at most once. -/
theorem pairs_ge (Q S : Finset ℕ) (κ : ℕ → ℕ) (h1 : ∀ q ∈ Q, (S.filter (fun p => κ p = q)).card ≤ 1) :
    Q.card * (S.card - 1) ≤ ((Q ×ˢ S).filter (fun qp => κ qp.2 ≠ qp.1)).card := by
  rw [card_filter, sum_product]
  have : ∀ q ∈ Q, S.card - 1 ≤ ∑ p ∈ S, if κ p ≠ q then 1 else 0 := by
    intro q hq
    rw [← card_filter]
    have := card_filter_add_card_filter_not (s := S) (fun p => κ p ≠ q)
    have h2 : (S.filter (fun p => ¬ κ p ≠ q)).card ≤ 1 := by
      simpa only [not_not] using h1 q hq
    omega
  calc Q.card * (S.card - 1) = ∑ _q ∈ Q, (S.card - 1) := by rw [sum_const, smul_eq_mul]
    _ ≤ _ := sum_le_sum this

/-- Each seam domino keeps at least `12` pairs. -/
theorem dom_ge_12 (hK : KeyInj 7 A M) (hg : (slab c m 7 P A M).Valid g) {r : Fin m}
    {xq xp : Cell c m} (hq : inJ v xq) (hp : inJ v xp) (hq2 : 2 ≤ xq.1.val) (hp1 : xp.1.val = 1)
    (hpr : xp.2 = r)
    (hnq : ((slab c m 7 P A M).nbrsOut xq (boxJ c m v)).card ≤ 2)
    (hnp : ((slab c m 7 P A M).nbrsOut xp (boxJ c m v)).card ≤ 2) (hA : ∀ v, (A v).card = 7)
    (h a₀ : ℕ) :
    12 ≤ ((((slab c m 7 P A M).avail (boxJ c m v) g xq).erase h ×ˢ
      ((slab c m 7 P A M).avail (boxJ c m v) g xp).erase a₀).filter
        (fun qp => M r qp.2 ≠ qp.1)).card := by
  have aq := card_avail_J hK hg hq hnq
  have ap := card_avail_J hK hg hp hnp
  rw [slab_D_fut hq2, card_range] at aq
  rw [slab_D_one hp1, hpr, hA] at ap
  have hge := pairs_ge (((slab c m 7 P A M).avail (boxJ c m v) g xq).erase h)
    (((slab c m 7 P A M).avail (boxJ c m v) g xp).erase a₀) (M r) (fun q hq' => by
      refine card_le_one.mpr fun p hp' p' hp'' => ?_
      rw [mem_filter] at hp' hp''
      have hpA : ∀ p, p ∈ ((slab c m 7 P A M).avail (boxJ c m v) g xp).erase a₀ → p ∈ A r :=
        fun p hp3 => by
          have := ((slab c m 7 P A M).mem_avail.mp (mem_erase.mp hp3).2).1
          rwa [slab_D_one hp1, hpr] at this
      have hq7 : q < 7 := by
        have := ((slab c m 7 P A M).mem_avail.mp (mem_erase.mp hq').2).1
        rwa [slab_D_fut hq2, mem_range] at this
      exact hK r p p' (hpA p hp'.1) (hpA p' hp''.1) (hp'.2.trans hp''.2.symm) (hp'.2 ▸ hq7))
  have e1 := pred_card_le_card_erase (s := (slab c m 7 P A M).avail (boxJ c m v) g xq) (a := h)
  have e2 := pred_card_le_card_erase (s := (slab c m 7 P A M).avail (boxJ c m v) g xp) (a := a₀)
  have : 4 * 3 ≤ (((slab c m 7 P A M).avail (boxJ c m v) g xq).erase h).card *
      ((((slab c m 7 P A M).avail (boxJ c m v) g xp).erase a₀).card - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

theorem key_card_le_one (hK : KeyInj 7 A M) (r : Fin m) {b : ℕ} (hb : b < 7) :
    ((A r).filter (fun a => M r a = b)).card ≤ 1 := by
  refine card_le_one.mpr fun a ha a' ha' => ?_
  rw [mem_filter] at ha ha'
  exact hK r a a' ha.1 ha'.1 (ha.2.trans ha'.2.symm) (by rw [ha.2]; exact hb)

theorem lJ_ratio (hK : KeyInj 7 A M) (hP : ∀ v a, a ∈ A v → 6 ≤ (P v).card ∨ a ∉ P v)
    (hv : v + 2 < m) (hg : (slab c m 7 P A M).Valid g) {a₀ : ℕ}
    (ha₀ : a₀ ∈ A ⟨v + 1, by omega⟩) :
    3 * ((slab c m 7 P A M).avail (boxJ c m v) g (jL hv)).card ≤
      4 * (((slab c m 7 P A M).avail (boxJ c m v) g (jL hv)).erase a₀).card := by
  by_cases hm : a₀ ∈ (slab c m 7 P A M).avail (boxJ c m v) g (jL hv)
  · have hPm : a₀ ∈ P ⟨v + 1, by omega⟩ := by
      have := ((slab c m 7 P A M).mem_avail.mp hm).1; rwa [slab_D_zero (jL_c hv).1] at this
    have hP6 := (hP _ a₀ ha₀).resolve_right (not_not.mpr hPm)
    have hin : inJ v (jL (c := c) hv) := by
      unfold inJ; rw [(jL_c hv).1, (jL_c hv).2]; omega
    have hav := card_avail_J hK hg hin (nbrsOut_jL (P := P) (A := A) (M := M) hv)
    rw [slab_D_zero (jL_c hv).1] at hav
    change (P ⟨v + 1, by omega⟩).card - 2 ≤ _ at hav
    rw [card_erase_of_mem hm]
    omega
  · rw [erase_eq_of_notMem hm]; omega

theorem wJ_ratio (hK : KeyInj 7 A M) (hv : v + 2 < m) (hg : (slab c m 7 P A M).Valid g)
    (a h : ℕ) : 3 * (optWJ P A M hv g a).card ≤ 4 * (optWJ P A M hv g h).card := by
  unfold optWJ
  split_ifs with h1
  · rw [card_map, card_map]
    have hin : inJ v (jW h1 hv) := by unfold inJ; rw [(jW_c h1 hv).1, (jW_c h1 hv).2]; omega
    have hav := card_avail_J hK hg hin (nbrsOut_jW (P := P) (A := A) (M := M) h1 hv)
    rw [slab_D_fut (show 2 ≤ (jW h1 hv).1.val by rw [(jW_c h1 hv).1]; omega), card_range] at hav
    have e1 := card_erase_le (s := (slab c m 7 P A M).avail (boxJ c m v) g (jW h1 hv)) (a := a)
    have e2 := pred_card_le_card_erase (s := (slab c m 7 P A M).avail (boxJ c m v) g (jW h1 hv))
      (a := h)
    omega
  · simp

theorem combineJ (E H SL SL0 WM WH Fu Fd Du Dd : ℕ) (hup : E ≤ 7 * (SL * (WM * (Fu * Fd))))
    (hlo : SL0 * (WH * (Du * Dd)) ≤ H) (hFu : Fu ≤ 1) (hFd : Fd ≤ 1) (hL : 3 * SL ≤ 4 * SL0)
    (hW : 3 * WM ≤ 4 * WH) (hDu : 12 ≤ Du) (hDd : 12 ≤ Dd) : E * 81 ≤ H * 7 := by
  have k1 : 9 * E ≤ 112 * (SL0 * WH) := by
    have hF : Fu * Fd ≤ 1 := by
      calc Fu * Fd ≤ 1 * 1 := Nat.mul_le_mul hFu hFd
        _ = 1 := rfl
    calc 9 * E ≤ 9 * (7 * (SL * (WM * (Fu * Fd)))) := Nat.mul_le_mul_left 9 hup
      _ ≤ 9 * (7 * (SL * (WM * 1))) := by gcongr
      _ = 7 * ((3 * SL) * (3 * WM)) := by ring
      _ ≤ 7 * ((4 * SL0) * (4 * WH)) := by gcongr
      _ = 112 * (SL0 * WH) := by ring
  have k2 : 144 * (SL0 * WH) ≤ H := by
    calc 144 * (SL0 * WH) = SL0 * (WH * (12 * 12)) := by ring
      _ ≤ SL0 * (WH * (Du * Dd)) := by gcongr
      _ ≤ H := hlo
  omega

/-- **The box inequality on one fibre.** -/
theorem fibre_J (hK : KeyInj 7 A M) (hA : ∀ v, (A v).card = 7)
    (hP : ∀ v a, a ∈ A v → 6 ≤ (P v).card ∨ a ∉ P v) (hc : 1 ≤ c) {x y h ℓ₀ : ℕ}
    (hx : x < 7) (hy : y < 7) (hh : h = x ∨ h = y) (hℓ : ℓ₀ = x ∨ ℓ₀ = y) (hv : v + 2 < m)
    {a₀ : ℕ} (ha₀ : a₀ ∈ A ⟨v + 1, by omega⟩) (h7 : 7 ≤ M ⟨v + 1, by omega⟩ a₀)
    (hg : (slab c m 7 P A M).Valid g) :
    (((slab c m 7 P A M).cls (boxJ c m v) g).filter
        (Event (A := A) M x y (vert3 hc v hv) ℓ₀)).card * 81 ≤
      (((slab c m 7 P A M).cls (boxJ c m v) g).filter (Hit hc ⟨v + 1, by omega⟩ a₀ h)).card * 7 := by
  have hh7 : h < 7 := by rcases hh with rfl | rfl <;> assumption
  have ho7 : oth x y ℓ₀ < 7 := by rcases oth_mem hℓ with e | e <;> rw [e] <;> assumption
  have hinQu : inJ v (jQu (m := m) hc hv) := by
    unfold inJ; rw [(jQu_c hc hv).1, (jQu_c hc hv).2]; omega
  have hinPu : inJ v (jPu (c := c) hv) := by
    unfold inJ; rw [(jPu_c hv).1, (jPu_c hv).2]; omega
  have hinQd : inJ v (jQd (m := m) hc hv) := by
    unfold inJ; rw [(jQd_c hc hv).1, (jQd_c hc hv).2]; omega
  have hinPd : inJ v (jPd (c := c) hv) := by
    unfold inJ; rw [(jPd_c hv).1, (jPd_c hv).2]; omega
  exact combineJ _ _ _ _ _ _ _ _ _ _
    (card_eventJ_le (P := P) (A := A) (M := M) (x := x) (y := y) (ℓ₀ := ℓ₀) hA hc hv g)
    (card_hitJ_ge (P := P) (A := A) (M := M) (g := g) hc hv hh7 ha₀ h7 hg)
    (key_card_le_one hK _ ho7) (key_card_le_one hK _ ho7)
    (lJ_ratio hK hP hv hg ha₀) (wJ_ratio hK hv hg _ _)
    (dom_ge_12 hK hg hinQu hinPu (le_of_eq (jQu_c hc hv).1.symm) (jPu_c hv).1 rfl
      (nbrsOut_jQu hc hv) (nbrsOut_jPu hv) hA h a₀)
    (dom_ge_12 hK hg hinQd hinPd (le_of_eq (jQd_c hc hv).1.symm) (jPd_c hv).1 rfl
      (nbrsOut_jQd hc hv) (nbrsOut_jPd hv) hA h a₀)

/-- **The vertical three-cell path against a star in its middle row** (`k = 7`, either phase):
`81 · #Event ≤ 7 · #Hit`. -/
theorem joint_three (hK : KeyInj 7 A M) (hA : ∀ v, (A v).card = 7)
    (hP : ∀ v a, a ∈ A v → 6 ≤ (P v).card ∨ a ∉ P v) (hc : 1 ≤ c) {x y h ℓ₀ : ℕ} (_hxy : x ≠ y)
    (hx : x < 7) (hy : y < 7) (hh : h = x ∨ h = y) (hℓ : ℓ₀ = x ∨ ℓ₀ = y) (v : ℕ) (hv : v + 2 < m)
    (_hhole : ∀ a ∈ A ⟨v + 1, by omega⟩, M ⟨v + 1, by omega⟩ a ≠ h) {a₀ : ℕ}
    (ha₀ : a₀ ∈ A ⟨v + 1, by omega⟩) (h7 : 7 ≤ M ⟨v + 1, by omega⟩ a₀) :
    ((slab c m 7 P A M).Ω.filter (Event (A := A) M x y (vert3 hc v hv) ℓ₀)).card * 81 ≤
      7 * ((slab c m 7 P A M).Ω.filter (Hit hc ⟨v + 1, by omega⟩ a₀ h)).card := by
  have := (slab c m 7 P A M).fibre_sum_two (boxJ c m v) _ _ 81 7 fun g hg =>
    fibre_J hK hA hP hc hx hy hh hℓ hv ha₀ h7 ((CSP.mem_Ω _).mp hg)
  rw [mul_comm 7]; exact this

end FinalJ

end GridGen.Gauge
