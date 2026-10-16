/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Star

/-!
# The box bound: a deleted seam pair is hit with probability at least `γ_k`

Let the seam pair `(a₀, x₀)` of row `v` be deleted (the key of `a₀` is `≥ k`). We show that a
`γ_k = (k-4)²(k-5)² / (k²(k-3)⁴)` fraction of the slab solutions puts `a₀` at `z₁ = (1, v)` and
`x₀` at `z₂ = (2, v)` (`box_bound`).

The proof conditions on everything outside the *box* `B`: `z₁`, `z₂` and their neighbours. These
are `y₁ = (0, v)`, `y₆ = (3, v)`, and the dominoes `y₂y₃ = (1..2, v-1)` and `y₄y₅ = (1..2, v+1)`,
whichever exist.

* **Upper bound.** A solution of the fibre is determined by its values on `B`. So the fibre has
  at most `k · k · α₁ · α₆ · τ_up · τ_down` elements. Here `α` counts the colours available at a
  single cell, and `τ` counts the compatible pairs on a domino. Absent cells contribute `1`.
* **Lower bound.** Put `a₀, x₀` on `z₁, z₂` and choose the rest independently. Each single cell
  loses at most one colour. Each domino loses at most `α₂ + α₃` of its `τ` pairs.
* **Arithmetic.** `α₁ ≥ k − 3` whenever `a₀` is available at `y₁`, and `α₆ ≥ k − 3`.
  On a domino `τ ≥ α₂(α₃ − 1)` with `α₂, α₃ ≥ k − 2`, which gives `2τ ≥ (k-3)(α₂+α₃)`.
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m k : ℕ} {P A : Fin m → Finset ℕ} {N : Fin m → ℕ → ℕ}

/-! ### The slab is a DP cover -/

/-- Keys are injective on the colours they pair with a label. -/
def KeyInj (k : ℕ) (A : Fin m → Finset ℕ) (N : Fin m → ℕ → ℕ) : Prop :=
  ∀ v a a', a ∈ A v → a' ∈ A v → N v a = N v a' → N v a < k → a = a'

theorem slab_irrefl : (slab c m k P A N).Irrefl := by
  intro x h
  rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

theorem slab_match (hK : KeyInj k A N) : (slab c m k P A N).Match := by
  intro x y b hb a a' ha ha' h h'
  by_cases hxy : x.1.val = 1 ∧ y.1.val = 2
  · rw [slab_conf_seam hxy.1 hxy.2, slab_conf_seam' hxy.2 hxy.1] at h h'
    rw [slab_D_fut (show 2 ≤ y.1.val by omega), mem_range] at hb
    rw [slab_D_one hxy.1] at ha ha'
    have e1 : N x.2 a = b := by rcases h with h | h <;> [exact h; exact h.symm]
    have e2 : N x.2 a' = b := by rcases h' with h | h <;> [exact h; exact h.symm]
    exact hK x.2 a a' ha ha' (e1.trans e2.symm) (e1 ▸ hb)
  by_cases hyx : x.1.val = 2 ∧ y.1.val = 1
  · rw [slab_conf_seam' hyx.1 hyx.2, slab_conf_seam hyx.2 hyx.1] at h h'
    have e1 : a = N y.2 b := by rcases h with h | h <;> [exact h; exact h.symm]
    have e2 : a' = N y.2 b := by rcases h' with h | h <;> [exact h; exact h.symm]
    exact e1.trans e2.symm
  · rw [slab_conf_eq hxy hyx, slab_conf_eq (by omega) (by omega)] at h h'
    have e1 : a = b := by rcases h with h | h <;> [exact h; exact h.symm]
    have e2 : a' = b := by rcases h' with h | h <;> [exact h; exact h.symm]
    exact e1.trans e2.symm

/-! ### The box -/

/-- Membership in the box around row `v`. -/
def inB (v : Fin m) (y : Cell c m) : Prop :=
  (y.2.val = v.val ∧ y.1.val ≤ 3) ∨
    ((y.1.val = 1 ∨ y.1.val = 2) ∧ (y.2.val + 1 = v.val ∨ y.2.val = v.val + 1))

/-- The box without its two centre cells. -/
def inY (v : Fin m) (y : Cell c m) : Prop :=
  inB v y ∧ ¬ (y.2.val = v.val ∧ (y.1.val = 1 ∨ y.1.val = 2))

/-- The box. -/
noncomputable def boxB (c : ℕ) (v : Fin m) : Finset (Cell c m) := univ.filter (inB v)

/-- The box without its centre. -/
noncomputable def boxY (c : ℕ) (v : Fin m) : Finset (Cell c m) := univ.filter (inY v)

theorem mem_boxB {v : Fin m} {y : Cell c m} : y ∈ boxB c v ↔ inB v y := by
  unfold boxB; simp

theorem mem_boxY {v : Fin m} {y : Cell c m} : y ∈ boxY c v ↔ inY v y := by
  unfold boxY; simp

/-- The seam cell of the box. -/
def z₁ (v : Fin m) : Cell c m := (1, v)

/-- The first future cell of the box. -/
def z₂ (hc : 1 ≤ c) (v : Fin m) : Cell c m := (fut0 hc, v)

theorem z₁_fst (v : Fin m) : (z₁ (c := c) v).1.val = 1 := Fin.val_one _

theorem z₂_fst (hc : 1 ≤ c) (v : Fin m) : (z₂ hc v).1.val = 2 := rfl

theorem cell_eq {x y : Cell c m} (h1 : x.1.val = y.1.val) (h2 : x.2.val = y.2.val) : x = y :=
  Prod.ext (Fin.ext h1) (Fin.ext h2)

/-- Outside its centre, the box is `Y`. -/
theorem inB_iff (hc : 1 ≤ c) {v : Fin m} {y : Cell c m} :
    inB v y ↔ inY v y ∨ y = z₁ v ∨ y = z₂ hc v := by
  unfold inY
  constructor
  · intro h
    by_cases hz : y.2.val = v.val ∧ (y.1.val = 1 ∨ y.1.val = 2)
    · right
      rcases hz.2 with h1 | h1
      · left; exact cell_eq (by rw [z₁_fst]; exact h1) hz.1
      · right; exact cell_eq (by rw [z₂_fst]; exact h1) hz.1
    · left; exact ⟨h, hz⟩
  · rintro (h | rfl | rfl)
    · exact h.1
    · left; exact ⟨rfl, by rw [z₁_fst]; omega⟩
    · left; exact ⟨rfl, by rw [z₂_fst]; omega⟩

theorem z₁_notMem_Y (v : Fin m) : ¬ inY v (z₁ (c := c) v) := by
  unfold inY; rw [z₁_fst]; exact fun h => h.2 ⟨rfl, Or.inl rfl⟩

theorem z₂_notMem_Y (hc : 1 ≤ c) (v : Fin m) : ¬ inY v (z₂ hc v) := by
  unfold inY; rw [z₂_fst]; exact fun h => h.2 ⟨rfl, Or.inr rfl⟩

theorem z₁_ne_z₂ (hc : 1 ≤ c) (v : Fin m) : z₁ v ≠ z₂ hc v := by
  intro h
  have := congrArg (fun x : Cell c m => x.1.val) h
  simp only [z₁_fst, z₂_fst] at this
  omega

theorem slabAdj_symm {x y : Cell c m} : slabAdj x y → slabAdj y x := by
  unfold slabAdj; omega

theorem slabAdj_irrefl {x : Cell c m} : ¬ slabAdj x x := by
  unfold slabAdj; omega

/-- Every neighbour of a centre cell is in the box. -/
theorem inB_of_adj_z₁ {v : Fin m} {w : Cell c m} (h : slabAdj (z₁ v) w) : inB v w := by
  unfold slabAdj at h; unfold inB
  have := z₁_fst (c := c) v
  simp only [z₁] at h this ⊢
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · right; rw [← h1]; exact ⟨Or.inl this, by omega⟩
  · left; rw [← h1]; exact ⟨rfl, by omega⟩

theorem inB_of_adj_z₂ (hc : 1 ≤ c) {v : Fin m} {w : Cell c m} (h : slabAdj (z₂ hc v) w) :
    inB v w := by
  unfold slabAdj at h; unfold inB
  have := z₂_fst hc v
  simp only [z₂] at h this ⊢
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · right; rw [← h1]; exact ⟨Or.inr this, by omega⟩
  · left; rw [← h1]; exact ⟨rfl, by omega⟩

/-- Inside `Y` the only edges are the two dominoes, each joining columns `1` and `2`. -/
theorem adj_in_Y {v : Fin m} {u u' : Cell c m} (hu : inY v u) (hu' : inY v u')
    (h : slabAdj u u') : u.2 = u'.2 ∧
      ((u.1.val = 1 ∧ u'.1.val = 2) ∨ (u.1.val = 2 ∧ u'.1.val = 1)) := by
  unfold inY inB at hu hu'
  unfold slabAdj at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exfalso
    have : u.1.val = u'.1.val := by rw [h1]
    omega
  · refine ⟨h1, ?_⟩
    have : u.2.val = u'.2.val := by rw [h1]
    omega

/-- A cell of `Y` next to `z₁` is in column `0` or `1`; one next to `z₂` in column `2` or `3`. -/
theorem fst_le_of_adj_z₁ {v : Fin m} {y : Cell c m} (hy : inY v y)
    (h : slabAdj y (z₁ v)) : y.1.val ≤ 1 := by
  unfold inY inB at hy; unfold slabAdj at h
  have := z₁_fst (c := c) v
  simp only [z₁] at h this
  omega

theorem le_fst_of_adj_z₂ (hc : 1 ≤ c) {v : Fin m} {y : Cell c m} (hy : inY v y)
    (h : slabAdj y (z₂ hc v)) : 2 ≤ y.1.val := by
  unfold inY inB at hy; unfold slabAdj at h
  have := z₂_fst hc v
  simp only [z₂] at h this
  omega

/-! ### The cells of `Y` -/

/-- The past cell of the box. -/
def y₁ (v : Fin m) : Cell c m := (0, v)

/-- The second future cell of the box (when the future has two columns). -/
def y₆ (h : 2 ≤ c) (v : Fin m) : Cell c m := (⟨3, by omega⟩, v)

/-- The seam cell of the upper domino. -/
def yU₁ {v : Fin m} (h : 1 ≤ v.val) : Cell c m := (1, ⟨v.val - 1, by omega⟩)

/-- The future cell of the upper domino. -/
def yU₂ (hc : 1 ≤ c) {v : Fin m} (h : 1 ≤ v.val) : Cell c m := (fut0 hc, ⟨v.val - 1, by omega⟩)

/-- The seam cell of the lower domino. -/
def yD₁ {v : Fin m} (h : v.val + 1 < m) : Cell c m := (1, ⟨v.val + 1, h⟩)

/-- The future cell of the lower domino. -/
def yD₂ (hc : 1 ≤ c) {v : Fin m} (h : v.val + 1 < m) : Cell c m := (fut0 hc, ⟨v.val + 1, h⟩)

theorem inY_cases (hc : 1 ≤ c) {v : Fin m} {y : Cell c m} (hy : inY v y) :
    y = y₁ v ∨ (∃ h : 2 ≤ c, y = y₆ h v) ∨
      (∃ h : 1 ≤ v.val, y = yU₁ (c := c) h ∨ y = yU₂ hc h) ∨
        (∃ h : v.val + 1 < m, y = yD₁ (c := c) h ∨ y = yD₂ hc h) := by
  unfold inY inB at hy
  have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  rcases hy with ⟨⟨hrow, hcol⟩ | ⟨hcol, hrow⟩, hnot⟩
  · have : y.1.val = 0 ∨ y.1.val = 3 := by omega
    rcases this with h0 | h3
    · left; exact cell_eq (by simp [y₁, h0]) hrow
    · right; left
      have h2 : 2 ≤ c := by have := y.1.isLt; omega
      exact ⟨h2, cell_eq (by simp [y₆, h3]) hrow⟩
  · right; right
    rcases hrow with hr | hr
    · left
      refine ⟨by omega, ?_⟩
      rcases hcol with hcl | hcl
      · left; exact cell_eq (by simp [yU₁, hcl, h1]) (by simp [yU₁]; omega)
      · right; exact cell_eq (by simp [yU₂, fut0, hcl]) (by simp [yU₂]; omega)
    · right
      refine ⟨by have := y.2.isLt; omega, ?_⟩
      rcases hcol with hcl | hcl
      · left; exact cell_eq (by simp [yD₁, hcl, h1]) (by simp [yD₁]; omega)
      · right; exact cell_eq (by simp [yD₂, fut0, hcl]) (by simp [yD₂]; omega)

theorem y₁_inY (v : Fin m) : inY v (y₁ (c := c) v) := by
  unfold inY inB y₁; simp

theorem y₆_inY (h : 2 ≤ c) (v : Fin m) : inY v (y₆ h v) := by
  unfold inY inB y₆; simp

theorem yU₁_inY {v : Fin m} (h : 1 ≤ v.val) : inY v (yU₁ (c := c) h) := by
  have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  unfold inY inB yU₁; dsimp only; rw [h1]; omega

theorem yU₂_inY (hc : 1 ≤ c) {v : Fin m} (h : 1 ≤ v.val) : inY v (yU₂ hc h) := by
  unfold inY inB yU₂ fut0; dsimp only; omega

theorem yD₁_inY {v : Fin m} (h : v.val + 1 < m) : inY v (yD₁ (c := c) h) := by
  have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  unfold inY inB yD₁; dsimp only; rw [h1]; omega

theorem yD₂_inY (hc : 1 ≤ c) {v : Fin m} (h : v.val + 1 < m) : inY v (yD₂ hc h) := by
  unfold inY inB yD₂ fut0; dsimp only; omega

/-! ### Shifting the centre -/

/-- `g` with the prescribed centre values. -/
def shift (hc : 1 ≤ c) (v : Fin m) (a₀ x₀ : ℕ) (g : Cell c m → ℕ) : Cell c m → ℕ :=
  Function.update (Function.update g (z₁ v) a₀) (z₂ hc v) x₀

theorem shift_z₁ (hc : 1 ≤ c) (v : Fin m) (a₀ x₀ : ℕ) (g : Cell c m → ℕ) :
    shift hc v a₀ x₀ g (z₁ v) = a₀ := by
  simp [shift, z₁_ne_z₂ hc v]

theorem shift_z₂ (hc : 1 ≤ c) (v : Fin m) (a₀ x₀ : ℕ) (g : Cell c m → ℕ) :
    shift hc v a₀ x₀ g (z₂ hc v) = x₀ := by
  simp [shift]

theorem shift_of_ne (hc : 1 ≤ c) {v : Fin m} {a₀ x₀ : ℕ} {g : Cell c m → ℕ} {y : Cell c m}
    (h1 : y ≠ z₁ v) (h2 : y ≠ z₂ hc v) : shift hc v a₀ x₀ g y = g y := by
  simp [shift, h1, h2]

/-- A neighbour of a centre cell outside `Y` is the other centre cell. -/
theorem eq_z₂_of_adj (hc : 1 ≤ c) {v : Fin m} {w : Cell c m}
    (h : slabAdj (z₁ v) w ∨ slabAdj w (z₁ v)) (hw : ¬ inY v w) : w = z₂ hc v := by
  have hB : inB v w := by
    rcases h with h | h
    · exact inB_of_adj_z₁ h
    · exact inB_of_adj_z₁ (slabAdj_symm h)
  rcases (inB_iff hc).mp hB with h' | rfl | rfl
  · exact absurd h' hw
  · exfalso; rcases h with h | h <;> exact slabAdj_irrefl h
  · rfl

theorem eq_z₁_of_adj (hc : 1 ≤ c) {v : Fin m} {w : Cell c m}
    (h : slabAdj (z₂ hc v) w ∨ slabAdj w (z₂ hc v)) (hw : ¬ inY v w) : w = z₁ v := by
  have hB : inB v w := by
    rcases h with h | h
    · exact inB_of_adj_z₂ hc h
    · exact inB_of_adj_z₂ hc (slabAdj_symm h)
  rcases (inB_iff hc).mp hB with h' | rfl | rfl
  · exact absurd h' hw
  · rfl
  · exfalso; rcases h with h | h <;> exact slabAdj_irrefl h

/-- **The shifted base is valid off `Y`.** -/
theorem validOff_shift (hc : 1 ≤ c) {v : Fin m} {a₀ x₀ : ℕ} {g : Cell c m → ℕ}
    (hg : (slab c m k P A N).Valid g) (ha : a₀ ∈ A v) (hx : x₀ < k) (hN : k ≤ N v a₀) :
    (slab c m k P A N).ValidOff (boxY c v) (shift hc v a₀ x₀ g) := by
  refine ⟨fun x hx' => ?_, fun x y hx' hy' hxy => ?_⟩
  · by_cases h1 : x = z₁ v
    · subst h1; rw [shift_z₁, slab_D_one (z₁_fst v)]; exact ha
    by_cases h2 : x = z₂ hc v
    · subst h2; rw [shift_z₂, slab_D_fut (by rw [z₂_fst]), mem_range]; exact hx
    rw [shift_of_ne hc h1 h2]; exact hg.1 x
  · rw [mem_boxY] at hx' hy'
    by_cases h1 : x = z₁ v
    · subst h1
      have hy2 := eq_z₂_of_adj hc (Or.inl hxy) hy'
      subst hy2
      rw [shift_z₁, shift_z₂, slab_conf_seam (z₁_fst v) (z₂_fst hc v)]
      intro he; simp only [z₁] at he; omega
    by_cases h2 : x = z₂ hc v
    · subst h2
      have hy1 := eq_z₁_of_adj hc (Or.inl hxy) hy'
      subst hy1
      rw [shift_z₁, shift_z₂, slab_conf_seam' (z₂_fst hc v) (z₁_fst v)]
      intro he; simp only [z₁] at he; omega
    by_cases h1' : y = z₁ v
    · subst h1'
      exact absurd (eq_z₂_of_adj hc (Or.inr hxy) hx') h2
    by_cases h2' : y = z₂ hc v
    · subst h2'
      exact absurd (eq_z₁_of_adj hc (Or.inr hxy) hx') h1
    rw [shift_of_ne hc h1 h2, shift_of_ne hc h1' h2']
    exact hg.2 x y hxy

/-- The centre value a cell of `Y` must avoid: `a₀` next to `z₁` (columns `0, 1`), `x₀` next to
`z₂` (columns `2, 3`). -/
def fz (a₀ x₀ : ℕ) (y : Cell c m) : ℕ := if y.1.val ≤ 1 then a₀ else x₀

/-- **Available after the shift.** A colour available at a cell of `Y` before the shift stays
available after it, unless it is the centre value that cell must avoid. -/
theorem mem_avail_shift (hc : 1 ≤ c) {v : Fin m} {a₀ x₀ : ℕ} {g : Cell c m → ℕ}
    {y : Cell c m} (hy : inY v y) {a : ℕ}
    (ha : a ∈ (slab c m k P A N).avail (boxB c v) g y) (hne : a ≠ fz a₀ x₀ y) :
    a ∈ (slab c m k P A N).avail (boxY c v) (shift hc v a₀ x₀ g) y := by
  rw [CSP.mem_avail] at ha ⊢
  refine ⟨ha.1, fun w hw => ?_⟩
  rw [mem_boxY] at hw
  by_cases hB : inB v w
  · rcases (inB_iff hc).mp hB with h | rfl | rfl
    · exact absurd h hw
    · -- `w = z₁`: the clash is an equality and `y` lies in column `0` or `1`
      rw [shift_z₁]
      have hcolY : ∀ h : slabAdj y (z₁ v), y.1.val ≤ 1 := fun h => fst_le_of_adj_z₁ hy h
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have h1 := hcolY h
        rw [slab_conf_eq (by rw [z₁_fst]; omega) (by rw [z₁_fst]; omega)]
        simp only [fz, if_pos h1] at hne; exact hne
      · have h1 := hcolY (slabAdj_symm h)
        rw [slab_conf_eq (by rw [z₁_fst]; omega) (by rw [z₁_fst]; omega)]
        simp only [fz, if_pos h1] at hne; exact fun e => hne e.symm
    · rw [shift_z₂]
      have hcolY : ∀ h : slabAdj y (z₂ hc v), 2 ≤ y.1.val := fun h => le_fst_of_adj_z₂ hc hy h
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have h1 := hcolY h
        rw [slab_conf_eq (by rw [z₂_fst]; omega) (by rw [z₂_fst]; omega)]
        simp only [fz, if_neg (show ¬ y.1.val ≤ 1 by omega)] at hne; exact hne
      · have h1 := hcolY (slabAdj_symm h)
        rw [slab_conf_eq (by rw [z₂_fst]; omega) (by rw [z₂_fst]; omega)]
        simp only [fz, if_neg (show ¬ y.1.val ≤ 1 by omega)] at hne; exact fun e => hne e.symm
  · have hwB : w ∉ boxB c v := by rw [mem_boxB]; exact hB
    have h1 : w ≠ z₁ v := by rintro rfl; exact hB ((inB_iff hc).mpr (Or.inr (Or.inl rfl)))
    have h2 : w ≠ z₂ hc v := by rintro rfl; exact hB ((inB_iff hc).mpr (Or.inr (Or.inr rfl)))
    rw [shift_of_ne hc h1 h2]
    exact ha.2 w hwB

/-! ### The upper bound -/

section Upper

variable (c k P A N) in
/-- Compatible pairs on a domino `y, y'`, from the colours available under `g`. -/
noncomputable def dom (U : Finset (Cell c m)) (g : Cell c m → ℕ) (y y' : Cell c m) :
    Finset (ℕ × ℕ) :=
  (((slab c m k P A N).avail U g y) ×ˢ ((slab c m k P A N).avail U g y')).filter
    (fun pq => ¬ (slab c m k P A N).conf y y' pq.1 pq.2 ∧
      ¬ (slab c m k P A N).conf y' y pq.2 pq.1)

variable (c k P A N) in
/-- The options at `y₆`: its available colours, or a single dummy when it is absent. -/
noncomputable def opt6 (v : Fin m) (g : Cell c m → ℕ) : Finset (Option ℕ) :=
  if h : 2 ≤ c then ((slab c m k P A N).avail (boxB c v) g (y₆ h v)).map Function.Embedding.some else {none}

variable (c k P A N) in
/-- The options on the upper domino. -/
noncomputable def optU (hc : 1 ≤ c) (v : Fin m) (g : Cell c m → ℕ) : Finset (Option (ℕ × ℕ)) :=
  if h : 1 ≤ v.val then (dom c k P A N (boxB c v) g (yU₁ h) (yU₂ hc h)).map Function.Embedding.some else {none}

variable (c k P A N) in
/-- The options on the lower domino. -/
noncomputable def optD (hc : 1 ≤ c) (v : Fin m) (g : Cell c m → ℕ) : Finset (Option (ℕ × ℕ)) :=
  if h : v.val + 1 < m then (dom c k P A N (boxB c v) g (yD₁ h) (yD₂ hc h)).map Function.Embedding.some
  else {none}

/-- The box values of an assignment. -/
def boxVals (hc : 1 ≤ c) (v : Fin m) (f : Cell c m → ℕ) :
    ℕ × ℕ × ℕ × Option ℕ × Option (ℕ × ℕ) × Option (ℕ × ℕ) :=
  (f (z₁ v), f (z₂ hc v), f (y₁ v),
    (if h : 2 ≤ c then some (f (y₆ h v)) else none),
    (if h : 1 ≤ v.val then some (f (yU₁ h), f (yU₂ hc h)) else none),
    (if h : v.val + 1 < m then some (f (yD₁ h), f (yD₂ hc h)) else none))

theorem slabAdj_dom₁ (hc : 1 ≤ c) {v : Fin m} (h : 1 ≤ v.val) :
    slabAdj (yU₁ (c := c) h) (yU₂ hc h) := by
  have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  unfold slabAdj yU₁ yU₂ fut0; dsimp only; rw [h1]; omega

theorem slabAdj_dom₂ (hc : 1 ≤ c) {v : Fin m} (h : v.val + 1 < m) :
    slabAdj (yD₁ (c := c) h) (yD₂ hc h) := by
  have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  unfold slabAdj yD₁ yD₂ fut0; dsimp only; rw [h1]; omega

theorem mem_dom_of_valid {U : Finset (Cell c m)} {g f : Cell c m → ℕ}
    (hf : f ∈ (slab c m k P A N).cls U g) {y y' : Cell c m} (hy : y ∈ U) (hy' : y' ∈ U)
    (hadj : slabAdj y y') : (f y, f y') ∈ dom c k P A N U g y y' := by
  unfold dom
  rw [mem_filter, mem_product]
  refine ⟨⟨CSP.mem_avail_of_mem_cls _ hf hy, CSP.mem_avail_of_mem_cls _ hf hy'⟩, ?_, ?_⟩
  · exact ((CSP.mem_cls _).mp hf).1.2 y y' hadj
  · exact ((CSP.mem_cls _).mp hf).1.2 y' y (slabAdj_symm hadj)

/-- **Upper bound on a fibre.** -/
theorem card_cls_le (hc : 1 ≤ c) (v : Fin m) (g : Cell c m → ℕ) :
    ((slab c m k P A N).cls (boxB c v) g).card ≤
      (A v).card * k * ((slab c m k P A N).avail (boxB c v) g (y₁ v)).card *
        (opt6 c k P A N v g).card * (optU c k P A N hc v g).card *
          (optD c k P A N hc v g).card := by
  set C := slab c m k P A N
  have hT : (A v ×ˢ range k ×ˢ C.avail (boxB c v) g (y₁ v) ×ˢ opt6 c k P A N v g ×ˢ
      optU c k P A N hc v g ×ˢ optD c k P A N hc v g).card =
        (A v).card * k * (C.avail (boxB c v) g (y₁ v)).card * (opt6 c k P A N v g).card *
          (optU c k P A N hc v g).card * (optD c k P A N hc v g).card := by
    simp only [card_product, card_range]; ring
  rw [← hT]
  refine card_le_card_of_injOn (boxVals hc v) ?_ ?_
  · intro f hf
    have hv := ((CSP.mem_cls _).mp hf).1
    simp only [coe_product, Set.mem_prod, mem_coe, boxVals]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hv.1 (z₁ v); rwa [slab_D_one (z₁_fst v)] at this
    · have := hv.1 (z₂ hc v); rwa [slab_D_fut (by rw [z₂_fst])] at this
    · exact CSP.mem_avail_of_mem_cls _ hf (mem_boxB.mpr (y₁_inY v).1)
    · unfold opt6
      split_ifs with h
      · exact mem_map_of_mem _ (CSP.mem_avail_of_mem_cls _ hf (mem_boxB.mpr (y₆_inY h v).1))
      · exact mem_singleton_self _
    · unfold optU
      split_ifs with h
      · exact mem_map_of_mem _ (mem_dom_of_valid hf (mem_boxB.mpr (yU₁_inY h).1)
          (mem_boxB.mpr (yU₂_inY hc h).1) (slabAdj_dom₁ hc h))
      · exact mem_singleton_self _
    · unfold optD
      split_ifs with h
      · exact mem_map_of_mem _ (mem_dom_of_valid hf (mem_boxB.mpr (yD₁_inY h).1)
          (mem_boxB.mpr (yD₂_inY hc h).1) (slabAdj_dom₂ hc h))
      · exact mem_singleton_self _
  · intro f hf f' hf' he
    simp only [boxVals, Prod.mk.injEq] at he
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := he
    have hf1 := (CSP.mem_cls _).mp hf
    have hf1' := (CSP.mem_cls _).mp hf'
    funext y
    by_cases hB : y ∈ boxB c v
    · rcases (inB_iff hc).mp (mem_boxB.mp hB) with hY | rfl | rfl
      · rcases inY_cases hc hY with rfl | ⟨h, rfl⟩ | ⟨h, rfl | rfl⟩ | ⟨h, rfl | rfl⟩
        · exact e3
        · simp only [dif_pos h, Option.some.injEq] at e4; exact e4
        · simp only [dif_pos h, Option.some.injEq, Prod.mk.injEq] at e5; exact e5.1
        · simp only [dif_pos h, Option.some.injEq, Prod.mk.injEq] at e5; exact e5.2
        · simp only [dif_pos h, Option.some.injEq, Prod.mk.injEq] at e6; exact e6.1
        · simp only [dif_pos h, Option.some.injEq, Prod.mk.injEq] at e6; exact e6.2
      · exact e1
      · exact e2
    · rw [hf1.2 y hB, hf1'.2 y hB]

end Upper

/-! ### The lower bound -/

section Lower

variable (c k P A N) in
/-- Options at `y₆` after the shift. -/
noncomputable def opt6' (v : Fin m) (x₀ : ℕ) (g : Cell c m → ℕ) : Finset (Option ℕ) :=
  if h : 2 ≤ c then (((slab c m k P A N).avail (boxB c v) g (y₆ h v)).erase x₀).map Function.Embedding.some
  else {none}

variable (c k P A N) in
/-- Options on the upper domino after the shift. -/
noncomputable def optU' (hc : 1 ≤ c) (v : Fin m) (a₀ x₀ : ℕ) (g : Cell c m → ℕ) :
    Finset (Option (ℕ × ℕ)) :=
  if h : 1 ≤ v.val then ((dom c k P A N (boxB c v) g (yU₁ h) (yU₂ hc h)).filter
    (fun pq => pq.1 ≠ a₀ ∧ pq.2 ≠ x₀)).map Function.Embedding.some else {none}

variable (c k P A N) in
/-- Options on the lower domino after the shift. -/
noncomputable def optD' (hc : 1 ≤ c) (v : Fin m) (a₀ x₀ : ℕ) (g : Cell c m → ℕ) :
    Finset (Option (ℕ × ℕ)) :=
  if h : v.val + 1 < m then ((dom c k P A N (boxB c v) g (yD₁ h) (yD₂ hc h)).filter
    (fun pq => pq.1 ≠ a₀ ∧ pq.2 ≠ x₀)).map Function.Embedding.some else {none}

/-- Fill the box from independent choices, around the shifted centre. -/
def fill (hc : 1 ≤ c) (v : Fin m) (a₀ x₀ : ℕ) (g : Cell c m → ℕ)
    (t : ℕ × Option ℕ × Option (ℕ × ℕ) × Option (ℕ × ℕ)) : Cell c m → ℕ := fun y =>
  if y.2.val = v.val ∧ y.1.val = 0 then t.1
  else if y.2.val = v.val ∧ y.1.val = 3 then t.2.1.getD 0
  else if y.2.val + 1 = v.val ∧ y.1.val = 1 then (t.2.2.1.getD (0, 0)).1
  else if y.2.val + 1 = v.val ∧ y.1.val = 2 then (t.2.2.1.getD (0, 0)).2
  else if y.2.val = v.val + 1 ∧ y.1.val = 1 then (t.2.2.2.getD (0, 0)).1
  else if y.2.val = v.val + 1 ∧ y.1.val = 2 then (t.2.2.2.getD (0, 0)).2
  else shift hc v a₀ x₀ g y

theorem fill_off (hc : 1 ≤ c) {v : Fin m} {a₀ x₀ : ℕ} {g : Cell c m → ℕ} {t}
    {y : Cell c m} (hy : ¬ inY v y) : fill hc v a₀ x₀ g t y = shift hc v a₀ x₀ g y := by
  unfold inY inB at hy
  unfold fill
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

theorem fill_y₁ (hc : 1 ≤ c) (v : Fin m) (a₀ x₀ : ℕ) (g : Cell c m → ℕ) (t) :
    fill hc v a₀ x₀ g t (y₁ v) = t.1 := by
  unfold fill y₁; simp

theorem fill_y₆ (hc : 1 ≤ c) (v : Fin m) (a₀ x₀ : ℕ) (g : Cell c m → ℕ) (t) (h : 2 ≤ c) :
    fill hc v a₀ x₀ g t (y₆ h v) = t.2.1.getD 0 := by
  unfold fill y₆; simp

theorem fill_yU₁ (hc : 1 ≤ c) {v : Fin m} (a₀ x₀ : ℕ) (g : Cell c m → ℕ) (t) (h : 1 ≤ v.val) :
    fill hc v a₀ x₀ g t (yU₁ h) = (t.2.2.1.getD (0, 0)).1 := by
  have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  unfold fill yU₁; dsimp only; rw [h1]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]

theorem fill_yU₂ (hc : 1 ≤ c) {v : Fin m} (a₀ x₀ : ℕ) (g : Cell c m → ℕ) (t) (h : 1 ≤ v.val) :
    fill hc v a₀ x₀ g t (yU₂ hc h) = (t.2.2.1.getD (0, 0)).2 := by
  unfold fill yU₂ fut0; dsimp only
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]

theorem fill_yD₁ (hc : 1 ≤ c) {v : Fin m} (a₀ x₀ : ℕ) (g : Cell c m → ℕ) (t)
    (h : v.val + 1 < m) : fill hc v a₀ x₀ g t (yD₁ h) = (t.2.2.2.getD (0, 0)).1 := by
  have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  unfold fill yD₁; dsimp only; rw [h1]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]

theorem fill_yD₂ (hc : 1 ≤ c) {v : Fin m} (a₀ x₀ : ℕ) (g : Cell c m → ℕ) (t)
    (h : v.val + 1 < m) : fill hc v a₀ x₀ g t (yD₂ hc h) = (t.2.2.2.getD (0, 0)).2 := by
  unfold fill yD₂ fut0; dsimp only
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos (by omega)]

end Lower

section Lower2

theorem mem_of_opt6' {v : Fin m} {x₀ : ℕ} {g : Cell c m → ℕ} {o : Option ℕ} (h : 2 ≤ c)
    (ho : o ∈ opt6' c k P A N v x₀ g) : ∃ q, o = some q ∧
      q ∈ ((slab c m k P A N).avail (boxB c v) g (y₆ h v)).erase x₀ := by
  unfold opt6' at ho; rw [dif_pos h, mem_map] at ho
  obtain ⟨q, hq, rfl⟩ := ho; exact ⟨q, rfl, hq⟩

theorem eq_none_of_opt6' {v : Fin m} {x₀ : ℕ} {g : Cell c m → ℕ} {o : Option ℕ} (h : ¬ 2 ≤ c)
    (ho : o ∈ opt6' c k P A N v x₀ g) : o = none := by
  unfold opt6' at ho; rw [dif_neg h, mem_singleton] at ho; exact ho

theorem mem_of_optU' (hc : 1 ≤ c) {v : Fin m} {a₀ x₀ : ℕ} {g : Cell c m → ℕ}
    {o : Option (ℕ × ℕ)} (h : 1 ≤ v.val) (ho : o ∈ optU' c k P A N hc v a₀ x₀ g) :
    ∃ pq, o = some pq ∧ pq ∈ dom c k P A N (boxB c v) g (yU₁ h) (yU₂ hc h) ∧
      pq.1 ≠ a₀ ∧ pq.2 ≠ x₀ := by
  unfold optU' at ho; rw [dif_pos h, mem_map] at ho
  obtain ⟨pq, hpq, rfl⟩ := ho; rw [mem_filter] at hpq; exact ⟨pq, rfl, hpq.1, hpq.2⟩

theorem eq_none_of_optU' (hc : 1 ≤ c) {v : Fin m} {a₀ x₀ : ℕ} {g : Cell c m → ℕ}
    {o : Option (ℕ × ℕ)} (h : ¬ 1 ≤ v.val) (ho : o ∈ optU' c k P A N hc v a₀ x₀ g) :
    o = none := by
  unfold optU' at ho; rw [dif_neg h, mem_singleton] at ho; exact ho

theorem mem_of_optD' (hc : 1 ≤ c) {v : Fin m} {a₀ x₀ : ℕ} {g : Cell c m → ℕ}
    {o : Option (ℕ × ℕ)} (h : v.val + 1 < m) (ho : o ∈ optD' c k P A N hc v a₀ x₀ g) :
    ∃ pq, o = some pq ∧ pq ∈ dom c k P A N (boxB c v) g (yD₁ h) (yD₂ hc h) ∧
      pq.1 ≠ a₀ ∧ pq.2 ≠ x₀ := by
  unfold optD' at ho; rw [dif_pos h, mem_map] at ho
  obtain ⟨pq, hpq, rfl⟩ := ho; rw [mem_filter] at hpq; exact ⟨pq, rfl, hpq.1, hpq.2⟩

theorem eq_none_of_optD' (hc : 1 ≤ c) {v : Fin m} {a₀ x₀ : ℕ} {g : Cell c m → ℕ}
    {o : Option (ℕ × ℕ)} (h : ¬ v.val + 1 < m) (ho : o ∈ optD' c k P A N hc v a₀ x₀ g) :
    o = none := by
  unfold optD' at ho; rw [dif_neg h, mem_singleton] at ho; exact ho

theorem mem_dom_iff {U : Finset (Cell c m)} {g : Cell c m → ℕ} {y y' : Cell c m} {pq : ℕ × ℕ} :
    pq ∈ dom c k P A N U g y y' ↔ (pq.1 ∈ (slab c m k P A N).avail U g y ∧
      pq.2 ∈ (slab c m k P A N).avail U g y') ∧
        ¬ (slab c m k P A N).conf y y' pq.1 pq.2 ∧ ¬ (slab c m k P A N).conf y' y pq.2 pq.1 := by
  unfold dom; rw [mem_filter, mem_product]

/-- **Lower bound on a fibre.** -/
theorem card_hit_ge (hc : 1 ≤ c) (v : Fin m) {a₀ x₀ : ℕ} {g : Cell c m → ℕ}
    (hg : (slab c m k P A N).Valid g) (ha : a₀ ∈ A v) (hx : x₀ < k) (hN : k ≤ N v a₀) :
    (((slab c m k P A N).avail (boxB c v) g (y₁ v)).erase a₀).card *
        (opt6' c k P A N v x₀ g).card * (optU' c k P A N hc v a₀ x₀ g).card *
          (optD' c k P A N hc v a₀ x₀ g).card ≤
      (((slab c m k P A N).cls (boxB c v) g).filter (Hit hc v a₀ x₀)).card := by
  set C := slab c m k P A N
  set S := ((C.avail (boxB c v) g (y₁ v)).erase a₀ ×ˢ opt6' c k P A N v x₀ g ×ˢ
    optU' c k P A N hc v a₀ x₀ g ×ˢ optD' c k P A N hc v a₀ x₀ g)
  have hS : S.card = ((C.avail (boxB c v) g (y₁ v)).erase a₀).card *
      (opt6' c k P A N v x₀ g).card * (optU' c k P A N hc v a₀ x₀ g).card *
        (optD' c k P A N hc v a₀ x₀ g).card := by
    simp only [S, card_product]; ring
  rw [← hS]
  have hval := validOff_shift (P := P) hc hg ha hx hN
  refine card_le_card_of_injOn (fill hc v a₀ x₀ g) ?_ ?_
  · intro t ht
    simp only [S, coe_product, Set.mem_prod, mem_coe] at ht
    obtain ⟨h1, h6, hU, hD⟩ := ht
    -- the filled assignment is in the fibre over `Y` of the shifted base
    have hY : fill hc v a₀ x₀ g t ∈ C.cls (boxY c v) (shift hc v a₀ x₀ g) := by
      refine C.mem_cls_of hval (fun x hx => fill_off hc (by rwa [mem_boxY] at hx))
        (fun u hu => ?_) (fun u u' hu hu' hadj => ?_)
      · rw [mem_boxY] at hu
        rcases inY_cases hc hu with rfl | ⟨h, rfl⟩ | ⟨h, rfl | rfl⟩ | ⟨h, rfl | rfl⟩
        · rw [fill_y₁]
          rw [mem_erase] at h1
          exact mem_avail_shift hc (y₁_inY v) h1.2 (by simp [fz, y₁, h1.1])
        · obtain ⟨q, hq, hq'⟩ := mem_of_opt6' h h6
          rw [fill_y₆, hq, Option.getD_some]
          rw [mem_erase] at hq'
          exact mem_avail_shift hc (y₆_inY h v) hq'.2 (by simp [fz, y₆, hq'.1])
        · obtain ⟨pq, hpq, hd, hne⟩ := mem_of_optU' hc h hU
          rw [fill_yU₁, hpq, Option.getD_some]
          have h1v : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
          exact mem_avail_shift hc (yU₁_inY h) ((mem_dom_iff.mp hd).1.1)
            (by simp only [fz, yU₁, h1v, le_refl, if_true]; exact hne.1)
        · obtain ⟨pq, hpq, hd, hne⟩ := mem_of_optU' hc h hU
          rw [fill_yU₂, hpq, Option.getD_some]
          exact mem_avail_shift hc (yU₂_inY hc h) ((mem_dom_iff.mp hd).1.2)
            (by simp only [fz, yU₂, fut0]; exact hne.2)
        · obtain ⟨pq, hpq, hd, hne⟩ := mem_of_optD' hc h hD
          rw [fill_yD₁, hpq, Option.getD_some]
          have h1v : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
          exact mem_avail_shift hc (yD₁_inY h) ((mem_dom_iff.mp hd).1.1)
            (by simp only [fz, yD₁, h1v, le_refl, if_true]; exact hne.1)
        · obtain ⟨pq, hpq, hd, hne⟩ := mem_of_optD' hc h hD
          rw [fill_yD₂, hpq, Option.getD_some]
          exact mem_avail_shift hc (yD₂_inY hc h) ((mem_dom_iff.mp hd).1.2)
            (by simp only [fz, yD₂, fut0]; exact hne.2)
      · rw [mem_boxY] at hu hu'
        obtain ⟨hrow, hcol⟩ := adj_in_Y hu hu' hadj
        have hu2 := hu
        unfold inY inB at hu2
        have hr : u.2.val + 1 = v.val ∨ u.2.val = v.val + 1 := by omega
        have h1v : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
        rcases hr with hr | hr
        · have h : 1 ≤ v.val := by omega
          obtain ⟨pq, hpq, hd, -⟩ := mem_of_optU' hc h hU
          have e1 : ∀ y : Cell c m, y.2 = u.2 → y.1.val = 1 → y = yU₁ h := fun y hy hc1 =>
            cell_eq (by simp [yU₁, hc1, h1v]) (by simp [yU₁, hy]; omega)
          have e2 : ∀ y : Cell c m, y.2 = u.2 → y.1.val = 2 → y = yU₂ hc h := fun y hy hc2 =>
            cell_eq (by simp [yU₂, fut0, hc2]) (by simp [yU₂, hy]; omega)
          have hd' := (mem_dom_iff.mp hd).2
          rcases hcol with ⟨hc1, hc2⟩ | ⟨hc2, hc1⟩
          · rw [e1 u rfl hc1, e2 u' hrow.symm hc2, fill_yU₁, fill_yU₂, hpq]
            exact hd'.1
          · rw [e2 u rfl hc2, e1 u' hrow.symm hc1, fill_yU₁, fill_yU₂, hpq]
            exact hd'.2
        · have h : v.val + 1 < m := by have := u.2.isLt; omega
          obtain ⟨pq, hpq, hd, -⟩ := mem_of_optD' hc h hD
          have e1 : ∀ y : Cell c m, y.2 = u.2 → y.1.val = 1 → y = yD₁ h := fun y hy hc1 =>
            cell_eq (by simp [yD₁, hc1, h1v]) (by simp [yD₁, hy]; omega)
          have e2 : ∀ y : Cell c m, y.2 = u.2 → y.1.val = 2 → y = yD₂ hc h := fun y hy hc2 =>
            cell_eq (by simp [yD₂, fut0, hc2]) (by simp [yD₂, hy]; omega)
          have hd' := (mem_dom_iff.mp hd).2
          rcases hcol with ⟨hc1, hc2⟩ | ⟨hc2, hc1⟩
          · rw [e1 u rfl hc1, e2 u' hrow.symm hc2, fill_yD₁, fill_yD₂, hpq]
            exact hd'.1
          · rw [e2 u rfl hc2, e1 u' hrow.symm hc1, fill_yD₁, fill_yD₂, hpq]
            exact hd'.2
    rw [mem_coe, mem_filter]
    have hYv := (C.mem_cls).mp hY
    refine ⟨(C.mem_cls).mpr ⟨hYv.1, fun x hx => ?_⟩, ?_, ?_⟩
    · have hxB : ¬ inB v x := by rwa [mem_boxB] at hx
      have hxY : x ∉ boxY c v := by rw [mem_boxY]; exact fun h => hxB h.1
      have h1 : x ≠ z₁ v := by rintro rfl; exact hxB ((inB_iff hc).mpr (Or.inr (Or.inl rfl)))
      have h2 : x ≠ z₂ hc v := by rintro rfl; exact hxB ((inB_iff hc).mpr (Or.inr (Or.inr rfl)))
      rw [hYv.2 x hxY, shift_of_ne hc h1 h2]
    · show fill hc v a₀ x₀ g t (z₁ v) = a₀
      rw [fill_off hc (z₁_notMem_Y v), shift_z₁]
    · show fill hc v a₀ x₀ g t (z₂ hc v) = x₀
      rw [fill_off hc (z₂_notMem_Y hc v), shift_z₂]
  · intro t ht t' ht' he
    simp only [S, coe_product, Set.mem_prod, mem_coe] at ht ht'
    obtain ⟨_, h6, hU, hD⟩ := ht
    obtain ⟨_, h6', hU', hD'⟩ := ht'
    obtain ⟨t1, t6, tU, tD⟩ := t
    obtain ⟨t1', t6', tU', tD'⟩ := t'
    dsimp only at h6 h6' hU hU' hD hD'
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := congrFun he (y₁ v); rwa [fill_y₁, fill_y₁] at this
    · by_cases h : 2 ≤ c
      · obtain ⟨q, rfl, -⟩ := mem_of_opt6' h h6
        obtain ⟨q', rfl, -⟩ := mem_of_opt6' h h6'
        have := congrFun he (y₆ h v)
        rw [fill_y₆, fill_y₆] at this
        simpa using this
      · rw [eq_none_of_opt6' h h6, eq_none_of_opt6' h h6']
    · by_cases h : 1 ≤ v.val
      · obtain ⟨pq, rfl, -⟩ := mem_of_optU' hc h hU
        obtain ⟨pq', rfl, -⟩ := mem_of_optU' hc h hU'
        have e1 := congrFun he (yU₁ h)
        have e2 := congrFun he (yU₂ hc h)
        rw [fill_yU₁, fill_yU₁] at e1
        rw [fill_yU₂, fill_yU₂] at e2
        simp only [Option.getD_some] at e1 e2
        rw [Prod.ext e1 e2]
      · rw [eq_none_of_optU' hc h hU, eq_none_of_optU' hc h hU']
    · by_cases h : v.val + 1 < m
      · obtain ⟨pq, rfl, -⟩ := mem_of_optD' hc h hD
        obtain ⟨pq', rfl, -⟩ := mem_of_optD' hc h hD'
        have e1 := congrFun he (yD₁ h)
        have e2 := congrFun he (yD₂ hc h)
        rw [fill_yD₁, fill_yD₁] at e1
        rw [fill_yD₂, fill_yD₂] at e2
        simp only [Option.getD_some] at e1 e2
        rw [Prod.ext e1 e2]
      · rw [eq_none_of_optD' hc h hD, eq_none_of_optD' hc h hD']

end Lower2

/-! ### Counting the box -/

section Count

theorem card_le_one_of_coords (S : Finset (Cell c m)) (a b : ℕ)
    (h : ∀ w ∈ S, w.1.val = a ∧ w.2.val = b) : S.card ≤ 1 :=
  card_le_one.mpr fun w hw w' hw' =>
    cell_eq ((h w hw).1.trans (h w' hw').1.symm) ((h w hw).2.trans (h w' hw').2.symm)

theorem card_le_of_coords (S : Finset (Cell c m)) (L : List (ℕ × ℕ))
    (h : ∀ w ∈ S, (w.1.val, w.2.val) ∈ L) : S.card ≤ L.length := by
  calc S.card ≤ L.toFinset.card := by
        refine card_le_card_of_injOn (fun w => (w.1.val, w.2.val)) (fun w hw => ?_) ?_
        · simpa using h w hw
        · intro w _ w' _ he
          simp only [Prod.mk.injEq] at he
          exact cell_eq he.1 he.2
    _ ≤ L.length := List.toFinset_card_le L

/-- Neighbours of a cell, by coordinates. -/
theorem adj_coords {y w : Cell c m} (h : (slab c m k P A N).adj y w ∨ (slab c m k P A N).adj w y) :
    (w.1.val = y.1.val ∧ (w.2.val + 1 = y.2.val ∨ w.2.val = y.2.val + 1)) ∨
      (w.2.val = y.2.val ∧ (w.1.val + 1 = y.1.val ∨ w.1.val = y.1.val + 1)) := by
  have h' : slabAdj y w ∨ slabAdj w y := h
  unfold slabAdj at h'
  rcases h' with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · left; exact ⟨by rw [h1], by omega⟩
  · right; exact ⟨by rw [h1], by omega⟩
  · left; exact ⟨by rw [h1], by omega⟩
  · right; exact ⟨by rw [h1], by omega⟩

theorem nbrsOut_y₁ (v : Fin m) :
    ((slab c m k P A N).nbrsOut (y₁ v) (boxB c v)).card ≤ 2 := by
  refine card_le_of_coords _ [(0, v.val - 1), (0, v.val + 1)] fun w hw => ?_
  rw [CSP.mem_nbrsOut, mem_boxB] at hw
  have hc := adj_coords hw.1
  have hB := hw.2
  have hy1 : (y₁ (c := c) v).1.val = 0 := rfl
  have hy2 : (y₁ (c := c) v).2.val = v.val := rfl
  rw [hy1, hy2] at hc
  unfold inB at hB
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  omega

theorem nbrsOut_y₆ (h : 2 ≤ c) (v : Fin m) :
    ((slab c m k P A N).nbrsOut (y₆ h v) (boxB c v)).card ≤ 3 := by
  refine card_le_of_coords _ [(4, v.val), (3, v.val - 1), (3, v.val + 1)] fun w hw => ?_
  rw [CSP.mem_nbrsOut, mem_boxB] at hw
  have hc := adj_coords hw.1
  have hB := hw.2
  have hy1 : (y₆ h v).1.val = 3 := rfl
  have hy2 : (y₆ h v).2.val = v.val := rfl
  rw [hy1, hy2] at hc
  unfold inB at hB
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  omega

theorem nbrsOut_yU₁ {v : Fin m} (h : 1 ≤ v.val) :
    ((slab c m k P A N).nbrsOut (yU₁ h) (boxB c v)).card ≤ 2 := by
  have h1v : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  refine card_le_of_coords _ [(0, v.val - 1), (1, v.val - 2)] fun w hw => ?_
  rw [CSP.mem_nbrsOut, mem_boxB] at hw
  have hc := adj_coords hw.1
  have hB := hw.2
  have hy1 : (yU₁ (c := c) h).1.val = 1 := h1v
  have hy2 : (yU₁ (c := c) h).2.val = v.val - 1 := rfl
  rw [hy1, hy2] at hc
  unfold inB at hB
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  omega

theorem nbrsOut_yU₂ (hc : 1 ≤ c) {v : Fin m} (h : 1 ≤ v.val) :
    ((slab c m k P A N).nbrsOut (yU₂ hc h) (boxB c v)).card ≤ 2 := by
  refine card_le_of_coords _ [(3, v.val - 1), (2, v.val - 2)] fun w hw => ?_
  rw [CSP.mem_nbrsOut, mem_boxB] at hw
  have hcc := adj_coords hw.1
  have hB := hw.2
  have hy1 : (yU₂ hc h).1.val = 2 := rfl
  have hy2 : (yU₂ hc h).2.val = v.val - 1 := rfl
  rw [hy1, hy2] at hcc
  unfold inB at hB
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  omega

theorem nbrsOut_yD₁ {v : Fin m} (h : v.val + 1 < m) :
    ((slab c m k P A N).nbrsOut (yD₁ h) (boxB c v)).card ≤ 2 := by
  have h1v : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  refine card_le_of_coords _ [(0, v.val + 1), (1, v.val + 2)] fun w hw => ?_
  rw [CSP.mem_nbrsOut, mem_boxB] at hw
  have hc := adj_coords hw.1
  have hB := hw.2
  have hy1 : (yD₁ (c := c) h).1.val = 1 := h1v
  have hy2 : (yD₁ (c := c) h).2.val = v.val + 1 := rfl
  rw [hy1, hy2] at hc
  unfold inB at hB
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  omega

theorem nbrsOut_yD₂ (hc : 1 ≤ c) {v : Fin m} (h : v.val + 1 < m) :
    ((slab c m k P A N).nbrsOut (yD₂ hc h) (boxB c v)).card ≤ 2 := by
  refine card_le_of_coords _ [(3, v.val + 1), (2, v.val + 2)] fun w hw => ?_
  rw [CSP.mem_nbrsOut, mem_boxB] at hw
  have hcc := adj_coords hw.1
  have hB := hw.2
  have hy1 : (yD₂ hc h).1.val = 2 := rfl
  have hy2 : (yD₂ hc h).2.val = v.val + 1 := rfl
  rw [hy1, hy2] at hcc
  unfold inB at hB
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  omega

end Count

section Arith

/-- Pairs of a domino: each colour at `y` excludes at most one colour at `y'`. -/
theorem card_dom_ge (hK : KeyInj k A N) {U : Finset (Cell c m)} {g : Cell c m → ℕ}
    {y y' : Cell c m} :
    ((slab c m k P A N).avail U g y).card * (((slab c m k P A N).avail U g y').card - 1) ≤
      (dom c k P A N U g y y').card := by
  set C := slab c m k P A N
  set A₁ := C.avail U g y
  set A₂ := C.avail U g y'
  have hsum : (dom c k P A N U g y y').card =
      ∑ p ∈ A₁, (A₂.filter (fun q => ¬ C.conf y y' p q ∧ ¬ C.conf y' y q p)).card := by
    unfold dom
    rw [card_filter, sum_product]
    refine sum_congr rfl fun p _ => ?_
    rw [card_filter]
  rw [hsum]
  calc A₁.card * (A₂.card - 1) = ∑ _p ∈ A₁, (A₂.card - 1) := by rw [sum_const, smul_eq_mul]
    _ ≤ _ := sum_le_sum fun p hp => ?_
  have hpD : p ∈ C.D y := (C.mem_avail.mp hp).1
  have hbad : (A₂.filter (fun q => ¬ ¬ (C.conf y y' p q ∨ C.conf y' y q p))).card ≤ 1 := by
    refine card_le_one.mpr fun q hq q' hq' => ?_
    rw [mem_filter, not_not] at hq hq'
    exact slab_match hK y' y p hpD q q' (C.mem_avail.mp hq.1).1 (C.mem_avail.mp hq'.1).1
      (hq.2.symm) (hq'.2.symm)
  have := card_filter_add_card_filter_not (s := A₂)
    (fun q => ¬ (C.conf y y' p q ∨ C.conf y' y q p))
  have e : A₂.filter (fun q => ¬ C.conf y y' p q ∧ ¬ C.conf y' y q p) =
      A₂.filter (fun q => ¬ (C.conf y y' p q ∨ C.conf y' y q p)) := by
    ext q; simp only [mem_filter, not_or]
  rw [e]
  omega

/-- Prescribing one end of a domino costs at most the other end's colours. -/
theorem card_dom_filter_ge {U : Finset (Cell c m)} {g : Cell c m → ℕ} {y y' : Cell c m}
    (a₀ x₀ : ℕ) :
    (dom c k P A N U g y y').card ≤ ((dom c k P A N U g y y').filter
      (fun pq => pq.1 ≠ a₀ ∧ pq.2 ≠ x₀)).card +
        ((slab c m k P A N).avail U g y').card + ((slab c m k P A N).avail U g y).card := by
  set D := dom c k P A N U g y y'
  have h1 : (D.filter (fun pq => pq.1 = a₀)).card ≤ ((slab c m k P A N).avail U g y').card := by
    refine card_le_card_of_injOn (fun pq => pq.2) (fun pq hpq => ?_) (fun pq hpq pq' hpq' he => ?_)
    · rw [mem_coe, mem_filter, mem_dom_iff] at hpq; exact hpq.1.1.2
    · rw [mem_coe, mem_filter] at hpq hpq'
      exact Prod.ext (hpq.2.trans hpq'.2.symm) he
  have h2 : (D.filter (fun pq => pq.2 = x₀)).card ≤ ((slab c m k P A N).avail U g y).card := by
    refine card_le_card_of_injOn (fun pq => pq.1) (fun pq hpq => ?_) (fun pq hpq pq' hpq' he => ?_)
    · rw [mem_coe, mem_filter, mem_dom_iff] at hpq; exact hpq.1.1.1
    · rw [mem_coe, mem_filter] at hpq hpq'
      exact Prod.ext he (hpq.2.trans hpq'.2.symm)
  have hsub : D ⊆ D.filter (fun pq => pq.1 ≠ a₀ ∧ pq.2 ≠ x₀) ∪
      (D.filter (fun pq => pq.1 = a₀) ∪ D.filter (fun pq => pq.2 = x₀)) := by
    intro pq hpq
    simp only [mem_union, mem_filter]
    by_cases ha : pq.1 = a₀
    · exact Or.inr (Or.inl ⟨hpq, ha⟩)
    by_cases hx : pq.2 = x₀
    · exact Or.inr (Or.inr ⟨hpq, hx⟩)
    exact Or.inl ⟨hpq, ha, hx⟩
  calc D.card ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left (card_union_le _ _) _
    _ ≤ _ := by omega

/-- The domino inequality: `(k-5)τ ≤ (k-3)s`. -/
theorem dom_arith {k α₂ α₃ τ s : ℕ} (hk : 5 ≤ k) (h2 : k - 2 ≤ α₂) (h3 : k - 2 ≤ α₃)
    (hτ : α₂ * (α₃ - 1) ≤ τ) (hs : τ ≤ s + α₃ + α₂) : (k - 5) * τ ≤ (k - 3) * s := by
  have h3' : 1 ≤ α₃ := by omega
  have e1 : ((α₃ - 1 : ℕ) : ℤ) = α₃ - 1 := by push_cast [Nat.cast_sub h3']; ring
  have hτ' : (α₂ : ℤ) * (α₃ - 1) ≤ τ := by rw [← e1]; exact_mod_cast hτ
  have hk5 : ((k - 5 : ℕ) : ℤ) = k - 5 := by push_cast [Nat.cast_sub hk]; ring
  have hk3 : ((k - 3 : ℕ) : ℤ) = k - 3 := by
    push_cast [Nat.cast_sub (show 3 ≤ k by omega)]; ring
  have h2' : (k : ℤ) - 2 ≤ α₂ := by
    have := Nat.cast_le (α := ℤ) |>.mpr h2; push_cast [Nat.cast_sub (show 2 ≤ k by omega)] at this
    linarith
  have h3'' : (k : ℤ) - 2 ≤ α₃ := by
    have := Nat.cast_le (α := ℤ) |>.mpr h3; push_cast [Nat.cast_sub (show 2 ≤ k by omega)] at this
    linarith
  have hs' : (τ : ℤ) ≤ s + α₃ + α₂ := by exact_mod_cast hs
  have hk' : (5 : ℤ) ≤ k := by exact_mod_cast hk
  suffices h : ((k : ℤ) - 5) * τ ≤ ((k : ℤ) - 3) * s by
    have := h; rw [← hk5, ← hk3] at this; exact_mod_cast this
  nlinarith [mul_le_mul_of_nonneg_left h2' (show (0 : ℤ) ≤ α₃ - 1 by linarith),
    mul_le_mul_of_nonneg_left h3'' (show (0 : ℤ) ≤ (k : ℤ) - 1 by linarith)]

/-- The single-cell inequality: `(k-4)α ≤ (k-3)(α-1)` once `α ≥ k-3`. -/
theorem single_arith {k α : ℕ} (hk : 4 ≤ k) (h : k - 3 ≤ α) : (k - 4) * α ≤ (k - 3) * (α - 1) := by
  rcases Nat.eq_zero_or_pos α with rfl | hα
  · simp
  have e : (k - 3) * (α - 1) = (k - 3) * α - (k - 3) := by rw [Nat.mul_sub, mul_one]
  have e2 : (k - 3) * α = (k - 4) * α + α := by
    rw [show k - 3 = (k - 4) + 1 by omega, add_mul, one_mul]
  rw [e, e2]
  omega

end Arith

section Final

theorem card_some_image {α : Type*} (S : Finset α) :
    (S.map Function.Embedding.some).card = S.card :=
  card_map _

/-- A cell of the future has `k` colours less the neighbours off the box. -/
theorem card_avail_fut_ge (hK : KeyInj k A N) {v : Fin m} {g : Cell c m → ℕ}
    (hg : (slab c m k P A N).Valid g) {y : Cell c m} (hy : inB v y) (hy2 : 2 ≤ y.1.val) :
    k - ((slab c m k P A N).nbrsOut y (boxB c v)).card ≤
      ((slab c m k P A N).avail (boxB c v) g y).card := by
  have := (slab c m k P A N).card_avail_ge (slab_match hK) slab_irrefl (mem_boxB.mpr hy)
    (fun x _ => hg.1 x)
  rwa [slab_D_fut hy2, card_range] at this

/-- **The box inequality on one fibre.** -/
theorem box_fibre (hk : 6 ≤ k) (hK : KeyInj k A N) (hA : ∀ v, (A v).card = k) (hc : 1 ≤ c)
    (v : Fin m) {a₀ x₀ : ℕ} (ha : a₀ ∈ A v) (hx : x₀ < k) (hN : k ≤ N v a₀)
    (hPv : k - 1 ≤ (P v).card ∨ a₀ ∉ P v) {g : Cell c m → ℕ}
    (hg : (slab c m k P A N).Valid g) :
    ((slab c m k P A N).cls (boxB c v) g).card * ((k - 4) ^ 2 * (k - 5) ^ 2) ≤
      (((slab c m k P A N).cls (boxB c v) g).filter (Hit hc v a₀ x₀)).card *
        (k ^ 2 * (k - 3) ^ 4) := by
  have hM := slab_match (c := c) (P := P) hK
  have hI : (slab c m k P A N : CSP (Cell c m)).Irrefl := slab_irrefl
  have hgD : ∀ x, x ∉ boxB c v → g x ∈ (slab c m k P A N).D x := fun x _ => hg.1 x
  -- the single cell `y₁`
  have h₁ : (k - 4) * ((slab c m k P A N).avail (boxB c v) g (y₁ v)).card ≤ (k - 3) * (((slab c m k P A N).avail (boxB c v) g (y₁ v)).erase a₀).card := by
    by_cases hm : a₀ ∈ (slab c m k P A N).avail (boxB c v) g (y₁ v)
    · have hP : a₀ ∈ P v := by
        have := ((slab c m k P A N).mem_avail.mp hm).1; rwa [slab_D_zero rfl] at this
      have hPc : k - 1 ≤ (P v).card := hPv.resolve_right (not_not.mpr hP)
      have hav := (slab c m k P A N).card_avail_ge hM hI (mem_boxB.mpr (y₁_inY (c := c) v).1) hgD
      rw [slab_D_zero rfl] at hav
      change (P v).card - _ ≤ _ at hav
      have hn := nbrsOut_y₁ (c := c) (k := k) (P := P) (A := A) (N := N) v
      rw [card_erase_of_mem hm]
      exact single_arith (by omega) (by omega)
    · rw [erase_eq_of_notMem hm]
      exact Nat.mul_le_mul_right _ (by omega)
  -- the single cell `y₆`
  have h₆ : (k - 4) * (opt6 c k P A N v g).card ≤ (k - 3) * (opt6' c k P A N v x₀ g).card := by
    unfold opt6 opt6'
    split_ifs with h
    · rw [card_some_image, card_some_image]
      by_cases hm : x₀ ∈ (slab c m k P A N).avail (boxB c v) g (y₆ h v)
      · rw [card_erase_of_mem hm]
        have hav := card_avail_fut_ge hK hg (y₆_inY h v).1 (show 2 ≤ (y₆ h v).1.val by
          show 2 ≤ 3; omega)
        have hn := nbrsOut_y₆ (k := k) (P := P) (A := A) (N := N) h v
        exact single_arith (by omega) (by omega)
      · rw [erase_eq_of_notMem hm]; exact Nat.mul_le_mul_right _ (by omega)
    · simp only [card_singleton, mul_one]; omega
  -- the dominoes
  have hdom : ∀ {y y' : Cell c m}, inY v y → inY v y' → k - 2 ≤ ((slab c m k P A N).avail (boxB c v) g y).card →
      k - 2 ≤ ((slab c m k P A N).avail (boxB c v) g y').card →
      (k - 5) * (dom c k P A N (boxB c v) g y y').card ≤
        (k - 3) * ((dom c k P A N (boxB c v) g y y').filter
          (fun pq => pq.1 ≠ a₀ ∧ pq.2 ≠ x₀)).card := by
    intro y y' _ _ h2 h3
    exact dom_arith (by omega) h2 h3 (card_dom_ge hK) (by
      have := card_dom_filter_ge (c := c) (k := k) (P := P) (A := A) (N := N)
        (U := boxB c v) (g := g) (y := y) (y' := y') a₀ x₀
      omega)
  have hU : (k - 5) * (optU c k P A N hc v g).card ≤ (k - 3) * (optU' c k P A N hc v a₀ x₀ g).card := by
    unfold optU optU'
    split_ifs with h
    · rw [card_some_image, card_some_image]
      refine hdom (yU₁_inY h) (yU₂_inY hc h) ?_ ?_
      · have hav := (slab c m k P A N).card_avail_ge hM hI (mem_boxB.mpr (yU₁_inY (c := c) h).1) hgD
        rw [slab_D_one (show (yU₁ (c := c) h).1.val = 1 from Fin.val_one _), hA] at hav
        have hn := nbrsOut_yU₁ (c := c) (k := k) (P := P) (A := A) (N := N) h
        omega
      · have hav := card_avail_fut_ge hK hg (yU₂_inY hc h).1 (show 2 ≤ (yU₂ hc h).1.val from le_rfl)
        have hn := nbrsOut_yU₂ (k := k) (P := P) (A := A) (N := N) hc h
        omega
    · simp only [card_singleton, mul_one]; omega
  have hD : (k - 5) * (optD c k P A N hc v g).card ≤ (k - 3) * (optD' c k P A N hc v a₀ x₀ g).card := by
    unfold optD optD'
    split_ifs with h
    · rw [card_some_image, card_some_image]
      refine hdom (yD₁_inY h) (yD₂_inY hc h) ?_ ?_
      · have hav := (slab c m k P A N).card_avail_ge hM hI (mem_boxB.mpr (yD₁_inY (c := c) h).1) hgD
        rw [slab_D_one (show (yD₁ (c := c) h).1.val = 1 from Fin.val_one _), hA] at hav
        have hn := nbrsOut_yD₁ (c := c) (k := k) (P := P) (A := A) (N := N) h
        omega
      · have hav := card_avail_fut_ge hK hg (yD₂_inY hc h).1 (show 2 ≤ (yD₂ hc h).1.val from le_rfl)
        have hn := nbrsOut_yD₂ (k := k) (P := P) (A := A) (N := N) hc h
        omega
    · simp only [card_singleton, mul_one]; omega
  -- assemble
  have hup := card_cls_le (k := k) (P := P) (A := A) (N := N) hc v g
  rw [hA] at hup
  have hlo := card_hit_ge (P := P) hc v hg ha hx hN
  calc ((slab c m k P A N).cls (boxB c v) g).card * ((k - 4) ^ 2 * (k - 5) ^ 2)
      ≤ (k * k * ((slab c m k P A N).avail (boxB c v) g (y₁ v)).card * (opt6 c k P A N v g).card * (optU c k P A N hc v g).card *
          (optD c k P A N hc v g).card) * ((k - 4) ^ 2 * (k - 5) ^ 2) :=
        Nat.mul_le_mul_right _ hup
    _ = k ^ 2 * (((k - 4) * ((slab c m k P A N).avail (boxB c v) g (y₁ v)).card) * ((k - 4) * (opt6 c k P A N v g).card) *
          ((k - 5) * (optU c k P A N hc v g).card) * ((k - 5) * (optD c k P A N hc v g).card)) := by
        ring
    _ ≤ k ^ 2 * (((k - 3) * (((slab c m k P A N).avail (boxB c v) g (y₁ v)).erase a₀).card) * ((k - 3) * (opt6' c k P A N v x₀ g).card) *
          ((k - 3) * (optU' c k P A N hc v a₀ x₀ g).card) *
            ((k - 3) * (optD' c k P A N hc v a₀ x₀ g).card)) := by
        gcongr
    _ = ((((slab c m k P A N).avail (boxB c v) g (y₁ v)).erase a₀).card * (opt6' c k P A N v x₀ g).card * (optU' c k P A N hc v a₀ x₀ g).card *
          (optD' c k P A N hc v a₀ x₀ g).card) * (k ^ 2 * (k - 3) ^ 4) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hlo

/-- **The box bound.** At least a `(k-4)²(k-5)²/(k²(k-3)⁴)` fraction of the slab solutions put
the unpaired colour `a₀` at `(1, v)` and `x₀` at `(2, v)`. -/
theorem box_bound (hk : 6 ≤ k) (hK : KeyInj k A N) (hA : ∀ v, (A v).card = k) (hc : 1 ≤ c)
    (v : Fin m) {a₀ x₀ : ℕ} (ha : a₀ ∈ A v) (hx : x₀ < k) (hN : k ≤ N v a₀)
    (hPv : k - 1 ≤ (P v).card ∨ a₀ ∉ P v) :
    (slab c m k P A N).Ω.card * ((k - 4) ^ 2 * (k - 5) ^ 2) ≤
      ((slab c m k P A N).Ω.filter (Hit hc v a₀ x₀)).card * (k ^ 2 * (k - 3) ^ 4) :=
  (slab c m k P A N).fibre_sum_ge (boxB c v) _ _ _ fun g hg =>
    box_fibre hk hK hA hc v ha hx hN hPv ((CSP.mem_Ω _).mp hg)

end Final

end GridGen.Gauge
