/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Eight.SlabR

/-!
# The vertical box: a relaxed diagonal pair is hit often

In the relaxed slab, let the label `ℓ` be relaxed on the vertical edge between `z₁ = (2, v)` and
`z₂ = (2, v + 1)`. We show that at `k = 8` at least a `152/27675` fraction of the solutions puts
`ℓ` on both cells (`boxV_bound`).

The proof conditions on everything outside the box: `z₁, z₂`, the list domino
`λ₁ = (1, v), λ₂ = (1, v + 1)`, the future domino `ρ₁ = (3, v), ρ₂ = (3, v + 1)`, and the cells
`μ = (2, v - 1)` and `δ = (2, v + 2)` of the first future column, whichever exist.

* **Upper bound.** Split the fibre by the centre values `(a, b)`. The rest is determined by
  `μ`, `δ` and the two dominoes, each from its available values; the list domino's colours must not
  be keyed `a`, `b`, and the future domino's labels must differ from `a`, `b`.
* **Lower bound.** Put `ℓ` on both centre cells (allowed: `ℓ` is relaxed there). Then `μ, δ` lose
  at most `ℓ`, the list domino loses the pairs keyed `ℓ`, and the future domino loses the pairs
  using `ℓ`.
* **Arithmetic.** `μ, δ` have at least `5` labels, so the ratio is at most `5/4`. The list domino's
  ratio is at most `30/19`: the colours keyed `ℓ` in the two rows differ (`ℓ` is not the label of
  a shared colour), so the pair of both is counted once among the excluded pairs. The future
  domino's ratio is `21/20, 25/20` or `30/20` as `a, b` are available at `ρ₁, ρ₂` or not, and at
  most two labels are unavailable at each. Summing over the `64` centre values gives
  `(5/4)² · (30/19) · 1476/20 = 27675/152`.
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m k : ℕ} {P A : Fin m → Finset ℕ} {N : Fin m → ℕ → ℕ} {R : Fin m → Finset ℕ}

/-! ### The box -/

/-- Membership in the vertical box at row `v`. -/
def inBV (v : Fin m) (y : Cell c m) : Prop :=
  ((y.2.val = v.val ∨ y.2.val = v.val + 1) ∧ 1 ≤ y.1.val ∧ y.1.val ≤ 3) ∨
    (y.1.val = 2 ∧ (y.2.val + 1 = v.val ∨ y.2.val = v.val + 2))

/-- The box without its two centre cells. -/
def inYV (v : Fin m) (y : Cell c m) : Prop :=
  inBV v y ∧ ¬ (y.1.val = 2 ∧ (y.2.val = v.val ∨ y.2.val = v.val + 1))

noncomputable def boxBV (c : ℕ) (v : Fin m) : Finset (Cell c m) := univ.filter (inBV v)

noncomputable def boxYV (c : ℕ) (v : Fin m) : Finset (Cell c m) := univ.filter (inYV v)

theorem mem_boxBV {v : Fin m} {y : Cell c m} : y ∈ boxBV c v ↔ inBV v y := by
  unfold boxBV; simp

theorem mem_boxYV {v : Fin m} {y : Cell c m} : y ∈ boxYV c v ↔ inYV v y := by
  unfold boxYV; simp

/-- The upper centre cell. -/
def zA (hc : 1 ≤ c) (v : Fin m) : Cell c m := (fut0 hc, v)

/-- The lower centre cell. -/
def zB (hc : 1 ≤ c) {v : Fin m} (hv : v.val + 1 < m) : Cell c m := (fut0 hc, ⟨v.val + 1, hv⟩)

/-- The list domino. -/
def lA (v : Fin m) : Cell c m := (1, v)

def lB {v : Fin m} (hv : v.val + 1 < m) : Cell c m := (1, ⟨v.val + 1, hv⟩)

/-- The cell above. -/
def uC (hc : 1 ≤ c) {v : Fin m} (h : 1 ≤ v.val) : Cell c m := (fut0 hc, ⟨v.val - 1, by omega⟩)

/-- The cell below. -/
def dC (hc : 1 ≤ c) {v : Fin m} (h : v.val + 2 < m) : Cell c m := (fut0 hc, ⟨v.val + 2, h⟩)

/-- The future domino. -/
def rA (h : 2 ≤ c) (v : Fin m) : Cell c m := (⟨3, by omega⟩, v)

def rB {v : Fin m} (hv : v.val + 1 < m) (h : 2 ≤ c) : Cell c m := (⟨3, by omega⟩, ⟨v.val + 1, hv⟩)

theorem inBV_iff (hc : 1 ≤ c) {v : Fin m} (hv : v.val + 1 < m) {y : Cell c m} :
    inBV v y ↔ inYV v y ∨ y = zA hc v ∨ y = zB hc hv := by
  unfold inYV
  constructor
  · intro h
    by_cases hz : y.1.val = 2 ∧ (y.2.val = v.val ∨ y.2.val = v.val + 1)
    · right
      rcases hz.2 with h2 | h2
      · left; exact cell_eq (by simp [zA, fut0, hz.1]) (by simp [zA, h2])
      · right; exact cell_eq (by simp [zB, fut0, hz.1]) (by simp [zB, h2])
    · left; exact ⟨h, hz⟩
  · rintro (h | rfl | rfl)
    · exact h.1
    · left; simp [zA, fut0]
    · left; simp [zB, fut0]

theorem zA_not_inYV (hc : 1 ≤ c) (v : Fin m) : ¬ inYV v (zA (c := c) hc v) := by
  unfold inYV; simp [zA, fut0]

theorem zB_not_inYV (hc : 1 ≤ c) {v : Fin m} (hv : v.val + 1 < m) : ¬ inYV v (zB (c := c) hc hv) := by
  unfold inYV; simp [zB, fut0]

theorem zA_ne_zB (hc : 1 ≤ c) {v : Fin m} (hv : v.val + 1 < m) : zA (c := c) hc v ≠ zB hc hv := by
  intro h; have := congrArg (fun x : Cell c m => x.2.val) h; simp [zA, zB] at this

/-- The cells of `Y`. -/
theorem inYV_cases (hc : 1 ≤ c) {v : Fin m} (hv : v.val + 1 < m) {y : Cell c m} (hy : inYV v y) :
    y = lA v ∨ y = lB hv ∨ (∃ h : 1 ≤ v.val, y = uC hc h) ∨ (∃ h : v.val + 2 < m, y = dC hc h) ∨
      (∃ h : 2 ≤ c, y = rA h v ∨ y = rB hv h) := by
  unfold inYV inBV at hy
  have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  rcases hy with ⟨⟨hrow, hc1, hc3⟩ | ⟨hcol, hrow⟩, hnot⟩
  · have : y.1.val = 1 ∨ y.1.val = 3 := by omega
    rcases this with hl | hr
    · rcases hrow with hr' | hr'
      · left; exact cell_eq (by simp [lA, hl]) (by simp [lA, hr'])
      · right; left; exact cell_eq (by simp [lB, hl]) (by simp [lB, hr'])
    · right; right; right; right
      have h2 : 2 ≤ c := by have := y.1.isLt; omega
      refine ⟨h2, ?_⟩
      rcases hrow with hr' | hr'
      · left; exact cell_eq (by simp [rA, hr]) (by simp [rA, hr'])
      · right; exact cell_eq (by simp [rB, hr]) (by simp [rB, hr'])
  · rcases hrow with hr' | hr'
    · right; right; left
      exact ⟨by omega, cell_eq (by simp [uC, fut0, hcol]) (by simp [uC]; omega)⟩
    · right; right; right; left
      exact ⟨by have := y.2.isLt; omega, cell_eq (by simp [dC, fut0, hcol]) (by simp [dC, hr'])⟩

theorem lA_inYV (v : Fin m) : inYV v (lA (c := c) v) := by
  have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  unfold inYV inBV lA; dsimp only; rw [h1]; omega

theorem lB_inYV {v : Fin m} (hv : v.val + 1 < m) : inYV v (lB (c := c) hv) := by
  have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  unfold inYV inBV lB; dsimp only; rw [h1]; omega

theorem uC_inYV (hc : 1 ≤ c) {v : Fin m} (h : 1 ≤ v.val) : inYV v (uC hc h) := by
  unfold inYV inBV uC fut0; dsimp only; omega

theorem dC_inYV (hc : 1 ≤ c) {v : Fin m} (h : v.val + 2 < m) : inYV v (dC hc h) := by
  unfold inYV inBV dC fut0; dsimp only; omega

theorem rA_inYV (h : 2 ≤ c) (v : Fin m) : inYV v (rA (c := c) h v) := by
  unfold inYV inBV rA; dsimp only; omega

theorem rB_inYV (h : 2 ≤ c) {v : Fin m} (hv : v.val + 1 < m) : inYV v (rB (c := c) hv h) := by
  unfold inYV inBV rB; dsimp only; omega

/-- Neighbours of the centre cells lie in the box. -/
theorem inBV_of_adj_centre (hc : 1 ≤ c) {v : Fin m} (hv : v.val + 1 < m) {w y : Cell c m}
    (hy : y = zA hc v ∨ y = zB hc hv) (h : slabAdj y w ∨ slabAdj w y) : inBV v w := by
  have hA1 : (zA (c := c) hc v).1.val = 2 := rfl
  have hA2 : (zA (c := c) hc v).2.val = v.val := rfl
  have hB1 : (zB (c := c) hc hv).1.val = 2 := rfl
  have hB2 : (zB (c := c) hc hv).2.val = v.val + 1 := rfl
  unfold inBV
  rcases hy with rfl | rfl <;> simp only [slabAdj, Fin.ext_iff] at h <;> omega

/-- Inside `Y` the only edges are the two dominoes. -/
theorem adj_in_YV {v : Fin m} {u u' : Cell c m} (hu : inYV v u) (hu' : inYV v u')
    (h : slabAdj u u') : u.1 = u'.1 ∧ (u.1.val = 1 ∨ u.1.val = 3) ∧
      ((u.2.val = v.val ∧ u'.2.val = v.val + 1) ∨ (u.2.val = v.val + 1 ∧ u'.2.val = v.val)) := by
  unfold inYV inBV at hu hu'
  unfold slabAdj at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨h1, ?_⟩
    have : u.1.val = u'.1.val := by rw [h1]
    omega
  · exfalso
    have : u.2.val = u'.2.val := by rw [h1]
    omega

/-! ### Shifting the centre -/

section Shift

variable (hc : 1 ≤ c) {v : Fin m} (hv : v.val + 1 < m)

/-- `g` with `ℓ` on both centre cells. -/
def shiftV (ℓ : ℕ) (g : Cell c m → ℕ) : Cell c m → ℕ :=
  Function.update (Function.update g (zA hc v) ℓ) (zB hc hv) ℓ

variable {hc hv}

theorem shiftV_zA (ℓ : ℕ) (g : Cell c m → ℕ) : shiftV hc hv ℓ g (zA hc v) = ℓ := by
  simp [shiftV, zA_ne_zB hc hv]

theorem shiftV_zB (ℓ : ℕ) (g : Cell c m → ℕ) : shiftV hc hv ℓ g (zB hc hv) = ℓ := by
  simp [shiftV]

theorem shiftV_of_ne {ℓ : ℕ} {g : Cell c m → ℕ} {y : Cell c m} (h1 : y ≠ zA hc v)
    (h2 : y ≠ zB hc hv) : shiftV hc hv ℓ g y = g y := by
  simp [shiftV, h1, h2]

theorem zA_fst : (zA (c := c) hc v).1.val = 2 := rfl
theorem zB_fst : (zB (c := c) hc hv).1.val = 2 := rfl

/-- **The shifted base is valid off `Y`.** -/
theorem validOff_shiftV {ℓ : ℕ} {g : Cell c m → ℕ} (hg : (slabR c m k P A N R).Valid g)
    (hℓ : ℓ < k) (hR : ℓ ∈ R v) :
    (slabR c m k P A N R).ValidOff (boxYV c v) (shiftV hc hv ℓ g) := by
  have hcen : ∀ y : Cell c m, y = zA hc v ∨ y = zB hc hv →
      shiftV hc hv ℓ g y = ℓ := by
    rintro y (rfl | rfl)
    · exact shiftV_zA ℓ g
    · exact shiftV_zB ℓ g
  -- a neighbour of a centre cell off `Y` is the other centre cell
  have hother : ∀ y w : Cell c m, (y = zA hc v ∨ y = zB hc hv) → (slabAdj y w ∨ slabAdj w y) →
      ¬ inYV v w → w = zA hc v ∨ w = zB hc hv := by
    intro y w hy hyw hw
    rcases (inBV_iff hc hv).mp (inBV_of_adj_centre hc hv hy hyw) with h | h | h
    · exact absurd h hw
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨fun x hx => ?_, fun x y hx hy hxy => ?_⟩
  · by_cases hcx : x = zA hc v ∨ x = zB hc hv
    · rw [hcen x hcx, slabR_D]
      rcases hcx with rfl | rfl
      · rw [slab_D_fut (by rw [zA_fst]), mem_range]; exact hℓ
      · rw [slab_D_fut (by rw [zB_fst]), mem_range]; exact hℓ
    · push Not at hcx
      rw [shiftV_of_ne hcx.1 hcx.2]; exact hg.1 x
  · rw [mem_boxYV] at hx hy
    by_cases hcx : x = zA hc v ∨ x = zB hc hv
    · have hcy := hother x y hcx (Or.inl hxy) hy
      rw [hcen x hcx, hcen y hcy, slabR_conf_two (by rcases hcx with rfl | rfl <;> rfl)
        (by rcases hcy with rfl | rfl <;> rfl)]
      rintro ⟨-, hn⟩
      apply hn
      refine ⟨by rcases hcx with rfl | rfl <;> rfl, by rcases hcy with rfl | rfl <;> rfl, ?_⟩
      rcases hcx with rfl | rfl <;> rcases hcy with rfl | rfl
      · exact absurd hxy slabAdj_irrefl
      · left; exact ⟨rfl, hR⟩
      · right; exact ⟨rfl, hR⟩
      · exact absurd hxy slabAdj_irrefl
    by_cases hcy : y = zA hc v ∨ y = zB hc hv
    · exact absurd (hother y x hcy (Or.inr hxy) hx) hcx
    push Not at hcx hcy
    rw [shiftV_of_ne hcx.1 hcx.2, shiftV_of_ne hcy.1 hcy.2]
    exact hg.2 x y hxy

/-- The condition a value at a cell of `Y` must meet next to the centre: a colour of the list
domino must not be keyed `ℓ`, a label elsewhere must differ from `ℓ`. -/
def CondC (N : Fin m → ℕ → ℕ) (ℓ : ℕ) (y : Cell c m) (a : ℕ) : Prop :=
  if y.1.val = 1 then N y.2 a ≠ ℓ else a ≠ ℓ

/-- A conflict with a centre value violates `CondC`. -/
theorem not_condC_of_conf {ℓ : ℕ} {y w : Cell c m} (hy : inYV v y)
    (hw : w = zA hc v ∨ w = zB hc hv) {a : ℕ}
    (h : (slabAdj y w ∧ (slabR c m k P A N R).conf y w a ℓ) ∨
      (slabAdj w y ∧ (slabR c m k P A N R).conf w y ℓ a)) : ¬ CondC N ℓ y a := by
  have hw2 : w.1.val = 2 := by rcases hw with rfl | rfl <;> rfl
  have hy13 : y.1.val = 1 ∨ y.1.val = 2 ∨ y.1.val = 3 := by unfold inYV inBV at hy; omega
  unfold CondC
  rcases hy13 with h1 | h2 | h3
  · rw [ite_eq_left h1]
    rcases h with ⟨-, hc'⟩ | ⟨-, hc'⟩
    · rw [slabR_conf_off (by omega), slab_conf_seam h1 hw2] at hc'; exact fun h => h hc'
    · rw [slabR_conf_off (by omega), slab_conf_seam' hw2 h1] at hc'; exact fun h => h hc'.symm
  · rw [ite_eq_right (by omega)]
    rcases h with ⟨-, hc'⟩ | ⟨-, hc'⟩
    · rw [slabR_conf_two h2 hw2] at hc'; exact fun h => h hc'.1
    · rw [slabR_conf_two hw2 h2] at hc'; exact fun h => h hc'.1.symm
  · rw [ite_eq_right (by omega)]
    rcases h with ⟨-, hc'⟩ | ⟨-, hc'⟩
    · rw [slabR_conf_off (by omega), slab_conf_eq (by omega) (by omega)] at hc'
      exact fun h => h hc'
    · rw [slabR_conf_off (by omega), slab_conf_eq (by omega) (by omega)] at hc'
      exact fun h => h hc'.symm

/-- **Available after the shift.** -/
theorem mem_avail_shiftV {ℓ : ℕ} {g : Cell c m → ℕ} {y : Cell c m} (hy : inYV v y) {a : ℕ}
    (ha : a ∈ (slabR c m k P A N R).avail (boxBV c v) g y) (hC : CondC N ℓ y a) :
    a ∈ (slabR c m k P A N R).avail (boxYV c v) (shiftV hc hv ℓ g) y := by
  rw [CSP.mem_avail] at ha ⊢
  refine ⟨ha.1, fun w hw => ?_⟩
  rw [mem_boxYV] at hw
  by_cases hB : inBV v w
  · rcases (inBV_iff hc hv).mp hB with h | h | h
    · exact absurd h hw
    · have hs : shiftV hc hv ℓ g w = ℓ := by rw [h]; exact shiftV_zA ℓ g
      rw [hs]
      exact ⟨fun hadj hcf => not_condC_of_conf (hv := hv) hy (Or.inl h) (Or.inl ⟨hadj, hcf⟩) hC,
        fun hadj hcf => not_condC_of_conf (hv := hv) hy (Or.inl h) (Or.inr ⟨hadj, hcf⟩) hC⟩
    · have hs : shiftV hc hv ℓ g w = ℓ := by rw [h]; exact shiftV_zB ℓ g
      rw [hs]
      exact ⟨fun hadj hcf => not_condC_of_conf (hc := hc) hy (Or.inr h) (Or.inl ⟨hadj, hcf⟩) hC,
        fun hadj hcf => not_condC_of_conf (hc := hc) hy (Or.inr h) (Or.inr ⟨hadj, hcf⟩) hC⟩
  · have hwB : w ∉ boxBV c v := by rw [mem_boxBV]; exact hB
    have h1 : w ≠ zA hc v := by rintro rfl; exact hB ((inBV_iff hc hv).mpr (Or.inr (Or.inl rfl)))
    have h2 : w ≠ zB hc hv := by rintro rfl; exact hB ((inBV_iff hc hv).mpr (Or.inr (Or.inr rfl)))
    rw [shiftV_of_ne h1 h2]
    exact ha.2 w hwB

end Shift

/-! ### Off-diagonal pairs -/

/-- Pairs of distinct values. -/
def offd (X Y : Finset ℕ) : Finset (ℕ × ℕ) := (X ×ˢ Y).filter (fun pq => pq.1 ≠ pq.2)

theorem mem_offd {X Y : Finset ℕ} {pq : ℕ × ℕ} :
    pq ∈ offd X Y ↔ pq.1 ∈ X ∧ pq.2 ∈ Y ∧ pq.1 ≠ pq.2 := by
  unfold offd; rw [mem_filter, mem_product]; tauto

theorem card_offd (X Y : Finset ℕ) : (offd X Y).card + (X ∩ Y).card = X.card * Y.card := by
  have h := card_filter_add_card_filter_not (s := X ×ˢ Y) (fun pq : ℕ × ℕ => pq.1 ≠ pq.2)
  rw [card_product] at h
  have e : ((X ×ˢ Y).filter fun pq : ℕ × ℕ => ¬ pq.1 ≠ pq.2) = (X ∩ Y).image fun z => (z, z) := by
    ext ⟨p, q⟩
    simp only [mem_filter, mem_product, not_not, mem_image, mem_inter, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hp, hq⟩, rfl⟩; exact ⟨p, ⟨hp, hq⟩, rfl, rfl⟩
    · rintro ⟨z, ⟨hz1, hz2⟩, rfl, rfl⟩; exact ⟨⟨hz1, hz2⟩, rfl⟩
  rw [e, card_image_of_injective _ (fun a b h => by simpa using h)] at h
  unfold offd; omega

/-! ### The upper bound -/

section Upper

variable (c k P A N R) in
/-- Options at the cell above. -/
noncomputable def optUv (hc : 1 ≤ c) (v : Fin m) (g : Cell c m → ℕ) : Finset (Option ℕ) :=
  if h : 1 ≤ v.val then ((slabR c m k P A N R).avail (boxBV c v) g (uC hc h)).map
    Function.Embedding.some else {none}

variable (c k P A N R) in
/-- Options at the cell below. -/
noncomputable def optDv (hc : 1 ≤ c) (v : Fin m) (g : Cell c m → ℕ) : Finset (Option ℕ) :=
  if h : v.val + 2 < m then ((slabR c m k P A N R).avail (boxBV c v) g (dC hc h)).map
    Function.Embedding.some else {none}

variable (c k P A N R) in
/-- Options on the list domino next to centre values `a, b`. -/
noncomputable def optLv {v : Fin m} (hv : v.val + 1 < m) (g : Cell c m → ℕ) (a b : ℕ) :
    Finset (ℕ × ℕ) :=
  offd (((slabR c m k P A N R).avail (boxBV c v) g (lA v)).filter (fun p => N v p ≠ a))
    (((slabR c m k P A N R).avail (boxBV c v) g (lB hv)).filter (fun q => N ⟨v.val + 1, hv⟩ q ≠ b))

variable (c k P A N R) in
/-- Options on the future domino next to centre values `a, b`. -/
noncomputable def optRv {v : Fin m} (hv : v.val + 1 < m) (g : Cell c m → ℕ) (a b : ℕ) :
    Finset (Option (ℕ × ℕ)) :=
  if h : 2 ≤ c then (offd (((slabR c m k P A N R).avail (boxBV c v) g (rA h v)).erase a)
    (((slabR c m k P A N R).avail (boxBV c v) g (rB hv h)).erase b)).map Function.Embedding.some
  else {none}

/-- The box values off the centre. -/
def boxValsV (hc : 1 ≤ c) {v : Fin m} (hv : v.val + 1 < m) (f : Cell c m → ℕ) :
    Option ℕ × Option ℕ × (ℕ × ℕ) × Option (ℕ × ℕ) :=
  ((if h : 1 ≤ v.val then some (f (uC hc h)) else none),
    (if h : v.val + 2 < m then some (f (dC hc h)) else none),
    (f (lA v), f (lB hv)),
    (if h : 2 ≤ c then some (f (rA h v), f (rB hv h)) else none))

theorem slabAdj_lAzA (hc : 1 ≤ c) (v : Fin m) : slabAdj (lA (c := c) v) (zA hc v) := by
  have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  unfold slabAdj lA zA fut0; dsimp only; rw [h1]; omega

theorem slabAdj_lBzB (hc : 1 ≤ c) {v : Fin m} (hv : v.val + 1 < m) :
    slabAdj (lB (c := c) hv) (zB hc hv) := by
  have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  unfold slabAdj lB zB fut0; dsimp only; rw [h1]; omega

theorem slabAdj_lAlB {v : Fin m} (hv : v.val + 1 < m) : slabAdj (lA (c := c) v) (lB hv) := by
  unfold slabAdj lA lB; dsimp only; omega

theorem slabAdj_zArA (hc : 1 ≤ c) (h : 2 ≤ c) (v : Fin m) : slabAdj (zA (c := c) hc v) (rA h v) := by
  unfold slabAdj zA rA fut0; dsimp only; omega

theorem slabAdj_zBrB (hc : 1 ≤ c) (h : 2 ≤ c) {v : Fin m} (hv : v.val + 1 < m) :
    slabAdj (zB (c := c) hc hv) (rB hv h) := by
  unfold slabAdj zB rB fut0; dsimp only; omega

theorem slabAdj_rArB (h : 2 ≤ c) {v : Fin m} (hv : v.val + 1 < m) :
    slabAdj (rA (c := c) h v) (rB hv h) := by
  unfold slabAdj rA rB; dsimp only; omega

/-- **The fibre over fixed centre values.** -/
theorem card_cls_ab_leV (hc : 1 ≤ c) {v : Fin m} (hv : v.val + 1 < m) (g : Cell c m → ℕ)
    (a b : ℕ) :
    (((slabR c m k P A N R).cls (boxBV c v) g).filter
        (fun f => f (zA hc v) = a ∧ f (zB hc hv) = b)).card ≤
      (optUv c k P A N R hc v g).card * (optDv c k P A N R hc v g).card *
        (optLv c k P A N R hv g a b).card * (optRv c k P A N R hv g a b).card := by
  set C := slabR c m k P A N R
  have h1v : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  have hT : (optUv c k P A N R hc v g ×ˢ optDv c k P A N R hc v g ×ˢ optLv c k P A N R hv g a b ×ˢ
      optRv c k P A N R hv g a b).card = (optUv c k P A N R hc v g).card *
        (optDv c k P A N R hc v g).card * (optLv c k P A N R hv g a b).card *
          (optRv c k P A N R hv g a b).card := by
    simp only [card_product]; ring
  rw [← hT]
  refine card_le_card_of_injOn (boxValsV hc hv) ?_ ?_
  · intro f hf
    rw [mem_coe, mem_filter] at hf
    obtain ⟨hf, ha, hb⟩ := hf
    have hv' := ((CSP.mem_cls _).mp hf).1
    have hB : ∀ y, inBV v y → y ∈ boxBV c v := fun y h => mem_boxBV.mpr h
    simp only [coe_product, Set.mem_prod, mem_coe, boxValsV]
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold optUv; split_ifs with h
      · exact mem_map_of_mem _ (CSP.mem_avail_of_mem_cls _ hf (hB _ (uC_inYV hc h).1))
      · exact mem_singleton_self _
    · unfold optDv; split_ifs with h
      · exact mem_map_of_mem _ (CSP.mem_avail_of_mem_cls _ hf (hB _ (dC_inYV hc h).1))
      · exact mem_singleton_self _
    · unfold optLv
      rw [mem_offd, mem_filter, mem_filter]
      refine ⟨⟨CSP.mem_avail_of_mem_cls _ hf (hB _ (lA_inYV v).1), fun e => ?_⟩,
        ⟨CSP.mem_avail_of_mem_cls _ hf (hB _ (lB_inYV hv).1), fun e => ?_⟩, fun e => ?_⟩
      · have := hv'.2 _ _ (slabAdj_lAzA hc v)
        rw [slabR_conf_off (by simp [lA, zA, fut0]), slab_conf_seam h1v rfl] at this
        exact this (by rw [ha]; exact e)
      · have := hv'.2 _ _ (slabAdj_lBzB hc hv)
        rw [slabR_conf_off (by simp [lB, zB, fut0]), slab_conf_seam h1v rfl] at this
        exact this (by rw [hb]; exact e)
      · have := hv'.2 _ _ (slabAdj_lAlB (c := c) hv)
        rw [slabR_conf_off (by simp [lA, lB]), slab_conf_eq (by simp [lA, lB])
          (by simp [lA, lB])] at this
        exact this e
    · unfold optRv; split_ifs with h
      · refine mem_map_of_mem _ ?_
        rw [mem_offd, mem_erase, mem_erase]
        refine ⟨⟨fun e => ?_, CSP.mem_avail_of_mem_cls _ hf (hB _ (rA_inYV h v).1)⟩,
          ⟨fun e => ?_, CSP.mem_avail_of_mem_cls _ hf (hB _ (rB_inYV h hv).1)⟩, fun e => ?_⟩
        · have := hv'.2 _ _ (slabAdj_zArA hc h v)
          rw [slabR_conf_off (by simp [rA, zA, fut0]), slab_conf_eq (by simp [rA, zA, fut0])
            (by simp [rA, zA, fut0])] at this
          exact this (by rw [ha]; exact e.symm)
        · have := hv'.2 _ _ (slabAdj_zBrB hc h hv)
          rw [slabR_conf_off (by simp [rB, zB, fut0]), slab_conf_eq (by simp [rB, zB, fut0])
            (by simp [rB, zB, fut0])] at this
          exact this (by rw [hb]; exact e.symm)
        · have := hv'.2 _ _ (slabAdj_rArB (c := c) h hv)
          rw [slabR_conf_off (by simp [rA, rB]), slab_conf_eq (by simp [rA, rB])
            (by simp [rA, rB])] at this
          exact this e
      · exact mem_singleton_self _
  · intro f hf f' hf' he
    rw [mem_coe, mem_filter] at hf hf'
    simp only [boxValsV, Prod.mk.injEq] at he
    obtain ⟨eU, eD, ⟨eL1, eL2⟩, eR⟩ := he
    have hc1 := (CSP.mem_cls _).mp hf.1
    have hc1' := (CSP.mem_cls _).mp hf'.1
    funext y
    by_cases hyB : y ∈ boxBV c v
    · rcases (inBV_iff hc hv).mp (mem_boxBV.mp hyB) with hY | rfl | rfl
      · rcases inYV_cases hc hv hY with rfl | rfl | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl | rfl⟩
        · exact eL1
        · exact eL2
        · simp only [dite_eq_left h, Option.some.injEq] at eU; exact eU
        · simp only [dite_eq_left h, Option.some.injEq] at eD; exact eD
        · simp only [dite_eq_left h, Option.some.injEq, Prod.mk.injEq] at eR; exact eR.1
        · simp only [dite_eq_left h, Option.some.injEq, Prod.mk.injEq] at eR; exact eR.2
      · rw [hf.2.1, hf'.2.1]
      · rw [hf.2.2, hf'.2.2]
    · rw [hc1.2 y hyB, hc1'.2 y hyB]

/-- **The fibre, summed over the centre values.** -/
theorem card_cls_le_sumV (hc : 1 ≤ c) {v : Fin m} (hv : v.val + 1 < m) (g : Cell c m → ℕ) :
    ((slabR c m k P A N R).cls (boxBV c v) g).card ≤ ∑ a ∈ range k, ∑ b ∈ range k,
      (optUv c k P A N R hc v g).card * (optDv c k P A N R hc v g).card *
        (optLv c k P A N R hv g a b).card * (optRv c k P A N R hv g a b).card := by
  rw [card_eq_sum_card_fiberwise (f := fun f => (f (zA hc v), f (zB hc hv)))
    (t := range k ×ˢ range k)]
  · rw [sum_product]
    refine sum_le_sum fun a _ => sum_le_sum fun b _ => le_trans (le_of_eq ?_)
      (card_cls_ab_leV hc hv g a b)
    congr 1
  · intro f hf
    have hv' := ((CSP.mem_cls _).mp hf).1
    rw [mem_coe, mem_product]
    refine ⟨?_, ?_⟩
    · have := hv'.1 (zA hc v); rwa [slabR_D, slab_D_fut (by rw [zA_fst])] at this
    · have := hv'.1 (zB hc hv); rwa [slabR_D, slab_D_fut (by rw [zB_fst])] at this

end Upper

/-! ### The lower bound -/

section Lower

variable (c k P A N R) in
/-- Options at the cell above, avoiding `ℓ`. -/
noncomputable def optUv' (hc : 1 ≤ c) (v : Fin m) (ℓ : ℕ) (g : Cell c m → ℕ) : Finset (Option ℕ) :=
  if h : 1 ≤ v.val then (((slabR c m k P A N R).avail (boxBV c v) g (uC hc h)).erase ℓ).map
    Function.Embedding.some else {none}

variable (c k P A N R) in
/-- Options at the cell below, avoiding `ℓ`. -/
noncomputable def optDv' (hc : 1 ≤ c) (v : Fin m) (ℓ : ℕ) (g : Cell c m → ℕ) : Finset (Option ℕ) :=
  if h : v.val + 2 < m then (((slabR c m k P A N R).avail (boxBV c v) g (dC hc h)).erase ℓ).map
    Function.Embedding.some else {none}

/-- Fill the box from independent choices, around the shifted centre. -/
def fillV (hc : 1 ≤ c) {v : Fin m} (hv : v.val + 1 < m) (ℓ : ℕ) (g : Cell c m → ℕ)
    (t : Option ℕ × Option ℕ × (ℕ × ℕ) × Option (ℕ × ℕ)) : Cell c m → ℕ := fun y =>
  if y.1.val = 1 ∧ y.2.val = v.val then t.2.2.1.1
  else if y.1.val = 1 ∧ y.2.val = v.val + 1 then t.2.2.1.2
  else if y.1.val = 2 ∧ y.2.val + 1 = v.val then t.1.getD 0
  else if y.1.val = 2 ∧ y.2.val = v.val + 2 then t.2.1.getD 0
  else if y.1.val = 3 ∧ y.2.val = v.val then (t.2.2.2.getD (0, 0)).1
  else if y.1.val = 3 ∧ y.2.val = v.val + 1 then (t.2.2.2.getD (0, 0)).2
  else shiftV hc hv ℓ g y

variable {hc : 1 ≤ c} {v : Fin m} {hv : v.val + 1 < m} {ℓ : ℕ} {g : Cell c m → ℕ}
  {t : Option ℕ × Option ℕ × (ℕ × ℕ) × Option (ℕ × ℕ)}

theorem fillV_off {y : Cell c m} (hy : ¬ inYV v y) : fillV hc hv ℓ g t y = shiftV hc hv ℓ g y := by
  unfold inYV inBV at hy
  unfold fillV
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem fillV_lA : fillV hc hv ℓ g t (lA v) = t.2.2.1.1 := by
  have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  unfold fillV lA; dsimp only; rw [h1, ite_eq_left ⟨rfl, rfl⟩]

theorem fillV_lB : fillV hc hv ℓ g t (lB hv) = t.2.2.1.2 := by
  have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  unfold fillV lB; dsimp only; rw [h1, ite_eq_right (by omega), ite_eq_left ⟨rfl, rfl⟩]

theorem fillV_uC (h : 1 ≤ v.val) : fillV hc hv ℓ g t (uC hc h) = t.1.getD 0 := by
  unfold fillV uC fut0; dsimp only
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨rfl, by omega⟩]

theorem fillV_dC (h : v.val + 2 < m) : fillV hc hv ℓ g t (dC hc h) = t.2.1.getD 0 := by
  unfold fillV dC fut0; dsimp only
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_left ⟨rfl, rfl⟩]

theorem fillV_rA (h : 2 ≤ c) : fillV hc hv ℓ g t (rA h v) = (t.2.2.2.getD (0, 0)).1 := by
  unfold fillV rA; dsimp only
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_left ⟨rfl, rfl⟩]

theorem fillV_rB (h : 2 ≤ c) : fillV hc hv ℓ g t (rB hv h) = (t.2.2.2.getD (0, 0)).2 := by
  unfold fillV rB; dsimp only
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨rfl, rfl⟩]

theorem condC_lA {a : ℕ} (h : N v a ≠ ℓ) : CondC N ℓ (lA (c := c) v) a := by
  have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  unfold CondC lA; dsimp only; rw [h1, ite_eq_left rfl]; exact h

theorem condC_lB {a : ℕ} (h : N ⟨v.val + 1, hv⟩ a ≠ ℓ) : CondC N ℓ (lB (c := c) hv) a := by
  have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  unfold CondC lB; dsimp only; rw [h1, ite_eq_left rfl]; exact h

theorem condC_of_ne {y : Cell c m} (hy : y.1.val ≠ 1) {a : ℕ} (h : a ≠ ℓ) : CondC N ℓ y a := by
  unfold CondC; rw [ite_eq_right hy]; exact h

/-- **The lower bound on a fibre.** -/
theorem card_hit_geV (hg : (slabR c m k P A N R).Valid g) (hℓ : ℓ < k) (hR : ℓ ∈ R v) :
    (optUv' c k P A N R hc v ℓ g).card * (optDv' c k P A N R hc v ℓ g).card *
        (optLv c k P A N R hv g ℓ ℓ).card * (optRv c k P A N R hv g ℓ ℓ).card ≤
      (((slabR c m k P A N R).cls (boxBV c v) g).filter (HitV hc hv ℓ)).card := by
  set C := slabR c m k P A N R
  set S := optUv' c k P A N R hc v ℓ g ×ˢ optDv' c k P A N R hc v ℓ g ×ˢ
    optLv c k P A N R hv g ℓ ℓ ×ˢ optRv c k P A N R hv g ℓ ℓ
  have hS : S.card = (optUv' c k P A N R hc v ℓ g).card * (optDv' c k P A N R hc v ℓ g).card *
      (optLv c k P A N R hv g ℓ ℓ).card * (optRv c k P A N R hv g ℓ ℓ).card := by
    simp only [S, card_product]; ring
  rw [← hS]
  have hval := validOff_shiftV (P := P) (A := A) (N := N) (hc := hc) (hv := hv) hg hℓ hR
  have hB : ∀ y, inBV v y → y ∈ boxBV c v := fun y h => mem_boxBV.mpr h
  refine card_le_card_of_injOn (fillV hc hv ℓ g) ?_ ?_
  · intro t ht
    simp only [S, coe_product, Set.mem_prod, mem_coe] at ht
    obtain ⟨hU, hD, hL, hRd⟩ := ht
    rw [optLv, mem_offd, mem_filter, mem_filter] at hL
    obtain ⟨⟨hL1, hL1'⟩, ⟨hL2, hL2'⟩, hL12⟩ := hL
    have hY : fillV hc hv ℓ g t ∈ C.cls (boxYV c v) (shiftV hc hv ℓ g) := by
      refine C.mem_cls_of hval (fun x hx => fillV_off (by rwa [mem_boxYV] at hx))
        (fun u hu => ?_) (fun u u' hu hu' hadj => ?_)
      · rw [mem_boxYV] at hu
        rcases inYV_cases hc hv hu with rfl | rfl | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl | rfl⟩
        · rw [fillV_lA]; exact mem_avail_shiftV (lA_inYV v) hL1 (condC_lA hL1')
        · rw [fillV_lB]; exact mem_avail_shiftV (lB_inYV hv) hL2 (condC_lB hL2')
        · unfold optUv' at hU; rw [dite_eq_left h, mem_map] at hU
          obtain ⟨q, hq, hq'⟩ := hU
          rw [fillV_uC, ← hq', Function.Embedding.some_apply, Option.getD_some]
          rw [mem_erase] at hq
          exact mem_avail_shiftV (uC_inYV hc h) hq.2 (condC_of_ne (by simp [uC, fut0]) hq.1)
        · unfold optDv' at hD; rw [dite_eq_left h, mem_map] at hD
          obtain ⟨q, hq, hq'⟩ := hD
          rw [fillV_dC, ← hq', Function.Embedding.some_apply, Option.getD_some]
          rw [mem_erase] at hq
          exact mem_avail_shiftV (dC_inYV hc h) hq.2 (condC_of_ne (by simp [dC, fut0]) hq.1)
        · unfold optRv at hRd; rw [dite_eq_left h, mem_map] at hRd
          obtain ⟨pq, hpq, hpq'⟩ := hRd
          rw [fillV_rA, ← hpq', Function.Embedding.some_apply, Option.getD_some]
          rw [mem_offd, mem_erase, mem_erase] at hpq
          exact mem_avail_shiftV (rA_inYV h v) hpq.1.2 (condC_of_ne (by simp [rA]) hpq.1.1)
        · unfold optRv at hRd; rw [dite_eq_left h, mem_map] at hRd
          obtain ⟨pq, hpq, hpq'⟩ := hRd
          rw [fillV_rB, ← hpq', Function.Embedding.some_apply, Option.getD_some]
          rw [mem_offd, mem_erase, mem_erase] at hpq
          exact mem_avail_shiftV (rB_inYV h hv) hpq.2.1.2 (condC_of_ne (by simp [rB]) hpq.2.1.1)
      · rw [mem_boxYV] at hu hu'
        obtain ⟨hcol, hc13, hrow⟩ := adj_in_YV hu hu' hadj
        have hnc : ¬ (u.1.val = 2 ∧ u'.1.val = 2) := by rw [hcol]; omega
        have hn1 : ¬ (u.1.val = 1 ∧ u'.1.val = 2) := by rw [hcol]; omega
        have hn2 : ¬ (u.1.val = 2 ∧ u'.1.val = 1) := by rw [hcol]; omega
        rw [slabR_conf_off hnc, slab_conf_eq hn1 hn2]
        rcases hc13 with h1 | h3
        · have ea : ∀ y : Cell c m, y.1.val = 1 → y.2.val = v.val → y = lA v := fun y hy1 hy2 =>
            cell_eq (by simp [lA, hy1]) (by simp [lA, hy2])
          have eb : ∀ y : Cell c m, y.1.val = 1 → y.2.val = v.val + 1 → y = lB hv := fun y hy1 hy2 =>
            cell_eq (by simp [lB, hy1]) (by simp [lB, hy2])
          have h1' : u'.1.val = 1 := by rw [← hcol]; exact h1
          rcases hrow with ⟨r1, r2⟩ | ⟨r1, r2⟩
          · rw [ea u h1 r1, eb u' h1' r2, fillV_lA, fillV_lB]; exact hL12
          · rw [eb u h1 r1, ea u' h1' r2, fillV_lA, fillV_lB]; exact fun e => hL12 e.symm
        · have h2c : 2 ≤ c := by have := u.1.isLt; omega
          unfold optRv at hRd; rw [dite_eq_left h2c, mem_map] at hRd
          obtain ⟨pq, hpq, hpq'⟩ := hRd
          rw [mem_offd] at hpq
          have ea : ∀ y : Cell c m, y.1.val = 3 → y.2.val = v.val → y = rA h2c v := fun y hy1 hy2 =>
            cell_eq (by simp [rA, hy1]) (by simp [rA, hy2])
          have eb : ∀ y : Cell c m, y.1.val = 3 → y.2.val = v.val + 1 → y = rB hv h2c :=
            fun y hy1 hy2 => cell_eq (by simp [rB, hy1]) (by simp [rB, hy2])
          have h3' : u'.1.val = 3 := by rw [← hcol]; exact h3
          rcases hrow with ⟨r1, r2⟩ | ⟨r1, r2⟩
          · rw [ea u h3 r1, eb u' h3' r2, fillV_rA, fillV_rB, ← hpq']
            simpa using hpq.2.2
          · rw [eb u h3 r1, ea u' h3' r2, fillV_rA, fillV_rB, ← hpq']
            simpa using fun e => hpq.2.2 e.symm
    rw [mem_coe, mem_filter]
    have hYv := (C.mem_cls).mp hY
    refine ⟨(C.mem_cls).mpr ⟨hYv.1, fun x hx => ?_⟩, ?_, ?_⟩
    · have hxB : ¬ inBV v x := by rwa [mem_boxBV] at hx
      have hxY : x ∉ boxYV c v := by rw [mem_boxYV]; exact fun h => hxB h.1
      have h1 : x ≠ zA hc v := by
        rintro rfl; exact hxB ((inBV_iff hc hv).mpr (Or.inr (Or.inl rfl)))
      have h2 : x ≠ zB hc hv := by
        rintro rfl; exact hxB ((inBV_iff hc hv).mpr (Or.inr (Or.inr rfl)))
      rw [hYv.2 x hxY, shiftV_of_ne h1 h2]
    · show fillV hc hv ℓ g t (zA hc v) = ℓ
      rw [fillV_off (zA_not_inYV hc v), shiftV_zA]
    · show fillV hc hv ℓ g t (zB hc hv) = ℓ
      rw [fillV_off (zB_not_inYV hc hv), shiftV_zB]
  · intro t ht t' ht' he
    simp only [S, coe_product, Set.mem_prod, mem_coe] at ht ht'
    obtain ⟨hU, hD, _, hRd⟩ := ht
    obtain ⟨hU', hD', _, hRd'⟩ := ht'
    obtain ⟨tU, tD, tL, tR⟩ := t
    obtain ⟨tU', tD', tL', tR'⟩ := t'
    dsimp only at hU hU' hD hD' hRd hRd'
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_cases h : 1 ≤ v.val
      · unfold optUv' at hU hU'
        rw [dite_eq_left h, mem_map] at hU hU'
        obtain ⟨q, -, rfl⟩ := hU
        obtain ⟨q', -, rfl⟩ := hU'
        have := congrFun he (uC hc h)
        rw [fillV_uC, fillV_uC] at this
        simpa using this
      · unfold optUv' at hU hU'
        rw [dite_eq_right h, mem_singleton] at hU hU'
        rw [hU, hU']
    · by_cases h : v.val + 2 < m
      · unfold optDv' at hD hD'
        rw [dite_eq_left h, mem_map] at hD hD'
        obtain ⟨q, -, rfl⟩ := hD
        obtain ⟨q', -, rfl⟩ := hD'
        have := congrFun he (dC hc h)
        rw [fillV_dC, fillV_dC] at this
        simpa using this
      · unfold optDv' at hD hD'
        rw [dite_eq_right h, mem_singleton] at hD hD'
        rw [hD, hD']
    · have e1 := congrFun he (lA v)
      have e2 := congrFun he (lB hv)
      rw [fillV_lA, fillV_lA] at e1
      rw [fillV_lB, fillV_lB] at e2
      exact Prod.ext e1 e2
    · by_cases h : 2 ≤ c
      · unfold optRv at hRd hRd'
        rw [dite_eq_left h, mem_map] at hRd hRd'
        obtain ⟨pq, -, rfl⟩ := hRd
        obtain ⟨pq', -, rfl⟩ := hRd'
        have e1 := congrFun he (rA h v)
        have e2 := congrFun he (rB hv h)
        rw [fillV_rA, fillV_rA] at e1
        rw [fillV_rB, fillV_rB] at e2
        simp only [Function.Embedding.some_apply, Option.getD_some] at e1 e2
        rw [Prod.ext e1 e2]
      · unfold optRv at hRd hRd'
        rw [dite_eq_right h, mem_singleton] at hRd hRd'
        rw [hRd, hRd']

end Lower

/-! ### Counting at `k = 8` -/

section Count

theorem nbrsOut_cell_le {v : Fin m} (y : Cell c m) (L : List (ℕ × ℕ))
    (h : ∀ w : Cell c m, (slabAdj y w ∨ slabAdj w y) → ¬ inBV v w → (w.1.val, w.2.val) ∈ L) :
    ((slabR c m k P A N R).nbrsOut y (boxBV c v)).card ≤ L.length :=
  card_le_of_coords _ L fun w hw => by
    rw [CSP.mem_nbrsOut, mem_boxBV] at hw; exact h w hw.1 hw.2

theorem nbrsOut_uC (hc : 1 ≤ c) {v : Fin m} (h : 1 ≤ v.val) :
    ((slabR c m k P A N R).nbrsOut (uC hc h) (boxBV c v)).card ≤ 3 :=
  nbrsOut_cell_le _ [(2, v.val - 2), (1, v.val - 1), (3, v.val - 1)] fun w hw hB => by
    unfold slabAdj at hw; unfold inBV at hB
    simp only [uC, fut0, Fin.ext_iff, Fin.val_mk] at hw
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]; omega

theorem nbrsOut_dC (hc : 1 ≤ c) {v : Fin m} (h : v.val + 2 < m) :
    ((slabR c m k P A N R).nbrsOut (dC hc h) (boxBV c v)).card ≤ 3 :=
  nbrsOut_cell_le _ [(2, v.val + 3), (1, v.val + 2), (3, v.val + 2)] fun w hw hB => by
    unfold slabAdj at hw; unfold inBV at hB
    simp only [dC, fut0, Fin.ext_iff, Fin.val_mk] at hw
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]; omega

theorem nbrsOut_lA (v : Fin m) :
    ((slabR c m k P A N R).nbrsOut (lA v) (boxBV c v)).card ≤ 2 := by
  have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  exact nbrsOut_cell_le _ [(0, v.val), (1, v.val - 1)] fun w hw hB => by
    unfold slabAdj at hw; unfold inBV at hB
    simp only [lA, Fin.ext_iff, h1] at hw
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]; omega

theorem nbrsOut_lB {v : Fin m} (hv : v.val + 1 < m) :
    ((slabR c m k P A N R).nbrsOut (lB hv) (boxBV c v)).card ≤ 2 := by
  have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  exact nbrsOut_cell_le _ [(0, v.val + 1), (1, v.val + 2)] fun w hw hB => by
    unfold slabAdj at hw; unfold inBV at hB
    simp only [lB, Fin.ext_iff, h1, Fin.val_mk] at hw
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]; omega

theorem nbrsOut_rA (h : 2 ≤ c) (v : Fin m) :
    ((slabR c m k P A N R).nbrsOut (rA h v) (boxBV c v)).card ≤ 2 :=
  nbrsOut_cell_le _ [(4, v.val), (3, v.val - 1)] fun w hw hB => by
    unfold slabAdj at hw; unfold inBV at hB
    simp only [rA, Fin.ext_iff, Fin.val_mk] at hw
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]; omega

theorem nbrsOut_rB (h : 2 ≤ c) {v : Fin m} (hv : v.val + 1 < m) :
    ((slabR c m k P A N R).nbrsOut (rB hv h) (boxBV c v)).card ≤ 2 :=
  nbrsOut_cell_le _ [(4, v.val + 1), (3, v.val + 2)] fun w hw hB => by
    unfold slabAdj at hw; unfold inBV at hB
    simp only [rB, Fin.ext_iff, Fin.val_mk] at hw
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]; omega

variable (hK : KeyInj k A N) {g : Cell c m → ℕ} (hg : (slabR c m k P A N R).Valid g) {v : Fin m}
include hK hg

theorem avail_fut_ge {y : Cell c m} (hy : inBV v y) (hy2 : 2 ≤ y.1.val) :
    k - ((slabR c m k P A N R).nbrsOut y (boxBV c v)).card ≤
      ((slabR c m k P A N R).avail (boxBV c v) g y).card := by
  have := (slabR c m k P A N R).card_avail_ge (slabR_match hK) slabR_irrefl (mem_boxBV.mpr hy)
    (fun x _ => hg.1 x)
  rwa [slabR_D, slab_D_fut hy2, card_range] at this

theorem avail_list_ge (hA : ∀ v, (A v).card = k) {y : Cell c m} (hy : inBV v y)
    (hy1 : y.1.val = 1) :
    k - ((slabR c m k P A N R).nbrsOut y (boxBV c v)).card ≤
      ((slabR c m k P A N R).avail (boxBV c v) g y).card := by
  have := (slabR c m k P A N R).card_avail_ge (slabR_match hK) slabR_irrefl (mem_boxBV.mpr hy)
    (fun x _ => hg.1 x)
  rwa [slabR_D, slab_D_one hy1, hA] at this

end Count

/-! ### The ratios at `k = 8` -/

section Eight

theorem offd_mono {X X' Y Y' : Finset ℕ} (hX : X ⊆ X') (hY : Y ⊆ Y') : offd X Y ⊆ offd X' Y' := by
  intro pq h; rw [mem_offd] at h ⊢; exact ⟨hX h.1, hY h.2.1, h.2.2⟩

theorem erase_inter_erase (X Y : Finset ℕ) (a b : ℕ) :
    X.erase a ∩ Y.erase b = ((X ∩ Y).erase a).erase b := by
  ext z; simp only [mem_inter, mem_erase]; tauto

theorem ind_le_of_imp {p q : Prop} [Decidable p] [Decidable q] (h : p → q) :
    (if p then 1 else 0 : ℕ) ≤ if q then 1 else 0 := by
  split_ifs with h1 h2 <;> simp_all

theorem ind_inter (X Y : Finset ℕ) (a : ℕ) :
    (if a ∈ X ∩ Y then 1 else 0 : ℕ) = (if a ∈ X then 1 else 0) * (if a ∈ Y then 1 else 0) := by
  by_cases h1 : a ∈ X <;> by_cases h2 : a ∈ Y <;> simp [h1, h2]

theorem card_erase_ind (X : Finset ℕ) (a : ℕ) :
    (X.erase a).card + (if a ∈ X then 1 else 0) = X.card := by
  split_ifs with h
  · rw [card_erase_of_mem h]; have := card_pos.mpr ⟨a, h⟩; omega
  · rw [erase_eq_of_notMem h]; rfl

variable (hK : KeyInj 8 A N) (hA : ∀ v, (A v).card = 8) {g : Cell c m → ℕ}
  (hg : (slabR c m 8 P A N R).Valid g) (hc : 1 ≤ c) {v : Fin m} (hv : v.val + 1 < m)
include hK hg

theorem ratio_U (ℓ : ℕ) :
    4 * (optUv c 8 P A N R hc v g).card ≤ 5 * (optUv' c 8 P A N R hc v ℓ g).card := by
  unfold optUv optUv'
  split_ifs with h
  · rw [card_map, card_map]
    have hav := avail_fut_ge (P := P) (A := A) (N := N) (R := R) hK hg (uC_inYV hc h).1
      (show 2 ≤ (uC hc h).1.val from le_rfl)
    have hn := nbrsOut_uC (k := 8) (P := P) (A := A) (N := N) (R := R) hc h
    have := pred_card_le_card_erase (s := (slabR c m 8 P A N R).avail (boxBV c v) g (uC hc h))
      (a := ℓ)
    omega
  · simp

theorem ratio_D (ℓ : ℕ) :
    4 * (optDv c 8 P A N R hc v g).card ≤ 5 * (optDv' c 8 P A N R hc v ℓ g).card := by
  unfold optDv optDv'
  split_ifs with h
  · rw [card_map, card_map]
    have hav := avail_fut_ge (P := P) (A := A) (N := N) (R := R) hK hg (dC_inYV hc h).1
      (show 2 ≤ (dC hc h).1.val from le_rfl)
    have hn := nbrsOut_dC (k := 8) (P := P) (A := A) (N := N) (R := R) hc h
    have := pred_card_le_card_erase (s := (slabR c m 8 P A N R).avail (boxBV c v) g (dC hc h))
      (a := ℓ)
    omega
  · simp

include hA in
theorem ratio_L {ℓ : ℕ} (hℓ : ℓ < 8) (a b : ℕ) :
    19 * (optLv c 8 P A N R hv g a b).card ≤ 30 * (optLv c 8 P A N R hv g ℓ ℓ).card := by
  have h1v : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  have hα1 : 6 ≤ ((slabR c m 8 P A N R).avail (boxBV c v) g (lA v)).card := by
    have := avail_list_ge (P := P) (A := A) (N := N) (R := R) hK hg hA (lA_inYV v).1 h1v
    have := nbrsOut_lA (k := 8) (P := P) (A := A) (N := N) (R := R) (c := c) v
    omega
  have hα2 : 6 ≤ ((slabR c m 8 P A N R).avail (boxBV c v) g (lB hv)).card := by
    have := avail_list_ge (P := P) (A := A) (N := N) (R := R) hK hg hA (lB_inYV hv).1 h1v
    have := nbrsOut_lB (k := 8) (P := P) (A := A) (N := N) (R := R) (c := c) hv
    omega
  set C := slabR c m 8 P A N R
  set A1 := C.avail (boxBV c v) g (lA v)
  set A2 := C.avail (boxBV c v) g (lB hv)
  -- at most one colour of a row is keyed `ℓ`
  have hkey : ∀ (X : Finset ℕ) (w : Fin m), X ⊆ A w →
      X.card ≤ (X.filter (fun p => N w p ≠ ℓ)).card + 1 := by
    intro X w hX
    have hle : (X.filter (fun p => ¬ N w p ≠ ℓ)).card ≤ 1 := by
      refine card_le_one.mpr fun p hp p' hp' => ?_
      rw [mem_filter, not_not] at hp hp'
      exact hK w p p' (hX hp.1) (hX hp'.1) (hp.2.trans hp'.2.symm) (by rw [hp.2]; exact hℓ)
    have := card_filter_add_card_filter_not (s := X) (fun p => N w p ≠ ℓ)
    omega
  have hA1 : A1 ⊆ A v := fun p hp => by
    have := (C.mem_avail.mp hp).1; rwa [slabR_D, slab_D_one h1v] at this
  have hA2 : A2 ⊆ A ⟨v.val + 1, hv⟩ := fun p hp => by
    have := (C.mem_avail.mp hp).1; rwa [slabR_D, slab_D_one h1v] at this
  have hb1 := hkey A1 v hA1
  have hb2 := hkey A2 ⟨v.val + 1, hv⟩ hA2
  set B1 := A1.filter (fun p => N v p ≠ ℓ)
  set B2 := A2.filter (fun p => N ⟨v.val + 1, hv⟩ p ≠ ℓ)
  have hup : (optLv c 8 P A N R hv g a b).card ≤ (offd A1 A2).card :=
    card_le_card (offd_mono (filter_subset _ _) (filter_subset _ _))
  have e1 := card_offd A1 A2
  have e2 := card_offd B1 B2
  have hi : (B1 ∩ B2).card ≤ (A1 ∩ A2).card :=
    card_le_card (inter_subset_inter (filter_subset _ _) (filter_subset _ _))
  have hiA : (A1 ∩ A2).card ≤ A1.card := card_le_card inter_subset_left
  have hB1 : B1.card ≤ A1.card := card_le_card (filter_subset _ _)
  have hB2 : B2.card ≤ A2.card := card_le_card (filter_subset _ _)
  change 19 * (optLv c 8 P A N R hv g a b).card ≤ 30 * (offd B1 B2).card
  have hprod : (A1.card - 1) * (A2.card - 1) ≤ B1.card * B2.card :=
    Nat.mul_le_mul (by omega) (by omega)
  obtain ⟨p, hp⟩ : ∃ p, A1.card = 6 + p := ⟨A1.card - 6, by omega⟩
  obtain ⟨q, hq⟩ : ∃ q, A2.card = 6 + q := ⟨A2.card - 6, by omega⟩
  rw [hp, hq] at e1 hprod
  rw [hp] at hiA
  rw [show 6 + p - 1 = 5 + p by omega, show 6 + q - 1 = 5 + q by omega] at hprod
  nlinarith

/-- The future domino's ratio numerator: `21`, `25` or `30` by availability of the centre values. -/
noncomputable def gR (hv : v.val + 1 < m) (g : Cell c m → ℕ) (a b : ℕ) : ℕ :=
  if h : 2 ≤ c then
    21 + 4 * (if a ∈ (slabR c m 8 P A N R).avail (boxBV c v) g (rA h v) then 0 else 1) +
      4 * (if b ∈ (slabR c m 8 P A N R).avail (boxBV c v) g (rB hv h) then 0 else 1) +
        (if a ∈ (slabR c m 8 P A N R).avail (boxBV c v) g (rA h v) then 0 else 1) *
          (if b ∈ (slabR c m 8 P A N R).avail (boxBV c v) g (rB hv h) then 0 else 1)
  else 21

omit hK hg in
/-- The future domino's arithmetic. -/
theorem R_arith {α₁ α₂ i E I E' I' x y x' y' : ℤ} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1)
    (hx' : x' = 0 ∨ x' = 1) (hy' : y' = 0 ∨ y' = 1) (h1 : E + I = (α₁ - x) * (α₂ - y))
    (h2 : i ≤ I + x + y) (h3 : E' + I' = (α₁ - x') * (α₂ - y')) (h4 : I' + x' * y' = i)
    (hα₁ : 6 ≤ α₁) (hα₂ : 6 ≤ α₂) (hi₁ : i ≤ α₁) :
    20 * E ≤ (21 + 4 * (1 - x) + 4 * (1 - y) + (1 - x) * (1 - y)) * E' := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hx' with rfl | rfl <;>
    rcases hy' with rfl | rfl <;> nlinarith

set_option maxHeartbeats 800000 in
theorem ratio_R (ℓ a b : ℕ) :
    20 * (optRv c 8 P A N R hv g a b).card ≤
      gR (P := P) (A := A) (N := N) (R := R) hv g a b * (optRv c 8 P A N R hv g ℓ ℓ).card := by
  unfold optRv gR
  by_cases h : 2 ≤ c
  · rw [dite_eq_left h, dite_eq_left h, dite_eq_left h, card_map, card_map]
    have hα1 : 6 ≤ ((slabR c m 8 P A N R).avail (boxBV c v) g (rA h v)).card := by
      have := avail_fut_ge (P := P) (A := A) (N := N) (R := R) hK hg (rA_inYV h v).1
        (show 2 ≤ (rA (c := c) h v).1.val by simp [rA])
      have := nbrsOut_rA (k := 8) (P := P) (A := A) (N := N) (R := R) h v
      omega
    have hα2 : 6 ≤ ((slabR c m 8 P A N R).avail (boxBV c v) g (rB hv h)).card := by
      have := avail_fut_ge (P := P) (A := A) (N := N) (R := R) hK hg (rB_inYV h hv).1
        (show 2 ≤ (rB (c := c) hv h).1.val by simp [rB])
      have := nbrsOut_rB (k := 8) (P := P) (A := A) (N := N) (R := R) h hv
      omega
    set A1 := (slabR c m 8 P A N R).avail (boxBV c v) g (rA h v)
    set A2 := (slabR c m 8 P A N R).avail (boxBV c v) g (rB hv h)
    have ea := card_erase_ind A1 a
    have eb := card_erase_ind A2 b
    have ea' := card_erase_ind A1 ℓ
    have eb' := card_erase_ind A2 ℓ
    have e1 := card_offd (A1.erase a) (A2.erase b)
    have e2 := card_offd (A1.erase ℓ) (A2.erase ℓ)
    have hS := erase_inter_erase A1 A2 a b
    have hS' : (A1.erase ℓ) ∩ (A2.erase ℓ) = (A1 ∩ A2).erase ℓ := by
      rw [erase_inter_erase, erase_eq_of_notMem (notMem_erase ℓ _)]
    have f1 := card_erase_ind (A1 ∩ A2) a
    have f2 := card_erase_ind ((A1 ∩ A2).erase a) b
    have f3 := card_erase_ind (A1 ∩ A2) ℓ
    have g1 : (if a ∈ A1 ∩ A2 then 1 else 0) ≤ (if a ∈ A1 then 1 else 0) :=
      ind_le_of_imp fun h => (mem_inter.mp h).1
    have g2 : (if b ∈ (A1 ∩ A2).erase a then 1 else 0) ≤ (if b ∈ A2 then 1 else 0) :=
      ind_le_of_imp fun h => (mem_inter.mp (mem_of_mem_erase h)).2
    have g3 := ind_inter A1 A2 ℓ
    have hiA1 : (A1 ∩ A2).card ≤ A1.card := card_le_card inter_subset_left
    have hiA2 : (A1 ∩ A2).card ≤ A2.card := card_le_card inter_subset_right
    rw [hS] at e1
    rw [hS'] at e2
    have b01 : ∀ (P : Prop) [Decidable P], ((if P then 1 else 0 : ℕ) : ℤ) = 0 ∨
        ((if P then 1 else 0 : ℕ) : ℤ) = 1 := by
      intro P _; split_ifs <;> simp
    have h2n : (A1 ∩ A2).card ≤ (((A1 ∩ A2).erase a).erase b).card + (if a ∈ A1 then 1 else 0) +
        (if b ∈ A2 then 1 else 0) := by omega
    have key := R_arith (α₁ := A1.card) (α₂ := A2.card) (i := (A1 ∩ A2).card)
      (E := (offd (A1.erase a) (A2.erase b)).card) (I := (((A1 ∩ A2).erase a).erase b).card)
      (E' := (offd (A1.erase ℓ) (A2.erase ℓ)).card) (I' := ((A1 ∩ A2).erase ℓ).card)
      (x := (if a ∈ A1 then 1 else 0 : ℕ)) (y := (if b ∈ A2 then 1 else 0 : ℕ))
      (x' := (if ℓ ∈ A1 then 1 else 0 : ℕ)) (y' := (if ℓ ∈ A2 then 1 else 0 : ℕ))
      (b01 _) (b01 _) (b01 _) (b01 _)
      (by push_cast [← ea, ← eb] at e1 ⊢; linarith)
      (by exact_mod_cast h2n)
      (by push_cast [← ea', ← eb'] at e2 ⊢; linarith)
      (by rw [← f3, g3]; push_cast; ring)
      (by exact_mod_cast hα1) (by exact_mod_cast hα2) (by exact_mod_cast hiA1)
    have hgr : ((21 + 4 * (if a ∈ A1 then 0 else 1) + 4 * (if b ∈ A2 then 0 else 1) +
        (if a ∈ A1 then 0 else 1) * (if b ∈ A2 then 0 else 1) : ℕ) : ℤ) =
        21 + 4 * (1 - ((if a ∈ A1 then 1 else 0 : ℕ) : ℤ)) +
          4 * (1 - ((if b ∈ A2 then 1 else 0 : ℕ) : ℤ)) +
            (1 - ((if a ∈ A1 then 1 else 0 : ℕ) : ℤ)) * (1 - ((if b ∈ A2 then 1 else 0 : ℕ) : ℤ)) := by
      by_cases h1 : a ∈ A1 <;> by_cases h2 : b ∈ A2 <;> simp [h1, h2]
    have : (20 * (offd (A1.erase a) (A2.erase b)).card : ℤ) ≤
        ((21 + 4 * (if a ∈ A1 then 0 else 1) + 4 * (if b ∈ A2 then 0 else 1) +
          (if a ∈ A1 then 0 else 1) * (if b ∈ A2 then 0 else 1) : ℕ) : ℤ) *
            (offd (A1.erase ℓ) (A2.erase ℓ)).card := by rw [hgr]; exact key
    exact Int.ofNat_le.mp (by rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]; exact this)
  · rw [dite_eq_right h, dite_eq_right h, dite_eq_right h]; simp

omit hK hg in
/-- At most two labels are unavailable at a future cell of the domino. -/
theorem sum_ind_le {X : Finset ℕ} (hX : X ⊆ range 8) (h6 : 6 ≤ X.card) :
    ∑ a ∈ range 8, (if a ∈ X then 0 else 1 : ℕ) ≤ 2 := by
  rw [sum_ite, sum_const_zero, zero_add, sum_const, smul_eq_mul, mul_one]
  have e : (range 8).filter (fun a => ¬ a ∈ X) = range 8 \ X := by ext a; simp [mem_sdiff]
  rw [e, card_sdiff_of_subset hX, card_range]
  omega

theorem sum_gR : ∑ a ∈ range 8, ∑ b ∈ range 8,
    gR (P := P) (A := A) (N := N) (R := R) hv g a b ≤ 1476 := by
  unfold gR
  by_cases h : 2 ≤ c
  · simp only [dite_eq_left h]
    set A1 := (slabR c m 8 P A N R).avail (boxBV c v) g (rA h v)
    set A2 := (slabR c m 8 P A N R).avail (boxBV c v) g (rB hv h)
    have hsub : ∀ y : Cell c m, 2 ≤ y.1.val → (slabR c m 8 P A N R).avail (boxBV c v) g y ⊆
        range 8 := fun y hy z hz => by
      have := ((slabR c m 8 P A N R).mem_avail.mp hz).1; rwa [slabR_D, slab_D_fut hy] at this
    have h1 := sum_ind_le (hsub (rA h v) (show 2 ≤ 3 by omega)) (by
      have := avail_fut_ge (P := P) (A := A) (N := N) (R := R) hK hg (rA_inYV h v).1
        (show 2 ≤ (rA (c := c) h v).1.val by simp [rA])
      have := nbrsOut_rA (k := 8) (P := P) (A := A) (N := N) (R := R) h v
      omega)
    have h2 := sum_ind_le (hsub (rB hv h) (show 2 ≤ 3 by omega)) (by
      have := avail_fut_ge (P := P) (A := A) (N := N) (R := R) hK hg (rB_inYV h hv).1
        (show 2 ≤ (rB (c := c) hv h).1.val by simp [rB])
      have := nbrsOut_rB (k := 8) (P := P) (A := A) (N := N) (R := R) h hv
      omega)
    set I := fun a => (if a ∈ A1 then 0 else 1 : ℕ)
    set J := fun b => (if b ∈ A2 then 0 else 1 : ℕ)
    have e : ∀ a, ∑ b ∈ range 8, (21 + 4 * I a + 4 * J b + I a * J b) =
        168 + 32 * I a + 4 * (∑ b ∈ range 8, J b) + I a * ∑ b ∈ range 8, J b := by
      intro a
      simp only [sum_add_distrib, sum_const, card_range, smul_eq_mul, ← mul_sum]; ring
    calc ∑ a ∈ range 8, ∑ b ∈ range 8, (21 + 4 * I a + 4 * J b + I a * J b)
        = ∑ a ∈ range 8, (168 + 32 * I a + 4 * (∑ b ∈ range 8, J b) +
            I a * ∑ b ∈ range 8, J b) := sum_congr rfl fun a _ => e a
      _ = 1344 + 32 * (∑ a ∈ range 8, I a) + 32 * (∑ b ∈ range 8, J b) +
            (∑ a ∈ range 8, I a) * (∑ b ∈ range 8, J b) := by
          simp only [sum_add_distrib, sum_const, card_range, smul_eq_mul, ← mul_sum, ← sum_mul]
          ring
      _ ≤ 1476 := by
          have h1' : ∑ a ∈ range 8, I a ≤ 2 := h1
          have h2' : ∑ b ∈ range 8, J b ≤ 2 := h2
          have := Nat.mul_le_mul h1' h2'
          omega
  · simp only [dite_eq_right h, sum_const, card_range, smul_eq_mul]; norm_num

set_option maxHeartbeats 1000000 in
/-- **The vertical box inequality on one fibre** (`k = 8`). -/
theorem box_fibreV (hA : ∀ v, (A v).card = 8) {ℓ : ℕ} (hℓ : ℓ < 8) (hR : ℓ ∈ R v) :
    (((slabR c m 8 P A N R).cls (boxBV c v) g).card : ℚ) * 152 ≤
      ((((slabR c m 8 P A N R).cls (boxBV c v) g).filter (HitV hc hv ℓ)).card : ℚ) * 27675 := by
  set U' := (optUv' c 8 P A N R hc v ℓ g).card
  set D' := (optDv' c 8 P A N R hc v ℓ g).card
  set L' := (optLv c 8 P A N R hv g ℓ ℓ).card
  set R' := (optRv c 8 P A N R hv g ℓ ℓ).card
  have hup := card_cls_le_sumV (k := 8) (P := P) (A := A) (N := N) (R := R) hc hv g
  have hlo := card_hit_geV (P := P) (A := A) (N := N) (R := R) (hc := hc) (hv := hv) hg hℓ hR
  have hU := ratio_U (P := P) hK hg hc (v := v) ℓ
  have hD := ratio_D (P := P) hK hg hc (v := v) ℓ
  have hsum := sum_gR (P := P) (A := A) (N := N) (R := R) hK hg (c := c) hv
  have hterm : ∀ a b : ℕ, ((optUv c 8 P A N R hc v g).card : ℚ) * (optDv c 8 P A N R hc v g).card *
      (optLv c 8 P A N R hv g a b).card * (optRv c 8 P A N R hv g a b).card ≤
        (5 / 4 * U') * (5 / 4 * D') * (30 / 19 * L') *
          ((gR (P := P) (A := A) (N := N) (R := R) hv g a b : ℚ) / 20 * R') := by
    intro a b
    have h1 : ((optUv c 8 P A N R hc v g).card : ℚ) ≤ 5 / 4 * U' := by
      have := (Nat.cast_le (α := ℚ)).mpr hU; push_cast at this; linarith
    have h2 : ((optDv c 8 P A N R hc v g).card : ℚ) ≤ 5 / 4 * D' := by
      have := (Nat.cast_le (α := ℚ)).mpr hD; push_cast at this; linarith
    have h3 : ((optLv c 8 P A N R hv g a b).card : ℚ) ≤ 30 / 19 * L' := by
      have := (Nat.cast_le (α := ℚ)).mpr (ratio_L (P := P) hK hA hg hv hℓ a b)
      push_cast at this; linarith
    have h4 : ((optRv c 8 P A N R hv g a b).card : ℚ) ≤
        (gR (P := P) (A := A) (N := N) (R := R) hv g a b : ℚ) / 20 * R' := by
      have := (Nat.cast_le (α := ℚ)).mpr (ratio_R (P := P) hK hg hv ℓ a b)
      push_cast at this
      rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]; linarith
    have p1 : (0 : ℚ) ≤ (optUv c 8 P A N R hc v g).card := Nat.cast_nonneg _
    have p2 : (0 : ℚ) ≤ (optDv c 8 P A N R hc v g).card := Nat.cast_nonneg _
    have p3 : (0 : ℚ) ≤ (optLv c 8 P A N R hv g a b).card := Nat.cast_nonneg _
    have p4 : (0 : ℚ) ≤ (optRv c 8 P A N R hv g a b).card := Nat.cast_nonneg _
    have q1 : (0 : ℚ) ≤ 5 / 4 * U' := mul_nonneg (by norm_num) (Nat.cast_nonneg _)
    have q2 : (0 : ℚ) ≤ 5 / 4 * D' := mul_nonneg (by norm_num) (Nat.cast_nonneg _)
    have q3 : (0 : ℚ) ≤ 30 / 19 * L' := mul_nonneg (by norm_num) (Nat.cast_nonneg _)
    exact mul_le_mul (mul_le_mul (mul_le_mul h1 h2 p2 q1) h3 p3 (mul_nonneg q1 q2)) h4 p4
      (mul_nonneg (mul_nonneg q1 q2) q3)
  have hcls : (((slabR c m 8 P A N R).cls (boxBV c v) g).card : ℚ) ≤
      ∑ a ∈ range 8, ∑ b ∈ range 8, (5 / 4 * U') * (5 / 4 * D') * (30 / 19 * L') *
        ((gR (P := P) (A := A) (N := N) (R := R) hv g a b : ℚ) / 20 * R') := by
    have := (Nat.cast_le (α := ℚ)).mpr hup
    push_cast at this
    exact le_trans this (sum_le_sum fun a _ => sum_le_sum fun b _ => hterm a b)
  have heq : ∑ a ∈ range 8, ∑ b ∈ range 8, (5 / 4 * (U' : ℚ)) * (5 / 4 * D') * (30 / 19 * L') *
      ((gR (P := P) (A := A) (N := N) (R := R) hv g a b : ℚ) / 20 * R') =
        (25 / 16 * (30 / 19) / 20) * (U' * D' * L' * R') *
          ((∑ a ∈ range 8, ∑ b ∈ range 8, gR (P := P) (A := A) (N := N) (R := R) hv g a b : ℕ) : ℚ) := by
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun b _ => ?_
    ring
  have hsumq : ((∑ a ∈ range 8, ∑ b ∈ range 8, gR (P := P) (A := A) (N := N) (R := R) hv g a b : ℕ) : ℚ)
      ≤ 1476 := by exact_mod_cast hsum
  have hloq : (U' : ℚ) * D' * L' * R' ≤
      ((((slabR c m 8 P A N R).cls (boxBV c v) g).filter (HitV hc hv ℓ)).card : ℚ) := by
    exact_mod_cast hlo
  have hpos : (0 : ℚ) ≤ U' * D' * L' * R' :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  rw [heq] at hcls
  nlinarith

omit hg in
/-- **The vertical box bound** (`k = 8`): at least a `152/27675` fraction of the relaxed-slab
solutions put the relaxed label `ℓ` on both cells of its edge. -/
theorem boxV_bound (hA : ∀ v, (A v).card = 8) {ℓ : ℕ} (hℓ : ℓ < 8) (hR : ℓ ∈ R v) :
    (slabR c m 8 P A N R).Ω.card * 152 ≤
      ((slabR c m 8 P A N R).Ω.filter (HitV hc hv ℓ)).card * 27675 :=
  (slabR c m 8 P A N R).fibre_sum_ge (boxBV c v) _ _ _ fun _ hg' => by
    have := box_fibreV hK ((CSP.mem_Ω _).mp hg') hc hv hA hℓ hR
    exact_mod_cast this

end Eight


/-! ### The ratios at every `k` -/

section General

/-- A single cell's ratio: one label fewer out of at least `k - 3`. -/
theorem ratio_arith1 {k α β : ℕ} (hk : 4 ≤ k) (hα : k - 3 ≤ α) (hβ : α ≤ β + 1) :
    (k - 4) * α ≤ (k - 3) * β := by
  obtain ⟨u, rfl⟩ : ∃ u, k = 4 + u := ⟨k - 4, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, α = u + 1 + r := ⟨α - (u + 1), by omega⟩
  rw [show 4 + u - 4 = u by omega, show 4 + u - 3 = u + 1 by omega]
  have h := Nat.mul_le_mul_left (u + 1) (show u + r ≤ β by omega)
  nlinarith

/-- A domino's ratio: from at least `a = k - 2` colours on each cell, each cell loses at most one
colour and the diagonal pairs are excluded, so the ratio is at most `a(a-1)/((a-1)² - a)`. -/
theorem dom_ratio_arith {k x y i j b₁ b₂ up low : ℕ} (hk : 5 ≤ k) (hx : k - 2 ≤ x)
    (hy : k - 2 ≤ y) (hi : i ≤ x) (hup : up + i ≤ x * y) (hb₁ : x ≤ b₁ + 1) (hb₂ : y ≤ b₂ + 1)
    (hj : j ≤ i) (hlow : low + j = b₁ * b₂) :
    ((k - 3) ^ 2 - (k - 2)) * up ≤ (k - 2) * (k - 3) * low := by
  obtain ⟨t, rfl⟩ : ∃ t, k = 5 + t := ⟨k - 5, by omega⟩
  obtain ⟨p, rfl⟩ : ∃ p, x = 3 + t + p := ⟨x - (3 + t), by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, y = 3 + t + q := ⟨y - (3 + t), by omega⟩
  have e1 : (5 + t - 3) ^ 2 - (5 + t - 2) = t ^ 2 + 3 * t + 1 := by
    rw [show 5 + t - 3 = 2 + t by omega, show 5 + t - 2 = 3 + t by omega]
    have : (2 + t) ^ 2 = t ^ 2 + 3 * t + 1 + (3 + t) := by ring
    omega
  rw [e1, show 5 + t - 2 = 3 + t by omega, show 5 + t - 3 = 2 + t by omega]
  have hb₁' : (2 + t + p : ℤ) ≤ b₁ := by omega
  have hb₂' : (2 + t + q : ℤ) ≤ b₂ := by omega
  zify at hup hlow hi hj ⊢
  have h1 : ((2 + t + p : ℤ)) * (2 + t + q) ≤ (b₁ : ℤ) * b₂ :=
    mul_le_mul hb₁' hb₂' (by positivity) (by omega)
  have key : ((3 + t : ℤ) * (2 + t)) * (((3 + t + p : ℤ) - 1) * ((3 + t + q : ℤ) - 1) - i) -
      ((t : ℤ) ^ 2 + 3 * t + 1) * ((3 + t + p : ℤ) * (3 + t + q) - i) =
        (2 * (3 + t : ℤ) - 1) * ((3 + t + p : ℤ) - i) + (2 + t : ℤ) ^ 2 * p + (3 + t : ℤ) ^ 2 * q +
          (2 * (3 + t : ℤ) - 1) * p * q := by ring
  have hpos : 0 ≤ (2 * (3 + t : ℤ) - 1) * ((3 + t + p : ℤ) - i) + (2 + t : ℤ) ^ 2 * p +
      (3 + t : ℤ) ^ 2 * q + (2 * (3 + t : ℤ) - 1) * p * q := by
    have : (0 : ℤ) ≤ (3 + t + p : ℤ) - i := by linarith
    have h2 : (0 : ℤ) ≤ 2 * (3 + t : ℤ) - 1 := by omega
    exact add_nonneg (add_nonneg (add_nonneg (mul_nonneg h2 this) (by positivity)) (by positivity))
      (mul_nonneg (mul_nonneg h2 (by positivity)) (by positivity))
  have hD : (0 : ℤ) ≤ (t : ℤ) ^ 2 + 3 * t + 1 := by positivity
  have hN : (0 : ℤ) ≤ (3 + t : ℤ) * (2 + t) := by positivity
  calc ((t : ℤ) ^ 2 + 3 * t + 1) * up ≤ ((t : ℤ) ^ 2 + 3 * t + 1) * ((3 + t + p : ℤ) * (3 + t + q) - i) :=
        mul_le_mul_of_nonneg_left (by linarith) hD
    _ ≤ ((3 + t : ℤ) * (2 + t)) * (((3 + t + p : ℤ) - 1) * ((3 + t + q : ℤ) - 1) - i) := by linarith
    _ ≤ (3 + t) * (2 + t) * low := mul_le_mul_of_nonneg_left (by nlinarith) hN

variable (hK : KeyInj k A N) (hA : ∀ v, (A v).card = k) {g : Cell c m → ℕ}
  (hg : (slabR c m k P A N R).Valid g) (hc : 1 ≤ c) {v : Fin m} (hv : v.val + 1 < m)
include hK hg

theorem ratio_U_gen (hk : 4 ≤ k) (ℓ : ℕ) :
    (k - 4) * (optUv c k P A N R hc v g).card ≤ (k - 3) * (optUv' c k P A N R hc v ℓ g).card := by
  unfold optUv optUv'
  split_ifs with h
  · rw [card_map, card_map]
    have hav := avail_fut_ge (P := P) (A := A) (N := N) (R := R) hK hg (uC_inYV hc h).1
      (show 2 ≤ (uC hc h).1.val from le_rfl)
    have hn := nbrsOut_uC (k := k) (P := P) (A := A) (N := N) (R := R) hc h
    have := pred_card_le_card_erase (s := (slabR c m k P A N R).avail (boxBV c v) g (uC hc h))
      (a := ℓ)
    exact ratio_arith1 hk (by omega) (by omega)
  · simp only [card_singleton, mul_one]; omega

theorem ratio_D_gen (hk : 4 ≤ k) (ℓ : ℕ) :
    (k - 4) * (optDv c k P A N R hc v g).card ≤ (k - 3) * (optDv' c k P A N R hc v ℓ g).card := by
  unfold optDv optDv'
  split_ifs with h
  · rw [card_map, card_map]
    have hav := avail_fut_ge (P := P) (A := A) (N := N) (R := R) hK hg (dC_inYV hc h).1
      (show 2 ≤ (dC hc h).1.val from le_rfl)
    have hn := nbrsOut_dC (k := k) (P := P) (A := A) (N := N) (R := R) hc h
    have := pred_card_le_card_erase (s := (slabR c m k P A N R).avail (boxBV c v) g (dC hc h))
      (a := ℓ)
    exact ratio_arith1 hk (by omega) (by omega)
  · simp only [card_singleton, mul_one]; omega

include hA in
theorem ratio_L_gen (hk : 5 ≤ k) {ℓ : ℕ} (hℓ : ℓ < k) (a b : ℕ) :
    ((k - 3) ^ 2 - (k - 2)) * (optLv c k P A N R hv g a b).card ≤
      (k - 2) * (k - 3) * (optLv c k P A N R hv g ℓ ℓ).card := by
  have h1v : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  have hα1 : k - 2 ≤ ((slabR c m k P A N R).avail (boxBV c v) g (lA v)).card := by
    have := avail_list_ge (P := P) (A := A) (N := N) (R := R) hK hg hA (lA_inYV v).1 h1v
    have := nbrsOut_lA (k := k) (P := P) (A := A) (N := N) (R := R) (c := c) v
    omega
  have hα2 : k - 2 ≤ ((slabR c m k P A N R).avail (boxBV c v) g (lB hv)).card := by
    have := avail_list_ge (P := P) (A := A) (N := N) (R := R) hK hg hA (lB_inYV hv).1 h1v
    have := nbrsOut_lB (k := k) (P := P) (A := A) (N := N) (R := R) (c := c) hv
    omega
  set C := slabR c m k P A N R
  set A1 := C.avail (boxBV c v) g (lA v)
  set A2 := C.avail (boxBV c v) g (lB hv)
  have hkey : ∀ (X : Finset ℕ) (w : Fin m), X ⊆ A w →
      X.card ≤ (X.filter (fun p => N w p ≠ ℓ)).card + 1 := by
    intro X w hX
    have hle : (X.filter (fun p => ¬ N w p ≠ ℓ)).card ≤ 1 := by
      refine card_le_one.mpr fun p hp p' hp' => ?_
      rw [mem_filter, not_not] at hp hp'
      exact hK w p p' (hX hp.1) (hX hp'.1) (hp.2.trans hp'.2.symm) (by rw [hp.2]; exact hℓ)
    have := card_filter_add_card_filter_not (s := X) (fun p => N w p ≠ ℓ)
    omega
  have hA1 : A1 ⊆ A v := fun p hp => by
    have := (C.mem_avail.mp hp).1; rwa [slabR_D, slab_D_one h1v] at this
  have hA2 : A2 ⊆ A ⟨v.val + 1, hv⟩ := fun p hp => by
    have := (C.mem_avail.mp hp).1; rwa [slabR_D, slab_D_one h1v] at this
  have hb1 := hkey A1 v hA1
  have hb2 := hkey A2 ⟨v.val + 1, hv⟩ hA2
  set B1 := A1.filter (fun p => N v p ≠ ℓ)
  set B2 := A2.filter (fun p => N ⟨v.val + 1, hv⟩ p ≠ ℓ)
  have hup : (optLv c k P A N R hv g a b).card ≤ (offd A1 A2).card :=
    card_le_card (offd_mono (filter_subset _ _) (filter_subset _ _))
  have e1 := card_offd A1 A2
  have e2 := card_offd B1 B2
  have hi : (B1 ∩ B2).card ≤ (A1 ∩ A2).card :=
    card_le_card (inter_subset_inter (filter_subset _ _) (filter_subset _ _))
  have hiA : (A1 ∩ A2).card ≤ A1.card := card_le_card inter_subset_left
  change _ ≤ (k - 2) * (k - 3) * (offd B1 B2).card
  exact dom_ratio_arith hk hα1 hα2 hiA (by omega) hb1 hb2 hi e2

theorem ratio_R_gen (hk : 5 ≤ k) (ℓ a b : ℕ) :
    ((k - 3) ^ 2 - (k - 2)) * (optRv c k P A N R hv g a b).card ≤
      (k - 2) * (k - 3) * (optRv c k P A N R hv g ℓ ℓ).card := by
  unfold optRv
  by_cases h : 2 ≤ c
  · rw [dite_eq_left h, dite_eq_left h, card_map, card_map]
    have hα1 : k - 2 ≤ ((slabR c m k P A N R).avail (boxBV c v) g (rA h v)).card := by
      have := avail_fut_ge (P := P) (A := A) (N := N) (R := R) hK hg (rA_inYV h v).1
        (show 2 ≤ (rA (c := c) h v).1.val by simp [rA])
      have := nbrsOut_rA (k := k) (P := P) (A := A) (N := N) (R := R) h v
      omega
    have hα2 : k - 2 ≤ ((slabR c m k P A N R).avail (boxBV c v) g (rB hv h)).card := by
      have := avail_fut_ge (P := P) (A := A) (N := N) (R := R) hK hg (rB_inYV h hv).1
        (show 2 ≤ (rB (c := c) hv h).1.val by simp [rB])
      have := nbrsOut_rB (k := k) (P := P) (A := A) (N := N) (R := R) h hv
      omega
    set A1 := (slabR c m k P A N R).avail (boxBV c v) g (rA h v)
    set A2 := (slabR c m k P A N R).avail (boxBV c v) g (rB hv h)
    have hup : (offd (A1.erase a) (A2.erase b)).card ≤ (offd A1 A2).card :=
      card_le_card (offd_mono (erase_subset _ _) (erase_subset _ _))
    have e1 := card_offd A1 A2
    have e2 := card_offd (A1.erase ℓ) (A2.erase ℓ)
    have hi : ((A1.erase ℓ) ∩ (A2.erase ℓ)).card ≤ (A1 ∩ A2).card :=
      card_le_card (inter_subset_inter (erase_subset _ _) (erase_subset _ _))
    have hiA : (A1 ∩ A2).card ≤ A1.card := card_le_card inter_subset_left
    have hb1 := pred_card_le_card_erase (s := A1) (a := ℓ)
    have hb2 := pred_card_le_card_erase (s := A2) (a := ℓ)
    exact dom_ratio_arith hk hα1 hα2 hiA (by omega) (by omega) (by omega) hi e2
  · rw [dite_eq_right h, dite_eq_right h, card_singleton, mul_one, mul_one]
    refine le_trans (Nat.sub_le _ _) ?_
    rw [pow_two]
    exact Nat.mul_le_mul_right _ (by omega)

/-- **The vertical box inequality on one fibre**, at every `k ≥ 5`. -/
theorem box_fibreV_gen (hk : 5 ≤ k) (hA : ∀ v, (A v).card = k) {ℓ : ℕ} (hℓ : ℓ < k)
    (hR : ℓ ∈ R v) :
    ((slabR c m k P A N R).cls (boxBV c v) g).card * ((k - 4) ^ 2 * ((k - 3) ^ 2 - (k - 2)) ^ 2) ≤
      (((slabR c m k P A N R).cls (boxBV c v) g).filter (HitV hc hv ℓ)).card *
        (k ^ 2 * (k - 3) ^ 2 * ((k - 2) * (k - 3)) ^ 2) := by
  set D := (k - 3) ^ 2 - (k - 2)
  set Q := (k - 2) * (k - 3)
  set U' := (optUv' c k P A N R hc v ℓ g).card
  set D' := (optDv' c k P A N R hc v ℓ g).card
  set L' := (optLv c k P A N R hv g ℓ ℓ).card
  set R' := (optRv c k P A N R hv g ℓ ℓ).card
  have hup := card_cls_le_sumV (k := k) (P := P) (A := A) (N := N) (R := R) hc hv g
  have hlo := card_hit_geV (P := P) (A := A) (N := N) (R := R) (hc := hc) (hv := hv) hg hℓ hR
  have hU := ratio_U_gen (P := P) hK hg hc (v := v) (by omega) ℓ
  have hD := ratio_D_gen (P := P) hK hg hc (v := v) (by omega) ℓ
  calc ((slabR c m k P A N R).cls (boxBV c v) g).card * ((k - 4) ^ 2 * D ^ 2)
      ≤ (∑ a ∈ range k, ∑ b ∈ range k,
          (optUv c k P A N R hc v g).card * (optDv c k P A N R hc v g).card *
            (optLv c k P A N R hv g a b).card * (optRv c k P A N R hv g a b).card) *
          ((k - 4) ^ 2 * D ^ 2) := Nat.mul_le_mul_right _ hup
    _ = ∑ a ∈ range k, ∑ b ∈ range k,
          ((k - 4) * (optUv c k P A N R hc v g).card) * ((k - 4) * (optDv c k P A N R hc v g).card) *
            (D * (optLv c k P A N R hv g a b).card) * (D * (optRv c k P A N R hv g a b).card) := by
        rw [sum_mul]
        refine sum_congr rfl fun a _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun b _ => ?_
        ring
    _ ≤ ∑ a ∈ range k, ∑ b ∈ range k, ((k - 3) * U') * ((k - 3) * D') * (Q * L') * (Q * R') :=
        sum_le_sum fun a _ => sum_le_sum fun b _ =>
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hU hD)
            (ratio_L_gen (P := P) hK hA hg hv hk hℓ a b)) (ratio_R_gen (P := P) hK hg hv hk ℓ a b)
    _ = (U' * D' * L' * R') * (k ^ 2 * (k - 3) ^ 2 * Q ^ 2) := by
        simp only [sum_const, card_range, smul_eq_mul]; ring
    _ ≤ _ := Nat.mul_le_mul_right _ hlo

omit hg in
/-- **The vertical box bound at every `k ≥ 5`**: at least a
`(k-4)²((k-3)² - (k-2))² / (k²(k-3)²((k-2)(k-3))²)` fraction of the relaxed-slab solutions put
the relaxed label `ℓ` on both cells of its edge. -/
theorem boxV_bound_gen (hk : 5 ≤ k) (hA : ∀ v, (A v).card = k) {ℓ : ℕ} (hℓ : ℓ < k)
    (hR : ℓ ∈ R v) :
    (slabR c m k P A N R).Ω.card * ((k - 4) ^ 2 * ((k - 3) ^ 2 - (k - 2)) ^ 2) ≤
      ((slabR c m k P A N R).Ω.filter (HitV hc hv ℓ)).card *
        (k ^ 2 * (k - 3) ^ 2 * ((k - 2) * (k - 3)) ^ 2) :=
  (slabR c m k P A N R).fibre_sum_ge (boxBV c v) _ _ _ fun _ hg' =>
    box_fibreV_gen hK ((CSP.mem_Ω _).mp hg') hc hv hk hA hℓ hR

end General

end GridGen.Gauge
