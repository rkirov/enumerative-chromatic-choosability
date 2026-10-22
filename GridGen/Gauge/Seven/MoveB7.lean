/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Seven.Move7
import GridGen.Gauge.Seven.Short7

/-!
# The move bound at `k = 7`

A move through the hole of a freshly deleted star loses at most `θ · #Hit + ε · Z`. The bad set is
split at the hole row (`bad_le_H`, `bad_le_D`):

* **absorbed paths** cost `thW L · #Hit` each: the two-cell path by the box bound `θ₂ ≤ 13/100`,
  longer ones by the absorbed chain bound (`absorb_chain_head`, `absorb_chain_last`);
* **residual paths**: three cells are vertical through the star's future cell (`vert_three`) and
  cost `jntW 3 · #Hit = 7/81 · #Hit` per phase by the joint box bound; longer ones cost
  `rhW L · Z` per phase by the chain bound (`event_chain_le`).

Summing with the path counts of `Counts7` gives the constants `thetaM + thetaJ` and `epsM`. The box bounds
are hypotheses here (`Boxes7`); the D orientation of `θ₂` is the H orientation reflected.
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

/-- **The box bounds** the move bound takes. -/
structure Boxes7 : Prop where
  /-- The vertical three-cell residual chain against the star of its middle row, one phase. -/
  joint3 : ∀ {c m : ℕ} {P A : Fin m → Finset ℕ} {M : Fin m → ℕ → ℕ}, KeyInj 7 A M →
    (∀ v, (A v).card = 7) → (∀ v a, a ∈ A v → 6 ≤ (P v).card ∨ a ∉ P v) → ∀ (hc : 1 ≤ c)
    {x y h ℓ₀ : ℕ}, x ≠ y → x < 7 → y < 7 → (h = x ∨ h = y) → (ℓ₀ = x ∨ ℓ₀ = y) →
    ∀ (v : ℕ) (hv : v + 2 < m),
      (∀ a ∈ A ⟨v + 1, by omega⟩, M ⟨v + 1, by omega⟩ a ≠ h) → ∀ {a₀ : ℕ},
        a₀ ∈ A ⟨v + 1, by omega⟩ → 7 ≤ M ⟨v + 1, by omega⟩ a₀ →
      ((slab c m 7 P A M).Ω.filter (Event (A := A) M x y (vert3 hc v hv) ℓ₀)).card * 81 ≤
        7 * ((slab c m 7 P A M).Ω.filter (Hit hc ⟨v + 1, by omega⟩ a₀ h)).card
  /-- The two-cell path against the star, hole in the head row. -/
  absH : ∀ {c m : ℕ} {P A : Fin m → Finset ℕ} {M : Fin m → ℕ → ℕ}, KeyInj 7 A M →
    (∀ v, (A v).card = 7) → (∀ v a, a ∈ A v → 6 ≤ (P v).card ∨ a ∉ P v) → ∀ (hc : 1 ≤ c)
    {x y h : ℕ}, x ≠ y → x < 7 → y < 7 → (h = x ∨ h = y) → ∀ (v : ℕ) (hv : v + 1 < m),
      (∀ a ∈ A ⟨v + 1, hv⟩, M ⟨v + 1, hv⟩ a ≠ h) → ∀ {a₀ : ℕ}, a₀ ∈ A ⟨v + 1, hv⟩ →
        7 ≤ M ⟨v + 1, hv⟩ a₀ →
      ((slab c m 7 P A M).Ω.filter (Event (A := A) M x y
        (vert2 hc v hv) h)).card * 100 ≤
        13 * ((slab c m 7 P A M).Ω.filter (Hit hc ⟨v + 1, hv⟩ a₀ h)).card
  /-- The two-cell path against the star, hole in the last row. -/
  absD : ∀ {c m : ℕ} {P A : Fin m → Finset ℕ} {M : Fin m → ℕ → ℕ}, KeyInj 7 A M →
    (∀ v, (A v).card = 7) → (∀ v a, a ∈ A v → 6 ≤ (P v).card ∨ a ∉ P v) → ∀ (hc : 1 ≤ c)
    {x y h : ℕ}, x ≠ y → x < 7 → y < 7 → (h = x ∨ h = y) → ∀ (v : ℕ) (hv : v + 1 < m),
      (∀ a ∈ A ⟨v, by omega⟩, M ⟨v, by omega⟩ a ≠ h) → ∀ {a₀ : ℕ}, a₀ ∈ A ⟨v, by omega⟩ →
        7 ≤ M ⟨v, by omega⟩ a₀ →
      ((slab c m 7 P A M).Ω.filter (Event (A := A) M x y
        (vert2 hc v hv) (oth x y h))).card * 100 ≤
        13 * ((slab c m 7 P A M).Ω.filter (Hit hc ⟨v, by omega⟩ a₀ h)).card

/-- The absorbed weight of a path of `L` cells. -/
noncomputable def thW (L : ℕ) : ℚ := if L = 2 then 13 / 100 else 256 / 81 * (1 / 4) ^ L

/-- The residual weight of a path of `L` cells against `Z`, per phase (three cells are charged to
the star instead, `jntW`). -/
noncomputable def rhW (L : ℕ) : ℚ := if L = 3 then 0 else 1 / 12 * (1 / 4) ^ L

/-- The residual weight of a path of `L` cells against the star, per phase. -/
noncomputable def jntW (L : ℕ) : ℚ := if L = 3 then 7 / 81 else 0

theorem thW_nonneg (L : ℕ) : 0 ≤ thW L := by unfold thW; split_ifs <;> positivity

theorem rhW_nonneg (L : ℕ) : 0 ≤ rhW L := by unfold rhW; split_ifs <;> positivity

theorem jntW_nonneg (L : ℕ) : 0 ≤ jntW L := by unfold jntW; split_ifs <;> norm_num

/-- **The absorbed constant.** -/
noncomputable def thetaM : ℚ := ∑ L ∈ range 21, (A7 L : ℚ) * thW L + 64 * M7 / 4 ^ 20

/-- **The joint constant** (both phases). -/
noncomputable def thetaJ : ℚ := ∑ L ∈ range 21, (R7 L : ℚ) * (2 * jntW L)

/-- **The residual constant** (both phases). -/
noncomputable def epsM : ℚ := ∑ L ∈ range 21, (R7 L : ℚ) * (2 * rhW L) + 567 / 8 * M7 / 4 ^ 20

theorem thW_sum_le (c m : ℕ) :
    ∑ L ∈ range 21, (A7 L : ℚ) * thW L +
        ∑ L ∈ Ico 21 (Fintype.card (Cell c m) + 1), (tailA L : ℚ) * thW L ≤ thetaM := by
  unfold thetaM
  refine add_le_add le_rfl ?_
  have e : ∑ L ∈ Ico 21 (Fintype.card (Cell c m) + 1), (tailA L : ℚ) * thW L =
      256 / 81 * ∑ L ∈ Ico 21 (Fintype.card (Cell c m) + 1), (tailA L : ℚ) * (1 / 4) ^ L := by
    rw [mul_sum]
    refine sum_congr rfl fun L hL => ?_
    rw [mem_Ico] at hL
    rw [thW, ite_eq_right (by omega)]; ring
  rw [e]
  have := tailA_sum_le (Fintype.card (Cell c m) + 1)
  linarith

theorem rhW_sum_le (c m : ℕ) :
    ∑ L ∈ range 21, (R7 L : ℚ) * (2 * rhW L) +
        ∑ L ∈ Ico 21 (Fintype.card (Cell c m) + 1), (tailR L : ℚ) * (2 * rhW L) ≤ epsM := by
  unfold epsM
  refine add_le_add le_rfl ?_
  have e : ∑ L ∈ Ico 21 (Fintype.card (Cell c m) + 1), (tailR L : ℚ) * (2 * rhW L) =
      1 / 6 * ∑ L ∈ Ico 21 (Fintype.card (Cell c m) + 1), (tailR L : ℚ) * (1 / 4) ^ L := by
    rw [mul_sum]
    refine sum_congr rfl fun L hL => ?_
    rw [mem_Ico] at hL
    rw [rhW, ite_eq_right (by omega)]; ring
  rw [e]
  have := tailR_sum_le (Fintype.card (Cell c m) + 1)
  linarith

theorem jntW_sum_le (c m : ℕ) :
    ∑ L ∈ range 21, (R7 L : ℚ) * (2 * jntW L) +
        ∑ L ∈ Ico 21 (Fintype.card (Cell c m) + 1), (tailR L : ℚ) * (2 * jntW L) ≤ thetaJ := by
  unfold thetaJ
  have : ∑ L ∈ Ico 21 (Fintype.card (Cell c m) + 1), (tailR L : ℚ) * (2 * jntW L) = 0 :=
    sum_eq_zero fun L hL => by
      rw [mem_Ico] at hL; rw [jntW, ite_eq_right (by omega)]; ring
  rw [this, add_zero]

/-! ### Arithmetic of one path -/

theorem le_absorbed {E H : ℚ} (n : ℕ) (h : E * 27 * (4 ^ n * 3) ≤ 64 * H) :
    E ≤ 256 / 81 * (1 / 4) ^ (n + 1) * H := by
  have e : (256 / 81 : ℚ) * (1 / 4) ^ (n + 1) * H = 64 * H / (81 * 4 ^ n) := by
    rw [pow_succ, one_div_pow]; field_simp; ring
  rw [e, le_div_iff₀ (by positivity)]
  linarith

theorem le_residual {E Z : ℚ} (n : ℕ) (h : E * (4 ^ (n + 1) * 3) ≤ Z) :
    E ≤ 1 / 12 * (1 / 4) ^ n * Z := by
  have e : (1 / 12 : ℚ) * (1 / 4) ^ n * Z = Z / (4 ^ (n + 1) * 3) := by
    rw [one_div_pow, pow_succ]; field_simp; ring
  rw [e, le_div_iff₀ (by positivity)]
  exact h

/-! ### The constants -/

theorem thetaJ_le : thetaJ ≤ 14 / 81 := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20⟩ := R7_vals
  have h0 : R7 0 = 0 := by simp [R7]
  have h1 : R7 1 = 0 := by simp [R7]
  unfold thetaJ
  simp only [sum_range_succ, sum_range_zero, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, h14, h15, h16, h17, h18, h19, h20, jntW]
  norm_num

theorem thetaM_le : thetaM ≤ 41 / 200 := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20⟩ := A7_vals
  have h0 : A7 0 = 0 := by decide
  have h1 : A7 1 = 0 := by decide
  unfold thetaM
  simp only [sum_range_succ, sum_range_zero, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, h14, h15, h16, h17, h18, h19, h20, thW, M7]
  norm_num

theorem epsM_le : epsM ≤ 1 / 337 := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20⟩ := R7_vals
  have h0 : R7 0 = 0 := by simp [R7]
  have h1 : R7 1 = 0 := by simp [R7]
  unfold epsM
  simp only [sum_range_succ, sum_range_zero, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, h14, h15, h16, h17, h18, h19, h20, rhW, M7]
  norm_num

variable {c m : ℕ} {P A : Fin m → Finset ℕ} {M : Fin m → ℕ → ℕ}

/-! ### One path -/

section Paths

variable (B : Boxes7) (hK : KeyInj 7 A M) (hA : ∀ v, (A v).card = 7)
  (hP : ∀ v a, a ∈ A v → 6 ≤ (P v).card ∨ a ∉ P v) (hc : 1 ≤ c)

theorem headRow_vert3 {hc : 1 ≤ c} {v : ℕ} {hv : v + 2 < m} : headRow (vert3 hc v hv) = v + 2 := rfl

theorem lastRow_vert3 {hc : 1 ≤ c} {v : ℕ} {hv : v + 2 < m} : lastRow (vert3 hc v hv) = v := rfl

include B hK hA hP in
/-- **A residual path**, one phase: three cells against the star of the middle row, longer ones
against `Z`. -/
theorem resid_path {w x y h ℓ₀ : ℕ} (hxy : x ≠ y) (hx : x < 7) (hy : y < 7) (hh : h = x ∨ h = y)
    (hℓ : ℓ₀ = x ∨ ℓ₀ = y) {r : Fin m} (hhole : ∀ a ∈ A r, M r a ≠ h) {a₀ : ℕ} (ha₀ : a₀ ∈ A r)
    (h7 : 7 ≤ M r a₀) {l : List (Cell c m)} (hl : CrossPath hc w l) (hch : Chordless l)
    (hmid : ∀ v (hv : v + 2 < m), l = vert3 hc v hv → v + 1 = r.val) :
    (((slab c m 7 P A M).Ω.filter (Event (A := A) M x y l ℓ₀)).card : ℚ) ≤
      rhW l.length * (slab c m 7 P A M).Ω.card +
        jntW l.length * ((slab c m 7 P A M).Ω.filter (Hit hc r a₀ h)).card := by
  by_cases h3 : l.length = 3
  · obtain ⟨v, hv, rfl⟩ := vert_three hl hch h3
    have hv1 : v + 1 < m := Nat.lt_of_succ_lt hv
    have hr : r = ⟨v + 1, hv1⟩ := Fin.ext (hmid v hv rfl).symm
    subst hr
    have := B.joint3 hK hA hP hc hxy hx hy hh hℓ v hv hhole ha₀ h7
    rw [h3, rhW, ite_eq_left rfl, jntW, ite_eq_left rfl]
    have h' : (((slab c m 7 P A M).Ω.filter (Event (A := A) M x y (vert3 hc v hv) ℓ₀)).card : ℚ) * 81 ≤
        7 * ((slab c m 7 P A M).Ω.filter (Hit hc ⟨v + 1, hv1⟩ a₀ h)).card := by
      exact_mod_cast this
    have hZ : (0 : ℚ) ≤ (slab c m 7 P A M).Ω.card := by positivity
    linarith
  · rw [rhW, ite_eq_right h3, jntW, ite_eq_right h3, zero_mul, add_zero]
    have := event_chain_le (P := P) hK hA hc hx hy hℓ hl
    exact le_residual _ (by exact_mod_cast this)

include B hK hA hP in
/-- **An absorbed path, hole in the head row.** -/
theorem absH_path {w x y h : ℕ} (hxy : x ≠ y) (hx : x < 7) (hy : y < 7) (hh : h = x ∨ h = y)
    (hw : w + 1 < m) (hhole : ∀ a ∈ A ⟨w + 1, hw⟩, M ⟨w + 1, hw⟩ a ≠ h) {a₀ : ℕ}
    (ha₀ : a₀ ∈ A ⟨w + 1, hw⟩) (h7 : 7 ≤ M ⟨w + 1, hw⟩ a₀)
    {l : List (Cell c m)} (hl : CrossPath hc w l) (hch : Chordless l) (hrow : headRow l = w + 1) :
    (((slab c m 7 P A M).Ω.filter (Event (A := A) M x y l h)).card : ℚ) ≤
      thW l.length * ((slab c m 7 P A M).Ω.filter (Hit hc ⟨w + 1, hw⟩ a₀ h)).card := by
  have h2 := two_le_length hl
  by_cases hL : l.length = 2
  · obtain ⟨hw', rfl⟩ := vert_two hl hL
    have := B.absH hK hA hP hc hxy hx hy hh w hw hhole ha₀ h7
    rw [hL, thW, ite_eq_left rfl]
    have h' : (((slab c m 7 P A M).Ω.filter (Event (A := A) M x y (vert2 hc w hw') h)).card : ℚ) * 100 ≤
        13 * ((slab c m 7 P A M).Ω.filter (Hit hc ⟨w + 1, hw⟩ a₀ h)).card := by
      exact_mod_cast this
    linarith
  · obtain ⟨v₁, -, h1⟩ := hl.2.2.2.1
    have hv : v₁ = ⟨w + 1, hw⟩ := Fin.ext (by rw [headRow_of_head h1] at hrow; exact hrow)
    rw [hv] at h1
    have := absorb_chain_head hK hA hP hc hx hy hh ha₀ h7 hl hch h1 (by omega)
    rw [thW, ite_eq_right hL]
    obtain ⟨n, hn⟩ : ∃ n, l.length = n + 1 := ⟨l.length - 1, by omega⟩
    rw [hn] at this ⊢
    exact le_absorbed n (by exact_mod_cast this)

include B hK hA hP in
/-- **An absorbed path, hole in the last row.** -/
theorem absD_path {w x y h ℓ₀ : ℕ} (hxy : x ≠ y) (hx : x < 7) (hy : y < 7) (hh : h = x ∨ h = y)
    (hℓ : ℓ₀ = x ∨ ℓ₀ = y) (hw : w < m) (hhole : ∀ a ∈ A ⟨w, hw⟩, M ⟨w, hw⟩ a ≠ h) {a₀ : ℕ}
    (ha₀ : a₀ ∈ A ⟨w, hw⟩) (h7 : 7 ≤ M ⟨w, hw⟩ a₀)
    {l : List (Cell c m)} (hl : CrossPath hc w l) (hch : Chordless l) (hrow : lastRow l = w)
    (hlab : lab x y ℓ₀ (l.length - 1) = h) :
    (((slab c m 7 P A M).Ω.filter (Event (A := A) M x y l ℓ₀)).card : ℚ) ≤
      thW l.length * ((slab c m 7 P A M).Ω.filter (Hit hc ⟨w, hw⟩ a₀ h)).card := by
  have h2 := two_le_length hl
  by_cases hL : l.length = 2
  · obtain ⟨hw', rfl⟩ := vert_two hl hL
    have hℓh : ℓ₀ = oth x y h := by
      rw [← hlab]; simp only [hL, lab]; rw [ite_eq_right (by omega), oth_oth hxy hℓ]
    subst hℓh
    have := B.absD hK hA hP hc hxy hx hy hh w hw' hhole ha₀ h7
    rw [hL, thW, ite_eq_left rfl]
    have h' : (((slab c m 7 P A M).Ω.filter (Event (A := A) M x y (vert2 hc w hw') (oth x y h))).card : ℚ) * 100 ≤
        13 * ((slab c m 7 P A M).Ω.filter (Hit hc ⟨w, hw⟩ a₀ h)).card := by
      exact_mod_cast this
    linarith
  · obtain ⟨v₂, -, h2'⟩ := hl.2.2.2.2
    have hv : v₂ = ⟨w, hw⟩ := Fin.ext (by rw [lastRow_of_last h2'] at hrow; exact hrow)
    rw [hv] at h2'
    have := absorb_chain_last hK hA hP hc hx hy hℓ ha₀ h7 hl hch h2' hlab (by omega)
    rw [thW, ite_eq_right hL]
    obtain ⟨n, hn⟩ : ∃ n, l.length = n + 1 := ⟨l.length - 1, by omega⟩
    rw [hn] at this ⊢
    exact le_absorbed n (by exact_mod_cast this)

end Paths

theorem lab_inj {x y ℓ ℓ' : ℕ} (hxy : x ≠ y) (hℓ : ℓ = x ∨ ℓ = y) (hℓ' : ℓ' = x ∨ ℓ' = y)
    (j : ℕ) (h : lab x y ℓ j = lab x y ℓ' j) : ℓ = ℓ' := by
  unfold lab at h
  split_ifs at h
  · exact h
  · have := congrArg (oth x y) h
    rwa [oth_oth hxy hℓ, oth_oth hxy hℓ'] at this

/-! ### The move bound -/

section Move

variable (B : Boxes7) (hK : KeyInj 7 A M) (hA : ∀ v, (A v).card = 7)
  (hP : ∀ v a, a ∈ A v → 6 ≤ (P v).card ∨ a ∉ P v) (hc : 1 ≤ c)

include B hK hA hP in
/-- The residual sum. -/
theorem resid_sum {w x y h : ℕ} (hxy : x ≠ y) (hx : x < 7) (hy : y < 7) (hh : h = x ∨ h = y)
    {r : Fin m} (hhole : ∀ a ∈ A r, M r a ≠ h) {a₀ : ℕ} (ha₀ : a₀ ∈ A r) (h7 : 7 ≤ M r a₀)
    {Q : List (Cell c m) → Prop} [DecidablePred Q]
    (hQ : ∀ l, CrossPath hc w l → Q l →
      Chordless l ∧ ∀ v (hv : v + 2 < m), l = vert3 hc v hv → v + 1 = r.val) :
    ∑ l ∈ (crossPaths hc w).filter Q, ∑ ℓ₀ ∈ ({x, y} : Finset ℕ),
        (((slab c m 7 P A M).Ω.filter (Event (A := A) M x y l ℓ₀)).card : ℚ) ≤
      (∑ l ∈ (crossPaths hc w).filter Q, 2 * rhW l.length) * (slab c m 7 P A M).Ω.card +
        (∑ l ∈ (crossPaths hc w).filter Q, 2 * jntW l.length) *
          ((slab c m 7 P A M).Ω.filter (Hit hc r a₀ h)).card := by
  rw [sum_mul, sum_mul, ← sum_add_distrib]
  refine sum_le_sum fun l hl => ?_
  obtain ⟨hlc, hq⟩ := mem_filter.mp hl
  have hcp : CrossPath hc w l := (mem_filter.mp hlc).2
  obtain ⟨hch, hmid⟩ := hQ l hcp hq
  calc ∑ ℓ₀ ∈ ({x, y} : Finset ℕ),
        (((slab c m 7 P A M).Ω.filter (Event (A := A) M x y l ℓ₀)).card : ℚ)
      ≤ ∑ ℓ₀ ∈ ({x, y} : Finset ℕ), (rhW l.length * (slab c m 7 P A M).Ω.card +
          jntW l.length * ((slab c m 7 P A M).Ω.filter (Hit hc r a₀ h)).card) :=
        sum_le_sum fun ℓ₀ hℓ₀ => resid_path B hK hA hP hc hxy hx hy hh (by simpa using hℓ₀)
          hhole ha₀ h7 hcp hch hmid
    _ = _ := by
        rw [sum_const, card_pair hxy, nsmul_eq_mul]; push_cast; ring

include B hK hA hP in
/-- **The move bound, hole in row `w + 1`.** -/
theorem move_H {w x y h : ℕ} (hxy : x ≠ y) (hx : x < 7) (hy : y < 7) (hh : h = x ∨ h = y)
    (hw : w + 1 < m) (hhole : ∀ a ∈ A ⟨w + 1, hw⟩, M ⟨w + 1, hw⟩ a ≠ h) {a₀ : ℕ}
    (ha₀ : a₀ ∈ A ⟨w + 1, hw⟩) (h7 : 7 ≤ M ⟨w + 1, hw⟩ a₀) :
    (((slab c m 7 P A M).Ω.filter (Bad hc M w x y)).card : ℚ) ≤
      (thetaM + thetaJ) * ((slab c m 7 P A M).Ω.filter (Hit hc ⟨w + 1, hw⟩ a₀ h)).card +
        epsM * (slab c m 7 P A M).Ω.card := by
  set H := (((slab c m 7 P A M).Ω.filter (Hit hc ⟨w + 1, hw⟩ a₀ h)).card : ℚ)
  have hH0 : 0 ≤ H := by positivity
  rw [add_mul, add_assoc]
  refine le_trans (bad_le_H (P := P) hc hxy hh hw hhole) (add_le_add ?_ ?_)
  · calc _ ≤ ∑ l ∈ (crossPaths hc w).filter (fun l => Chordless l ∧ headRow l = w + 1),
          thW l.length * ((slab c m 7 P A M).Ω.filter (Hit hc ⟨w + 1, hw⟩ a₀ h)).card :=
          sum_le_sum fun l hl => by
            obtain ⟨hlc, hch, hrow⟩ := mem_filter.mp hl
            exact absH_path B hK hA hP hc hxy hx hy hh hw hhole ha₀ h7 (mem_filter.mp hlc).2 hch hrow
      _ = (∑ l ∈ (crossPaths hc w).filter (fun l => Chordless l ∧ headRow l = w + 1),
          thW l.length) * ((slab c m 7 P A M).Ω.filter (Hit hc ⟨w + 1, hw⟩ a₀ h)).card := by
          rw [sum_mul]
      _ ≤ _ := by
          have hs := sum_chordless_HA (m := m) hc w thW thW_nonneg
          have ht := thW_sum_le c m
          exact mul_le_mul_of_nonneg_right (hs.trans ht) (by positivity)
  · refine le_trans (resid_sum B hK hA hP hc hxy hx hy hh hhole ha₀ h7 fun l hl hq =>
      ⟨hq.1, fun v hv e => by
        obtain ⟨v₂, hw₂, h2⟩ := hl.2.2.2.2
        have h1 := lastRow_of_last h2
        have h3 := hq.2
        rw [e, lastRow_vert3] at h1; rw [e, headRow_vert3] at h3
        simp only; omega⟩) ?_
    have hs := sum_chordless_HR (m := m) hc w (fun L => 2 * rhW L)
      (fun L => mul_nonneg (by norm_num) (rhW_nonneg L))
    have ht := rhW_sum_le c m
    have hs' := sum_chordless_HR (m := m) hc w (fun L => 2 * jntW L)
      (fun L => mul_nonneg (by norm_num) (jntW_nonneg L))
    have ht' := jntW_sum_le c m
    rw [add_comm]
    exact add_le_add (mul_le_mul_of_nonneg_right (hs'.trans ht') hH0)
      (mul_le_mul_of_nonneg_right (hs.trans ht) (by positivity))

include B hK hA hP in
/-- **The move bound, hole in row `w`.** -/
theorem move_D {w x y h : ℕ} (hxy : x ≠ y) (hx : x < 7) (hy : y < 7) (hh : h = x ∨ h = y)
    (hw : w < m) (hhole : ∀ a ∈ A ⟨w, hw⟩, M ⟨w, hw⟩ a ≠ h) {a₀ : ℕ}
    (ha₀ : a₀ ∈ A ⟨w, hw⟩) (h7 : 7 ≤ M ⟨w, hw⟩ a₀) :
    (((slab c m 7 P A M).Ω.filter (Bad hc M w x y)).card : ℚ) ≤
      (thetaM + thetaJ) * ((slab c m 7 P A M).Ω.filter (Hit hc ⟨w, hw⟩ a₀ h)).card +
        epsM * (slab c m 7 P A M).Ω.card := by
  set H := (((slab c m 7 P A M).Ω.filter (Hit hc ⟨w, hw⟩ a₀ h)).card : ℚ)
  have hH0 : 0 ≤ H := by positivity
  rw [add_mul, add_assoc]
  refine le_trans (bad_le_D (P := P) hc hxy hh hw hhole) (add_le_add ?_ ?_)
  · calc _ ≤ ∑ l ∈ (crossPaths hc w).filter (fun l => Chordless l ∧ lastRow l = w),
          thW l.length * H :=
          sum_le_sum fun l hl => by
            obtain ⟨hlc, hch, hrow⟩ := mem_filter.mp hl
            have hcp : CrossPath hc w l := (mem_filter.mp hlc).2
            set F := ({x, y} : Finset ℕ).filter (fun ℓ₀ => lab x y ℓ₀ (l.length - 1) = h)
            have hF : F.card ≤ 1 := by
              refine card_le_one.mpr fun a ha b hb => ?_
              rw [mem_filter] at ha hb
              exact lab_inj hxy (by simpa using ha.1) (by simpa using hb.1) _ (ha.2.trans hb.2.symm)
            calc _ ≤ ∑ ℓ₀ ∈ F, thW l.length * H := sum_le_sum fun ℓ₀ hℓ₀ => by
                  rw [mem_filter] at hℓ₀
                  exact absD_path B hK hA hP hc hxy hx hy hh (by simpa using hℓ₀.1) hw hhole ha₀ h7
                    hcp hch hrow hℓ₀.2
              _ = F.card * (thW l.length * H) := by rw [sum_const, nsmul_eq_mul]
              _ ≤ 1 * (thW l.length * H) := mul_le_mul_of_nonneg_right (by exact_mod_cast hF)
                  (mul_nonneg (thW_nonneg _) (by positivity))
              _ = _ := one_mul _
      _ = (∑ l ∈ (crossPaths hc w).filter (fun l => Chordless l ∧ lastRow l = w),
          thW l.length) * H := by rw [sum_mul]
      _ ≤ _ := by
          have hs := sum_chordless_DA (m := m) hc w thW thW_nonneg
          have ht := thW_sum_le c m
          exact mul_le_mul_of_nonneg_right (hs.trans ht) (by positivity)
  · refine le_trans (resid_sum B hK hA hP hc hxy hx hy hh hhole ha₀ h7 fun l hl hq =>
      ⟨hq.1, fun v hv e => by
        obtain ⟨v₁, hw₁, h1⟩ := hl.2.2.2.1
        have h1' := headRow_of_head h1
        have h3 := hq.2
        rw [e, headRow_vert3] at h1'; rw [e, lastRow_vert3] at h3
        simp only; omega⟩) ?_
    have hs := sum_chordless_DR (m := m) hc w (fun L => 2 * rhW L)
      (fun L => mul_nonneg (by norm_num) (rhW_nonneg L))
    have ht := rhW_sum_le c m
    have hs' := sum_chordless_DR (m := m) hc w (fun L => 2 * jntW L)
      (fun L => mul_nonneg (by norm_num) (jntW_nonneg L))
    have ht' := jntW_sum_le c m
    rw [add_comm]
    exact add_le_add (mul_le_mul_of_nonneg_right (hs'.trans ht') hH0)
      (mul_le_mul_of_nonneg_right (hs.trans ht) (by positivity))

end Move

end GridGen.Gauge
