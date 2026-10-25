/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Pins5

/-!
# Height four, `k = 5`: the marginal blocks

The instances of `block_core` (`GridGen/Four/Pins5.lean`): for a block of one row or two adjacent
rows, the number of colourings in `sts X₁ X₂ X₃ X₄` (`|Xᵢ| ≥ 4`) with a given proper colouring of
the block is computed by prepending rows (`card_sts`, `card_sts3`, `card_sts2`), and lies between
`ℓ c` and `c`:

| block | `c` | `ℓ` |
|---|---|---|
| row 1 | `|sts3 X₂ X₃ X₄|` | `2/3` |
| row 2 | `|X₁| · |sts2 X₃ X₄|` | `1/2` |
| rows 1, 2 | `|sts2 X₃ X₄|` | `2/3` |
| rows 2, 3 | `|X₁| · |X₄|` | `9/16` |

Rows 3 and 4 and the pair 3, 4 follow by reversing the column (`card_filter_rev`). With the
weights `GU 5 w ∈ [ρ g, g]` this is `ai_research_notes/H4_K5_REVIEW_2026-10-24.md` Lemma B
(`blk_bound`); combined with the peeling chains it bounds every pin (`pin_sum`).
-/

namespace GridGen.Four

open Finset

/-! ### Counting with prescribed rows -/

theorem sts2_mono {C C' D : Finset ℕ} (h : C ⊆ C') : sts2 C D ⊆ sts2 C' D := by
  intro p hp; rw [mem_sts2] at hp ⊢; exact ⟨h hp.1, hp.2.1, hp.2.2⟩

theorem sts3_mono {B B' C D : Finset ℕ} (h : B ⊆ B') : sts3 B C D ⊆ sts3 B' C D := by
  intro p hp; rw [mem_sts3] at hp ⊢; exact ⟨h hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2⟩

theorem card_sts2_bounds (C D : Finset ℕ) :
    ((C.card : ℝ) - 1) * D.card ≤ (sts2 C D).card ∧ ((sts2 C D).card : ℝ) ≤ C.card * D.card := by
  have h := card_sts2 C D
  have h1 : ((C ∩ D).card : ℤ) ≤ D.card := by exact_mod_cast card_le_card inter_subset_right
  have h0 : (0 : ℤ) ≤ (C ∩ D).card := Nat.cast_nonneg _
  have hR : ((sts2 C D).card : ℝ) = (C.card : ℝ) * D.card - (C ∩ D).card := by exact_mod_cast h
  have h1' : ((C ∩ D).card : ℝ) ≤ D.card := by exact_mod_cast h1
  have h0' : (0 : ℝ) ≤ (C ∩ D).card := Nat.cast_nonneg _
  constructor <;> nlinarith

theorem card_sts3_bounds (B C D : Finset ℕ) :
    ((B.card : ℝ) - 1) * (sts2 C D).card ≤ (sts3 B C D).card ∧
      ((sts3 B C D).card : ℝ) ≤ B.card * (sts2 C D).card := by
  have h := card_sts3 B C D
  have h1 : (sts2 (B ∩ C) D).card ≤ (sts2 C D).card := card_le_card (sts2_mono inter_subset_right)
  have hR : ((sts3 B C D).card : ℝ) = (B.card : ℝ) * (sts2 C D).card - (sts2 (B ∩ C) D).card := by
    exact_mod_cast h
  have h1' : ((sts2 (B ∩ C) D).card : ℝ) ≤ (sts2 C D).card := by exact_mod_cast h1
  have h0' : (0 : ℝ) ≤ (sts2 (B ∩ C) D).card := Nat.cast_nonneg _
  constructor <;> nlinarith

theorem card_singleton_inter_le (x : ℕ) (X : Finset ℕ) : (({x} ∩ X).card : ℝ) ≤ 1 := by
  have := card_le_card (inter_subset_left (s₁ := ({x} : Finset ℕ)) (s₂ := X))
  rw [card_singleton] at this; exact_mod_cast this

theorem filt_r1 {A B C D : Finset ℕ} {x : ℕ} (hx : x ∈ A) :
    (sts A B C D).filter (fun t => rowfun 0 t = x) = sts {x} B C D := by
  ext t; simp only [mem_filter, mem_sts, mem_singleton]
  constructor
  · rintro ⟨⟨-, h2, h3, h4, p1, p2, p3⟩, h⟩; exact ⟨h, h2, h3, h4, p1, p2, p3⟩
  · rintro ⟨h, h2, h3, h4, p1, p2, p3⟩; exact ⟨⟨h ▸ hx, h2, h3, h4, p1, p2, p3⟩, h⟩

theorem filt_r2 {A B C D : Finset ℕ} {x : ℕ} (hx : x ∈ B) :
    (sts A B C D).filter (fun t => rowfun 1 t = x) = sts A {x} C D := by
  ext t; simp only [mem_filter, mem_sts, mem_singleton]
  constructor
  · rintro ⟨⟨h1, -, h3, h4, p1, p2, p3⟩, h⟩; exact ⟨h1, h, h3, h4, p1, p2, p3⟩
  · rintro ⟨h1, h, h3, h4, p1, p2, p3⟩; exact ⟨⟨h1, h ▸ hx, h3, h4, p1, p2, p3⟩, h⟩

theorem filt_r12 {A B C D : Finset ℕ} {x y : ℕ} (hx : x ∈ A) (hy : y ∈ B) :
    (sts A B C D).filter (fun t => (rowfun 0 t, rowfun 1 t) = (x, y)) = sts {x} {y} C D := by
  ext t; simp only [mem_filter, mem_sts, mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨-, -, h3, h4, p1, p2, p3⟩, h, h'⟩; exact ⟨h, h', h3, h4, p1, p2, p3⟩
  · rintro ⟨h, h', h3, h4, p1, p2, p3⟩; exact ⟨⟨h ▸ hx, h' ▸ hy, h3, h4, p1, p2, p3⟩, h, h'⟩

theorem filt_r23 {A B C D : Finset ℕ} {y z : ℕ} (hy : y ∈ B) (hz : z ∈ C) :
    (sts A B C D).filter (fun t => (rowfun 1 t, rowfun 2 t) = (y, z)) = sts A {y} {z} D := by
  ext t; simp only [mem_filter, mem_sts, mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨h1, -, -, h4, p1, p2, p3⟩, h, h'⟩; exact ⟨h1, h, h', h4, p1, p2, p3⟩
  · rintro ⟨h1, h, h', h4, p1, p2, p3⟩; exact ⟨⟨h1, h ▸ hy, h' ▸ hz, h4, p1, p2, p3⟩, h, h'⟩

/-- The count with row 1 prescribed: between `2/3` and `1` of `|sts3 X₂ X₃ X₄|`. -/
theorem count_r1 {A B C D : Finset ℕ} (hB : 4 ≤ B.card) {x : ℕ} (hx : x ∈ A) :
    2 / 3 * ((sts3 B C D).card : ℝ) ≤ ((sts A B C D).filter (fun t => rowfun 0 t = x)).card ∧
      (((sts A B C D).filter (fun t => rowfun 0 t = x)).card : ℝ) ≤ (sts3 B C D).card := by
  rw [filt_r1 hx]
  have h := card_sts {x} B C D
  rw [card_singleton] at h
  have hR : ((sts {x} B C D).card : ℝ) = (sts3 B C D).card - (sts3 ({x} ∩ B) C D).card := by
    have : ((sts {x} B C D).card : ℝ) = (1 : ℝ) * (sts3 B C D).card - (sts3 ({x} ∩ B) C D).card := by
      exact_mod_cast h
    linarith
  obtain ⟨a1, -⟩ := card_sts3_bounds B C D
  obtain ⟨-, b2⟩ := card_sts3_bounds ({x} ∩ B) C D
  have hs := card_singleton_inter_le x B
  have hS : (0 : ℝ) ≤ (sts2 C D).card := Nat.cast_nonneg _
  have hB' : (4 : ℝ) ≤ B.card := by exact_mod_cast hB
  have h0 : (0 : ℝ) ≤ (sts3 ({x} ∩ B) C D).card := Nat.cast_nonneg _
  rw [hR]
  constructor <;> nlinarith

/-- The count with row 2 prescribed: between `1/2` and `1` of `|X₁| · |sts2 X₃ X₄|`. -/
theorem count_r2 {A B C D : Finset ℕ} (hA : 4 ≤ A.card) (hC : 4 ≤ C.card) {x : ℕ} (hx : x ∈ B) :
    1 / 2 * ((A.card : ℝ) * (sts2 C D).card)
        ≤ ((sts A B C D).filter (fun t => rowfun 1 t = x)).card ∧
      (((sts A B C D).filter (fun t => rowfun 1 t = x)).card : ℝ) ≤ A.card * (sts2 C D).card := by
  rw [filt_r2 hx]
  have h := card_sts A {x} C D
  have hR : ((sts A {x} C D).card : ℝ)
      = (A.card : ℝ) * (sts3 {x} C D).card - (sts3 (A ∩ {x}) C D).card := by
    have e : ((sts A {x} C D).card : ℝ)
        = (A.card : ℝ) * (sts3 {x} C D).card - (sts3 (A ∩ {x}) C D).card := by exact_mod_cast h
    exact e
  have hb := card_sts3 {x} C D
  rw [card_singleton] at hb
  have hbR : ((sts3 {x} C D).card : ℝ) = (sts2 C D).card - (sts2 ({x} ∩ C) D).card := by
    have : ((sts3 {x} C D).card : ℝ) = (1 : ℝ) * (sts2 C D).card - (sts2 ({x} ∩ C) D).card := by
      exact_mod_cast hb
    linarith
  have hsub : ((sts3 (A ∩ {x}) C D).card : ℝ) ≤ (sts3 {x} C D).card := by
    exact_mod_cast card_le_card (sts3_mono inter_subset_right)
  obtain ⟨-, c2⟩ := card_sts2_bounds ({x} ∩ C) D
  obtain ⟨c3, -⟩ := card_sts2_bounds C D
  have hs := card_singleton_inter_le x C
  have hD : (0 : ℝ) ≤ D.card := Nat.cast_nonneg _
  have hA' : (4 : ℝ) ≤ A.card := by exact_mod_cast hA
  have hC' : (4 : ℝ) ≤ C.card := by exact_mod_cast hC
  have h0 : (0 : ℝ) ≤ (sts3 (A ∩ {x}) C D).card := Nat.cast_nonneg _
  have h0' : (0 : ℝ) ≤ (sts2 ({x} ∩ C) D).card := Nat.cast_nonneg _
  have hS : (0 : ℝ) ≤ (sts2 C D).card := Nat.cast_nonneg _
  -- `b = |sts3 {x} C D| ∈ [2/3 · S, S]`
  have hb1 : 2 / 3 * ((sts2 C D).card : ℝ) ≤ (sts3 {x} C D).card := by nlinarith
  have hb2 : ((sts3 {x} C D).card : ℝ) ≤ (sts2 C D).card := by linarith
  rw [hR]
  constructor <;> nlinarith

/-- The count with rows 1, 2 prescribed: between `2/3` and `1` of `|sts2 X₃ X₄|`. -/
theorem count_r12 {A B C D : Finset ℕ} (hC : 4 ≤ C.card) {x y : ℕ} (hx : x ∈ A) (hy : y ∈ B)
    (hxy : x ≠ y) :
    2 / 3 * ((sts2 C D).card : ℝ)
        ≤ ((sts A B C D).filter (fun t => (rowfun 0 t, rowfun 1 t) = (x, y))).card ∧
      (((sts A B C D).filter (fun t => (rowfun 0 t, rowfun 1 t) = (x, y))).card : ℝ)
        ≤ (sts2 C D).card := by
  rw [filt_r12 hx hy]
  have h := card_sts {x} {y} C D
  have e0 : ({x} : Finset ℕ) ∩ {y} = ∅ := by
    ext z; simp only [mem_inter, mem_singleton, notMem_empty, iff_false, not_and]
    rintro rfl rfl; exact hxy rfl
  rw [e0, card_singleton] at h
  have h00 : (sts3 (∅ : Finset ℕ) C D).card = 0 := by
    rw [Finset.card_eq_zero]; ext p; simp [mem_sts3]
  rw [h00] at h
  have hb := card_sts3 {y} C D
  rw [card_singleton] at hb
  push_cast at h hb
  have hR : ((sts {x} {y} C D).card : ℝ) = (sts2 C D).card - (sts2 ({y} ∩ C) D).card := by
    have e1 : ((sts {x} {y} C D).card : ℝ) = (sts3 {y} C D).card := by
      have : ((sts {x} {y} C D).card : ℤ) = (sts3 {y} C D).card := by linarith
      exact_mod_cast this
    have e2 : ((sts3 {y} C D).card : ℝ) = (1 : ℝ) * (sts2 C D).card - (sts2 ({y} ∩ C) D).card := by
      exact_mod_cast hb
    linarith
  obtain ⟨-, c2⟩ := card_sts2_bounds ({y} ∩ C) D
  obtain ⟨c3, -⟩ := card_sts2_bounds C D
  have hs := card_singleton_inter_le y C
  have hD : (0 : ℝ) ≤ D.card := Nat.cast_nonneg _
  have hC' : (4 : ℝ) ≤ C.card := by exact_mod_cast hC
  have h0' : (0 : ℝ) ≤ (sts2 ({y} ∩ C) D).card := Nat.cast_nonneg _
  rw [hR]
  constructor <;> nlinarith

/-- The count with rows 2, 3 prescribed: between `9/16` and `1` of `|X₁| · |X₄|`. -/
theorem count_r23 {A B C D : Finset ℕ} (hA : 4 ≤ A.card) (hD : 4 ≤ D.card) {y z : ℕ} (hy : y ∈ B)
    (hz : z ∈ C) (hyz : y ≠ z) :
    9 / 16 * ((A.card : ℝ) * D.card)
        ≤ ((sts A B C D).filter (fun t => (rowfun 1 t, rowfun 2 t) = (y, z))).card ∧
      (((sts A B C D).filter (fun t => (rowfun 1 t, rowfun 2 t) = (y, z))).card : ℝ)
        ≤ A.card * D.card := by
  rw [filt_r23 hy hz]
  have h := card_sts A {y} {z} D
  have hR : ((sts A {y} {z} D).card : ℝ)
      = (A.card : ℝ) * (sts3 {y} {z} D).card - (sts3 (A ∩ {y}) {z} D).card := by
    exact_mod_cast h
  have e0 : ({y} : Finset ℕ) ∩ {z} = ∅ := by
    ext x; simp only [mem_inter, mem_singleton, notMem_empty, iff_false, not_and]
    rintro rfl rfl; exact hyz rfl
  have hb := card_sts3 {y} {z} D
  rw [e0, card_singleton] at hb
  have h00 : (sts2 (∅ : Finset ℕ) D).card = 0 := by
    rw [Finset.card_eq_zero]; ext p; simp [mem_sts2]
  rw [h00] at hb
  have hz2 := card_sts2 {z} D
  rw [card_singleton] at hz2
  push_cast at hb hz2
  have hbR : ((sts3 {y} {z} D).card : ℝ) = D.card - ({z} ∩ D).card := by
    have : ((sts3 {y} {z} D).card : ℤ) = 1 * D.card - ({z} ∩ D).card := by linarith
    have : ((sts3 {y} {z} D).card : ℝ) = 1 * D.card - ({z} ∩ D).card := by exact_mod_cast this
    linarith
  have hsub : ((sts3 (A ∩ {y}) {z} D).card : ℝ) ≤ (sts3 {y} {z} D).card := by
    exact_mod_cast card_le_card (sts3_mono inter_subset_right)
  have hs := card_singleton_inter_le z D
  have hA' : (4 : ℝ) ≤ A.card := by exact_mod_cast hA
  have hD' : (4 : ℝ) ≤ D.card := by exact_mod_cast hD
  have h0 : (0 : ℝ) ≤ (sts3 (A ∩ {y}) {z} D).card := Nat.cast_nonneg _
  have h0' : (0 : ℝ) ≤ ({z} ∩ D).card := Nat.cast_nonneg _
  have hb1 : 3 / 4 * (D.card : ℝ) ≤ (sts3 {y} {z} D).card := by rw [hbR]; linarith
  have hb2 : ((sts3 {y} {z} D).card : ℝ) ≤ D.card := by rw [hbR]; linarith
  rw [hR]
  constructor <;> nlinarith

/-! ### Reversing the column -/

/-- The reversed column. -/
def rev4 (t : T4) : T4 := (r4 t, r3 t, r2 t, r1 t)

theorem rev4_rev4 (t : T4) : rev4 (rev4 t) = t := by
  obtain ⟨a, b, c, d⟩ := t; rfl

theorem mem_sts_rev {A B C D : Finset ℕ} {t : T4} : rev4 t ∈ sts D C B A ↔ t ∈ sts A B C D := by
  simp only [mem_sts, rev4, r1, r2, r3, r4]
  constructor
  · rintro ⟨h1, h2, h3, h4, p1, p2, p3⟩
    exact ⟨h4, h3, h2, h1, Ne.symm p3, Ne.symm p2, Ne.symm p1⟩
  · rintro ⟨h1, h2, h3, h4, p1, p2, p3⟩
    exact ⟨h4, h3, h2, h1, Ne.symm p3, Ne.symm p2, Ne.symm p1⟩

theorem card_filter_rev (A B C D : Finset ℕ) (P : T4 → Prop) [DecidablePred P] :
    ((sts A B C D).filter P).card = ((sts D C B A).filter (fun t => P (rev4 t))).card := by
  refine Finset.card_bij (fun t _ => rev4 t) (fun t ht => ?_) (fun t₁ _ t₂ _ h => ?_) (fun t ht => ?_)
  · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨mem_sts_rev.mpr h1, by rw [rev4_rev4]; exact h2⟩
  · have := congrArg rev4 h; rwa [rev4_rev4, rev4_rev4] at this
  · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp ht
    refine ⟨rev4 t, Finset.mem_filter.mpr ⟨?_, h2⟩, rev4_rev4 t⟩
    rw [← mem_sts_rev, rev4_rev4]; exact h1

/-! ### The weights -/

section weights

variable {w : Wt} {X₁ X₂ X₃ X₄ : Finset ℕ}

theorem u_bounds5 (hw : InBox 5 w) {t : T4} (ht : Proper t) :
    118 / 125 * vA 3 w ≤ GU 5 w t ∧ GU 5 w t ≤ vA 3 w := by
  have hA := vA_pos_of_inBox (by norm_num) hw
  have e3 : ((5 : ℕ) : ℝ) - 2 = 3 := by norm_num
  rw [e3] at hA
  have hg := gw_mem (nextW_inBox (by norm_num) hw) t
  rw [rho_five] at hg
  rw [GU_eq (by norm_num) w (by rw [e3]; exact hA.ne') ht, e3]
  constructor <;> nlinarith [hg.1, hg.2]

theorem u_ratio5 (hw : InBox 5 w) {t t' : T4} (ht : Proper t) (ht' : Proper t') :
    GU 5 w t ≤ 125 / 118 * GU 5 w t' := by
  have := GU_ratio (by norm_num) hw ht ht'
  rw [rho_five] at this; norm_num at this ⊢; linarith

end weights

/-! ### Blocks -/

/-- A block event: none, one row in a colour set, or two adjacent rows (`r`, `r + 1`) in colour
sets, with declared sizes. -/
inductive Blk
  | none
  | one (r : Fin 4) (D : Finset ℕ) (d : ℕ)
  | two (r : Fin 3) (D D' : Finset ℕ) (d d' : ℕ)

/-- `m/(m + ρ ℓ (M - m))` for `m < M`, else `1`. -/
def βQ (m M : ℕ) (ℓ : ℚ) : ℚ := if m < M then m / (m + 118 / 125 * ℓ * (M - m)) else 1

def ℓone (r : Fin 4) : ℚ := if r = 0 ∨ r = 3 then 2 / 3 else 1 / 2
def ℓtwo (r : Fin 3) : ℚ := if r = 1 then 9 / 16 else 2 / 3

namespace Blk

def ev : Blk → T4 → Bool
  | none, _ => true
  | one r D _, t => decide (rowfun r t ∈ D)
  | two r D D' _ _, t => decide (rowfun r.castSucc t ∈ D) && decide (rowfun r.succ t ∈ D')

def reads : Blk → Fin 4 → Bool
  | none, _ => false
  | one r _ _, i => decide (r = i)
  | two r _ _ _ _, i => decide (r.castSucc = i) || decide (r.succ = i)

def ok : Blk → Prop
  | none => True
  | one _ D d => D.card ≤ d
  | two _ D D' d d' => D.card ≤ d ∧ D'.card ≤ d'

def bnd : Blk → ℚ
  | none => 1
  | one r _ d => βQ d 4 (ℓone r)
  | two r _ _ d d' => βQ (d * d') 12 (ℓtwo r)

theorem ev_setRow {b : Blk} {i : Fin 4} (h : b.reads i = false) (t : T4) (x : ℕ) :
    b.ev (setRow i t x) = b.ev t := by
  cases b with
  | none => rfl
  | one r D d =>
    simp only [reads, decide_eq_false_iff_not] at h
    simp only [ev, rowfun_setRow_ne h]
  | two r D D' d d' =>
    simp only [reads, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    simp only [ev, rowfun_setRow_ne h.1, rowfun_setRow_ne h.2]

end Blk

/-- `block_core` with the bound `βQ`. -/
theorem block_beta {α : Type*} [DecidableEq α] (Ω : Finset T4) (u : T4 → ℝ) (π : T4 → α)
    (F T : Finset α) (hF : ∀ t ∈ Ω, π t ∈ F) {g c : ℝ} {ℓ : ℚ} (hℓ : 0 < ℓ)
    (hc : 0 ≤ c) (hg : 0 ≤ g) (hu : ∀ t ∈ Ω, 118 / 125 * g ≤ u t ∧ u t ≤ g)
    (hN : ∀ τ ∈ F, (ℓ : ℝ) * c ≤ ((Ω.filter (fun t => π t = τ)).card : ℝ) ∧
      ((Ω.filter (fun t => π t = τ)).card : ℝ) ≤ c)
    {m M : ℕ} (hm : (F ∩ T).card ≤ m) (hM : M ≤ F.card) :
    ∑ t ∈ Ω.filter (fun t => π t ∈ T), u t ≤ ((βQ m M ℓ : ℚ) : ℝ) * ∑ t ∈ Ω, u t := by
  have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hu0 : ∀ t ∈ Ω, 0 ≤ u t := fun t ht =>
    le_trans (mul_nonneg (by norm_num) hg) (hu t ht).1
  have h := block_core Ω u π F T hF (ρ := 118 / 125) (by norm_num) hℓ'.le hc hg hu hN hm hM
  unfold βQ
  split_ifs with hmM
  · have hmM' : (m : ℝ) < M := by exact_mod_cast hmM
    have hpos : (0 : ℝ) < (m : ℝ) + 118 / 125 * (ℓ : ℝ) * ((M : ℝ) - m) := by
      have : (0 : ℝ) < 118 / 125 * (ℓ : ℝ) * ((M : ℝ) - m) :=
        mul_pos (mul_pos (by norm_num) hℓ') (by linarith)
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    push_cast
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    linarith
  · push_cast
    rw [one_mul]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun t ht _ => hu0 t ht)

section instances

variable {w : Wt} {X₁ X₂ X₃ X₄ : Finset ℕ}

/-- `block_beta` for the weights `GU 5 w` on `sts X₁ X₂ X₃ X₄`. -/
theorem block_GU (hw : InBox 5 w) {α : Type*} [DecidableEq α] (π : T4 → α) (F T : Finset α)
    (hF : ∀ t ∈ sts X₁ X₂ X₃ X₄, π t ∈ F) {c : ℝ} {ℓ : ℚ} (hℓ : 0 < ℓ) (hc : 0 ≤ c)
    (hN : ∀ τ ∈ F, (ℓ : ℝ) * c ≤ (((sts X₁ X₂ X₃ X₄).filter (fun t => π t = τ)).card : ℝ) ∧
      (((sts X₁ X₂ X₃ X₄).filter (fun t => π t = τ)).card : ℝ) ≤ c)
    {m M : ℕ} (hm : (F ∩ T).card ≤ m) (hM : M ≤ F.card) :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => π t ∈ T), GU 5 w t
      ≤ ((βQ m M ℓ : ℚ) : ℝ) * ∑ t ∈ sts X₁ X₂ X₃ X₄, GU 5 w t := by
  have hA := vA_pos_of_inBox (by norm_num) hw
  rw [show ((5 : ℕ) : ℝ) - 2 = 3 by norm_num] at hA
  exact block_beta _ _ π F T hF hℓ hc hA.le
    (fun t ht => u_bounds5 hw (proper_of_mem_sts ht)) hN hm hM

theorem card_inter_le_of {α : Type*} [DecidableEq α] (F T : Finset α) {m : ℕ} (h : T.card ≤ m) :
    (F ∩ T).card ≤ m := (card_le_card inter_subset_right).trans h

theorem twelve_le (C D : Finset ℕ) (hC : 4 ≤ C.card) (hD : 4 ≤ D.card) : 12 ≤ (sts2 C D).card := by
  have h := (card_sts2_bounds C D).1
  have hC' : (4 : ℝ) ≤ C.card := by exact_mod_cast hC
  have hD' : (4 : ℝ) ≤ D.card := by exact_mod_cast hD
  have : (12 : ℝ) ≤ (sts2 C D).card := by nlinarith
  exact_mod_cast this

/-- **Lemma B, one row.** -/
theorem blk_row (hw : InBox 5 w) (h₁ : 4 ≤ X₁.card) (h₂ : 4 ≤ X₂.card) (h₃ : 4 ≤ X₃.card)
    (h₄ : 4 ≤ X₄.card) (r : Fin 4) (D : Finset ℕ) {d : ℕ} (hd : D.card ≤ d) :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => rowfun r t ∈ D), GU 5 w t
      ≤ ((βQ d 4 (ℓone r) : ℚ) : ℝ) * ∑ t ∈ sts X₁ X₂ X₃ X₄, GU 5 w t := by
  have hm := card_inter_le_of (X₁) D hd
  fin_cases r
  · refine block_GU hw (rowfun 0) X₁ D (fun t ht => (mem_sts.mp ht).1) (c := (sts3 X₂ X₃ X₄).card)
      (by norm_num [ℓone]) (Nat.cast_nonneg _) (fun x hx => ?_) (card_inter_le_of _ D hd) h₁
    have := count_r1 (C := X₃) (D := X₄) h₂ hx
    exact ⟨le_of_eq_of_le (by norm_num [ℓone]) this.1, this.2⟩
  · refine block_GU hw (rowfun 1) X₂ D (fun t ht => (mem_sts.mp ht).2.1)
      (c := (X₁.card : ℝ) * (sts2 X₃ X₄).card) (by norm_num [ℓone]) (by positivity)
      (fun x hx => ?_) (card_inter_le_of _ D hd) h₂
    have := count_r2 (D := X₄) h₁ h₃ hx
    exact ⟨le_of_eq_of_le (by norm_num [ℓone]) this.1, this.2⟩
  · refine block_GU hw (rowfun 2) X₃ D (fun t ht => (mem_sts.mp ht).2.2.1)
      (c := (X₄.card : ℝ) * (sts2 X₂ X₁).card) (by norm_num [ℓone]) (by positivity)
      (fun x hx => ?_) (card_inter_le_of _ D hd) h₃
    rw [card_filter_rev]
    have e : (sts X₄ X₃ X₂ X₁).filter (fun t => rowfun 2 (rev4 t) = x)
        = (sts X₄ X₃ X₂ X₁).filter (fun t => rowfun 1 t = x) := rfl
    rw [e]
    have := count_r2 (D := X₁) h₄ h₂ hx
    exact ⟨le_of_eq_of_le (by norm_num [ℓone]) this.1, this.2⟩
  · refine block_GU hw (rowfun 3) X₄ D (fun t ht => (mem_sts.mp ht).2.2.2.1)
      (c := (sts3 X₃ X₂ X₁).card) (by norm_num [ℓone]) (Nat.cast_nonneg _)
      (fun x hx => ?_) (card_inter_le_of _ D hd) h₄
    rw [card_filter_rev]
    have e : (sts X₄ X₃ X₂ X₁).filter (fun t => rowfun 3 (rev4 t) = x)
        = (sts X₄ X₃ X₂ X₁).filter (fun t => rowfun 0 t = x) := rfl
    rw [e]
    have := count_r1 (C := X₂) (D := X₁) h₃ hx
    exact ⟨le_of_eq_of_le (by norm_num [ℓone]) this.1, this.2⟩

/-- **Lemma B, two adjacent rows.** -/
theorem blk_pair (hw : InBox 5 w) (h₁ : 4 ≤ X₁.card) (h₂ : 4 ≤ X₂.card) (h₃ : 4 ≤ X₃.card)
    (h₄ : 4 ≤ X₄.card) (r : Fin 3) (D D' : Finset ℕ) {d d' : ℕ} (hd : D.card ≤ d)
    (hd' : D'.card ≤ d') :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => (rowfun r.castSucc t, rowfun r.succ t) ∈ D ×ˢ D'),
        GU 5 w t
      ≤ ((βQ (d * d') 12 (ℓtwo r) : ℚ) : ℝ) * ∑ t ∈ sts X₁ X₂ X₃ X₄, GU 5 w t := by
  have hT : (D ×ˢ D').card ≤ d * d' := by rw [card_product]; exact Nat.mul_le_mul hd hd'
  fin_cases r
  · refine block_GU hw (fun t => (rowfun 0 t, rowfun 1 t)) (sts2 X₁ X₂) (D ×ˢ D')
      (fun t ht => ?_) (c := (sts2 X₃ X₄).card) (by norm_num [ℓtwo]) (Nat.cast_nonneg _)
      (fun τ hτ => ?_) (card_inter_le_of _ _ hT) (twelve_le _ _ h₁ h₂)
    · obtain ⟨a1, a2, -, -, p1, -, -⟩ := mem_sts.mp ht
      exact mem_sts2.mpr ⟨a1, a2, p1⟩
    · obtain ⟨x, y⟩ := τ
      obtain ⟨hx, hy, hxy⟩ := mem_sts2.mp hτ
      have := count_r12 (D := X₄) h₃ hx hy hxy
      exact ⟨le_of_eq_of_le (by norm_num [ℓtwo]) this.1, this.2⟩
  · refine block_GU hw (fun t => (rowfun 1 t, rowfun 2 t)) (sts2 X₂ X₃) (D ×ˢ D')
      (fun t ht => ?_) (c := (X₁.card : ℝ) * X₄.card) (by norm_num [ℓtwo]) (by positivity)
      (fun τ hτ => ?_) (card_inter_le_of _ _ hT) (twelve_le _ _ h₂ h₃)
    · obtain ⟨-, a2, a3, -, -, p2, -⟩ := mem_sts.mp ht
      exact mem_sts2.mpr ⟨a2, a3, p2⟩
    · obtain ⟨y, z⟩ := τ
      obtain ⟨hy, hz, hyz⟩ := mem_sts2.mp hτ
      have := count_r23 h₁ h₄ hy hz hyz
      exact ⟨le_of_eq_of_le (by norm_num [ℓtwo]) this.1, this.2⟩
  · refine block_GU hw (fun t => (rowfun 2 t, rowfun 3 t)) (sts2 X₃ X₄) (D ×ˢ D')
      (fun t ht => ?_) (c := (sts2 X₂ X₁).card) (by norm_num [ℓtwo]) (Nat.cast_nonneg _)
      (fun τ hτ => ?_) (card_inter_le_of _ _ hT) (twelve_le _ _ h₃ h₄)
    · obtain ⟨-, -, a3, a4, -, -, p3⟩ := mem_sts.mp ht
      exact mem_sts2.mpr ⟨a3, a4, p3⟩
    · obtain ⟨x, y⟩ := τ
      obtain ⟨hx, hy, hxy⟩ := mem_sts2.mp hτ
      rw [card_filter_rev]
      have e : (sts X₄ X₃ X₂ X₁).filter (fun t => (rowfun 2 (rev4 t), rowfun 3 (rev4 t)) = (x, y))
          = (sts X₄ X₃ X₂ X₁).filter (fun t => (rowfun 0 t, rowfun 1 t) = (y, x)) := by
        refine Finset.filter_congr (fun t _ => ?_)
        simp only [rev4, rowfun, Prod.mk.injEq]; exact and_comm
      rw [e]
      have := count_r12 (D := X₁) h₂ hy hx (Ne.symm hxy)
      exact ⟨le_of_eq_of_le (by norm_num [ℓtwo]) this.1, this.2⟩

/-- **Lemma B** for a block event. -/
theorem blk_bound (hw : InBox 5 w) (h₁ : 4 ≤ X₁.card) (h₂ : 4 ≤ X₂.card) (h₃ : 4 ≤ X₃.card)
    (h₄ : 4 ≤ X₄.card) (b : Blk) (hb : b.ok) :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => b.ev t = true), GU 5 w t
      ≤ ((b.bnd : ℚ) : ℝ) * ∑ t ∈ sts X₁ X₂ X₃ X₄, GU 5 w t := by
  cases b with
  | none =>
    simp only [Blk.ev, Blk.bnd, Finset.filter_true_of_mem (fun _ _ => rfl)]; push_cast; simp
  | one r D d =>
    have e : (sts X₁ X₂ X₃ X₄).filter (fun t => (Blk.one r D d).ev t = true)
        = (sts X₁ X₂ X₃ X₄).filter (fun t => rowfun r t ∈ D) :=
      Finset.filter_congr (fun t _ => by simp [Blk.ev])
    rw [e]; exact blk_row hw h₁ h₂ h₃ h₄ r D hb
  | two r D D' d d' =>
    have e : (sts X₁ X₂ X₃ X₄).filter (fun t => (Blk.two r D D' d d').ev t = true)
        = (sts X₁ X₂ X₃ X₄).filter
          (fun t => (rowfun r.castSucc t, rowfun r.succ t) ∈ D ×ˢ D') :=
      Finset.filter_congr (fun t _ => by simp [Blk.ev, Finset.mem_product])
    rw [e]; exact blk_pair hw h₁ h₂ h₃ h₄ r D D' hb.1 hb.2

/-- **A pin**: a block event and a peeling chain. -/
theorem pin_sum (hw : InBox 5 w) (h₁ : 4 ≤ X₁.card) (h₂ : 4 ≤ X₂.card) (h₃ : 4 ≤ X₃.card)
    (h₄ : 4 ≤ X₄.card) (b : Blk) (hb : b.ok) (fs : List Fac) (hfs : PeelOK b.reads fs) :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => (allEv fs t && b.ev t) = true), GU 5 w t
      ≤ ((((fs.map Fac.bnd).prod * b.bnd : ℚ)) : ℝ) * ∑ t ∈ sts X₁ X₂ X₃ X₄, GU 5 w t := by
  have hu0 : ∀ t, 0 ≤ GU 5 w t := GU_nonneg (by norm_num) hw
  have hR : ∀ t ∈ sts X₁ X₂ X₃ X₄, ∀ t' ∈ sts X₁ X₂ X₃ X₄, GU 5 w t ≤ 125 / 118 * GU 5 w t' :=
    fun t ht t' ht' => u_ratio5 hw (proper_of_mem_sts ht) (proper_of_mem_sts ht')
  have h1 := peel_chain (GU 5 w) hu0 hR h₁ h₂ h₃ h₄ b.reads b.ev
    (fun i hi t x => Blk.ev_setRow hi t x) fs hfs
  have h2 := blk_bound hw h₁ h₂ h₃ h₄ b hb
  have hp : (0 : ℝ) ≤ (((fs.map Fac.bnd).prod : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ (fs.map Fac.bnd).prod :=
      List.prod_nonneg (fun x hx => by
        obtain ⟨f, -, rfl⟩ := List.mem_map.mp hx; exact f.bnd_nonneg)
    exact_mod_cast this
  calc _ ≤ (((fs.map Fac.bnd).prod : ℚ) : ℝ)
        * ∑ t ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => b.ev t = true), GU 5 w t := h1
    _ ≤ (((fs.map Fac.bnd).prod : ℚ) : ℝ) * (((b.bnd : ℚ) : ℝ) * ∑ t ∈ sts X₁ X₂ X₃ X₄, GU 5 w t) :=
        mul_le_mul_of_nonneg_left h2 hp
    _ = _ := by push_cast; ring

end instances

end GridGen.Four
