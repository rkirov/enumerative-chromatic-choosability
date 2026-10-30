/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.Cone
import GridGen.Explicit

/-!
# Height six at `k = 6`: the statement and the bridge to GridGen's hypotheses

`GridGen/Five/Bridge.lean` and `GridGen/Five/K5/Bridge.lean` with six rows, at `k = 6`, the
weights in the cone `InCone6` (`GridGen/Six/Cone.lean`). The row graph `pathG 5` has six
vertices, the rows `q1 — … — q6` of a path. A state of its column is a 6-tuple (`toT`, `ofT`),
the proper colourings from lists `X` are `sts (X q1) … (X q6)` (`mem_states6`), compatibility is
`compat` (`compat6`), and sums over states are sums over tuples (`sum_states6`,
`sum_states6_filter`).

* `Seam66Holds`: for every weight in the cone, every previous column with lists `X` of five or
  six colours and every next column with `6`-lists `B`, the weighted successors from `B` dominate
  the uniform prediction, summed over the proper states of `X`.
* `Init66Holds`: a column of `6`-lists, weighted by pattern, weighs at least the uniform column.

GridGen's reference is `Φ i s = fseq6 i · gw (wseq6 i) s` on proper states (`Φ_eq6`), and
`Φ (i+1) s = fseq6 i · GU 6 (wseq6 i) s` (`Φ_succ_eq6`); the pattern-preserving `patCap` needs
the height (six) to be at most `k` (`samePat_patCap`), which is why this route is at `k = 6`
(review, `H6_K6_REVIEW_2026-10-29.md` §4). The two inequalities give GridGen's explicit two-step,
first-seam and initial hypotheses, and `ecc_pathG_five_of_holds6` the grid.
-/

namespace GridGen.Six

open Finset SimpleGraph ListColoring
open scoped SimpleGraph

/-- The six rows. -/
abbrev V6 := PathV 5

/-! ### The six rows -/

/-- The first row: the pendant vertex of `pathG 5`. -/
def q1 : PathV 5 := (none : Option (PathV 4))

def q2 : PathV 5 := (some (none : Option (PathV 3)) : Option (PathV 4))

def q3 : PathV 5 :=
  (some (some (none : Option (PathV 2)) : Option (PathV 3)) : Option (PathV 4))

def q4 : PathV 5 :=
  (some (some (some (none : Option (PathV 1)) : Option (PathV 2)) : Option (PathV 3)) :
    Option (PathV 4))

def q5 : PathV 5 :=
  (some (some (some (some (none : Option (PathV 0)) : Option (PathV 1)) : Option (PathV 2)) :
    Option (PathV 3)) : Option (PathV 4))

def q6 : PathV 5 :=
  (some (some (some (some (some () : Option (PathV 0)) : Option (PathV 1)) : Option (PathV 2)) :
    Option (PathV 3)) : Option (PathV 4))

/-- Every vertex of `pathG 5` is one of the six rows. -/
theorem row_eq6 (x : PathV 5) : x = q1 ∨ x = q2 ∨ x = q3 ∨ x = q4 ∨ x = q5 ∨ x = q6 := by
  match x with
  | none => exact Or.inl rfl
  | some none => exact Or.inr (Or.inl rfl)
  | some (some none) => exact Or.inr (Or.inr (Or.inl rfl))
  | some (some (some none)) => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | some (some (some (some none))) => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | some (some (some (some (some u)))) =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [q6, Subsingleton.elim u ()])))))

/-- Adjacency in `pathG 5`: consecutive rows. -/
theorem pathFive_adj_iff {x y : PathV 5} :
    (pathG 5).Adj x y ↔ (x = q1 ∧ y = q2) ∨ (x = q2 ∧ y = q1) ∨ (x = q2 ∧ y = q3)
      ∨ (x = q3 ∧ y = q2) ∨ (x = q3 ∧ y = q4) ∨ (x = q4 ∧ y = q3) ∨ (x = q4 ∧ y = q5)
      ∨ (x = q5 ∧ y = q4) ∨ (x = q5 ∧ y = q6) ∨ (x = q6 ∧ y = q5) := by
  revert x y
  decide

theorem adj_q12 : (pathG 5).Adj q1 q2 := pathFive_adj_iff.mpr (Or.inl ⟨rfl, rfl⟩)
theorem adj_q23 : (pathG 5).Adj q2 q3 :=
  pathFive_adj_iff.mpr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
theorem adj_q34 : (pathG 5).Adj q3 q4 :=
  pathFive_adj_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
theorem adj_q45 : (pathG 5).Adj q4 q5 :=
  pathFive_adj_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))))
theorem adj_q56 : (pathG 5).Adj q5 q6 :=
  pathFive_adj_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨rfl, rfl⟩)))))))))

/-! ### States as tuples -/

/-- A state of the six-row column as a tuple. -/
def toT (s : State V6) : T6 := (s q1, s q2, s q3, s q4, s q5, s q6)

/-- A tuple as a state of the six-row column. -/
def ofT (t : T6) : State V6 :=
  fun x => if x = q1 then r1 t else if x = q2 then r2 t else if x = q3 then r3 t
    else if x = q4 then r4 t else if x = q5 then r5 t else r6 t

@[simp] theorem ofT_q1 (t : T6) : ofT t q1 = r1 t := by simp [ofT]
@[simp] theorem ofT_q2 (t : T6) : ofT t q2 = r2 t := by
  simp [ofT, show q2 ≠ q1 by decide]
@[simp] theorem ofT_q3 (t : T6) : ofT t q3 = r3 t := by
  simp [ofT, show q3 ≠ q1 by decide, show q3 ≠ q2 by decide]
@[simp] theorem ofT_q4 (t : T6) : ofT t q4 = r4 t := by
  simp [ofT, show q4 ≠ q1 by decide, show q4 ≠ q2 by decide, show q4 ≠ q3 by decide]
@[simp] theorem ofT_q5 (t : T6) : ofT t q5 = r5 t := by
  simp [ofT, show q5 ≠ q1 by decide, show q5 ≠ q2 by decide, show q5 ≠ q3 by decide,
    show q5 ≠ q4 by decide]
@[simp] theorem ofT_q6 (t : T6) : ofT t q6 = r6 t := by
  simp [ofT, show q6 ≠ q1 by decide, show q6 ≠ q2 by decide, show q6 ≠ q3 by decide,
    show q6 ≠ q4 by decide, show q6 ≠ q5 by decide]

theorem toT_ofT (t : T6) : toT (ofT t) = t := by
  obtain ⟨a, b, c, d, e, f⟩ := t
  simp [toT]

theorem ofT_toT (s : State V6) : ofT (toT s) = s := by
  funext x
  rcases row_eq6 x with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [toT]

theorem mem_states6 {X : Lists V6} {s : State V6} :
    s ∈ states (pathG 5) X ↔ toT s ∈ sts (X q1) (X q2) (X q3) (X q4) (X q5) (X q6) := by
  rw [mem_states, mem_sts]
  constructor
  · rintro ⟨hmem, hprop⟩
    exact ⟨hmem _, hmem _, hmem _, hmem _, hmem _, hmem _, hprop adj_q12, hprop adj_q23,
      hprop adj_q34, hprop adj_q45, hprop adj_q56⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h12, h23, h34, h45, h56⟩
    refine ⟨fun v => ?_, fun x y hxy => ?_⟩
    · rcases row_eq6 v with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5
      · exact h6
    · rcases pathFive_adj_iff.mp hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h12
      · exact Ne.symm h12
      · exact h23
      · exact Ne.symm h23
      · exact h34
      · exact Ne.symm h34
      · exact h45
      · exact Ne.symm h45
      · exact h56
      · exact Ne.symm h56

theorem compat6 (s t : State V6) : Compat s t ↔ compat (toT s) (toT t) := by
  constructor
  · intro h; exact ⟨h _, h _, h _, h _, h _, h _⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩ v
    rcases row_eq6 v with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6

/-- Sums over the states of a six-row column, as sums over tuples. -/
theorem sum_states6 {β : Type*} [AddCommMonoid β] (X : Lists V6) (f : State V6 → β) :
    ∑ s ∈ states (pathG 5) X, f s
      = ∑ t ∈ sts (X q1) (X q2) (X q3) (X q4) (X q5) (X q6), f (ofT t) := by
  refine Finset.sum_nbij' toT ofT ?_ ?_ ?_ ?_ ?_
  · intro s hs; exact mem_states6.mp hs
  · intro t ht; exact mem_states6.mpr (by rw [toT_ofT]; exact ht)
  · intro s _; exact ofT_toT s
  · intro t _; exact toT_ofT t
  · intro s _; rw [ofT_toT]

/-- Sums over the successors of a state, as sums over the colourings of the punctured lists. -/
theorem sum_states6_filter {β : Type*} [AddCommMonoid β] (X : Lists V6) (s₀ : State V6)
    (f : State V6 → β) :
    ∑ s ∈ (states (pathG 5) X).filter (Compat s₀), f s
      = ∑ t ∈ sts ((X q1).erase (s₀ q1)) ((X q2).erase (s₀ q2)) ((X q3).erase (s₀ q3))
          ((X q4).erase (s₀ q4)) ((X q5).erase (s₀ q5)) ((X q6).erase (s₀ q6)), f (ofT t) := by
  have e : sts ((X q1).erase (s₀ q1)) ((X q2).erase (s₀ q2)) ((X q3).erase (s₀ q3))
      ((X q4).erase (s₀ q4)) ((X q5).erase (s₀ q5)) ((X q6).erase (s₀ q6))
        = (sts (X q1) (X q2) (X q3) (X q4) (X q5) (X q6)).filter (compat (toT s₀)) :=
    (filter_compat_sts (toT s₀) _ _ _ _ _ _).symm
  rw [e]
  refine Finset.sum_nbij' toT ofT ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_filter] at hs ⊢
    exact ⟨mem_states6.mp hs.1, (compat6 _ _).mp hs.2⟩
  · intro t ht
    rw [Finset.mem_filter] at ht ⊢
    refine ⟨mem_states6.mpr (by rw [toT_ofT]; exact ht.1), ?_⟩
    rw [compat6, toT_ofT]; exact ht.2
  · intro s _; exact ofT_toT s
  · intro t _; exact toT_ofT t
  · intro s _; rw [ofT_toT]

/-! ### Patterns at height six -/

theorem pat_lt_of_lt6 {s : State V6} {v w : V6} (h : s v < s w) : pat s v < pat s w := by
  unfold pat
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨s v, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem s (Finset.mem_univ v), h⟩, ?_⟩
    simp [Finset.mem_filter]
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 h⟩

theorem pat_eq_iff6 {s : State V6} {v w : V6} : pat s v = pat s w ↔ s v = s w := by
  constructor
  · intro h
    rcases lt_trichotomy (s v) (s w) with hlt | heq | hgt
    · exact absurd h (ne_of_lt (pat_lt_of_lt6 hlt))
    · exact heq
    · exact absurd h (ne_of_gt (pat_lt_of_lt6 hgt))
  · intro h; unfold pat; rw [h]

theorem image6 (s : State V6) :
    Finset.univ.image s = {s q1, s q2, s q3, s q4, s q5, s q6} := by
  ext c
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨v, rfl⟩
    rcases row_eq6 v with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

theorem pat_le_five (s : State V6) (v : V6) : pat s v ≤ 5 := by
  unfold pat
  rw [image6]
  have hv : s v ∈ ({s q1, s q2, s q3, s q4, s q5, s q6} : Finset ℕ) := by
    rcases row_eq6 v with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  calc (({s q1, s q2, s q3, s q4, s q5, s q6} : Finset ℕ).filter (· < s v)).card
      ≤ (({s q1, s q2, s q3, s q4, s q5, s q6} : Finset ℕ).erase (s v)).card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_filter] at hx
        exact Finset.mem_erase.mpr ⟨ne_of_lt hx.2, hx.1⟩
    _ = ({s q1, s q2, s q3, s q4, s q5, s q6} : Finset ℕ).card - 1 := Finset.card_erase_of_mem hv
    _ ≤ 5 := by
        have h6 := Finset.card_le_six (a := s q1) (b := s q2) (c := s q3) (d := s q4) (e := s q5)
          (f := s q6)
        omega

theorem patCap_eq_pat6 {k : ℕ} (hk : 6 ≤ k) (s : State V6) (v : V6) :
    patCap k s v = pat s v := by
  unfold patCap
  exact Nat.min_eq_left (by have := pat_le_five s v; omega)

/-- The capped pattern has the equality pattern of the state. -/
theorem samePat_patCap {k : ℕ} (hk : 6 ≤ k) (s : State V6) :
    SamePat (toT (patCap k s)) (toT s) := by
  simp only [SamePat, toT, r1, r2, r3, r4, r5, r6, patCap_eq_pat6 hk]
  exact ⟨pat_eq_iff6, pat_eq_iff6, pat_eq_iff6, pat_eq_iff6, pat_eq_iff6, pat_eq_iff6,
    pat_eq_iff6, pat_eq_iff6, pat_eq_iff6, pat_eq_iff6⟩

theorem proper_patCap {k : ℕ} (hk : 6 ≤ k) {s : State V6} (hs : Proper (toT s)) :
    Proper (toT (patCap k s)) := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hs
  simp only [Proper, toT, r1, r2, r3, r4, r5, r6, patCap_eq_pat6 hk] at p1 p2 p3 p4 p5 ⊢
  exact ⟨fun h => p1 (pat_eq_iff6.mp h), fun h => p2 (pat_eq_iff6.mp h),
    fun h => p3 (pat_eq_iff6.mp h), fun h => p4 (pat_eq_iff6.mp h),
    fun h => p5 (pat_eq_iff6.mp h)⟩

theorem rowsIn_patCap {k : ℕ} (hk : 6 ≤ k) (s : State V6) :
    RowsIn (toT (patCap k s)) (range k) := by
  simp only [RowsIn, toT, r1, r2, r3, r4, r5, r6, patCap_eq_pat6 hk, Finset.mem_range]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := pat_le_five s q1; omega
  · have := pat_le_five s q2; omega
  · have := pat_le_five s q3; omega
  · have := pat_le_five s q4; omega
  · have := pat_le_five s q5; omega
  · have := pat_le_five s q6; omega

/-! ### The uniform futures and the reference -/

theorem unif_apply6 (k : ℕ) (v : V6) : unif (V := V6) k v = range k := rfl

/-- GridGen's uniform futures of the six-row column are the height-six uniform futures. -/
theorem F_eq_Fu (k : ℕ) : ∀ i (s : State V6), (F (pathG 5) k i s : ℝ) = Fu k i (toT s)
  | 0, s => by rw [F_zero]; simp [Fu]
  | i + 1, s => by
      rw [F_succ]
      push_cast
      rw [sum_states6_filter]
      simp only [unif_apply6, F_eq_Fu k i, toT_ofT]
      rfl

/-- **The reference by pattern** at `k = 6`. -/
theorem Φ_eq6 (i : ℕ) {s : State V6} (hs : Proper (toT s)) :
    (Φ (pathG 5) 6 i s : ℝ) = fseq6 i * gw (wseq6 i) (toT s) := by
  unfold Φ
  rw [F_eq_Fu, Fu_eq6 i _ (proper_patCap (by norm_num) hs) (rowsIn_patCap (by norm_num) s),
    gw_congr _ (samePat_patCap (by norm_num) s)]

/-- **One step of the reference** at `k = 6`. -/
theorem Φ_succ_eq6 (i : ℕ) {s : State V6} (hs : Proper (toT s)) :
    (Φ (pathG 5) 6 (i + 1) s : ℝ) = fseq6 i * GU 6 (wseq6 i) (toT s) := by
  unfold Φ
  rw [F_eq_Fu, Fu_succ_eq6 i (proper_patCap (by norm_num) hs) (rowsIn_patCap (by norm_num) s),
    GU_congr 6 _ (canon_congr (samePat_patCap (by norm_num) s))]

/-! ### The statement -/

/-- **The height-six seam inequality at `k = 6`**, on the cone. -/
def Seam66Holds : Prop :=
  ∀ (w : Wt6), InCone6 w →
  ∀ (X₁ X₂ X₃ X₄ X₅ X₆ B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ),
    (5 ≤ X₁.card ∧ X₁.card ≤ 6) → (5 ≤ X₂.card ∧ X₂.card ≤ 6) →
    (5 ≤ X₃.card ∧ X₃.card ≤ 6) → (5 ≤ X₄.card ∧ X₄.card ≤ 6) →
    (5 ≤ X₅.card ∧ X₅.card ≤ 6) → (5 ≤ X₆.card ∧ X₆.card ≤ 6) →
    B₁.card = 6 → B₂.card = 6 → B₃.card = 6 → B₄.card = 6 → B₅.card = 6 → B₆.card = 6 →
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GB w B₁ B₂ B₃ B₄ B₅ B₆ s

/-- **The height-six initial inequality at `k = 6`**, on the cone. -/
def Init66Holds : Prop :=
  ∀ (w : Wt6), InCone6 w →
  ∀ (X₁ X₂ X₃ X₄ X₅ X₆ : Finset ℕ),
    X₁.card = 6 → X₂.card = 6 → X₃.card = 6 → X₄.card = 6 → X₅.card = 6 → X₆.card = 6 →
    ∑ s ∈ sts (range 6) (range 6) (range 6) (range 6) (range 6) (range 6), gw w s
      ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, gw w s

/-! ### The seams -/

theorem sum_succ_Φ6 (i : ℕ) (B : Lists V6) (s : State V6) :
    ∑ t ∈ (states (pathG 5) B).filter (Compat s), (Φ (pathG 5) 6 i t : ℝ)
      = fseq6 i * GB (wseq6 i) (B q1) (B q2) (B q3) (B q4) (B q5) (B q6) (toT s) := by
  rw [sum_states6_filter, GB, G, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Φ_eq6 i (by rw [toT_ofT]; exact proper_of_mem_sts ht), toT_ofT]

theorem seam_sum6 (hS : Seam66Holds) (i : ℕ) (X B : Lists V6)
    (hX : ∀ v, 6 - 1 ≤ (X v).card ∧ (X v).card ≤ 6) (hB : ∀ v, (B v).card = 6) :
    ∑ t ∈ sts (X q1) (X q2) (X q3) (X q4) (X q5) (X q6), (Φ (pathG 5) 6 (i + 1) (ofT t) : ℝ)
      ≤ ∑ t ∈ sts (X q1) (X q2) (X q3) (X q4) (X q5) (X q6),
          ∑ u ∈ (states (pathG 5) B).filter (Compat (ofT t)), (Φ (pathG 5) 6 i u : ℝ) := by
  have hl : ∀ t ∈ sts (X q1) (X q2) (X q3) (X q4) (X q5) (X q6),
      (Φ (pathG 5) 6 (i + 1) (ofT t) : ℝ) = fseq6 i * GU 6 (wseq6 i) t := by
    intro t ht
    rw [Φ_succ_eq6 i (by rw [toT_ofT]; exact proper_of_mem_sts ht), toT_ofT]
  have hr : ∀ t ∈ sts (X q1) (X q2) (X q3) (X q4) (X q5) (X q6),
      ∑ u ∈ (states (pathG 5) B).filter (Compat (ofT t)), (Φ (pathG 5) 6 i u : ℝ)
        = fseq6 i * GB (wseq6 i) (B q1) (B q2) (B q3) (B q4) (B q5) (B q6) t := by
    intro t _
    rw [sum_succ_Φ6 i B (ofT t), toT_ofT]
  rw [Finset.sum_congr rfl hl, Finset.sum_congr rfl hr, ← Finset.mul_sum, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (hS _ (wseq6_inCone i) _ _ _ _ _ _ _ _ _ _ _ _ (hX q1) (hX q2) (hX q3) (hX q4) (hX q5)
      (hX q6) (hB q1) (hB q2) (hB q3) (hB q4) (hB q5) (hB q6))
    (fseq6_pos i).le

/-- **The explicit two-step inequality for `pathG 5` at `k = 6`.** -/
theorem twoStepExplicit_of_seam6 (hS : Seam66Holds) : TwoStepExplicit (pathG 5) 6 := by
  intro L hL j s₀ _ i
  have key := seam_sum6 hS i (fun v => (L (j + 1) v).erase (s₀ v)) (L (j + 1 + 1))
    (fun v => ⟨by have := Finset.pred_card_le_card_erase (s := L (j + 1) v) (a := s₀ v)
                  rw [hL (j + 1) v] at this; exact this,
               by have := Finset.card_erase_le (s := L (j + 1) v) (a := s₀ v)
                  rw [hL (j + 1) v] at this; exact this⟩)
    (fun v => hL (j + 1 + 1) v)
  rw [← sum_states6_filter (L (j + 1)) s₀ (fun s => (Φ (pathG 5) 6 (i + 1) s : ℝ)),
    ← sum_states6_filter (L (j + 1)) s₀
      (fun s => ∑ u ∈ (states (pathG 5) (L (j + 1 + 1))).filter (Compat s),
        (Φ (pathG 5) 6 i u : ℝ))] at key
  unfold cols
  exact_mod_cast key

/-- **The explicit first seam for `pathG 5` at `k = 6`.** -/
theorem firstSeamExplicit_of_seam6 (hS : Seam66Holds) : FirstSeamExplicit (pathG 5) 6 := by
  intro L hL i
  have key := seam_sum6 hS i (L 0) (L 1)
    (fun v => ⟨by rw [hL 0 v]; norm_num, by rw [hL 0 v]⟩) (fun v => hL 1 v)
  rw [← sum_states6 (L 0) (fun s => (Φ (pathG 5) 6 (i + 1) s : ℝ)),
    ← sum_states6 (L 0) (fun s => ∑ u ∈ (states (pathG 5) (L 1)).filter (Compat s),
        (Φ (pathG 5) 6 i u : ℝ))] at key
  unfold cols
  exact_mod_cast key

/-- **The initial condition for `pathG 5` at `k = 6`.** -/
theorem init_of_init66 (hI : Init66Holds) : Init (pathG 5) 6 := by
  intro X hX n
  have hL : ∑ s ∈ states (pathG 5) (unif 6), (F (pathG 5) 6 n s : ℝ)
      = fseq6 n * ∑ t ∈ sts (range 6) (range 6) (range 6) (range 6) (range 6) (range 6),
          gw (wseq6 n) t := by
    rw [sum_states6, Finset.mul_sum]
    simp only [unif_apply6]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [F_eq_Fu, toT_ofT, Fu_eq6 n t (proper_of_mem_sts ht)]
    rw [mem_sts] at ht
    exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2.1⟩
  have hR : ∑ s ∈ states (pathG 5) X, (Φ (pathG 5) 6 n s : ℝ)
      = fseq6 n * ∑ t ∈ sts (X q1) (X q2) (X q3) (X q4) (X q5) (X q6), gw (wseq6 n) t := by
    rw [sum_states6, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Φ_eq6 n (by rw [toT_ofT]; exact proper_of_mem_sts ht), toT_ofT]
  have key : ∑ s ∈ states (pathG 5) (unif 6), (F (pathG 5) 6 n s : ℝ)
      ≤ ∑ s ∈ states (pathG 5) X, (Φ (pathG 5) 6 n s : ℝ) := by
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_left
      (hI _ (wseq6_inCone n) _ _ _ _ _ _ (hX q1) (hX q2) (hX q3) (hX q4) (hX q5) (hX q6))
      (fseq6_pos n).le
  exact_mod_cast key

/-- **`P₆ □ P_{n+1}` is `6`-ECC, given the height-six seam and initial inequalities at
`k = 6`.** -/
theorem ecc_pathG_five_of_holds6 (hS : Seam66Holds) (hI : Init66Holds) (n : ℕ) :
    (pathG 5 □ pathG n).ECCAt 6 :=
  ecc_of_explicit (pathG 5) (twoStepExplicit_of_seam6 hS) (firstSeamExplicit_of_seam6 hS)
    (init_of_init66 hI) n

end GridGen.Six
