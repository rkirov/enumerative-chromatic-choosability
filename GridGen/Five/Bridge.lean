/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Cone
import GridGen.Explicit

/-!
# Height five: from the seam inequality to GridGen's hypotheses

`GridGen/Four/Bridge.lean` with five rows, at `k = 6`. The row graph `pathG 4` has five
vertices, the rows `q1 — q2 — q3 — q4 — q5` of a path. A state of its column is a 5-tuple
(`toT`, `ofT`), the proper colourings from lists `X` are `sts (X q1) … (X q5)` (`mem_states5`),
compatibility is `compat` (`compat5`), and sums over states are sums over tuples (`sum_states5`,
`sum_states5_filter`).

With these, GridGen's uniform futures `F (pathG 4) k i` are the height-five uniform futures
`Fu k i` (`F_eq_Fu`), and the reference `Φ = F ∘ patCap` of a proper state is, at `k = 6`, by
the uniform transfer of `GridGen/Five/Cone.lean` (`Fu_eq`, `Fu_succ_eq`),

* `Φ i s = fseq i · gw (wseq i) s` (`Φ_eq`), and
* `Φ (i+1) s = fseq i · GU 6 (wseq i) s` (`Φ_succ_eq`),

with `wseq i` in the invariant box and `fseq i > 0`. Then the two-step inequality of
`GridGen/Explicit.lean`, summed over the states `s` of column `j+1` compatible with `s₀`, is
`fseq i` times the seam inequality `Seam5Holds 6` on the punctured lists
`X v = (L (j+1) v).erase (s₀ v)` — of `5` or `6` colours — and the next column's `6`-lists
(`twoStepExplicit_of_seam`); the first seam is the same with the unpunctured lists
(`firstSeamExplicit_of_seam`); and the initial condition is `fseq n` times `Init5Holds 6`
(`init_of_init5`).
-/

namespace GridGen.Five

open Finset SimpleGraph ListColoring

/-- The five rows. -/
abbrev V5 := PathV 4

/-! ### The five rows -/

/-- The first row: the pendant vertex of `pathG 4`. -/
def q1 : PathV 4 := (none : Option (PathV 3))

/-- The second row. -/
def q2 : PathV 4 := (some (none : Option (PathV 2)) : Option (PathV 3))

/-- The third row. -/
def q3 : PathV 4 :=
  (some (some (none : Option (PathV 1)) : Option (PathV 2)) : Option (PathV 3))

/-- The fourth row. -/
def q4 : PathV 4 :=
  (some (some (some (none : Option (PathV 0)) : Option (PathV 1)) : Option (PathV 2)) :
    Option (PathV 3))

/-- The fifth row. -/
def q5 : PathV 4 :=
  (some (some (some (some () : Option (PathV 0)) : Option (PathV 1)) : Option (PathV 2)) :
    Option (PathV 3))

/-- Every vertex of `pathG 4` is one of the five rows. -/
theorem row_eq5 (x : PathV 4) : x = q1 ∨ x = q2 ∨ x = q3 ∨ x = q4 ∨ x = q5 := by
  match x with
  | none => exact Or.inl rfl
  | some none => exact Or.inr (Or.inl rfl)
  | some (some none) => exact Or.inr (Or.inr (Or.inl rfl))
  | some (some (some none)) => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | some (some (some (some u))) =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (by rw [q5, Subsingleton.elim u ()]))))

/-- Adjacency in `pathG 4`: consecutive rows. -/
theorem pathFour_adj_iff {x y : PathV 4} :
    (pathG 4).Adj x y ↔ (x = q1 ∧ y = q2) ∨ (x = q2 ∧ y = q1) ∨ (x = q2 ∧ y = q3)
      ∨ (x = q3 ∧ y = q2) ∨ (x = q3 ∧ y = q4) ∨ (x = q4 ∧ y = q3) ∨ (x = q4 ∧ y = q5)
      ∨ (x = q5 ∧ y = q4) := by
  revert x y
  decide

theorem adj_q12 : (pathG 4).Adj q1 q2 := pathFour_adj_iff.mpr (Or.inl ⟨rfl, rfl⟩)
theorem adj_q23 : (pathG 4).Adj q2 q3 :=
  pathFour_adj_iff.mpr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
theorem adj_q34 : (pathG 4).Adj q3 q4 :=
  pathFour_adj_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
theorem adj_q45 : (pathG 4).Adj q4 q5 :=
  pathFour_adj_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))))

/-! ### States as tuples -/

/-- A state of the five-row column as a tuple. -/
def toT (s : State V5) : T5 := (s q1, s q2, s q3, s q4, s q5)

/-- A tuple as a state of the five-row column. -/
def ofT (t : T5) : State V5 :=
  fun x => if x = q1 then r1 t else if x = q2 then r2 t else if x = q3 then r3 t
    else if x = q4 then r4 t else r5 t

@[simp] theorem ofT_q1 (t : T5) : ofT t q1 = r1 t := by simp [ofT]
@[simp] theorem ofT_q2 (t : T5) : ofT t q2 = r2 t := by
  simp [ofT, show q2 ≠ q1 by decide]
@[simp] theorem ofT_q3 (t : T5) : ofT t q3 = r3 t := by
  simp [ofT, show q3 ≠ q1 by decide, show q3 ≠ q2 by decide]
@[simp] theorem ofT_q4 (t : T5) : ofT t q4 = r4 t := by
  simp [ofT, show q4 ≠ q1 by decide, show q4 ≠ q2 by decide, show q4 ≠ q3 by decide]
@[simp] theorem ofT_q5 (t : T5) : ofT t q5 = r5 t := by
  simp [ofT, show q5 ≠ q1 by decide, show q5 ≠ q2 by decide, show q5 ≠ q3 by decide,
    show q5 ≠ q4 by decide]

theorem toT_ofT (t : T5) : toT (ofT t) = t := by
  obtain ⟨a, b, c, d, e⟩ := t
  simp [toT]

theorem ofT_toT (s : State V5) : ofT (toT s) = s := by
  funext x
  rcases row_eq5 x with rfl | rfl | rfl | rfl | rfl <;> simp [toT]

theorem mem_states5 {X : Lists V5} {s : State V5} :
    s ∈ states (pathG 4) X ↔ toT s ∈ sts (X q1) (X q2) (X q3) (X q4) (X q5) := by
  rw [mem_states, mem_sts]
  constructor
  · rintro ⟨hmem, hprop⟩
    exact ⟨hmem _, hmem _, hmem _, hmem _, hmem _, hprop adj_q12, hprop adj_q23, hprop adj_q34,
      hprop adj_q45⟩
  · rintro ⟨h1, h2, h3, h4, h5, h12, h23, h34, h45⟩
    refine ⟨fun v => ?_, fun x y hxy => ?_⟩
    · rcases row_eq5 v with rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5
    · rcases pathFour_adj_iff.mp hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h12
      · exact Ne.symm h12
      · exact h23
      · exact Ne.symm h23
      · exact h34
      · exact Ne.symm h34
      · exact h45
      · exact Ne.symm h45

theorem compat5 (s t : State V5) : Compat s t ↔ compat (toT s) (toT t) := by
  constructor
  · intro h; exact ⟨h _, h _, h _, h _, h _⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩ v
    rcases row_eq5 v with rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5

/-- Sums over the states of a five-row column, as sums over tuples. -/
theorem sum_states5 {β : Type*} [AddCommMonoid β] (X : Lists V5) (f : State V5 → β) :
    ∑ s ∈ states (pathG 4) X, f s
      = ∑ t ∈ sts (X q1) (X q2) (X q3) (X q4) (X q5), f (ofT t) := by
  refine Finset.sum_nbij' toT ofT ?_ ?_ ?_ ?_ ?_
  · intro s hs; exact mem_states5.mp hs
  · intro t ht; exact mem_states5.mpr (by rw [toT_ofT]; exact ht)
  · intro s _; exact ofT_toT s
  · intro t _; exact toT_ofT t
  · intro s _; rw [ofT_toT]

/-- Sums over the successors of a state, as sums over the colourings of the punctured lists. -/
theorem sum_states5_filter {β : Type*} [AddCommMonoid β] (X : Lists V5) (s₀ : State V5)
    (f : State V5 → β) :
    ∑ s ∈ (states (pathG 4) X).filter (Compat s₀), f s
      = ∑ t ∈ sts ((X q1).erase (s₀ q1)) ((X q2).erase (s₀ q2)) ((X q3).erase (s₀ q3))
          ((X q4).erase (s₀ q4)) ((X q5).erase (s₀ q5)), f (ofT t) := by
  have e : sts ((X q1).erase (s₀ q1)) ((X q2).erase (s₀ q2)) ((X q3).erase (s₀ q3))
      ((X q4).erase (s₀ q4)) ((X q5).erase (s₀ q5))
        = (sts (X q1) (X q2) (X q3) (X q4) (X q5)).filter (compat (toT s₀)) :=
    (filter_compat_sts (toT s₀) _ _ _ _ _).symm
  rw [e]
  refine Finset.sum_nbij' toT ofT ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_filter] at hs ⊢
    exact ⟨mem_states5.mp hs.1, (compat5 _ _).mp hs.2⟩
  · intro t ht
    rw [Finset.mem_filter] at ht ⊢
    refine ⟨mem_states5.mpr (by rw [toT_ofT]; exact ht.1), ?_⟩
    rw [compat5, toT_ofT]; exact ht.2
  · intro s _; exact ofT_toT s
  · intro t _; exact toT_ofT t
  · intro s _; rw [ofT_toT]

/-! ### Patterns at height five -/

theorem pat_lt_of_lt5 {s : State V5} {v w : V5} (h : s v < s w) : pat s v < pat s w := by
  unfold pat
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨s v, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem s (Finset.mem_univ v), h⟩, ?_⟩
    simp [Finset.mem_filter]
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 h⟩

theorem pat_eq_iff5 {s : State V5} {v w : V5} : pat s v = pat s w ↔ s v = s w := by
  constructor
  · intro h
    rcases lt_trichotomy (s v) (s w) with hlt | heq | hgt
    · exact absurd h (ne_of_lt (pat_lt_of_lt5 hlt))
    · exact heq
    · exact absurd h (ne_of_gt (pat_lt_of_lt5 hgt))
  · intro h; unfold pat; rw [h]

theorem image5 (s : State V5) :
    Finset.univ.image s = {s q1, s q2, s q3, s q4, s q5} := by
  ext c
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨v, rfl⟩
    rcases row_eq5 v with rfl | rfl | rfl | rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

theorem pat_le_four (s : State V5) (v : V5) : pat s v ≤ 4 := by
  unfold pat
  rw [image5]
  have hv : s v ∈ ({s q1, s q2, s q3, s q4, s q5} : Finset ℕ) := by
    rcases row_eq5 v with rfl | rfl | rfl | rfl | rfl <;> simp
  calc (({s q1, s q2, s q3, s q4, s q5} : Finset ℕ).filter (· < s v)).card
      ≤ (({s q1, s q2, s q3, s q4, s q5} : Finset ℕ).erase (s v)).card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_filter] at hx
        exact Finset.mem_erase.mpr ⟨ne_of_lt hx.2, hx.1⟩
    _ = ({s q1, s q2, s q3, s q4, s q5} : Finset ℕ).card - 1 := Finset.card_erase_of_mem hv
    _ ≤ 4 := by
        have h4 := Finset.card_le_four (a := s q2) (b := s q3) (c := s q4) (d := s q5)
        have := Finset.card_insert_le (s q1) ({s q2, s q3, s q4, s q5} : Finset ℕ)
        omega

theorem patCap_eq_pat5 {k : ℕ} (hk : 5 ≤ k) (s : State V5) (v : V5) :
    patCap k s v = pat s v := by
  unfold patCap
  exact Nat.min_eq_left (by have := pat_le_four s v; omega)

/-- The capped pattern has the equality pattern of the state. -/
theorem samePat_patCap {k : ℕ} (hk : 5 ≤ k) (s : State V5) :
    SamePat (toT (patCap k s)) (toT s) := by
  simp only [SamePat, toT, r1, r2, r3, r4, r5, patCap_eq_pat5 hk]
  exact ⟨pat_eq_iff5, pat_eq_iff5, pat_eq_iff5, pat_eq_iff5, pat_eq_iff5, pat_eq_iff5⟩

theorem proper_patCap {k : ℕ} (hk : 5 ≤ k) {s : State V5} (hs : Proper (toT s)) :
    Proper (toT (patCap k s)) := by
  obtain ⟨p1, p2, p3, p4⟩ := hs
  simp only [Proper, toT, r1, r2, r3, r4, r5, patCap_eq_pat5 hk] at p1 p2 p3 p4 ⊢
  exact ⟨fun h => p1 (pat_eq_iff5.mp h), fun h => p2 (pat_eq_iff5.mp h),
    fun h => p3 (pat_eq_iff5.mp h), fun h => p4 (pat_eq_iff5.mp h)⟩

theorem rowsIn_patCap {k : ℕ} (hk : 5 ≤ k) (s : State V5) :
    RowsIn (toT (patCap k s)) (range k) := by
  simp only [RowsIn, toT, r1, r2, r3, r4, r5, patCap_eq_pat5 hk, Finset.mem_range]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := pat_le_four s q1; omega
  · have := pat_le_four s q2; omega
  · have := pat_le_four s q3; omega
  · have := pat_le_four s q4; omega
  · have := pat_le_four s q5; omega

/-! ### The uniform futures and the reference -/

theorem unif_apply5 (k : ℕ) (v : V5) : unif (V := V5) k v = range k := rfl

/-- GridGen's uniform futures of the five-row column are the height-five uniform futures. -/
theorem F_eq_Fu (k : ℕ) : ∀ i (s : State V5), (F (pathG 4) k i s : ℝ) = Fu k i (toT s)
  | 0, s => by rw [F_zero]; simp [Fu]
  | i + 1, s => by
      rw [F_succ]
      push_cast
      rw [sum_states5_filter]
      simp only [unif_apply5, F_eq_Fu k i, toT_ofT]
      rfl

/-- **The reference by pattern**: `Φ i s = fseq i · gw (wseq i) s` on proper states, at
`k = 6`. -/
theorem Φ_eq (i : ℕ) {s : State V5} (hs : Proper (toT s)) :
    (Φ (pathG 4) 6 i s : ℝ) = fseq i * gw (wseq i) (toT s) := by
  unfold Φ
  rw [F_eq_Fu, Fu_eq i _ (proper_patCap (by norm_num) hs) (rowsIn_patCap (by norm_num) s),
    gw_congr _ (samePat_patCap (by norm_num) s)]

/-- **One step of the reference**: `Φ (i+1) s = fseq i · GU 6 (wseq i) s` on proper states. -/
theorem Φ_succ_eq (i : ℕ) {s : State V5} (hs : Proper (toT s)) :
    (Φ (pathG 4) 6 (i + 1) s : ℝ) = fseq i * GU 6 (wseq i) (toT s) := by
  unfold Φ
  rw [F_eq_Fu, Fu_succ_eq i (proper_patCap (by norm_num) hs) (rowsIn_patCap (by norm_num) s),
    GU_congr 6 _ (canon_congr (samePat_patCap (by norm_num) s))]

/-! ### The seams -/

/-- The successors of `s` in a column with lists `B`, weighted by the reference at horizon
`i`. -/
theorem sum_succ_Φ (i : ℕ) (B : Lists V5) (s : State V5) :
    ∑ t ∈ (states (pathG 4) B).filter (Compat s), (Φ (pathG 4) 6 i t : ℝ)
      = fseq i * GB (wseq i) (B q1) (B q2) (B q3) (B q4) (B q5) (toT s) := by
  rw [sum_states5_filter, GB, G, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Φ_eq i (by rw [toT_ofT]; exact proper_of_mem_sts ht), toT_ofT]

/-- The core of both seam statements: `Seam5Holds 6` on lists `X` (of `5` or `6` colours) and
the next column's `6`-lists `B`, scaled by `fseq i`. -/
theorem seam_sum (hS : Seam5Holds 6) (i : ℕ) (X B : Lists V5)
    (hX : ∀ v, 6 - 1 ≤ (X v).card ∧ (X v).card ≤ 6) (hB : ∀ v, (B v).card = 6) :
    ∑ t ∈ sts (X q1) (X q2) (X q3) (X q4) (X q5), (Φ (pathG 4) 6 (i + 1) (ofT t) : ℝ)
      ≤ ∑ t ∈ sts (X q1) (X q2) (X q3) (X q4) (X q5),
          ∑ u ∈ (states (pathG 4) B).filter (Compat (ofT t)), (Φ (pathG 4) 6 i u : ℝ) := by
  have hl : ∀ t ∈ sts (X q1) (X q2) (X q3) (X q4) (X q5),
      (Φ (pathG 4) 6 (i + 1) (ofT t) : ℝ) = fseq i * GU 6 (wseq i) t := by
    intro t ht
    rw [Φ_succ_eq i (by rw [toT_ofT]; exact proper_of_mem_sts ht), toT_ofT]
  have hr : ∀ t ∈ sts (X q1) (X q2) (X q3) (X q4) (X q5),
      ∑ u ∈ (states (pathG 4) B).filter (Compat (ofT t)), (Φ (pathG 4) 6 i u : ℝ)
        = fseq i * GB (wseq i) (B q1) (B q2) (B q3) (B q4) (B q5) t := by
    intro t _
    rw [sum_succ_Φ i B (ofT t), toT_ofT]
  rw [Finset.sum_congr rfl hl, Finset.sum_congr rfl hr, ← Finset.mul_sum, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (hS _ (wseq_inBox i) _ _ _ _ _ _ _ _ _ _ (hX q1) (hX q2) (hX q3) (hX q4) (hX q5) (hB q1)
      (hB q2) (hB q3) (hB q4) (hB q5))
    (fseq_pos i).le

/-- **The explicit two-step inequality for `pathG 4`, from the height-five seam inequality.** -/
theorem twoStepExplicit_of_seam (hS : Seam5Holds 6) : TwoStepExplicit (pathG 4) 6 := by
  intro L hL j s₀ _ i
  have key := seam_sum hS i (fun v => (L (j + 1) v).erase (s₀ v)) (L (j + 1 + 1))
    (fun v => ⟨by have := Finset.pred_card_le_card_erase (s := L (j + 1) v) (a := s₀ v)
                  rw [hL (j + 1) v] at this; exact this,
               by have := Finset.card_erase_le (s := L (j + 1) v) (a := s₀ v)
                  rw [hL (j + 1) v] at this; exact this⟩)
    (fun v => hL (j + 1 + 1) v)
  rw [← sum_states5_filter (L (j + 1)) s₀ (fun s => (Φ (pathG 4) 6 (i + 1) s : ℝ)),
    ← sum_states5_filter (L (j + 1)) s₀
      (fun s => ∑ u ∈ (states (pathG 4) (L (j + 1 + 1))).filter (Compat s),
        (Φ (pathG 4) 6 i u : ℝ))] at key
  unfold cols
  exact_mod_cast key

/-- **The explicit first seam for `pathG 4`, from the height-five seam inequality.** -/
theorem firstSeamExplicit_of_seam (hS : Seam5Holds 6) : FirstSeamExplicit (pathG 4) 6 := by
  intro L hL i
  have key := seam_sum hS i (L 0) (L 1)
    (fun v => ⟨by rw [hL 0 v]; norm_num, by rw [hL 0 v]⟩) (fun v => hL 1 v)
  rw [← sum_states5 (L 0) (fun s => (Φ (pathG 4) 6 (i + 1) s : ℝ)),
    ← sum_states5 (L 0) (fun s => ∑ u ∈ (states (pathG 4) (L 1)).filter (Compat s),
        (Φ (pathG 4) 6 i u : ℝ))] at key
  unfold cols
  exact_mod_cast key

/-! ### The initial condition -/

/-- **The initial condition for `pathG 4`, from the height-five initial inequality.** -/
theorem init_of_init5 (hI : Init5Holds 6) : Init (pathG 4) 6 := by
  intro X hX n
  have hL : ∑ s ∈ states (pathG 4) (unif 6), (F (pathG 4) 6 n s : ℝ)
      = fseq n * ∑ t ∈ sts (range 6) (range 6) (range 6) (range 6) (range 6), gw (wseq n) t := by
    rw [sum_states5, Finset.mul_sum]
    simp only [unif_apply5]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [F_eq_Fu, toT_ofT, Fu_eq n t (proper_of_mem_sts ht)]
    rw [mem_sts] at ht
    exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1⟩
  have hR : ∑ s ∈ states (pathG 4) X, (Φ (pathG 4) 6 n s : ℝ)
      = fseq n * ∑ t ∈ sts (X q1) (X q2) (X q3) (X q4) (X q5), gw (wseq n) t := by
    rw [sum_states5, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Φ_eq n (by rw [toT_ofT]; exact proper_of_mem_sts ht), toT_ofT]
  have key : ∑ s ∈ states (pathG 4) (unif 6), (F (pathG 4) 6 n s : ℝ)
      ≤ ∑ s ∈ states (pathG 4) X, (Φ (pathG 4) 6 n s : ℝ) := by
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_left
      (hI _ (wseq_inBox n) _ _ _ _ _ (hX q1) (hX q2) (hX q3) (hX q4) (hX q5)) (fseq_pos n).le
  exact_mod_cast key

end GridGen.Five
