/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Cone
import GridGen.Explicit

/-!
# Height four: from the seam inequality to GridGen's hypotheses

The row graph `pathG 3` has four vertices, the rows `q1 — q2 — q3 — q4` of a path. A state of
its column is a 4-tuple (`toT`, `ofT`), the proper colourings from lists `X` are
`sts (X q1) (X q2) (X q3) (X q4)` (`mem_states4`), compatibility is `compat` (`compat4`), and sums
over states are sums over tuples (`sum_states4`, `sum_states4_filter`).

With these, GridGen's uniform futures `F (pathG 3) k i` are the height-four uniform futures
`Fu k i` (`F_eq_Fu`), and the reference `Φ = F ∘ patCap` of a proper state is, by the uniform
transfer of `GridGen/Four/Cone.lean` (`Fu_eq`, `Fu_succ_eq`),

* `Φ i s = fseq k i · gw (wseq k i) s` (`Φ_eq`), and
* `Φ (i+1) s = fseq k i · GU k (wseq k i) s` (`Φ_succ_eq`),

with `wseq k i` in the invariant box and `fseq k i > 0`. Then the two-step inequality of
`GridGen/Explicit.lean`, summed over the states `s` of column `j+1` compatible with `s₀`, is
`fseq k i` times the seam inequality `Seam4Holds k` on the punctured lists
`X v = (L (j+1) v).erase (s₀ v)` — of `k - 1` or `k` colours — and the next column's `k`-lists
(`twoStepExplicit_of_seam`); the first seam is the same with the unpunctured lists
(`firstSeamExplicit_of_seam`); and the initial condition is `fseq k n` times `Init4Holds k`
(`init_of_init4`).
-/

namespace GridGen.Four

open Finset SimpleGraph ListColoring

/-- The four rows. -/
abbrev V4 := PathV 3

/-! ### The four rows -/

/-- The first row: the pendant vertex of `pathG 3`. -/
def q1 : PathV 3 := (none : Option (PathV 2))

/-- The second row. -/
def q2 : PathV 3 := (some (none : Option (PathV 1)) : Option (PathV 2))

/-- The third row. -/
def q3 : PathV 3 := (some (some (none : Option (PathV 0)) : Option (PathV 1)) : Option (PathV 2))

/-- The fourth row. -/
def q4 : PathV 3 := (some (some (some () : Option (PathV 0)) : Option (PathV 1)) : Option (PathV 2))

/-- Every vertex of `pathG 3` is one of the four rows. -/
theorem row_eq4 (x : PathV 3) : x = q1 ∨ x = q2 ∨ x = q3 ∨ x = q4 := by
  match x with
  | none => exact Or.inl rfl
  | some none => exact Or.inr (Or.inl rfl)
  | some (some none) => exact Or.inr (Or.inr (Or.inl rfl))
  | some (some (some u)) => exact Or.inr (Or.inr (Or.inr (by rw [q4, Subsingleton.elim u ()])))

/-- Adjacency in `pathG 3`: consecutive rows. -/
theorem pathThree_adj_iff {x y : PathV 3} :
    (pathG 3).Adj x y ↔ (x = q1 ∧ y = q2) ∨ (x = q2 ∧ y = q1) ∨ (x = q2 ∧ y = q3)
      ∨ (x = q3 ∧ y = q2) ∨ (x = q3 ∧ y = q4) ∨ (x = q4 ∧ y = q3) := by
  revert x y
  decide

theorem adj_q12 : (pathG 3).Adj q1 q2 := pathThree_adj_iff.mpr (Or.inl ⟨rfl, rfl⟩)
theorem adj_q23 : (pathG 3).Adj q2 q3 :=
  pathThree_adj_iff.mpr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
theorem adj_q34 : (pathG 3).Adj q3 q4 :=
  pathThree_adj_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))

/-! ### States as tuples -/

/-- A state of the four-row column as a tuple. -/
def toT (s : State V4) : T4 := (s q1, s q2, s q3, s q4)

/-- A tuple as a state of the four-row column. -/
def ofT (t : T4) : State V4 :=
  fun x => if x = q1 then r1 t else if x = q2 then r2 t else if x = q3 then r3 t else r4 t

@[simp] theorem ofT_q1 (t : T4) : ofT t q1 = r1 t := by simp [ofT]
@[simp] theorem ofT_q2 (t : T4) : ofT t q2 = r2 t := by
  simp [ofT, show q2 ≠ q1 by decide]
@[simp] theorem ofT_q3 (t : T4) : ofT t q3 = r3 t := by
  simp [ofT, show q3 ≠ q1 by decide, show q3 ≠ q2 by decide]
@[simp] theorem ofT_q4 (t : T4) : ofT t q4 = r4 t := by
  simp [ofT, show q4 ≠ q1 by decide, show q4 ≠ q2 by decide, show q4 ≠ q3 by decide]

theorem toT_ofT (t : T4) : toT (ofT t) = t := by
  obtain ⟨a, b, c, d⟩ := t
  simp [toT]

theorem ofT_toT (s : State V4) : ofT (toT s) = s := by
  funext x
  rcases row_eq4 x with rfl | rfl | rfl | rfl <;> simp [toT]

theorem mem_states4 {X : Lists V4} {s : State V4} :
    s ∈ states (pathG 3) X ↔ toT s ∈ sts (X q1) (X q2) (X q3) (X q4) := by
  rw [mem_states, mem_sts]
  constructor
  · rintro ⟨hmem, hprop⟩
    exact ⟨hmem _, hmem _, hmem _, hmem _, hprop adj_q12, hprop adj_q23, hprop adj_q34⟩
  · rintro ⟨h1, h2, h3, h4, h12, h23, h34⟩
    refine ⟨fun v => ?_, fun x y hxy => ?_⟩
    · rcases row_eq4 v with rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    · rcases pathThree_adj_iff.mp hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h12
      · exact Ne.symm h12
      · exact h23
      · exact Ne.symm h23
      · exact h34
      · exact Ne.symm h34

theorem compat4 (s t : State V4) : Compat s t ↔ compat (toT s) (toT t) := by
  constructor
  · intro h; exact ⟨h _, h _, h _, h _⟩
  · rintro ⟨h1, h2, h3, h4⟩ v
    rcases row_eq4 v with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4

/-- Sums over the states of a four-row column, as sums over tuples. -/
theorem sum_states4 {β : Type*} [AddCommMonoid β] (X : Lists V4) (f : State V4 → β) :
    ∑ s ∈ states (pathG 3) X, f s = ∑ t ∈ sts (X q1) (X q2) (X q3) (X q4), f (ofT t) := by
  refine Finset.sum_nbij' toT ofT ?_ ?_ ?_ ?_ ?_
  · intro s hs; exact mem_states4.mp hs
  · intro t ht; exact mem_states4.mpr (by rw [toT_ofT]; exact ht)
  · intro s _; exact ofT_toT s
  · intro t _; exact toT_ofT t
  · intro s _; rw [ofT_toT]

/-- Sums over the successors of a state, as sums over the colourings of the punctured lists. -/
theorem sum_states4_filter {β : Type*} [AddCommMonoid β] (X : Lists V4) (s₀ : State V4)
    (f : State V4 → β) :
    ∑ s ∈ (states (pathG 3) X).filter (Compat s₀), f s
      = ∑ t ∈ sts ((X q1).erase (s₀ q1)) ((X q2).erase (s₀ q2)) ((X q3).erase (s₀ q3))
          ((X q4).erase (s₀ q4)), f (ofT t) := by
  have e : sts ((X q1).erase (s₀ q1)) ((X q2).erase (s₀ q2)) ((X q3).erase (s₀ q3))
      ((X q4).erase (s₀ q4)) = (sts (X q1) (X q2) (X q3) (X q4)).filter (compat (toT s₀)) :=
    (filter_compat_sts (toT s₀) _ _ _ _).symm
  rw [e]
  refine Finset.sum_nbij' toT ofT ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_filter] at hs ⊢
    exact ⟨mem_states4.mp hs.1, (compat4 _ _).mp hs.2⟩
  · intro t ht
    rw [Finset.mem_filter] at ht ⊢
    refine ⟨mem_states4.mpr (by rw [toT_ofT]; exact ht.1), ?_⟩
    rw [compat4, toT_ofT]; exact ht.2
  · intro s _; exact ofT_toT s
  · intro t _; exact toT_ofT t
  · intro s _; rw [ofT_toT]

/-! ### Patterns at height four -/

theorem pat_lt_of_lt4 {s : State V4} {v w : V4} (h : s v < s w) : pat s v < pat s w := by
  unfold pat
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨s v, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem s (Finset.mem_univ v), h⟩, ?_⟩
    simp [Finset.mem_filter]
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 h⟩

theorem pat_eq_iff4 {s : State V4} {v w : V4} : pat s v = pat s w ↔ s v = s w := by
  constructor
  · intro h
    rcases lt_trichotomy (s v) (s w) with hlt | heq | hgt
    · exact absurd h (ne_of_lt (pat_lt_of_lt4 hlt))
    · exact heq
    · exact absurd h (ne_of_gt (pat_lt_of_lt4 hgt))
  · intro h; unfold pat; rw [h]

theorem image4 (s : State V4) :
    Finset.univ.image s = {s q1, s q2, s q3, s q4} := by
  ext c
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨v, rfl⟩
    rcases row_eq4 v with rfl | rfl | rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

theorem pat_le_three (s : State V4) (v : V4) : pat s v ≤ 3 := by
  unfold pat
  rw [image4]
  have hv : s v ∈ ({s q1, s q2, s q3, s q4} : Finset ℕ) := by
    rcases row_eq4 v with rfl | rfl | rfl | rfl <;> simp
  calc (({s q1, s q2, s q3, s q4} : Finset ℕ).filter (· < s v)).card
      ≤ (({s q1, s q2, s q3, s q4} : Finset ℕ).erase (s v)).card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_filter] at hx
        exact Finset.mem_erase.mpr ⟨ne_of_lt hx.2, hx.1⟩
    _ = ({s q1, s q2, s q3, s q4} : Finset ℕ).card - 1 := Finset.card_erase_of_mem hv
    _ ≤ 3 := by
        have := Finset.card_le_four (a := s q1) (b := s q2) (c := s q3) (d := s q4); omega

theorem patCap_eq_pat4 {k : ℕ} (hk : 4 ≤ k) (s : State V4) (v : V4) :
    patCap k s v = pat s v := by
  unfold patCap
  exact Nat.min_eq_left (by have := pat_le_three s v; omega)

/-- The capped pattern has the equality pattern of the state. -/
theorem samePat_patCap {k : ℕ} (hk : 4 ≤ k) (s : State V4) :
    SamePat (toT (patCap k s)) (toT s) := by
  simp only [SamePat, toT, r1, r2, r3, r4, patCap_eq_pat4 hk]
  exact ⟨pat_eq_iff4, pat_eq_iff4, pat_eq_iff4⟩

theorem proper_patCap {k : ℕ} (hk : 4 ≤ k) {s : State V4} (hs : Proper (toT s)) :
    Proper (toT (patCap k s)) := by
  obtain ⟨p1, p2, p3⟩ := hs
  simp only [Proper, toT, r1, r2, r3, r4, patCap_eq_pat4 hk] at p1 p2 p3 ⊢
  exact ⟨fun h => p1 (pat_eq_iff4.mp h), fun h => p2 (pat_eq_iff4.mp h),
    fun h => p3 (pat_eq_iff4.mp h)⟩

theorem rowsIn_patCap {k : ℕ} (hk : 4 ≤ k) (s : State V4) : RowsIn (toT (patCap k s)) (range k) := by
  simp only [RowsIn, toT, r1, r2, r3, r4, patCap_eq_pat4 hk, Finset.mem_range]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := pat_le_three s q1; omega
  · have := pat_le_three s q2; omega
  · have := pat_le_three s q3; omega
  · have := pat_le_three s q4; omega

/-- `canon` reads only the equality pattern. -/
theorem canon_congr {s t : T4} (h : SamePat s t) : canon s = canon t := by
  obtain ⟨h13, h24, h14⟩ := h
  have e1 : (r3 s = r1 s) ↔ (r3 t = r1 t) := by rw [eq_comm, h13, eq_comm]
  have e2 : (r4 s = r2 s) ↔ (r4 t = r2 t) := by rw [eq_comm, h24, eq_comm]
  have e3 : (r4 s = r1 s) ↔ (r4 t = r1 t) := by rw [eq_comm, h14, eq_comm]
  simp only [canon, e1, e2, e3]

/-! ### The uniform futures and the reference -/

theorem unif_apply4 (k : ℕ) (v : V4) : unif (V := V4) k v = range k := rfl

/-- GridGen's uniform futures of the four-row column are the height-four uniform futures. -/
theorem F_eq_Fu (k : ℕ) : ∀ i (s : State V4), (F (pathG 3) k i s : ℝ) = Fu k i (toT s)
  | 0, s => by rw [F_zero]; simp [Fu]
  | i + 1, s => by
      rw [F_succ]
      push_cast
      rw [sum_states4_filter]
      simp only [unif_apply4, F_eq_Fu k i, toT_ofT]
      rfl

/-- **The reference by pattern**: `Φ i s = fseq k i · gw (wseq k i) s` on proper states. -/
theorem Φ_eq {k : ℕ} (hk : 5 ≤ k) (i : ℕ) {s : State V4} (hs : Proper (toT s)) :
    (Φ (pathG 3) k i s : ℝ) = fseq k i * gw (wseq k i) (toT s) := by
  unfold Φ
  rw [F_eq_Fu, Fu_eq hk i _ (proper_patCap (by omega) hs) (rowsIn_patCap (by omega) s),
    gw_congr _ (samePat_patCap (by omega) s)]

/-- **One step of the reference**: `Φ (i+1) s = fseq k i · GU k (wseq k i) s` on proper states. -/
theorem Φ_succ_eq {k : ℕ} (hk : 5 ≤ k) (i : ℕ) {s : State V4} (hs : Proper (toT s)) :
    (Φ (pathG 3) k (i + 1) s : ℝ) = fseq k i * GU k (wseq k i) (toT s) := by
  unfold Φ
  rw [F_eq_Fu, Fu_succ_eq hk i (proper_patCap (by omega) hs) (rowsIn_patCap (by omega) s),
    GU_congr k _ (canon_congr (samePat_patCap (by omega) s))]

/-! ### The seams -/

/-- The successors of `s` in a column with lists `B`, weighted by the reference at horizon
`i`. -/
theorem sum_succ_Φ {k : ℕ} (hk : 5 ≤ k) (i : ℕ) (B : Lists V4) (s : State V4) :
    ∑ t ∈ (states (pathG 3) B).filter (Compat s), (Φ (pathG 3) k i t : ℝ)
      = fseq k i * GB (wseq k i) (B q1) (B q2) (B q3) (B q4) (toT s) := by
  rw [sum_states4_filter, GB, G, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Φ_eq hk i (by rw [toT_ofT]; exact proper_of_mem_sts ht), toT_ofT]

/-- The core of both seam statements: `Seam4Holds` on lists `X` (of `k - 1` or `k` colours) and
the next column's `k`-lists `B`, scaled by `fseq k i`. -/
theorem seam_sum {k : ℕ} (hk : 5 ≤ k) (hS : Seam4Holds k) (i : ℕ) (X B : Lists V4)
    (hX : ∀ v, k - 1 ≤ (X v).card ∧ (X v).card ≤ k) (hB : ∀ v, (B v).card = k) :
    ∑ t ∈ sts (X q1) (X q2) (X q3) (X q4), (Φ (pathG 3) k (i + 1) (ofT t) : ℝ)
      ≤ ∑ t ∈ sts (X q1) (X q2) (X q3) (X q4),
          ∑ u ∈ (states (pathG 3) B).filter (Compat (ofT t)), (Φ (pathG 3) k i u : ℝ) := by
  have hl : ∀ t ∈ sts (X q1) (X q2) (X q3) (X q4),
      (Φ (pathG 3) k (i + 1) (ofT t) : ℝ) = fseq k i * GU k (wseq k i) t := by
    intro t ht
    rw [Φ_succ_eq hk i (by rw [toT_ofT]; exact proper_of_mem_sts ht), toT_ofT]
  have hr : ∀ t ∈ sts (X q1) (X q2) (X q3) (X q4),
      ∑ u ∈ (states (pathG 3) B).filter (Compat (ofT t)), (Φ (pathG 3) k i u : ℝ)
        = fseq k i * GB (wseq k i) (B q1) (B q2) (B q3) (B q4) t := by
    intro t _
    rw [sum_succ_Φ hk i B (ofT t), toT_ofT]
  rw [Finset.sum_congr rfl hl, Finset.sum_congr rfl hr, ← Finset.mul_sum, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (hS _ (wseq_inBox hk i) _ _ _ _ _ _ _ _ (hX q1) (hX q2) (hX q3) (hX q4) (hB q1) (hB q2)
      (hB q3) (hB q4))
    (fseq_pos hk i).le

/-- **The explicit two-step inequality for `pathG 3`, from the height-four seam inequality.** -/
theorem twoStepExplicit_of_seam {k : ℕ} (hk : 5 ≤ k) (hS : Seam4Holds k) :
    TwoStepExplicit (pathG 3) k := by
  intro L hL j s₀ _ i
  have key := seam_sum hk hS i (fun v => (L (j + 1) v).erase (s₀ v)) (L (j + 1 + 1))
    (fun v => ⟨by have := Finset.pred_card_le_card_erase (s := L (j + 1) v) (a := s₀ v)
                  rw [hL (j + 1) v] at this; exact this,
               by have := Finset.card_erase_le (s := L (j + 1) v) (a := s₀ v)
                  rw [hL (j + 1) v] at this; exact this⟩)
    (fun v => hL (j + 1 + 1) v)
  rw [← sum_states4_filter (L (j + 1)) s₀ (fun s => (Φ (pathG 3) k (i + 1) s : ℝ)),
    ← sum_states4_filter (L (j + 1)) s₀
      (fun s => ∑ u ∈ (states (pathG 3) (L (j + 1 + 1))).filter (Compat s),
        (Φ (pathG 3) k i u : ℝ))] at key
  unfold cols
  exact_mod_cast key

/-- **The explicit first seam for `pathG 3`, from the height-four seam inequality.** -/
theorem firstSeamExplicit_of_seam {k : ℕ} (hk : 5 ≤ k) (hS : Seam4Holds k) :
    FirstSeamExplicit (pathG 3) k := by
  intro L hL i
  have key := seam_sum hk hS i (L 0) (L 1)
    (fun v => ⟨by rw [hL 0 v]; omega, by rw [hL 0 v]⟩) (fun v => hL 1 v)
  rw [← sum_states4 (L 0) (fun s => (Φ (pathG 3) k (i + 1) s : ℝ)),
    ← sum_states4 (L 0) (fun s => ∑ u ∈ (states (pathG 3) (L 1)).filter (Compat s),
        (Φ (pathG 3) k i u : ℝ))] at key
  unfold cols
  exact_mod_cast key

/-! ### The initial condition -/

/-- **The initial condition for `pathG 3`, from the height-four initial inequality.** -/
theorem init_of_init4 {k : ℕ} (hk : 5 ≤ k) (hI : Init4Holds k) : Init (pathG 3) k := by
  intro X hX n
  have hL : ∑ s ∈ states (pathG 3) (unif k), (F (pathG 3) k n s : ℝ)
      = fseq k n * ∑ t ∈ sts (range k) (range k) (range k) (range k), gw (wseq k n) t := by
    rw [sum_states4, Finset.mul_sum]
    simp only [unif_apply4]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [F_eq_Fu, toT_ofT, Fu_eq hk n t (proper_of_mem_sts ht)]
    rw [mem_sts] at ht
    exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1⟩
  have hR : ∑ s ∈ states (pathG 3) X, (Φ (pathG 3) k n s : ℝ)
      = fseq k n * ∑ t ∈ sts (X q1) (X q2) (X q3) (X q4), gw (wseq k n) t := by
    rw [sum_states4, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Φ_eq hk n (by rw [toT_ofT]; exact proper_of_mem_sts ht), toT_ofT]
  have key : ∑ s ∈ states (pathG 3) (unif k), (F (pathG 3) k n s : ℝ)
      ≤ ∑ s ∈ states (pathG 3) X, (Φ (pathG 3) k n s : ℝ) := by
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_left
      (hI _ (wseq_inBox hk n) _ _ _ _ (hX q1) (hX q2) (hX q3) (hX q4)) (fseq_pos hk n).le
  exact_mod_cast key

end GridGen.Four
