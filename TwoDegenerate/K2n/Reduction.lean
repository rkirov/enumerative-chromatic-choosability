/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import TwoDegenerate.K2n.Checker
import TwoDegenerate.Counterexample

/-!
# Reducing four-list colourings of `K₂,ₙ` to a numeric certificate

Fix a four-list assignment on `K₂,ₙ`: lists `A`, `B` on the two hubs and `T w` on the right
vertices. The colouring count is `∑_{a ∈ A} ∑_{b ∈ B} ∏_w |T w \ {a, b}|`
(`col_completeBipartite_two_right`). Three reductions turn the claim `P(K₂,ₙ, 4) ≤` that count
into finitely many numeric statements, one for each overlap `r = |A ∩ B|`.

1. **Push into `A ∪ B`.** Replacing `T w` by a four-set `T' w ⊆ A ∪ B` containing
   `T w ∩ (A ∪ B)` can only shrink `|T w \ {a, b}|` for `a ∈ A`, `b ∈ B` (`exists_push`).
2. **Encode.** List `A ∩ B`, `A \ B`, `B \ A` in increasing order; a four-set `S ⊆ A ∪ B` is then
   determined, for the count, by its membership bits `key S` over that list, and
   `|S \ {a_i, b_j}| = pairVal r (key S) i j` (`card_sdiff_pair_eq_pairVal`).
3. **Group.** The product over the right vertices depends only on how many of them have each
   key, so the count is `∑_p ∏_κ (row κ)_p ^ m_κ` with `∑_κ m_κ = n`, which is the checker's
   `Goal` (`evalC_map`).

`le_col_of_keyGoals` assembles these: given the five numeric goals, every four-list assignment on
`K₂,ₙ` has at least `T` colourings.
-/

namespace SimpleGraph.TwoDegenerate.K2n

open Finset

/-! ### The numeric side -/

/-- Membership bit `x` of a key, as `0` or `1`. -/
def bit (κ : List Bool) (x : ℕ) : ℕ := if κ.getD x false then 1 else 0

/-- Position of the `j`-th colour of `B` in the key: `A ∩ B` first, then `A \ B`, then `B \ A`. -/
def posB (r j : ℕ) : ℕ := if j < r then j else j + 4 - r

/-- `|S \ {a_i, b_j}|` in terms of the key of `S`, for a four-set `S`. -/
def pairVal (r : ℕ) (κ : List Bool) (i j : ℕ) : ℕ :=
  4 + (if i = j ∧ j < r then bit κ i else 0) - bit κ i - bit κ (posB r j)

/-- The sixteen pairs `(i, j)`, `i, j < 4`, in the order `4 i + j`. -/
def pairs16 : List (ℕ × ℕ) := (List.range 4).flatMap fun i => (List.range 4).map fun j => (i, j)

/-- The row of a key: its sixteen pair values. -/
def rowOf (r : ℕ) (κ : List Bool) : List ℕ := pairs16.map fun p => pairVal r κ p.1 p.2

theorem evalC_map {α β : Type*} (P : List β) (K : List α) (g : α → β → ℕ) (h : β → ℕ)
    (m : α → ℕ) :
    evalC (K.map fun t => P.map (g t)) (P.map h) (K.map m) =
      P.map fun p => h p * (K.map fun t => g t p ^ m t).prod := by
  induction K generalizing h with
  | nil => simp [evalC]
  | cons t K ih =>
    simp only [List.map_cons, evalC, stepPow, List.zipWith_map, List.zipWith_self]
    rw [ih (fun p => h p * g t p ^ m t)]
    simp [mul_assoc]

theorem sum_pairs16 (f : ℕ × ℕ → ℕ) :
    (pairs16.map f).sum = ∑ i ∈ range 4, ∑ j ∈ range 4, f (i, j) := by
  simp [pairs16, Finset.sum_range_succ, List.range_succ]
  ring

/-! ### Encoding four-sets inside `A ∪ B` -/

section Encoding

variable (A B : Finset ℕ)

/-- `A ∩ B`, `A \ B` and `B \ A`, each in increasing order. -/
def lI : List ℕ := (A ∩ B).sort (· ≤ ·)
def lP : List ℕ := (A \ B).sort (· ≤ ·)
def lQ : List ℕ := (B \ A).sort (· ≤ ·)
/-- `A`, `B` and `A ∪ B` as lists, with `A ∩ B` first. -/
def lA : List ℕ := lI A B ++ lP A B
def lB : List ℕ := lI A B ++ lQ A B
def lU : List ℕ := lA A B ++ lQ A B

/-- The membership bits of `S` along `lU A B`. -/
def key (S : Finset ℕ) : List Bool := (lU A B).map fun x => decide (x ∈ S)

variable {A B}

theorem nodup_lA : (lA A B).Nodup := by
  refine List.nodup_append.mpr ⟨sort_nodup _ _, sort_nodup _ _, fun x hx y hy => ?_⟩
  rw [lI, mem_sort] at hx; rw [lP, mem_sort] at hy
  rintro rfl; simp_all

theorem nodup_lU : (lU A B).Nodup := by
  refine List.nodup_append.mpr ⟨nodup_lA, sort_nodup _ _, fun x hx y hy => ?_⟩
  rw [lA, List.mem_append, lI, lP, mem_sort, mem_sort] at hx; rw [lQ, mem_sort] at hy
  rintro rfl; simp_all

theorem mem_lA {x : ℕ} : x ∈ lA A B ↔ x ∈ A := by
  simp only [lA, lI, lP, List.mem_append, mem_sort, mem_inter, mem_sdiff]; tauto

theorem mem_lB {x : ℕ} : x ∈ lB A B ↔ x ∈ B := by
  simp only [lB, lI, lQ, List.mem_append, mem_sort, mem_inter, mem_sdiff]; tauto

theorem mem_lU {x : ℕ} : x ∈ lU A B ↔ x ∈ A ∪ B := by
  simp only [lU, List.mem_append, mem_lA, lQ, mem_sort, mem_sdiff, mem_union]; tauto

theorem nodup_lB : (lB A B).Nodup := by
  refine List.nodup_append.mpr ⟨sort_nodup _ _, sort_nodup _ _, fun x hx y hy => ?_⟩
  rw [lI, mem_sort] at hx; rw [lQ, mem_sort] at hy
  rintro rfl; simp_all

theorem length_lI : (lI A B).length = (A ∩ B).card := length_sort _

theorem length_lA (hA : A.card = 4) : (lA A B).length = 4 := by
  rw [← List.toFinset_card_of_nodup nodup_lA, ← hA]
  congr 1; ext x; simp [mem_lA]

theorem length_lB (hB : B.card = 4) : (lB A B).length = 4 := by
  rw [← List.toFinset_card_of_nodup nodup_lB, ← hB]
  congr 1; ext x; simp [mem_lB]

theorem length_lQ (hB : B.card = 4) :
    (lQ A B).length = 4 - (A ∩ B).card := by
  have := length_lB (A := A) hB
  rw [lB, List.length_append, length_lI] at this
  omega

theorem length_lU (hA : A.card = 4) (hB : B.card = 4) :
    (lU A B).length = 8 - (A ∩ B).card := by
  have h1 := length_lQ (A := A) hB
  have h2 : (A ∩ B).card ≤ 4 := hA ▸ card_le_card inter_subset_left
  rw [lU, List.length_append, length_lA hA]; omega

/-- A sum over `A` is a sum over the positions of `lA`. -/
theorem sum_eq_sum_range {l : List ℕ} (hl : l.Nodup) (f : ℕ → ℕ) :
    ∑ x ∈ l.toFinset, f x = ∑ i ∈ range l.length, f (l.getD i 0) := by
  rw [List.sum_toFinset _ hl]
  clear hl
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, sum_range_succ', add_comm]
    simp

theorem toFinset_lA : (lA A B).toFinset = A := by ext x; simp [mem_lA]
theorem toFinset_lB : (lB A B).toFinset = B := by ext x; simp [mem_lB]

theorem getD_eq_getElem' (l : List ℕ) {i : ℕ} (h : i < l.length) : l.getD i 0 = l[i] := by
  simp [List.getD, List.getElem?_eq_getElem h]

theorem getD_app_left (l₁ l₂ : List ℕ) {i : ℕ} (h : i < l₁.length) :
    (l₁ ++ l₂).getD i 0 = l₁.getD i 0 := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_right (l₁ l₂ : List ℕ) {i : ℕ} (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i 0 = l₂.getD (i - l₁.length) 0 := by
  simp [List.getD, List.getElem?_append_right h]

/-- The colours at the positions of the key. -/
theorem getD_lU_left {i : ℕ} (hi : i < (lA A B).length) :
    (lU A B).getD i 0 = (lA A B).getD i 0 := by
  rw [lU, getD_app_left _ _ hi]

theorem getD_lB_eq {j : ℕ} (hA : A.card = 4) (hB : B.card = 4) (hj : j < 4) :
    (lB A B).getD j 0 = (lU A B).getD (posB (A ∩ B).card j) 0 := by
  have hI := length_lI (A := A) (B := B)
  have hQ := length_lQ (A := A) hB
  unfold posB
  split_ifs with hjr
  · rw [getD_lU_left (by rw [length_lA hA]; omega), lA, lB,
      getD_app_left _ _ (by omega), getD_app_left _ _ (by omega)]
  · rw [lB, getD_app_right _ _ (by omega), lU,
      getD_app_right _ _ (by rw [length_lA hA]; omega), length_lA hA, hI]
    congr 1; omega

theorem getD_key (S : Finset ℕ) {x : ℕ} (hx : x < (lU A B).length) :
    (key A B S).getD x false = decide ((lU A B).getD x 0 ∈ S) := by
  simp [key, List.getD, List.getElem?_map, List.getElem?_eq_getElem hx]

/-- `a_i = b_j` exactly when `i = j` falls inside `A ∩ B`. -/
theorem getD_lA_eq_getD_lB_iff (hA : A.card = 4) (hB : B.card = 4) {i j : ℕ} (hi : i < 4)
    (hj : j < 4) :
    (lA A B).getD i 0 = (lB A B).getD j 0 ↔ i = j ∧ j < (A ∩ B).card := by
  have hI := length_lI (A := A) (B := B)
  have hlA := length_lA (A := A) (B := B) hA
  have hQ := length_lQ (A := A) hB
  by_cases hjr : j < (A ∩ B).card
  · have hb : (lB A B).getD j 0 = (lA A B).getD j 0 := by
      rw [lB, lA, getD_app_left _ _ (by omega), getD_app_left _ _ (by omega)]
    rw [hb, getD_eq_getElem' _ (by omega), getD_eq_getElem' _ (by omega),
      nodup_lA.getElem_inj_iff]
    simp [hjr]
  · simp only [hjr, and_false, iff_false]
    intro h
    have ha : (lA A B).getD i 0 ∈ A := by
      rw [← mem_lA, getD_eq_getElem' _ (by omega)]; exact List.getElem_mem _
    have hb : (lB A B).getD j 0 ∈ B \ A := by
      rw [lB, getD_app_right _ _ (by omega), getD_eq_getElem' _ (by omega), ← mem_sort
        (· ≤ ·)]
      exact List.getElem_mem _
    rw [h] at ha
    exact (mem_sdiff.mp hb).2 ha

theorem card_sdiff_pair_eq_pairVal (hA : A.card = 4) (hB : B.card = 4) {S : Finset ℕ}
    (hS : S.card = 4) {i j : ℕ} (hi : i < 4) (hj : j < 4) :
    (S \ {(lA A B).getD i 0, (lB A B).getD j 0}).card =
      pairVal (A ∩ B).card (key A B S) i j := by
  have hU := length_lU (A := A) (B := B) hA hB
  have hr : (A ∩ B).card ≤ 4 := hA ▸ card_le_card inter_subset_left
  have hbitA : bit (key A B S) i = if (lA A B).getD i 0 ∈ S then 1 else 0 := by
    rw [bit, getD_key S (by omega), getD_lU_left (by rw [length_lA hA]; omega)]
    simp
  have hbitB : bit (key A B S) (posB (A ∩ B).card j) =
      if (lB A B).getD j 0 ∈ S then 1 else 0 := by
    have : posB (A ∩ B).card j < (lU A B).length := by unfold posB; split_ifs <;> omega
    rw [bit, getD_key S this, ← getD_lB_eq hA hB hj]
    simp
  rw [card_sdiff, hS, pairVal, hbitA, hbitB]
  have heq := getD_lA_eq_getD_lB_iff hA hB hi hj
  set a := (lA A B).getD i 0
  set b := (lB A B).getD j 0
  by_cases hab : a = b
  · have hc := heq.mp hab
    rw [if_pos hc, ← hab, insert_eq_of_mem (mem_singleton_self a)]
    by_cases haS : a ∈ S <;> simp [haS]
  · have hc : ¬ (i = j ∧ j < (A ∩ B).card) := fun h => hab (heq.mpr h)
    rw [if_neg hc]
    by_cases haS : a ∈ S <;> by_cases hbS : b ∈ S <;>
      simp [haS, hbS, insert_inter_of_mem, insert_inter_of_notMem, card_insert_of_notMem, hab]

theorem count_true_key {S : Finset ℕ} (hsub : S ⊆ A ∪ B) (hS : S.card = 4) :
    (key A B S).count true = 4 := by
  have h1 : ∀ l : List ℕ, (l.map fun x => decide (x ∈ S)).count true =
      (l.filter fun x => decide (x ∈ S)).length := by
    intro l; induction l with
    | nil => simp
    | cons x l ih => by_cases hx : x ∈ S <;> simp [hx, ih]
  rw [key, h1, ← List.toFinset_card_of_nodup (nodup_lU.filter _), List.toFinset_filter, ← hS]
  congr 1; ext x
  simp only [mem_filter, List.mem_toFinset, mem_lU, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩

end Encoding

/-! ### Pushing the right lists into `A ∪ B` -/

theorem card_sdiff_pair (S : Finset ℕ) (a b : ℕ) :
    (S \ {a, b}).card = S.card - ({a, b} ∩ S).card := card_sdiff

theorem exists_push {A B : Finset ℕ} (hA : A.card = 4) {S : Finset ℕ} (hS : S.card = 4) :
    ∃ S', S' ⊆ A ∪ B ∧ S'.card = 4 ∧
      ∀ a ∈ A, ∀ b ∈ B, (S' \ {a, b}).card ≤ (S \ {a, b}).card := by
  obtain ⟨u, hsu, hut, hu⟩ := exists_subsuperset_card_eq (s := S ∩ (A ∪ B)) (t := A ∪ B)
    (n := 4) inter_subset_right (hS ▸ card_le_card inter_subset_left)
    (hA ▸ card_le_card subset_union_left)
  refine ⟨u, hut, hu, fun a ha b hb => ?_⟩
  rw [card_sdiff_pair, card_sdiff_pair, hu, hS]
  refine Nat.sub_le_sub_left (card_le_card fun x hx => ?_) 4
  obtain ⟨hxab, hxS⟩ := mem_inter.mp hx
  refine mem_inter.mpr ⟨hxab, hsu (mem_inter.mpr ⟨hxS, ?_⟩)⟩
  rcases mem_insert.mp hxab with rfl | h
  · exact mem_union_left _ ha
  · rw [mem_singleton.mp h]; exact mem_union_right _ hb

/-! ### All keys -/

/-- Every Boolean list of length `n`. -/
def allBool : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBool n).flatMap fun l => [false :: l, true :: l]

theorem mem_allBool : ∀ l : List Bool, l ∈ allBool l.length
  | [] => by simp [allBool]
  | x :: l => by
    simp only [List.length_cons, allBool, List.mem_flatMap]
    exact ⟨l, mem_allBool l, by cases x <;> simp⟩

/-! ### Grouping the right vertices by key -/

theorem prod_eq_prod_keys {n : ℕ} {K : List (List Bool)} (hK : K.Nodup)
    (f : Fin n → List Bool) (hf : ∀ w, f w ∈ K) (G : List Bool → ℕ) :
    ∏ w, G (f w) = (K.map fun t => G t ^ (univ.filter fun w => f w = t).card).prod := by
  classical
  rw [← prod_fiberwise_of_maps_to (t := K.toFinset) (fun w _ => List.mem_toFinset.mpr (hf w)),
    List.prod_toFinset _ hK]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  rw [prod_congr rfl fun w hw => by rw [(mem_filter.mp hw).2], prod_const]

theorem sum_card_keys {n : ℕ} {K : List (List Bool)} (hK : K.Nodup)
    (f : Fin n → List Bool) (hf : ∀ w, f w ∈ K) :
    (K.map fun t => (univ.filter fun w => f w = t).card).sum = n := by
  classical
  rw [← List.sum_toFinset _ hK, ← card_eq_sum_card_fiberwise (fun w _ => by
    simpa using hf w), card_univ, Fintype.card_fin]

/-- The constant list of partial products. -/
def ones16 : List ℕ := pairs16.map fun _ => 1

/-! ### Assembly -/

/-- The numeric statement for overlap `r`: a complete, duplicate-free list of keys, and the
checker's goal for their rows. -/
def KeyGoal (T n r : ℕ) (K : List (List Bool)) : Prop :=
  K.Nodup ∧ (∀ κ ∈ allBool (8 - r), κ.count true = 4 → κ ∈ K) ∧
    Goal T (K.map (rowOf r)) ones16 n

/-- Given the numeric goal for every overlap, every four-list assignment on `K₂,ₙ` has at least
`T` colourings. -/
theorem le_col_of_keyGoals {n T : ℕ} (goals : ∀ r ≤ 4, ∃ K, KeyGoal T n r K)
    (L : ListAssignment (Fin 2 ⊕ Fin n)) (hL : IsNListAssignment L 4) :
    T ≤ (completeBipartiteGraph (Fin 2) (Fin n)).col L := by
  classical
  rw [col_completeBipartite_two_right]
  set A := L (Sum.inl 0)
  set B := L (Sum.inl 1)
  have hA : A.card = 4 := hL _
  have hB : B.card = 4 := hL _
  -- Push every right list into `A ∪ B`.
  choose T' hT'sub hT'card hT'le using fun w => exists_push (B := B) hA (hL (Sum.inr w))
  refine le_trans ?_ (sum_le_sum fun a ha => sum_le_sum fun b hb =>
    prod_le_prod' fun w _ => hT'le w a ha b hb)
  -- Fix the overlap and its numeric goal.
  set r := (A ∩ B).card with hr
  obtain ⟨K, hKnodup, hKall, hgoal⟩ := goals r (hA ▸ card_le_card inter_subset_left)
  have hkey : ∀ w, key A B (T' w) ∈ K := fun w => by
    refine hKall _ ?_ (count_true_key (hT'sub w) (hT'card w))
    have := mem_allBool (key A B (T' w))
    rw [key, List.length_map, length_lU hA hB] at this
    exact this
  set m : List Bool → ℕ := fun t => (univ.filter fun w => key A B (T' w) = t).card
  -- Rewrite the sum over `A × B` as the checker's sum over the sixteen pairs.
  have hsumA : ∀ f : ℕ → ℕ, ∑ a ∈ A, f a = ∑ i ∈ range 4, f ((lA A B).getD i 0) := by
    intro f
    conv_lhs => rw [← toFinset_lA (A := A) (B := B)]
    rw [sum_eq_sum_range nodup_lA, length_lA hA]
  have hsumB : ∀ f : ℕ → ℕ, ∑ b ∈ B, f b = ∑ j ∈ range 4, f ((lB A B).getD j 0) := by
    intro f
    conv_lhs => rw [← toFinset_lB (A := A) (B := B)]
    rw [sum_eq_sum_range nodup_lB, length_lB hB]
  rw [hsumA]
  simp_rw [hsumB]
  have hpair : ∀ i ∈ range 4, ∀ j ∈ range 4,
      ∏ w, (T' w \ {(lA A B).getD i 0, (lB A B).getD j 0}).card =
        (K.map fun t => pairVal r t i j ^ m t).prod := by
    intro i hi j hj
    rw [prod_congr rfl fun w _ => card_sdiff_pair_eq_pairVal hA hB (hT'card w)
      (mem_range.mp hi) (mem_range.mp hj)]
    exact prod_eq_prod_keys hKnodup (fun w => key A B (T' w)) hkey (fun t => pairVal r t i j)
  rw [sum_congr rfl fun i hi => sum_congr rfl fun j hj => hpair i hi j hj]
  have hms : (K.map m).sum = n := by
    simpa [m] using sum_card_keys hKnodup (fun w => key A B (T' w)) hkey
  have := hgoal (K.map m) (by simp) hms
  have hrow : K.map (rowOf r) = K.map fun t => pairs16.map fun p => pairVal r t p.1 p.2 := rfl
  rw [hrow, ones16, evalC_map, sum_pairs16] at this
  simpa using this



end SimpleGraph.TwoDegenerate.K2n
