/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import NonPersistence.AtK

/-!
# The bad `(k + 1)`-list assignment

Zhang–Dong's assignment (2.3), with `k = m + 3` and the colors named concretely:

* `C = {0, …, m + 1}` — `k - 1` colors, shared by every list;
* `B₁ = {m + 2, m + 3}`, given to the clique and to `s₁`;
* `B₂ = {m + 4, m + 5}`, given to `s₂`;
* `D j`, for `j < 4`, one of the four transversals of `B₁ × B₂`, given to the `j`-th kind of
  apex.

Every list has `(k - 1) + 2 = k + 1` colors. Note that `C ∪ B₁ = range (m + 4)` exactly, so on
the clique and on `s₁` the assignment *is* the constant one — only `s₂` and the apexes differ.
That is what makes the comparison in `NonPersistence/Compare.lean` an inclusion of coloring sets
rather than a computation.
-/

open Finset SimpleGraph

namespace ZhangDong

/-! ### The color sets -/

/-- The `k - 1` shared colors. -/
def C (m : ℕ) : Finset ℕ := Finset.range (m + 2)

/-- The four transversals of `B₁ × B₂`. Only `j < 4` is ever used. -/
def D (m : ℕ) : ℕ → Finset ℕ
  | 0 => {m + 2, m + 4}
  | 1 => {m + 2, m + 5}
  | 2 => {m + 3, m + 4}
  | _ => {m + 3, m + 5}

/-- The list of the apex added at step `i`: the shared colors plus one transversal, cycling. -/
def A (m : ℕ) (i : ℕ) : Finset ℕ := C m ∪ D m (i % 4)

/-- The list assignment on `H m`: the clique and `s₁` get the full `range (m + 4)`, and `s₂` gets
the shared colors plus `B₂`. -/
def LH (m : ℕ) : ListAssignment (Option (Option (XV m)))
  | none => C m ∪ {m + 4, m + 5}
  | some none => Finset.range (m + 4)
  | some (some _) => Finset.range (m + 4)

/-- The bad assignment on all of `zd m t`. -/
def Lbad (m t : ℕ) : ListAssignment (TowerV (Option (Option (XV m))) (4 * t)) :=
  towerListF (LH m) (A m) (4 * t)

/-! ### Every list has `k + 1 = m + 4` colors -/

theorem notMem_C (m : ℕ) {a : ℕ} (h : m + 2 ≤ a) : a ∉ C m := by
  simp only [C, Finset.mem_range]
  omega

theorem card_union_C (m : ℕ) {a b : ℕ} (ha : m + 2 ≤ a) (hb : m + 2 ≤ b) (hab : a ≠ b) :
    (C m ∪ {a, b}).card = m + 4 := by
  rw [Finset.card_union_of_disjoint, Finset.card_insert_of_notMem (by simpa using hab),
    Finset.card_singleton, C, Finset.card_range]
  refine Finset.disjoint_right.mpr fun c hc => ?_
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact notMem_C m ha
  · rw [Finset.mem_singleton] at hc
    subst hc
    exact notMem_C m hb

theorem card_D (m : ℕ) {j : ℕ} (hj : j < 4) : (C m ∪ D m j).card = m + 4 := by
  match j, hj with
  | 0, _ => exact card_union_C m (by omega) (by omega) (by omega)
  | 1, _ => exact card_union_C m (by omega) (by omega) (by omega)
  | 2, _ => exact card_union_C m (by omega) (by omega) (by omega)
  | 3, _ => exact card_union_C m (by omega) (by omega) (by omega)

theorem card_A (m i : ℕ) : (A m i).card = m + 4 :=
  card_D m (Nat.mod_lt i (by omega))

theorem card_LH (m : ℕ) (v : Option (Option (XV m))) : (LH m v).card = m + 4 := by
  rcases v with _ | _ | i
  · exact card_union_C m (by omega) (by omega) (by omega)
  · exact Finset.card_range _
  · exact Finset.card_range _

theorem isNListAssignment_Lbad (m t : ℕ) : IsNListAssignment (Lbad m t) (m + 4) :=
  isNListAssignment_towerListF (card_LH m) (card_A m) (4 * t)

/-! ### `C ∪ B₁` is the full palette -/

theorem range_eq_C_union (m : ℕ) : Finset.range (m + 4) = C m ∪ {m + 2, m + 3} := by
  ext c
  simp only [C, Finset.mem_range, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  omega

end ZhangDong
