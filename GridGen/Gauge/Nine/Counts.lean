/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Paths

/-!
# Exact crossing-path counts up to twelve cells

`cntW` counts what `enum` lists, without building the lists (`length_enum`). That makes kernel
evaluation of the shape counts up to twelve cells affordable: `1, 2, 4, 10, 31, 76, 212, 552, 1607,
4250, 12296` for `L = 2, …, 12`.
-/

open Finset

namespace GridGen.Gauge

/-- The number of valid shape walks with `n` steps (`enum`, counted). -/
def cntW : ℤ → ℤ → Option (Fin 4) → ℕ → ℕ
  | x, y, _, 0 => if x = 0 ∧ y ≤ 0 then 1 else 0
  | x, y, prev, n + 1 =>
      if (n + 1 : ℤ) < x + max y 0 then 0
      else ([0, 1, 2, 3] : List (Fin 4)).foldr (fun d acc =>
        (if prev ≠ some (opp d) ∧ 0 ≤ x + dx d then cntW (x + dx d) (y + dy d) (some d) n else 0)
          + acc) 0

theorem length_enum : ∀ (n : ℕ) (x y : ℤ) (prev : Option (Fin 4)),
    (enum x y prev n).length = cntW x y prev n := by
  intro n
  induction n with
  | zero => intro x y prev; simp only [enum, cntW]; split_ifs <;> rfl
  | succ n ih =>
      intro x y prev
      simp only [enum, cntW]
      split_ifs
      · rfl
      · simp only [List.flatMap_cons, List.flatMap_nil, List.length_append, List.foldr_cons,
          List.foldr_nil, List.append_nil]
        congr 1 <;> [skip; congr 1 <;> [skip; congr 1 <;> [skip; skip]]] <;>
          (split_ifs <;> simp [ih])

/-- The shape counts, counted. -/
def shapeCnt (L : ℕ) : ℕ := ((List.range (L - 1)).map fun d : ℕ => cntW 0 ((d : ℤ) + 1) none (L - 1)).sum

theorem shapeCount_eq_cnt (L : ℕ) : shapeCount L = shapeCnt L := by
  unfold shapeCount shapeCnt
  congr 1
  refine List.map_congr_left fun d _ => length_enum _ _ _ _

theorem shapeCnt_8 : shapeCnt 8 = 212 := by unfold shapeCnt; decide +kernel
theorem shapeCnt_9 : shapeCnt 9 = 552 := by unfold shapeCnt; decide +kernel
theorem shapeCnt_10 : shapeCnt 10 = 1607 := by unfold shapeCnt; decide +kernel
theorem shapeCnt_11 : shapeCnt 11 = 4250 := by unfold shapeCnt; decide +kernel
theorem shapeCnt_12 : shapeCnt 12 = 12296 := by unfold shapeCnt; decide +kernel

end GridGen.Gauge
