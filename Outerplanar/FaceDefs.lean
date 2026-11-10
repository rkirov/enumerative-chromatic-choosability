/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Pot

/-!
# The face operation: definitions

A face is a path `u, x 0, …, x (m - 1), v` whose ends are joined by the root edge. Each of its
`m + 1` path edges carries a pair profile `E j`, each interior vertex a weight. `faceSum` is the
resulting pair profile on `(u, v)`.
-/

namespace Outerplanar

open Finset

variable {m : ℕ}

/-- The lists along the path `u, x 0, …, x (m - 1), v`. -/
def pathList (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ) : Fin (m + 2) → Finset ℕ :=
  Fin.cons Lu (Fin.snoc Li Lv)

/-- A colouring of the path, from the colours of its ends and of its interior. -/
def pathCol (c d : ℕ) (g : Fin m → ℕ) : Fin (m + 2) → ℕ := Fin.cons c (Fin.snoc g d)

/-- The pair profile of a face: the sum over the colourings `g` of the interior of the interior
weights times the profiles of the `m + 1` edges of the path. -/
noncomputable def faceSum (Li : Fin m → Finset ℕ) (ω : Fin m → ℕ → ℝ)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (c d : ℕ) : ℝ :=
  ∑ g ∈ Fintype.piFinset Li, (∏ j, ω j (g j)) *
    ∏ j : Fin (m + 1), E j (pathCol c d g j.castSucc) (pathCol c d g j.succ)

end Outerplanar
