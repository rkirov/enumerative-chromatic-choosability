/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.FaceDefs

/-!
# Closure under the face operation, as a property

`FaceClosed k m` says that the invariant `HasPot` passes from the `m + 1` path edges of a face
with `m` interior vertices to its root edge, with the constant of the constant-list count. It is
proved from the capacity lemma in `Outerplanar/Face.lean` and used by the induction over the
graph in `Outerplanar/Graph.lean`.
-/

namespace Outerplanar

open Finset

/-- The invariant is closed under faces with `m` interior vertices, at list size `k`. -/
def FaceClosed (k m : ℕ) : Prop :=
  ∀ (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ), Lu.card = k → Lv.card = k →
    (∀ j, (Li j).card = k) → ∀ (ω : Fin m → ℕ → ℝ), (∀ j, ∀ c ∈ Li j, 0 < ω j c) →
    ∀ (E : Fin (m + 1) → ℕ → ℕ → ℝ), (∀ j c d, 0 ≤ E j c d) → ∀ (A : Fin (m + 1) → ℝ),
    (∀ j, 0 < A j) →
    (∀ j : Fin (m + 1),
      HasPot (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) →
    HasPot Lu Lv (faceSum Li ω E)
      ((((k : ℝ) - 1) ^ (m + 1) - (-1) ^ (m + 1)) / k * (∏ j, A j) * ∏ j, gmean (Li j) (ω j))

end Outerplanar
