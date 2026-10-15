/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Defs

/-!
# The height-four seam inequality: statement

The interface between the two halves of `GridGen/Four/`.

* `GU k w s`: the pattern-weighted number of uniform successors of a column `s`, computed on the
  canonical realisation `canon s` of its equality pattern inside `{0, …, k-1}`.
* `InBox k w`: the pattern weights lie in the box `[ρ, 1]³`, `ρ = 1 - 2/(k-2)³`, which the uniform
  transfer maps into itself (`GridGen/Four/Cone.lean`).
* `Seam4Holds k`: for every previous column with lists `X` of `k - 1` or `k` colours, every next
  column with `k`-lists `B` and every weight in the box, the weighted successors from `B` dominate
  the uniform prediction, summed over the proper states of `X`.

`GridGen/Four/Seam.lean` proves `Seam4Holds k` for `8 ≤ k ≤ 15` and `GridGen/Four/Seam7.lean` at
`k = 7`; the bridge to GridGen's
telescoping (`GridGen/Four/Bridge.lean`) turns it into `TwoStepExplicit` and
`FirstSeamExplicit` for `pathG 3` at every horizon.
-/

namespace GridGen.Four

open Finset

/-- The canonical realisation of the equality pattern of a proper column: colours numbered
`0, 1, 2, 3` in order of first appearance. -/
def canon (s : T4) : T4 :=
  (0, 1, if r3 s = r1 s then 0 else 2,
    if r4 s = r2 s then 1 else if r4 s = r1 s then 0 else if r3 s = r1 s then 2 else 3)

/-- The pattern-weighted number of uniform successors of `s`. -/
noncomputable def GU (k : ℕ) (w : Wt) (s : T4) : ℝ :=
  G w ((range k).erase (r1 (canon s))) ((range k).erase (r2 (canon s)))
    ((range k).erase (r3 (canon s))) ((range k).erase (r4 (canon s)))

/-- The pattern-weighted number of successors of `s` in a column with lists `B₁, …, B₄`. -/
noncomputable def GB (w : Wt) (B₁ B₂ B₃ B₄ : Finset ℕ) (s : T4) : ℝ :=
  G w (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))

/-- The lower edge of the invariant box. -/
noncomputable def rho (k : ℕ) : ℝ := 1 - 2 / ((k : ℝ) - 2) ^ 3

/-- The pattern weights lie in the invariant box. -/
def InBox (k : ℕ) (w : Wt) : Prop :=
  rho k ≤ w.a ∧ w.a ≤ 1 ∧ rho k ≤ w.b ∧ w.b ≤ 1 ∧ rho k ≤ w.c ∧ w.c ≤ 1

/-- **The height-four seam inequality at list size `k`.** -/
def Seam4Holds (k : ℕ) : Prop :=
  ∀ (w : Wt), InBox k w →
  ∀ (X₁ X₂ X₃ X₄ B₁ B₂ B₃ B₄ : Finset ℕ),
    (k - 1 ≤ X₁.card ∧ X₁.card ≤ k) → (k - 1 ≤ X₂.card ∧ X₂.card ≤ k) →
    (k - 1 ≤ X₃.card ∧ X₃.card ≤ k) → (k - 1 ≤ X₄.card ∧ X₄.card ≤ k) →
    B₁.card = k → B₂.card = k → B₃.card = k → B₄.card = k →
    ∑ s ∈ sts X₁ X₂ X₃ X₄, GU k w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄, GB w B₁ B₂ B₃ B₄ s

/-- **The height-four initial inequality at list size `k`**: a column of `k`-lists, weighted by
pattern, weighs at least the uniform column. -/
def Init4Holds (k : ℕ) : Prop :=
  ∀ (w : Wt), InBox k w →
  ∀ (X₁ X₂ X₃ X₄ : Finset ℕ), X₁.card = k → X₂.card = k → X₃.card = k → X₄.card = k →
    ∑ s ∈ sts (range k) (range k) (range k) (range k), gw w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄, gw w s

end GridGen.Four
