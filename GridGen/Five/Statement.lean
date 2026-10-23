/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Defs

/-!
# The height-five seam inequality: statement

The interface between the two halves of `GridGen/Five/`, `GridGen/Four/Statement.lean` with five
rows and a box with one lower edge per pattern orbit.

* `GU k w s`: the pattern-weighted number of uniform successors of a column `s`, computed on the
  canonical realisation `canon s` of its equality pattern inside `{0, …, k-1}`.
* `InBox5 w`: the pattern weights lie in the per-orbit box `lo5 i ≤ w i ≤ 1` of
  `ai_research_notes/h5k6/boxes_k6.json` (`H5_K6_FEASIBILITY_2026-10-23.md` §1). Its lower edges
  are exact rationals, the minimal invariant box at `k = 6` rounded down to `1/2000`; the
  alternating orbit has `lo5 0 = 1`, so `w 0 = 1`. The uniform transfer at `k = 6` maps the box
  into itself (`GridGen/Five/Cone.lean`). The box is the `k = 6` box: the statements below take
  `k` as a parameter, as at height four, but only `k = 6` is used.
* `Seam5Holds k`: for every previous column with lists `X` of `k - 1` or `k` colours, every next
  column with `k`-lists `B` and every weight in the box, the weighted successors from `B` dominate
  the uniform prediction, summed over the proper states of `X`.
* `Init5Holds k`: a column of `k`-lists, weighted by pattern, weighs at least the uniform column.

The bridge to GridGen's telescoping (`GridGen/Five/Bridge.lean`) turns `Seam5Holds 6` into
`TwoStepExplicit` and `FirstSeamExplicit` for `pathG 4` at every horizon, and `Init5Holds 6` into
GridGen's initial condition.
-/

namespace GridGen.Five

open Finset

/-- The canonical realisation of the equality pattern of a proper column: colours numbered
`0, 1, 2, …` in order of first appearance. -/
def canon (s : T5) : T5 :=
  (0, 1, if r3 s = r1 s then 0 else 2,
    if r4 s = r2 s then 1 else if r4 s = r1 s then 0 else if r3 s = r1 s then 2 else 3,
    if r5 s = r3 s then (if r3 s = r1 s then 0 else 2)
    else if r5 s = r2 s then 1
    else if r5 s = r1 s then 0
    else if r4 s = r2 s ∨ r4 s = r1 s then (if r3 s = r1 s then 2 else 3)
    else if r3 s = r1 s then 3 else 4)

/-- The pattern-weighted number of uniform successors of `s`. -/
noncomputable def GU (k : ℕ) (w : Wt5) (s : T5) : ℝ :=
  G w ((range k).erase (r1 (canon s))) ((range k).erase (r2 (canon s)))
    ((range k).erase (r3 (canon s))) ((range k).erase (r4 (canon s)))
    ((range k).erase (r5 (canon s)))

/-- The pattern-weighted number of successors of `s` in a column with lists `B₁, …, B₅`. -/
noncomputable def GB (w : Wt5) (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (s : T5) : ℝ :=
  G w (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s)) (B₅.erase (r5 s))

/-- The lower edges of the invariant box at `k = 6`, one per orbit (numbering of
`GridGen/Five/Defs.lean`): `01010` `1`, `01012/01212` `987/1000`, `01020` `1977/2000`,
`01021/01202` `1947/2000`, `01023/01232` `1953/2000`, `01201` `959/1000`, `01203/01231`
`481/500`, `01210` `977/1000`, `01213` `1951/2000`, `01230` `1933/2000`, `01234` `1931/2000`. -/
def lo5 : Fin 11 → ℚ :=
  ![1, 987 / 1000, 1977 / 2000, 1947 / 2000, 1953 / 2000, 959 / 1000, 481 / 500, 977 / 1000,
    1951 / 2000, 1933 / 2000, 1931 / 2000]

/-- The pattern weights lie in the invariant box; in particular `w 0 = 1`. -/
def InBox5 (w : Wt5) : Prop := ∀ i, (lo5 i : ℝ) ≤ w i ∧ w i ≤ 1

/-- **The height-five seam inequality at list size `k`** (with the `k = 6` box). -/
def Seam5Holds (k : ℕ) : Prop :=
  ∀ (w : Wt5), InBox5 w →
  ∀ (X₁ X₂ X₃ X₄ X₅ B₁ B₂ B₃ B₄ B₅ : Finset ℕ),
    (k - 1 ≤ X₁.card ∧ X₁.card ≤ k) → (k - 1 ≤ X₂.card ∧ X₂.card ≤ k) →
    (k - 1 ≤ X₃.card ∧ X₃.card ≤ k) → (k - 1 ≤ X₄.card ∧ X₄.card ≤ k) →
    (k - 1 ≤ X₅.card ∧ X₅.card ≤ k) →
    B₁.card = k → B₂.card = k → B₃.card = k → B₄.card = k → B₅.card = k →
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU k w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GB w B₁ B₂ B₃ B₄ B₅ s

/-- **The height-five initial inequality at list size `k`** (with the `k = 6` box): a column of
`k`-lists, weighted by pattern, weighs at least the uniform column. -/
def Init5Holds (k : ℕ) : Prop :=
  ∀ (w : Wt5), InBox5 w →
  ∀ (X₁ X₂ X₃ X₄ X₅ : Finset ℕ),
    X₁.card = k → X₂.card = k → X₃.card = k → X₄.card = k → X₅.card = k →
    ∑ s ∈ sts (range k) (range k) (range k) (range k) (range k), gw w s
      ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, gw w s

end GridGen.Five
