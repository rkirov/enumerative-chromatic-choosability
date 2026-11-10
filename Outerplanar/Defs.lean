/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset

/-!
# Partial covers of a cycle: definitions

A *partial `k`-fold cover* of the cycle on `Fin n` puts a fibre `F i` of `k` colours over every
vertex and a partial matching `M i` between the fibres over `i` and `i + 1`. A colouring picks one
colour per vertex and never both ends of a matched pair. The capacity lemma (see
`ai_research_notes/OUTERPLANAR_PROOF_DRAFT_2026-11-09.md`, sections 2 and 3) bounds the weighted
number of colourings from below, for weights whose product over every fibre is one.

Everything here is a definition; the theorems are in the other files of this directory.
-/

namespace Outerplanar

open Finset

/-- A partial cover of the cycle on `Fin n`: fibres and, on every edge `i → i + 1`, a relation
between the fibre over `i` and the fibre over `i + 1`. -/
structure Cover (n : ℕ) where
  /-- the fibre over a vertex -/
  F : Fin n → Finset ℕ
  /-- `M i x y`: the colour `x` over `i` is matched with the colour `y` over `i + 1` -/
  M : Fin n → ℕ → ℕ → Prop

variable {n : ℕ} [NeZero n]

open Classical in
/-- The colourings of the cover on the active set `A`; off `A` they are pinned to `b`. -/
noncomputable def Cover.cols (P : Cover n) (A : Finset (Fin n)) (b : Fin n → ℕ) :
    Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun i => if i ∈ A then P.F i else {b i}).filter
    fun f => ∀ i, i ∈ A → i + 1 ∈ A → ¬ P.M i (f i) (f (i + 1))

/-- The weighted number of colourings on the active set. -/
noncomputable def Cover.Z (P : Cover n) (A : Finset (Fin n)) (b : Fin n → ℕ)
    (w : Fin n → ℕ → ℝ) : ℝ :=
  ∑ f ∈ P.cols A b, ∏ i ∈ A, w i (f i)

/-- Every `M i` is a partial matching between the fibres over `i` and `i + 1`. -/
def Cover.IsMatching (P : Cover n) : Prop :=
  ∀ i, (∀ x ∈ P.F i, ∀ y ∈ P.F (i + 1), ∀ y' ∈ P.F (i + 1), P.M i x y → P.M i x y' → y = y') ∧
    (∀ x ∈ P.F i, ∀ x' ∈ P.F i, ∀ y ∈ P.F (i + 1), P.M i x y → P.M i x' y → x = x')

/-- No colour is matched all the way round the cycle to itself in one turn. -/
def Cover.NoClosedThread (P : Cover n) : Prop :=
  ¬ ∃ f : Fin n → ℕ, (∀ i, f i ∈ P.F i) ∧ ∀ i, P.M i (f i) (f (i + 1))

/-- Weights that are positive on the fibres over `A` and have product one over each of them. -/
def Cover.Normalized (P : Cover n) (A : Finset (Fin n)) (w : Fin n → ℕ → ℝ) : Prop :=
  ∀ i ∈ A, (∀ c ∈ P.F i, 0 < w i c) ∧ ∏ c ∈ P.F i, w i c = 1

/-- The capacity of the cover on `A` is at least `C`. -/
def Cover.CapGE (P : Cover n) (A : Finset (Fin n)) (b : Fin n → ℕ) (C : ℝ) : Prop :=
  ∀ w, P.Normalized A w → C ≤ P.Z A b w

/-- The cover with the colour `b i` removed from the fibre over `i`. -/
def Cover.erase (P : Cover n) (b : Fin n → ℕ) : Cover n where
  F i := (P.F i).erase (b i)
  M := P.M

/-- `b` is a section of the cover that is matched along every edge except `e → e + 1`, where
both of its ends are unmatched. -/
def Cover.IsCutSection (P : Cover n) (b : Fin n → ℕ) (e : Fin n) : Prop :=
  (∀ i, b i ∈ P.F i) ∧ (∀ i, i ≠ e → P.M i (b i) (b (i + 1))) ∧
    (∀ y ∈ P.F (e + 1), ¬ P.M e (b e) y) ∧ (∀ x ∈ P.F e, ¬ P.M e x (b (e + 1)))

/-- The target of the capacity lemma: the number of colourings of a full cover whose monodromy
is a derangement. -/
def lam (k n : ℕ) : ℝ := ((k : ℝ) - 1) ^ n - (-1) ^ n

/-! ### Laws on the sets of vertices carrying the removed colour -/

/-- `J` has no two cyclically consecutive elements, except possibly across the edge
`e → e + 1`. -/
def Good (e : Fin n) (J : Finset (Fin n)) : Prop := ∀ i, i ≠ e → i ∈ J → i + 1 ∉ J

/-- The capacity bound for an `m`-fold cover on the complement of a nonempty good set: a vertex
whose predecessor is in `J` starts an arc and has `m` colours, every other one has `m - 1`. -/
def arcW (m : ℕ) (J : Finset (Fin n)) : ℝ :=
  ∏ i ∈ Jᶜ, if i - 1 ∈ J then (m : ℝ) else (m : ℝ) - 1

/-- `arcW`, with the value `g0` at the empty set. -/
def gW (m : ℕ) (g0 : ℝ) (J : Finset (Fin n)) : ℝ := if J = ∅ then g0 else arcW m J

/-- A law on good sets with all marginals `1 / k` whose entropy relative to `gW (k - 1) g0`
is at least `log C`. Given a cut section of a `k`-fold cover whose erased cover has capacity at
least `g0`, such a law shows that the capacity is at least `C`. -/
def Witness (k : ℕ) (e : Fin n) (g0 C : ℝ) : Prop :=
  ∃ p : Finset (Fin n) → ℝ, (∀ J, 0 ≤ p J) ∧
    (∀ J, 0 < p J → Good e J ∧ 0 < gW (k - 1) g0 J) ∧
    ∑ J, p J = 1 ∧ (∀ i, ∑ J with i ∈ J, p J = 1 / (k : ℝ)) ∧
    Real.log C ≤ ∑ J, p J * Real.log (gW (k - 1) g0 J / p J)

end Outerplanar
