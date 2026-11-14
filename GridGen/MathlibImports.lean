/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic

/-!
# The part of Mathlib that `GridGen/` uses

Five files of `GridGen/` used to `import Mathlib`, and 332 modules -- every certificate module of
the height-four, five and six grids among them -- inherited all of it: 5.7 GB of mapped files and
about half a minute of import work per module. The imports above are the modules that define a
constant some `GridGen` declaration refers to (computed from the built library, 2026-11-13, and
reduced to those not implied by another), together with `Mathlib.Tactic` for tactic syntax.
That is under half of Mathlib: 2.9 GB and a quarter of the import work.

If a `GridGen` file needs something outside this set, add the import here or in that file.
-/
