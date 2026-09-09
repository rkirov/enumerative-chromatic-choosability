/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Checks.TwoCycles
import Checks.RubinHard
import Checks.ThetaGen
import Checks.CoreExtract
import Checks.ThetaClass

/-!
# Brute-force sanity checks

`#guard` sweeps that verify statements numerically before (or beside) their proofs, collected
here because together they cost minutes of evaluation. Nothing depends on this library; it is not
a default build target, and CI builds it separately (`lake build Checks`).
-/
