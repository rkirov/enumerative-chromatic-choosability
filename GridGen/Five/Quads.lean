/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Height five at `k = 6`: the mismatch quads with exact certificates

The mismatches `μⱼ = 6 - |Bⱼ₋₁ ∩ Bⱼ|`, `j = 2, …, 5`, form a quad. The quads listed here are
certified exactly, column type by column type (`GridGen/Five/Small5.lean`); every other quad is
covered by the analytic certificate or a dual certificate over the state bits. The list is closed
under reversal (row reflection): every quad of total mismatch one or two, and
`(0,0,2,1)`, `(0,0,3,0)`, `(0,1,1,1)`, `(0,1,2,0)`, `(0,2,0,1)` with their reversals.
-/

namespace GridGen.Five

/-- The quads certified exactly. -/
def exactQuads5 : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0, 0, 0, 1), (1, 0, 0, 0), (0, 0, 1, 0), (0, 1, 0, 0),
   (0, 0, 0, 2), (2, 0, 0, 0), (0, 0, 2, 0), (0, 2, 0, 0), (0, 0, 1, 1), (1, 1, 0, 0),
   (0, 1, 0, 1), (1, 0, 1, 0), (1, 0, 0, 1), (0, 1, 1, 0),
   (0, 0, 2, 1), (1, 2, 0, 0), (0, 0, 3, 0), (0, 3, 0, 0), (0, 1, 1, 1), (1, 1, 1, 0),
   (0, 1, 2, 0), (0, 2, 1, 0), (0, 2, 0, 1), (1, 0, 2, 0)]

theorem exactQuads5_rev : ∀ q ∈ exactQuads5,
    (q.2.2.2, q.2.2.1, q.2.1, q.1) ∈ exactQuads5 := by decide

end GridGen.Five
