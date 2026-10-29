/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.K5.BitCert.LP00
import GridGen.Five.K5.BitCert.LP01
import GridGen.Five.K5.BitCert.LP02
import GridGen.Five.K5.BitCert.PW00

/-!
# Height five at `k = 5`: all state-bit certificates

The pointwise classes (`ptAll`) and the classes closed by dual certificates (`lpAll`), one per
reflection class of mismatch quads off `(0,0,0,0)` and the residual exact classes.
-/

namespace GridGen.Five.K5

/-- All classes closed by a dual certificate. -/
def lpAll : List ((ℕ × ℕ × ℕ × ℕ) × BitCert5) :=
  List.flatten [bitLP00, bitLP01, bitLP02]

/-- All pointwise classes. -/
def ptAll : List (ℕ × ℕ × ℕ × ℕ) :=
  List.flatten [ptPW00]

theorem lpAll_ok : ∀ x ∈ lpAll, bitOK5 RM x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2 = true := by
  intro x hx
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.mp hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  exacts [bitLP00_ok x hx, bitLP01_ok x hx, bitLP02_ok x hx]

theorem ptAll_ok : ∀ x ∈ ptAll, ptOK5 NM x.1 x.2.1 x.2.2.1 x.2.2.2 = true := by
  intro x hx
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.mp hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl
  exacts [ptPW00_ok x hx]

end GridGen.Five.K5
