/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.K5.BitCert.LP00
import GridGen.Five.K5.BitCert.LP01
import GridGen.Five.K5.BitCert.LP02
import GridGen.Five.K5.BitCert.LP03
import GridGen.Five.K5.BitCert.LP04
import GridGen.Five.K5.BitCert.LP05
import GridGen.Five.K5.BitCert.LP06
import GridGen.Five.K5.BitCert.LP07
import GridGen.Five.K5.BitCert.LP08
import GridGen.Five.K5.BitCert.LP09
import GridGen.Five.K5.BitCert.LP10
import GridGen.Five.K5.BitCert.LP11
import GridGen.Five.K5.BitCert.LP12
import GridGen.Five.K5.BitCert.LP13
import GridGen.Five.K5.BitCert.LP14
import GridGen.Five.K5.BitCert.LP15
import GridGen.Five.K5.BitCert.LP16
import GridGen.Five.K5.BitCert.LP17
import GridGen.Five.K5.BitCert.LP18
import GridGen.Five.K5.BitCert.LP19
import GridGen.Five.K5.BitCert.LP20
import GridGen.Five.K5.BitCert.LP21
import GridGen.Five.K5.BitCert.LP22
import GridGen.Five.K5.BitCert.LP23
import GridGen.Five.K5.BitCert.LP24
import GridGen.Five.K5.BitCert.LP25
import GridGen.Five.K5.BitCert.LP26
import GridGen.Five.K5.BitCert.LP27
import GridGen.Five.K5.BitCert.LP28
import GridGen.Five.K5.BitCert.LP29
import GridGen.Five.K5.BitCert.LP30
import GridGen.Five.K5.BitCert.LP31
import GridGen.Five.K5.BitCert.PW00
import GridGen.Five.K5.BitCert.PW01
import GridGen.Five.K5.BitCert.PW02
import GridGen.Five.K5.BitCert.PW03
import GridGen.Five.K5.BitCert.PW04
import GridGen.Five.K5.BitCert.PW05
import GridGen.Five.K5.BitCert.PW06
import GridGen.Five.K5.BitCert.PW07
import GridGen.Five.K5.BitCert.PW08
import GridGen.Five.K5.BitCert.PW09
import GridGen.Five.K5.BitCert.PW10
import GridGen.Five.K5.BitCert.PW11
import GridGen.Five.K5.BitCert.PW12
import GridGen.Five.K5.BitCert.PW13
import GridGen.Five.K5.BitCert.PW14
import GridGen.Five.K5.BitCert.PW15
import GridGen.Five.K5.BitCert.PW16
import GridGen.Five.K5.BitCert.PW17
import GridGen.Five.K5.BitCert.PW18
import GridGen.Five.K5.BitCert.PW19

/-!
# Height five at `k = 5`: all state-bit certificates

The pointwise classes (`ptAll`) and the classes closed by dual certificates (`lpAll`), one per
reflection class of mismatch quads off `(0,0,0,0)` and the residual exact classes.
-/

namespace GridGen.Five.K5

/-- All classes closed by a dual certificate. -/
def lpAll : List ((ℕ × ℕ × ℕ × ℕ) × BitCert5) :=
  List.flatten [bitLP00, bitLP01, bitLP02, bitLP03, bitLP04, bitLP05, bitLP06, bitLP07, bitLP08, bitLP09, bitLP10, bitLP11, bitLP12, bitLP13, bitLP14, bitLP15, bitLP16, bitLP17, bitLP18, bitLP19, bitLP20, bitLP21, bitLP22, bitLP23, bitLP24, bitLP25, bitLP26, bitLP27, bitLP28, bitLP29, bitLP30, bitLP31]

/-- All pointwise classes. -/
def ptAll : List (ℕ × ℕ × ℕ × ℕ) :=
  List.flatten [ptPW00, ptPW01, ptPW02, ptPW03, ptPW04, ptPW05, ptPW06, ptPW07, ptPW08, ptPW09, ptPW10, ptPW11, ptPW12, ptPW13, ptPW14, ptPW15, ptPW16, ptPW17, ptPW18, ptPW19]

theorem lpAll_ok : ∀ x ∈ lpAll, bitOK5 RM x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2 = true := by
  intro x hx
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.mp hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [bitLP00_ok x hx, bitLP01_ok x hx, bitLP02_ok x hx, bitLP03_ok x hx, bitLP04_ok x hx, bitLP05_ok x hx, bitLP06_ok x hx, bitLP07_ok x hx, bitLP08_ok x hx, bitLP09_ok x hx, bitLP10_ok x hx, bitLP11_ok x hx, bitLP12_ok x hx, bitLP13_ok x hx, bitLP14_ok x hx, bitLP15_ok x hx, bitLP16_ok x hx, bitLP17_ok x hx, bitLP18_ok x hx, bitLP19_ok x hx, bitLP20_ok x hx, bitLP21_ok x hx, bitLP22_ok x hx, bitLP23_ok x hx, bitLP24_ok x hx, bitLP25_ok x hx, bitLP26_ok x hx, bitLP27_ok x hx, bitLP28_ok x hx, bitLP29_ok x hx, bitLP30_ok x hx, bitLP31_ok x hx]

theorem ptAll_ok : ∀ x ∈ ptAll, ptOK5 NM x.1 x.2.1 x.2.2.1 x.2.2.2 = true := by
  intro x hx
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.mp hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [ptPW00_ok x hx, ptPW01_ok x hx, ptPW02_ok x hx, ptPW03_ok x hx, ptPW04_ok x hx, ptPW05_ok x hx, ptPW06_ok x hx, ptPW07_ok x hx, ptPW08_ok x hx, ptPW09_ok x hx, ptPW10_ok x hx, ptPW11_ok x hx, ptPW12_ok x hx, ptPW13_ok x hx, ptPW14_ok x hx, ptPW15_ok x hx, ptPW16_ok x hx, ptPW17_ok x hx, ptPW18_ok x hx, ptPW19_ok x hx]

end GridGen.Five.K5
