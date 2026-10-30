/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.BitData.LP00
import GridGen.Six.BitData.LP01
import GridGen.Six.BitData.LP02
import GridGen.Six.BitData.LP03
import GridGen.Six.BitData.LP04
import GridGen.Six.BitData.LP05
import GridGen.Six.BitData.LP06
import GridGen.Six.BitData.LP07
import GridGen.Six.BitData.LP08
import GridGen.Six.BitData.LP09
import GridGen.Six.BitData.LP10
import GridGen.Six.BitData.LP11
import GridGen.Six.BitData.LP12
import GridGen.Six.BitData.LP13
import GridGen.Six.BitData.LP14
import GridGen.Six.BitData.LP15
import GridGen.Six.BitData.LP16
import GridGen.Six.BitData.LP17
import GridGen.Six.BitData.LP18
import GridGen.Six.BitData.LP19
import GridGen.Six.BitData.PP00
import GridGen.Six.BitData.PP01
import GridGen.Six.BitData.PP02
import GridGen.Six.BitData.PP03
import GridGen.Six.BitData.PP04
import GridGen.Six.BitData.PP05
import GridGen.Six.BitData.PP06
import GridGen.Six.BitData.PW00
import GridGen.Six.BitData.PW01
import GridGen.Six.BitData.PW02
import GridGen.Six.BitData.PW03
import GridGen.Six.BitData.PW04
import GridGen.Six.BitData.PW05
import GridGen.Six.BitData.PW06
import GridGen.Six.BitData.PW07
import GridGen.Six.BitData.PW08
import GridGen.Six.BitData.PW09
import GridGen.Six.BitData.PW10

/-!
# Height six at `k = 6`: all state-bit certificates

The compact certificates (`lpAll`, 775), the pattern-aware ones (`ppAll`, 28) and the pointwise
classes (`pwAll`, 7768), one per reflection class of mismatch vectors outside `0` and the three
single-mismatch shapes (Codex's (OpenAI) split, `ai_research_notes/cx/h6k6/NOTE.md`).
-/

namespace GridGen.Six

def lpAll : List BCert6 := List.flatten [lp00, lp01, lp02, lp03, lp04, lp05, lp06, lp07, lp08, lp09, lp10, lp11, lp12, lp13, lp14, lp15, lp16, lp17, lp18, lp19]
def ppAll : List BCert6 := List.flatten [pp00, pp01, pp02, pp03, pp04, pp05, pp06]
def pwAll : List (List ℕ) := List.flatten [pw00, pw01, pw02, pw03, pw04, pw05, pw06, pw07, pw08, pw09, pw10]

theorem lpAll_ok : ∀ C ∈ lpAll, certOKc C = true := by
  intro C hC
  obtain ⟨l, hl, hC⟩ := List.mem_flatten.mp hC
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [lp00_ok C hC, lp01_ok C hC, lp02_ok C hC, lp03_ok C hC, lp04_ok C hC, lp05_ok C hC, lp06_ok C hC, lp07_ok C hC, lp08_ok C hC, lp09_ok C hC, lp10_ok C hC, lp11_ok C hC, lp12_ok C hC, lp13_ok C hC, lp14_ok C hC, lp15_ok C hC, lp16_ok C hC, lp17_ok C hC, lp18_ok C hC, lp19_ok C hC]

theorem ppAll_ok : ∀ C ∈ ppAll, certStatic C = true ∧ certOKpat C 0 13 = true ∧
    certOKpat C 13 13 = true ∧ certOKpat C 26 13 = true ∧ certOKpat C 39 13 = true := by
  intro C hC
  obtain ⟨l, hl, hC⟩ := List.mem_flatten.mp hC
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [pp00_ok C hC, pp01_ok C hC, pp02_ok C hC, pp03_ok C hC, pp04_ok C hC, pp05_ok C hC, pp06_ok C hC]

theorem pwAll_ok : ∀ m ∈ pwAll,
    ptChk NML (m.getD 0 0) (m.getD 1 0) (m.getD 2 0) (m.getD 3 0) (m.getD 4 0) = true := by
  intro m hm
  obtain ⟨l, hl, hm⟩ := List.mem_flatten.mp hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [List.all_eq_true.mp pw00_ok m hm, List.all_eq_true.mp pw01_ok m hm, List.all_eq_true.mp pw02_ok m hm, List.all_eq_true.mp pw03_ok m hm, List.all_eq_true.mp pw04_ok m hm, List.all_eq_true.mp pw05_ok m hm, List.all_eq_true.mp pw06_ok m hm, List.all_eq_true.mp pw07_ok m hm, List.all_eq_true.mp pw08_ok m hm, List.all_eq_true.mp pw09_ok m hm, List.all_eq_true.mp pw10_ok m hm]

end GridGen.Six
