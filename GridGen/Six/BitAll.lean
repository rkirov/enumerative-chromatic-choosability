/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.BitData.LP00
import GridGen.Six.BitData.LP01
import GridGen.Six.BitData.LP02
import GridGen.Six.BitData.PP00
import GridGen.Six.BitData.PP01
import GridGen.Six.BitData.PW

/-!
# Height six at `k = 6`: all state-bit certificates

The compact certificates (`lpAll`, 775), the pattern-aware ones (`ppAll`, 28) and the pointwise
classes (`pwAll`, 7768, checked at 496 dominating classes), one per reflection class of mismatch
vectors outside `0` and the three single-mismatch shapes (Codex's (OpenAI) split,
`ai_research_notes/cx/h6k6/NOTE.md`).
-/

namespace GridGen.Six

def lpAll : List BCert6 := lp00 ++ lp01 ++ lp02
def ppAll : List BCert6 := pp00 ++ pp01
def pwAll : List (List ℕ) := (pwG.map Prod.snd).flatten

theorem lpAll_ok : ∀ C ∈ lpAll, certOKc C = true := by
  have h : lpAll.all certOKc = true := by
    simp only [lpAll, List.all_append, lp00_ok, lp01_ok, lp02_ok, Bool.and_self]
  exact List.all_eq_true.mp h

theorem ppAll_ok : ∀ C ∈ ppAll, certStatic C = true ∧ certOKpat C 0 13 = true ∧
    certOKpat C 13 13 = true ∧ certOKpat C 26 13 = true ∧ certOKpat C 39 13 = true := by
  have h : ppAll.all ppOK = true := by
    simp only [ppAll, List.all_append, pp00_ok, pp01_ok, Bool.and_self]
  intro C hC
  have hC := List.all_eq_true.mp h C hC
  simpa only [ppOK, Bool.and_eq_true, and_assoc] using hC

theorem pwAll_ok : ∀ m ∈ pwAll, ∃ a : List ℕ,
    ptChk NML (a.getD 0 0) (a.getD 1 0) (a.getD 2 0) (a.getD 3 0) (a.getD 4 0) = true ∧
    domR (a.getD 0 0) (m.getD 0 0) = true ∧ domR (a.getD 1 0) (m.getD 1 0) = true ∧
    domR (a.getD 2 0) (m.getD 2 0) = true ∧ domR (a.getD 3 0) (m.getD 3 0) = true ∧
    domR (a.getD 4 0) (m.getD 4 0) = true := by
  intro m hm
  obtain ⟨l, hl, hm⟩ := List.mem_flatten.mp hm
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hl
  have h := List.all_eq_true.mp pwG_ok g hg
  simp only [pwgOK, Bool.and_eq_true, List.all_eq_true] at h
  have hd := h.2 m hm
  exact ⟨g.1, h.1, hd.1.1.1.1, hd.1.1.1.2, hd.1.1.2, hd.1.2, hd.2⟩

end GridGen.Six
