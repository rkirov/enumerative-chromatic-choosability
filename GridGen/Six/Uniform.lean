/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.PatCount

/-!
# Height six: the uniform transfer at `k = 6`, by orbit counts

For each of the fifty-two canonical patterns `c` (`canons`, the proper partitions of
`GridGen/Six/PartData.lean`), the uniform successors of `c` — the proper colourings from the
lists `{0, …, 5} ∖ {cᵢ}` — are counted by the orbit of their pattern through the Möbius counts
of `GridGen/Six/PatCount.lean` (`uOK_all`, one kernel evaluation). The counts depend only on the
orbit of `c`, and they are the rows of the reduced transfer matrix `Vmat6` of
`ai_research_notes/cx/h6k6/cone6.json` (Codex, OpenAI; recomputed independently in
`H6_K6_REVIEW_2026-10-29.md` §1). A proper column in orbit `i` has weighted uniform successor
count `rowV6 i w` (`GU_six`).
-/

namespace GridGen.Six

open Finset


/-- The rows of the reduced uniform transfer at `k = 6`. -/
def VL : List (List ℕ) := data% "[[21,136,104,136,336,136,312,72,52,240,240,336,168,528,24,168,104,240,240,84,384,336,52,168,240,528,168,528,84,192,192,216],[17,127,94,111,312,111,306,70,43,237,228,276,138,510,30,195,98,261,240,99,426,312,55,174,264,558,138,510,99,210,216,228],[13,94,114,98,273,82,264,98,43,240,309,234,135,498,43,240,85,273,234,135,498,225,55,126,312,486,99,426,138,222,288,228],[17,111,98,127,312,111,306,82,55,264,261,312,174,558,30,198,86,237,237,96,420,276,43,138,237,510,138,510,99,216,210,228],[14,104,91,104,296,92,288,79,45,256,247,257,142,536,36,227,81,254,226,112,472,257,45,142,256,536,115,476,115,238,238,248],[17,111,82,111,276,127,306,69,43,237,225,312,138,510,30,195,98,240,261,99,426,312,43,138,237,510,174,558,96,210,210,228],[13,102,88,102,288,102,289,75,46,250,238,288,144,526,32,206,92,250,250,103,440,288,46,144,250,526,144,526,103,220,220,234],[9,70,98,82,237,69,225,126,55,300,312,234,138,504,55,300,73,237,234,138,504,198,43,102,273,432,96,420,174,270,288,228],[13,86,86,110,270,86,276,110,71,348,276,270,174,576,42,270,68,216,216,108,456,216,34,108,216,456,108,456,135,288,228,240],[10,79,80,88,256,79,250,100,58,325,252,256,144,538,45,284,72,227,227,114,476,224,36,112,227,472,112,472,142,298,238,248],[10,76,103,87,247,75,238,104,46,252,323,245,142,518,46,252,78,247,245,142,518,211,46,108,286,448,103,440,144,228,298,234],[14,92,78,104,257,104,288,78,45,256,245,296,142,536,36,227,81,226,254,112,472,257,36,115,224,476,142,536,112,238,234,248],[14,92,90,116,284,92,288,92,58,288,284,284,181,596,36,228,72,224,224,110,468,230,36,115,224,476,115,476,114,240,234,248],[11,85,83,93,268,85,263,84,48,269,259,268,149,557,38,238,76,236,236,117,490,238,38,119,236,493,119,493,119,248,245,256],[6,60,86,60,216,60,192,110,42,270,276,216,108,456,71,348,84,270,270,174,576,216,34,108,216,456,108,456,135,288,228,240],[7,65,80,66,227,65,206,100,45,284,252,227,114,476,58,325,81,256,256,144,538,224,36,112,227,472,112,472,142,298,238,248],[13,98,85,86,243,98,276,73,34,216,234,243,108,456,42,243,105,282,282,135,516,282,42,135,243,516,135,516,108,228,228,240],[10,87,91,79,254,80,250,79,36,227,247,226,112,472,45,256,94,296,256,142,536,256,45,142,256,536,114,474,115,238,238,248],[10,80,78,79,226,87,250,78,36,227,245,254,112,472,45,256,94,256,296,142,536,256,36,114,224,474,142,536,112,238,234,248],[7,66,90,64,224,66,206,92,36,228,284,224,110,468,58,288,90,284,284,181,596,228,36,115,224,476,115,476,114,240,234,248],[8,71,83,70,236,71,220,84,38,238,259,236,117,490,48,269,86,268,268,149,557,237,38,119,236,493,119,493,119,248,245,256],[14,104,75,92,257,104,288,66,36,224,211,257,115,476,36,224,94,256,256,114,474,296,45,142,256,536,142,536,112,234,238,248],[13,110,110,86,270,86,276,86,34,216,276,216,108,456,34,216,84,270,216,108,456,270,71,174,348,576,108,456,135,228,288,240],[14,116,84,92,284,92,288,68,36,224,216,230,115,476,36,224,90,284,228,115,476,284,58,181,288,596,115,476,114,234,240,248],[10,88,104,79,256,79,250,91,36,227,286,224,112,472,36,227,81,256,224,112,472,256,58,144,325,538,112,472,142,238,298,248],[11,93,81,85,268,85,263,72,38,236,224,238,119,493,38,236,86,268,237,119,493,268,48,149,269,557,119,493,119,245,248,256],[14,92,66,92,230,116,288,64,36,224,206,284,115,476,36,224,90,228,284,115,476,284,36,115,224,476,181,596,110,234,234,248],[11,85,71,85,238,93,263,70,38,236,220,268,119,493,38,236,86,237,268,119,493,268,38,119,236,493,149,557,117,245,245,256],[7,66,92,66,230,64,206,116,45,284,288,224,114,476,45,284,72,230,224,114,476,224,45,114,284,476,110,468,181,298,298,248],[8,70,74,72,238,70,220,90,48,298,228,238,120,496,48,298,76,238,238,120,496,234,38,117,238,490,117,490,149,309,248,256],[8,72,96,70,238,70,220,96,38,238,298,234,117,490,38,238,76,238,234,117,490,238,48,120,298,496,117,490,149,248,309,256],[9,76,76,76,248,76,234,76,40,248,234,248,124,512,40,248,80,248,248,124,512,248,40,124,248,512,124,512,124,256,256,265]]"

/-- The reduced uniform transfer at `k = 6`: `Vmat6 i j` is the number of uniform successors in
orbit `j` of a column in orbit `i`. -/
def Vmat6 (i j : Fin 32) : ℕ := (VL.getD i []).getD j 0

/-- The fifty-two canonical patterns (first-occurrence strings). -/
def canons : List T6 := data% "[(0,1,0,1,0,1),(0,1,0,1,0,5),(0,1,0,1,4,0),(0,1,0,1,4,1),(0,1,0,1,4,5),(0,1,0,3,0,1),(0,1,0,3,0,3),(0,1,0,3,0,5),(0,1,0,3,1,0),(0,1,0,3,1,3),(0,1,0,3,1,5),(0,1,0,3,4,0),(0,1,0,3,4,1),(0,1,0,3,4,3),(0,1,0,3,4,5),(0,1,2,0,1,0),(0,1,2,0,1,2),(0,1,2,0,1,5),(0,1,2,0,2,0),(0,1,2,0,2,1),(0,1,2,0,2,5),(0,1,2,0,4,0),(0,1,2,0,4,1),(0,1,2,0,4,2),(0,1,2,0,4,5),(0,1,2,1,0,1),(0,1,2,1,0,2),(0,1,2,1,0,5),(0,1,2,1,2,0),(0,1,2,1,2,1),(0,1,2,1,2,5),(0,1,2,1,4,0),(0,1,2,1,4,1),(0,1,2,1,4,2),(0,1,2,1,4,5),(0,1,2,3,0,1),(0,1,2,3,0,2),(0,1,2,3,0,3),(0,1,2,3,0,5),(0,1,2,3,1,0),(0,1,2,3,1,2),(0,1,2,3,1,3),(0,1,2,3,1,5),(0,1,2,3,2,0),(0,1,2,3,2,1),(0,1,2,3,2,3),(0,1,2,3,2,5),(0,1,2,3,4,0),(0,1,2,3,4,1),(0,1,2,3,4,2),(0,1,2,3,4,3),(0,1,2,3,4,5)]"

theorem canons_eq : canons = PART.filter properB := by decide +kernel

/-- The mask of `{0, …, 5} ∖ {x}`. -/
def umask (x : ℕ) : ℕ := 63 - 2 ^ x

theorem range_erase_mask {x : ℕ} (hx : x < 6) : (range 6).erase x = setOf (umask x) := by
  interval_cases x <;> decide

/-- The masks of the uniform successor lists of `c`. -/
def ums (c : T6) : List ℕ := [umask (r1 c), umask (r2 c), umask (r3 c), umask (r4 c), umask (r5 c),
  umask (r6 c)]

/-- The uniform check at one canonical pattern. -/
def uOK (c : T6) : Bool :=
  (List.range 32).all fun o => decide (cntO o (ums c) = ((VL.getD (orb c) []).getD o 0 : ℤ))

theorem uOK_0 : (canons.take 13).all uOK = true := by decide +kernel
theorem uOK_1 : ((canons.drop 13).take 13).all uOK = true := by decide +kernel
theorem uOK_2 : ((canons.drop 26).take 13).all uOK = true := by decide +kernel
theorem uOK_3 : (canons.drop 39).all uOK = true := by decide +kernel

theorem uOK_all : ∀ c ∈ canons, uOK c = true := by
  intro c hc
  rw [← List.take_append_drop 13 canons] at hc
  rcases List.mem_append.mp hc with h | h
  · exact List.all_eq_true.mp uOK_0 c h
  rw [← List.take_append_drop 13 (canons.drop 13)] at h
  rcases List.mem_append.mp h with h | h
  · exact List.all_eq_true.mp uOK_1 c h
  rw [List.drop_drop, ← List.take_append_drop 13 (canons.drop (13 + 13))] at h
  rcases List.mem_append.mp h with h | h
  · exact List.all_eq_true.mp uOK_2 c h
  · rw [List.drop_drop] at h; exact List.all_eq_true.mp uOK_3 c h

/-- On proper columns the canonical realisation is the first-occurrence string. -/
theorem canon_eq_foT {s : T6} (hs : Proper s) : canon s = foT s := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hs
  have e0 : fo s 0 = 0 := by unfold fo; simp
  have e1 : fo s 1 = 1 := by
    unfold fo; simp only [rowAt]; rw [if_neg p1, if_pos trivial]
  have e2 : fo s 2 = if r3 s = r1 s then 0 else 2 := by
    unfold fo; simp only [rowAt]
    by_cases h1 : r3 s = r1 s
    · rw [if_pos h1.symm, if_pos h1]
    · rw [if_neg (Ne.symm h1), if_neg h1, if_neg p2, if_pos trivial]
  have e3 : fo s 3 = if r4 s = r1 s then 0 else if r4 s = r2 s then 1 else 3 := by
    unfold fo; simp only [rowAt]
    by_cases h1 : r4 s = r1 s
    · rw [if_pos h1.symm, if_pos h1]
    rw [if_neg (Ne.symm h1), if_neg h1]
    by_cases h2 : r4 s = r2 s
    · rw [if_pos h2.symm, if_pos h2]
    · rw [if_neg (Ne.symm h2), if_neg h2, if_neg p3, if_pos trivial]
  have e4 : fo s 4 = if r5 s = r1 s then 0 else if r5 s = r2 s then 1 else if r5 s = r3 s then 2
      else 4 := by
    unfold fo; simp only [rowAt]
    by_cases h1 : r5 s = r1 s
    · rw [if_pos h1.symm, if_pos h1]
    rw [if_neg (Ne.symm h1), if_neg h1]
    by_cases h2 : r5 s = r2 s
    · rw [if_pos h2.symm, if_pos h2]
    rw [if_neg (Ne.symm h2), if_neg h2]
    by_cases h3 : r5 s = r3 s
    · rw [if_pos h3.symm, if_pos h3]
    · rw [if_neg (Ne.symm h3), if_neg h3, if_neg p4, if_pos trivial]
  have e5 : fo s 5 = if r6 s = r1 s then 0 else if r6 s = r2 s then 1 else if r6 s = r3 s then 2
      else if r6 s = r4 s then 3 else 5 := by
    unfold fo; simp only [rowAt]
    by_cases h1 : r6 s = r1 s
    · rw [if_pos h1.symm, if_pos h1]
    rw [if_neg (Ne.symm h1), if_neg h1]
    by_cases h2 : r6 s = r2 s
    · rw [if_pos h2.symm, if_pos h2]
    rw [if_neg (Ne.symm h2), if_neg h2]
    by_cases h3 : r6 s = r3 s
    · rw [if_pos h3.symm, if_pos h3]
    rw [if_neg (Ne.symm h3), if_neg h3]
    by_cases h4 : r6 s = r4 s
    · rw [if_pos h4.symm, if_pos h4]
    · rw [if_neg (Ne.symm h4), if_neg h4, if_neg p5]
  simp only [canon, foT, e0, e1, e2, e3, e4, e5]

/-- The canonical realisation of a proper column is one of the fifty-two canonical patterns. -/
theorem canon_mem {s : T6} (hs : Proper s) : canon s ∈ canons := by
  rw [canon_eq_foT hs, canons_eq, List.mem_filter]
  exact ⟨foT_mem_PART s, (properB_iff _).mpr ((proper_foT_iff s).mpr hs)⟩

/-- **A weighted count is a combination of orbit counts.** -/
theorem G_eq_sum_orb (w : Wt6) (A B C D E F : Finset ℕ) :
    G w A B C D E F = ∑ o, (((sts A B C D E F).filter (fun t => orb t = o)).card : ℝ) * w o := by
  unfold G gw
  rw [← Finset.sum_fiberwise (sts A B C D E F) orb (fun t => w (orb t))]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.mp ht).2]), Finset.sum_const,
    nsmul_eq_mul]

/-- The reduced uniform transfer, row `i`, applied to the weights. -/
noncomputable def rowV6 (i : Fin 32) (w : Wt6) : ℝ := ∑ j, (Vmat6 i j : ℝ) * w j

theorem rowsIn_canon_lt {s : T6} : r1 (canon s) < 6 ∧ r2 (canon s) < 6 ∧ r3 (canon s) < 6 ∧
    r4 (canon s) < 6 ∧ r5 (canon s) < 6 ∧ r6 (canon s) < 6 := by
  have h := rowsIn_canon (k := 6) le_rfl s
  simp only [RowsIn, Finset.mem_range] at h
  exact h

/-- **The uniform successors at `k = 6`**: a proper column in orbit `i` has weighted uniform
successor count `rowV6 i w`. -/
theorem GU_six (w : Wt6) {s : T6} (hs : Proper s) : GU 6 w s = rowV6 (orb s) w := by
  have hc := uOK_all _ (canon_mem hs)
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := rowsIn_canon_lt (s := s)
  unfold GU
  rw [range_erase_mask l1, range_erase_mask l2, range_erase_mask l3, range_erase_mask l4,
    range_erase_mask l5, range_erase_mask l6, G_eq_sum_orb, rowV6, orb_congr (samePat_canon hs)]
  refine Finset.sum_congr rfl fun o _ => ?_
  have h := card_orb_setOf (ums (canon s)) o
  have hv := List.all_eq_true.mp hc o (List.mem_range.mpr o.2)
  rw [decide_eq_true_eq] at hv
  rw [hv] at h
  have h' : (((sts (setOf (umask (r1 (canon s)))) (setOf (umask (r2 (canon s))))
      (setOf (umask (r3 (canon s)))) (setOf (umask (r4 (canon s)))) (setOf (umask (r5 (canon s))))
      (setOf (umask (r6 (canon s))))).filter (fun t => orb t = o)).card : ℝ)
      = (Vmat6 (orb (canon s)) o : ℝ) := by exact_mod_cast h
  rw [h']

end GridGen.Six
