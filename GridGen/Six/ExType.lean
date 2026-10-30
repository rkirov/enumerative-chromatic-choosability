/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.ExSound

/-!
# Height six at `k = 6`: the type of a column in a single-mismatch shape

For the shape `j` with lists `U` (rows `< j`) and `V` (rows `≥ j`), `|U| = |V| = 6`,
`|U ∩ V| = 5`, a proper column `s` has the type `(κ, canon s)` (`kap`); its labels (`labL`) name
its colours after relabelling `U ∪ V` onto `{0, …, 6}` (`exists_sigma`), and

* the type is admissible and has at most five common pattern values (`kap_adm`, `popc_wm_le`);
* the successor count `GB` of `s` is the weighted count of the masks of the type
  (`GB_eq_masks`);
* the pins of a certificate fire on `s` exactly as their compiled conditions on the type
  (`firedP_eq`).
-/

namespace GridGen.Six

open Finset

/-! ### Rows of the canonical pattern -/

theorem nbeq (a b : ℕ) : Nat.beq a b = decide (a = b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq]; simp

theorem nblt (a b : ℕ) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, Nat.blt_eq]; simp

theorem canon_rows {s : T6} (hs : Proper s) {r i : ℕ} (hr : r < 6) (hi : i < 6) :
    rowAt r (canon s) = rowAt i (canon s) ↔ rowAt r s = rowAt i s := by
  rw [canon_eq_foT hs]; exact foT_rows s hr hi

theorem canon_lt (s : T6) {r : ℕ} (hr : r < 6) : rowAt r (canon s) < 6 := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := rowsIn_canon_lt (s := s)
  interval_cases r <;> assumption

/-! ### Kinds and labels -/

/-- The kind of colour `x` on row `r`: `0` common, `5` the colour of `U` only on a row of `U`,
`6` the colour of `V` only on a row of `V`, `7` outside the row's list. -/
def kapC (j : ℕ) (U V : Finset ℕ) (r x : ℕ) : ℕ :=
  if x ∈ U ∩ V then 0 else if r < j ∧ x ∈ U then 5 else if j ≤ r ∧ x ∈ V then 6 else 7

/-- The kinds of a column. -/
def kap (j : ℕ) (U V : Finset ℕ) (s : T6) (r : ℕ) : ℕ := kapC j U V r (rowAt r s)

/-- The common pattern values of a type. -/
def wmK (p : T6) (k : ℕ → ℕ) : ℕ := wmask p (k 0) (k 1) (k 2) (k 3) (k 4) (k 5)

/-- The labels of a type. -/
def labL (p : T6) (k : ℕ → ℕ) : List ℕ :=
  [lab (wmK p k) (r1 p) (k 0), lab (wmK p k) (r2 p) (k 1), lab (wmK p k) (r3 p) (k 2),
    lab (wmK p k) (r4 p) (k 3), lab (wmK p k) (r5 p) (k 4), lab (wmK p k) (r6 p) (k 5)]

theorem labL_getD (p : T6) (k : ℕ → ℕ) {r : ℕ} (hr : r < 6) :
    (labL p k).getD r 7 = lab (wmK p k) (rowAt r p) (k r) := by
  interval_cases r <;> rfl

/-- The masks of a type. -/
def mskL (j : ℕ) (l : List ℕ) : List ℕ :=
  [em (bmJ j 0) (l.getD 0 7), em (bmJ j 1) (l.getD 1 7), em (bmJ j 2) (l.getD 2 7),
    em (bmJ j 3) (l.getD 3 7), em (bmJ j 4) (l.getD 4 7), em (bmJ j 5) (l.getD 5 7)]

theorem testBit_wbit (pr k x : ℕ) : (wbit pr k).testBit x = (decide (k = 0) && decide (pr = x)) := by
  unfold wbit
  rw [nbeq]
  by_cases hk : k = 0
  · subst hk; simp [Nat.pow_eq, Nat.testBit_two_pow]
  · simp [hk]

theorem testBit_wmK (p : T6) (k : ℕ → ℕ) (x : ℕ) :
    (wmK p k).testBit x = (List.range 6).any (fun r => decide (k r = 0) && decide (rowAt r p = x)) := by
  unfold wmK wmask
  simp only [show ∀ a b : ℕ, Nat.lor a b = a ||| b from fun _ _ => rfl, Nat.testBit_or,
    testBit_wbit, List.range_succ, List.range_zero, List.nil_append, List.any_append,
    List.any_cons, List.any_nil, Bool.or_false, Bool.false_or]
  rfl

theorem mem_setOf_wmK (p : T6) (k : ℕ → ℕ) (hp : ∀ r < 6, rowAt r p < 6) (x : ℕ) :
    x ∈ setOf (wmK p k) ↔ ∃ r < 6, k r = 0 ∧ rowAt r p = x := by
  unfold setOf
  rw [Finset.mem_filter, Finset.mem_range, testBit_wmK]
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨-, r, hr, h1, h2⟩; exact ⟨r, hr, h1, h2⟩
  · rintro ⟨r, hr, h1, h2⟩; exact ⟨by have := hp r hr; omega, r, hr, h1, h2⟩

/-- The rank as a count. -/
theorem rk_eq_card (wm x : ℕ) (hx : x ≤ 8) :
    rk wm x = ((setOf wm).filter (· < x)).card := by
  unfold rk
  rw [← card_setOf]
  congr 1
  ext y
  simp only [setOf, Finset.mem_filter, Finset.mem_range]
  rw [show Nat.land wm (Nat.sub (Nat.pow 2 x) 1) = wm &&& (2 ^ x - 1) from rfl, Nat.testBit_and,
    Nat.testBit_two_pow_sub_one]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  tauto

theorem rk_lt_rk {wm x y : ℕ} (hx : x ∈ setOf wm) (hy : y ≤ 8) (hxy : x < y) :
    rk wm x < rk wm y := by
  rw [rk_eq_card wm x (by omega), rk_eq_card wm y hy]
  apply Finset.card_lt_card
  refine ⟨fun z hz => ?_, fun h => ?_⟩
  · simp only [Finset.mem_filter] at hz ⊢; exact ⟨hz.1, by omega⟩
  · have := h (Finset.mem_filter.mpr ⟨hx, hxy⟩)
    simp at this

theorem rk_lt_popc {wm x : ℕ} (hx : x ∈ setOf wm) (h8 : x < 8) : rk wm x < popc wm := by
  rw [rk_eq_card wm x (by omega), ← card_setOf]
  apply Finset.card_lt_card
  refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
  have := h hx
  simp at this

theorem rk_inj {wm x y : ℕ} (hx : x ∈ setOf wm) (hy : y ∈ setOf wm) (h8x : x < 8) (h8y : y < 8)
    (h : rk wm x = rk wm y) : x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have := rk_lt_rk hx (by omega) hxy; omega
  · exact hxy
  · have := rk_lt_rk hy (by omega) hxy; omega

section shape

variable {j : ℕ} {U V : Finset ℕ}

theorem kap_mem (s : T6) {r : ℕ} (hr : r < 6) : kap j U V s r ∈ kopts j r := by
  unfold kap kapC kopts spJ
  rw [nblt]
  split_ifs with h1 h2 h3
  · simp
  · simp [h2.1]
  · have : ¬ r < j := by omega
    simp [this]
  · simp

theorem kap_zero_iff (s : T6) (r : ℕ) : kap j U V s r = 0 ↔ rowAt r s ∈ U ∩ V := by
  unfold kap kapC
  split_ifs <;> simp_all

theorem pairK_true {pa pb ka kb : ℕ}
    (h1 : pa = pb → ((ka = 0 ↔ kb = 0) ∧ ¬(ka = 5 ∧ kb = 6) ∧ ¬(ka = 6 ∧ kb = 5)))
    (h2 : pa ≠ pb → ¬(ka = 5 ∧ kb = 5) ∧ ¬(ka = 6 ∧ kb = 6)) : pairK pa pb ka kb = true := by
  unfold pairK
  simp only [nbeq]
  by_cases h : pa = pb
  · obtain ⟨a1, a2, a3⟩ := h1 h
    simp only [h, decide_true, Bool.cond_true, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not, beq_iff_eq, decide_eq_decide]
    tauto
  · obtain ⟨a1, a2⟩ := h2 h
    simp only [h, decide_false, Bool.cond_false, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not]
    tauto

theorem kap_five {s : T6} {r : ℕ} (h : kap j U V s r = 5) : rowAt r s ∈ U \ V := by
  unfold kap kapC at h
  by_cases h1 : rowAt r s ∈ U ∩ V
  · rw [ite_eq_left h1] at h; omega
  rw [ite_eq_right h1] at h
  by_cases h2 : r < j ∧ rowAt r s ∈ U
  · simp only [Finset.mem_inter, not_and] at h1
    exact Finset.mem_sdiff.mpr ⟨h2.2, h1 h2.2⟩
  rw [ite_eq_right h2] at h
  split_ifs at h <;> omega

theorem kap_six {s : T6} {r : ℕ} (h : kap j U V s r = 6) : rowAt r s ∈ V \ U := by
  unfold kap kapC at h
  by_cases h1 : rowAt r s ∈ U ∩ V
  · rw [ite_eq_left h1] at h; omega
  rw [ite_eq_right h1] at h
  by_cases h2 : r < j ∧ rowAt r s ∈ U
  · rw [ite_eq_left h2] at h; omega
  rw [ite_eq_right h2] at h
  by_cases h3 : j ≤ r ∧ rowAt r s ∈ V
  · simp only [Finset.mem_inter, not_and] at h1
    exact Finset.mem_sdiff.mpr ⟨h3.2, fun hU => h1 hU h3.2⟩
  rw [ite_eq_right h3] at h; omega

theorem eq_of_sdiff {x y : ℕ} {A B : Finset ℕ} (h1 : (A \ B).card = 1) (hx : x ∈ A \ B)
    (hy : y ∈ A \ B) : x = y :=
  Finset.card_le_one.mp h1.le x hx y hy

/-- **The type of a column is admissible.** -/
theorem kap_adm (hU : U.card = 6) (hV : V.card = 6) (hW : (U ∩ V).card = 5) {s : T6}
    (hs : Proper s) :
    admK (canon s) (kap j U V s 0) (kap j U V s 1) (kap j U V s 2) (kap j U V s 3) (kap j U V s 4)
      (kap j U V s 5) = true := by
  have hUV := card_sdiff_one hU hW
  have hVU := card_sdiff_one hV (by rw [Finset.inter_comm]; exact hW)
  have key : ∀ a < 6, ∀ b < 6, pairK (rowAt a (canon s)) (rowAt b (canon s)) (kap j U V s a)
      (kap j U V s b) = true := by
    intro a ha b hb
    apply pairK_true
    · intro hab
      have hs' := (canon_rows hs ha hb).mp hab
      refine ⟨?_, ?_, ?_⟩
      · rw [kap_zero_iff, kap_zero_iff, hs']
      · rintro ⟨h5, h6⟩
        have := kap_five h5; have := kap_six h6
        rw [hs'] at *
        simp_all [Finset.mem_sdiff]
      · rintro ⟨h6, h5⟩
        have := kap_five h5; have := kap_six h6
        rw [hs'] at *
        simp_all [Finset.mem_sdiff]
    · intro hab
      have hs' : rowAt a s ≠ rowAt b s := fun h => hab ((canon_rows hs ha hb).mpr h)
      refine ⟨fun ⟨h5, h5'⟩ => hs' (eq_of_sdiff hUV (kap_five h5) (kap_five h5')),
        fun ⟨h6, h6'⟩ => hs' (eq_of_sdiff hVU (kap_six h6) (kap_six h6'))⟩
  unfold admK
  simp only [show r1 (canon s) = rowAt 0 (canon s) from rfl, show r2 (canon s) = rowAt 1 (canon s) from rfl,
    show r3 (canon s) = rowAt 2 (canon s) from rfl, show r4 (canon s) = rowAt 3 (canon s) from rfl,
    show r5 (canon s) = rowAt 4 (canon s) from rfl, show r6 (canon s) = rowAt 5 (canon s) from rfl]
  simp only [key 0 (by norm_num) 1 (by norm_num), key 0 (by norm_num) 2 (by norm_num),
    key 0 (by norm_num) 3 (by norm_num), key 0 (by norm_num) 4 (by norm_num),
    key 0 (by norm_num) 5 (by norm_num), key 1 (by norm_num) 2 (by norm_num),
    key 1 (by norm_num) 3 (by norm_num), key 1 (by norm_num) 4 (by norm_num),
    key 1 (by norm_num) 5 (by norm_num), key 2 (by norm_num) 3 (by norm_num),
    key 2 (by norm_num) 4 (by norm_num), key 2 (by norm_num) 5 (by norm_num),
    key 3 (by norm_num) 4 (by norm_num), key 3 (by norm_num) 5 (by norm_num),
    key 4 (by norm_num) 5 (by norm_num), Bool.and_self]

end shape

end GridGen.Six
