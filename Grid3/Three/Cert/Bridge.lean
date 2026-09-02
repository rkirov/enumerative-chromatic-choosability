import Mathlib
import Grid3.Three.Cert.Decode

/-!
# Reflection, part 2: real-valued couplings from certificate records

From the integer facts of `checkRecord_*_spec`, build the real law of a canonical column and the
real coupling of a canonical seam, indexed by packed states in `Fin SB`, and prove the per-seam
hypotheses consumed by the entropy capstone.
-/

open Finset

namespace Grid3.Three.Cert

-- never unfold the generated tables or the law lookup during elaboration
attribute [local irreducible] LAWTABLE TYPETABLE subTable typeIndex countOf cntOf colours

/-- `√17` as a real -/
noncomputable def s17 : ℝ := Real.sqrt 17
lemma s17_sq : s17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
lemma s17_pos : 0 < s17 := Real.sqrt_pos.mpr (by norm_num)
lemma s17_mul_self : s17 * s17 = 17 := by rw [← sq, s17_sq]

/-! ### Sign tests for `P + Q·√17` -/

/-- `negQ17 P Q = true` means `P + Q√17 < 0` -/
lemma negQ17_sound (P Q : Int) (h : negQ17 P Q = true) : (P : ℝ) + (Q : ℝ) * s17 < 0 := by
  unfold negQ17 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  have h17 := s17_mul_self
  have hs := s17_pos
  rcases h with (⟨hP, hQ⟩ | ⟨⟨hP, hQ⟩, hlt⟩) | ⟨⟨hP, hQ⟩, hlt⟩
  · have : (Q : ℝ) * s17 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hQ) hs.le
    have : (P : ℝ) < 0 := by exact_mod_cast hP
    linarith
  · have hP' : (P : ℝ) < 0 := by exact_mod_cast hP
    have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hlt' : (17 : ℝ) * Q * Q < P * P := by exact_mod_cast hlt
    have hpos : 0 ≤ (Q : ℝ) * s17 := by positivity
    by_contra hc
    push Not at hc
    have hle : -(P : ℝ) ≤ Q * s17 := by linarith
    have := mul_le_mul hle hle (by linarith) hpos
    nlinarith [h17]
  · have hP' : (0 : ℝ) ≤ P := by exact_mod_cast hP
    have hQ' : (Q : ℝ) < 0 := by exact_mod_cast hQ
    have hlt' : (P : ℝ) * P < 17 * Q * Q := by exact_mod_cast hlt
    have hpos : 0 ≤ -(Q : ℝ) * s17 := by nlinarith
    by_contra hc
    push Not at hc
    have hle : -(Q : ℝ) * s17 ≤ P := by linarith
    have := mul_le_mul hle hle hpos hP'
    nlinarith [h17]

/-- `nonnegQ17 P Q = true` means `P + Q√17 ≥ 0` -/
lemma nonnegQ17_sound (P Q : Int) (h : nonnegQ17 P Q = true) : 0 ≤ (P : ℝ) + (Q : ℝ) * s17 := by
  unfold nonnegQ17 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  rcases h with ⟨hneg, -⟩ | ⟨hP, hQ⟩
  · by_contra hlt
    push Not at hlt
    have h17 := s17_mul_self
    have hs := s17_pos
    have : negQ17 P Q = true := by
      unfold negQ17
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      by_cases hP : P < 0
      · by_cases hQ : Q ≤ 0
        · exact Or.inl (Or.inl ⟨hP, hQ⟩)
        · push Not at hQ
          refine Or.inl (Or.inr ⟨⟨hP, hQ⟩, ?_⟩)
          have hP' : (P : ℝ) < 0 := by exact_mod_cast hP
          have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
          have hlt2 : (Q : ℝ) * s17 < -P := by linarith
          have hpos : 0 ≤ (Q : ℝ) * s17 := by positivity
          have := mul_lt_mul'' hlt2 hlt2 hpos hpos
          have : (17 : ℝ) * Q * Q < P * P := by nlinarith [h17]
          exact_mod_cast this
      · push Not at hP
        have hP' : (0 : ℝ) ≤ P := by exact_mod_cast hP
        have hQ : Q < 0 := by
          by_contra hQ; push Not at hQ
          have : (0 : ℝ) ≤ Q := by exact_mod_cast hQ
          nlinarith
        refine Or.inr ⟨⟨hP, hQ⟩, ?_⟩
        have hQ' : (Q : ℝ) < 0 := by exact_mod_cast hQ
        have hlt2 : (P : ℝ) < -Q * s17 := by linarith
        have := mul_lt_mul'' hlt2 hlt2 hP' hP'
        have : (P : ℝ) * P < 17 * Q * Q := by nlinarith [h17]
        exact_mod_cast this
    rw [this] at hneg; exact absurd hneg (by decide)
  · rw [hP, hQ]; simp

/-! ### Real values of laws and entries -/

/-- the real law of a canonical column at a packed state -/
noncomputable def lawR (m : Nat) (pats : List Nat) (c : Fin SB) : ℝ :=
  if c.val ∈ stsOf pats then (lawE0 m pats c.val : ℝ) / 108000 + (lawE1 m c.val : ℝ) / 204000 * s17 else 0

/-- the real value of a `ℚ(√17)` entry `v0/108000 + v1·√17/204000` -/
noncomputable def entryVal (v0 : Nat) (v1 : Int) : ℝ := (v0 : ℝ) / 108000 + (v1 : ℝ) / 204000 * s17

lemma entryVal_eq (v0 : Nat) (v1 : Int) :
    entryVal v0 v1 = (((17 * v0 : Int) : ℝ) + ((9 * v1 : Int) : ℝ) * s17) / 1836000 := by
  unfold entryVal; push_cast; ring

lemma entryVal_nonneg (v0 : Nat) (v1 : Int) (h : nonnegQ17 (17 * v0) (9 * v1) = true) : 0 ≤ entryVal v0 v1 := by
  rw [entryVal_eq]
  have := nonnegQ17_sound _ _ h
  positivity

/-- the real law is nonnegative -/
lemma lawR_nonneg (m : Nat) (pats : List Nat) (c : Fin SB) : 0 ≤ lawR m pats c := by
  unfold lawR
  split
  · unfold lawE0 lawE1
    have hs := s17_pos
    have h17 := s17_mul_self
    split
    · split <;> nlinarith
    · simp only [Int.cast_zero, zero_div, zero_mul, add_zero]; positivity
  · exact le_refl 0

/-! ### The states of a column are distinct -/

lemma rowList_nodup (pats : List Nat) (r : Nat) : (rowList pats r).Nodup :=
  List.Nodup.filter _ (List.nodup_range)

lemma pack_inj {c0 c1 c2 d0 d1 d2 : Nat} (h0 : c0 < 32) (h1 : c1 < 32) (h2 : c2 < 32)
    (h0' : d0 < 32) (h1' : d1 < 32) (h2' : d2 < 32)
    (h : c0 * 1024 + c1 * 32 + c2 = d0 * 1024 + d1 * 32 + d2) : c0 = d0 ∧ c1 = d1 ∧ c2 = d2 := by omega

/-- the innermost loop of `states` -/
def inner2 (c0 c1 : Nat) (L2 : List Nat) : List Nat :=
  L2.flatMap fun c2 => if c2 == c1 then [] else [c0 * 1024 + c1 * 32 + c2]
/-- the middle loop of `states` -/
def inner1 (c0 : Nat) (L1 L2 : List Nat) : List Nat :=
  L1.flatMap fun c1 => if c1 == c0 then [] else inner2 c0 c1 L2

lemma states_eq (L0 L1 L2 : List Nat) : states L0 L1 L2 = L0.flatMap fun c0 => inner1 c0 L1 L2 := rfl

lemma mem_inner2 (c0 c1 : Nat) (L2 : List Nat) (x : Nat) :
    x ∈ inner2 c0 c1 L2 ↔ ∃ c2 ∈ L2, c2 ≠ c1 ∧ x = c0 * 1024 + c1 * 32 + c2 := by
  unfold inner2
  simp only [List.mem_flatMap, beq_iff_eq]
  constructor
  · rintro ⟨c2, hc2, hx⟩
    split at hx
    · simp at hx
    · exact ⟨c2, hc2, by assumption, List.mem_singleton.mp hx⟩
  · rintro ⟨c2, hc2, hne, rfl⟩
    exact ⟨c2, hc2, by rw [if_neg hne]; exact List.mem_singleton_self _⟩

lemma mem_inner1 (c0 : Nat) (L1 L2 : List Nat) (x : Nat) :
    x ∈ inner1 c0 L1 L2 ↔ ∃ c1 ∈ L1, c1 ≠ c0 ∧ ∃ c2 ∈ L2, c2 ≠ c1 ∧ x = c0 * 1024 + c1 * 32 + c2 := by
  unfold inner1
  simp only [List.mem_flatMap, beq_iff_eq]
  constructor
  · rintro ⟨c1, hc1, hx⟩
    split at hx
    · simp at hx
    · exact ⟨c1, hc1, by assumption, (mem_inner2 c0 c1 L2 x).mp hx⟩
  · rintro ⟨c1, hc1, hne, h2⟩
    exact ⟨c1, hc1, by rw [if_neg hne]; exact (mem_inner2 c0 c1 L2 x).mpr h2⟩

lemma mem_states (L0 L1 L2 : List Nat) (x : Nat) :
    x ∈ states L0 L1 L2 ↔ ∃ c0 ∈ L0, ∃ c1 ∈ L1, c1 ≠ c0 ∧ ∃ c2 ∈ L2, c2 ≠ c1 ∧ x = c0 * 1024 + c1 * 32 + c2 := by
  rw [states_eq, List.mem_flatMap]
  simp only [mem_inner1]

lemma inner2_nodup (c0 c1 : Nat) (L2 : List Nat) (n2 : L2.Nodup) (b2 : ∀ c ∈ L2, c < 32) :
    (inner2 c0 c1 L2).Nodup := by
  unfold inner2
  rw [List.nodup_flatMap]
  refine ⟨fun c2 _ => by split <;> simp, ?_⟩
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [Function.onFun]
  have hne : L2[i] ≠ L2[j] := fun h => absurd (n2.getElem_inj_iff.mp h) (Nat.ne_of_lt hij)
  rw [List.disjoint_left]
  intro x hx hx'
  split at hx
  · simp at hx
  · split at hx'
    · simp at hx'
    · rw [List.mem_singleton] at hx hx'
      subst hx
      exact hne (by omega)

lemma inner1_nodup (c0 : Nat) (L1 L2 : List Nat) (n1 : L1.Nodup) (n2 : L2.Nodup)
    (b1 : ∀ c ∈ L1, c < 32) (b2 : ∀ c ∈ L2, c < 32) : (inner1 c0 L1 L2).Nodup := by
  unfold inner1
  rw [List.nodup_flatMap]
  refine ⟨fun c1 _ => ?_, ?_⟩
  · split
    · exact List.nodup_nil
    · exact inner2_nodup c0 c1 L2 n2 b2
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [Function.onFun]
  have hne : L1[i] ≠ L1[j] := fun h => absurd (n1.getElem_inj_iff.mp h) (Nat.ne_of_lt hij)
  rw [List.disjoint_left]
  intro x hx hx'
  split at hx
  · simp at hx
  · split at hx'
    · simp at hx'
    · obtain ⟨c2, hc2, -, rfl⟩ := (mem_inner2 _ _ _ _).mp hx
      obtain ⟨d2, hd2, -, heq⟩ := (mem_inner2 _ _ _ _).mp hx'
      have := b1 _ (List.getElem_mem hi); have := b1 _ (List.getElem_mem hj)
      have := b2 c2 hc2; have := b2 d2 hd2
      exact hne (by omega)

lemma states_nodup (L0 L1 L2 : List Nat) (n0 : L0.Nodup) (n1 : L1.Nodup) (n2 : L2.Nodup)
    (b0 : ∀ c ∈ L0, c < 32) (b1 : ∀ c ∈ L1, c < 32) (b2 : ∀ c ∈ L2, c < 32) :
    (states L0 L1 L2).Nodup := by
  rw [states_eq, List.nodup_flatMap]
  refine ⟨fun c0 _ => inner1_nodup c0 L1 L2 n1 n2 b1 b2, ?_⟩
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [Function.onFun]
  have hne : L0[i] ≠ L0[j] := fun h => absurd (n0.getElem_inj_iff.mp h) (Nat.ne_of_lt hij)
  rw [List.disjoint_left]
  intro x hx hx'
  obtain ⟨c1, hc1, -, c2, hc2, -, rfl⟩ := (mem_inner1 _ _ _ _).mp hx
  obtain ⟨d1, hd1, -, d2, hd2, -, heq⟩ := (mem_inner1 _ _ _ _).mp hx'
  have := b0 _ (List.getElem_mem hi); have := b0 _ (List.getElem_mem hj)
  have := b1 c1 hc1; have := b1 d1 hd1; have := b2 c2 hc2; have := b2 d2 hd2
  exact hne (by omega)

lemma stsOf_nodup (pats : List Nat) (h32 : pats.length ≤ 32) : (stsOf pats).Nodup :=
  states_nodup _ _ _ (rowList_nodup pats 0) (rowList_nodup pats 1) (rowList_nodup pats 2)
    (fun c hc => by have := rowList_lt pats 0 c hc; omega)
    (fun c hc => by have := rowList_lt pats 1 c hc; omega)
    (fun c hc => by have := rowList_lt pats 2 c hc; omega)

-- from here on the state lists are opaque atoms
attribute [local irreducible] stsOf states rowList

/-! ### The coupling of a record at packed states -/

/-- a rational entry as a `ℚ(√17)` entry with zero irrational part -/
def toQ (e : EntR) : EntQ := (e.1, e.2.1, e.2.2.1, 0, e.2.2.2)

/-- the real coupling: sum of the entries whose (left, right) states are `(c, s)` -/
noncomputable def Xof (es : List EntQ) (sL sR : List Nat) (c s : Fin SB) : ℝ :=
  (es.map fun e => if sL.getD e.1 0 = c.val ∧ sR.getD e.2.1 0 = s.val then entryVal e.2.2.1 e.2.2.2.1 else 0).sum

lemma Xof_nonneg (es : List EntQ) (sL sR : List Nat) (hnn : ∀ e ∈ es, nonnegQ17 (17 * e.2.2.1) (9 * e.2.2.2.1) = true)
    (c s : Fin SB) : 0 ≤ Xof es sL sR c s := by
  unfold Xof
  apply List.sum_nonneg
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  split
  · exact entryVal_nonneg _ _ (hnn e he)
  · exact le_refl 0

/-- summing the coupling over the right state collapses the right condition -/
lemma sum_Xof_row (es : List EntQ) (sL sR : List Nat) (hR : ∀ e ∈ es, sR.getD e.2.1 0 < SB) (c : Fin SB) :
    ∑ s : Fin SB, Xof es sL sR c s
      = (es.map fun e => if sL.getD e.1 0 = c.val then entryVal e.2.2.1 e.2.2.2.1 else 0).sum := by
  unfold Xof
  induction es with
  | nil => simp
  | cons e es ih =>
    have hR' : ∀ e' ∈ es, sR.getD e'.2.1 0 < SB := fun e' he' => hR e' (List.mem_cons_of_mem e he')
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih hR']
    refine congrArg₂ (· + ·) ?_ rfl
    have hlt := hR e (List.mem_cons_self ..)
    rw [Finset.sum_eq_single ⟨sR.getD e.2.1 0, hlt⟩]
    · show (if sL.getD e.1 0 = c.val ∧ sR.getD e.2.1 0 = sR.getD e.2.1 0 then _ else (0 : ℝ)) = _
      simp only [eq_self_iff_true, and_true]
    · intro b _ hb
      rw [if_neg]
      rintro ⟨-, h2⟩
      exact hb (Fin.ext h2.symm)
    · intro h; exact absurd (Finset.mem_univ _) h

lemma sum_Xof_col (es : List EntQ) (sL sR : List Nat) (hL : ∀ e ∈ es, sL.getD e.1 0 < SB) (s : Fin SB) :
    ∑ c : Fin SB, Xof es sL sR c s
      = (es.map fun e => if sR.getD e.2.1 0 = s.val then entryVal e.2.2.1 e.2.2.2.1 else 0).sum := by
  unfold Xof
  induction es with
  | nil => simp
  | cons e es ih =>
    have hL' : ∀ e' ∈ es, sL.getD e'.1 0 < SB := fun e' he' => hL e' (List.mem_cons_of_mem e he')
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih hL']
    refine congrArg₂ (· + ·) ?_ rfl
    have hlt := hL e (List.mem_cons_self ..)
    rw [Finset.sum_eq_single ⟨sL.getD e.1 0, hlt⟩]
    · show (if sL.getD e.1 0 = sL.getD e.1 0 ∧ sR.getD e.2.1 0 = s.val then _ else (0 : ℝ)) = _
      simp only [eq_self_iff_true, true_and]
    · intro b _ hb
      rw [if_neg]
      rintro ⟨h1, -⟩
      exact hb (Fin.ext h1.symm)
    · intro h; exact absurd (Finset.mem_univ _) h

/-- the list sum of entry values over a key class, as the integer row sums -/
lemma sum_entryVal_key (es : List EntQ) (key : EntQ → Nat) (i : Nat) :
    (es.map fun e => if key e = i then entryVal e.2.2.1 e.2.2.2.1 else 0).sum
      = (sumR (fun e => if e.1 = i then e.2.2.1 else 0) (es.map fun e => (key e, e.2.1, e.2.2.1, e.2.2.2.2)) : ℝ) / 108000
        + (sumInt (fun e => if key e = i then e.2.2.2.1 else 0) es : ℝ) / 204000 * s17 := by
  induction es with
  | nil => simp [sumR, sumInt]
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons, sumR, sumInt, ih]
    by_cases h : key e = i
    · simp only [h, if_true]; unfold entryVal; push_cast; ring
    · simp only [h, if_false]; push_cast; ring

/-! ### Marginals of the coupling against the laws -/

/-- for a nodup state list, `getD` of a valid index equals `l[i]` iff the index is `i` -/
lemma getD_eq_iff (l : List Nat) (hnd : l.Nodup) (i j : Nat) (hi : i < l.length) (hj : j < l.length) :
    l.getD j 0 = l[i] ↔ j = i := by
  rw [getD_of_lt hj]
  exact hnd.getElem_inj_iff

lemma sumR_col_map (es : List EntQ) (j : Nat) :
    sumR (fun e => if e.1 = j then e.2.2.1 else 0) (es.map fun e => (e.2.1, e.2.1, e.2.2.1, e.2.2.2.2))
      = colSumR (es.map toR) j := by
  unfold colSumR
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.map_cons, sumR] at ih ⊢; rw [ih]; rfl

/-- row marginal: the coupling of a row sums to the law digits of that row -/
lemma sum_Xof_row_eq (es : List EntQ) (sL sR : List Nat) (hndL : sL.Nodup)
    (hL : ∀ e ∈ es, e.1 < sL.length) (hR : ∀ e ∈ es, e.2.1 < sR.length) (hSR : ∀ st ∈ sR, st < SB)
    (i : Nat) (hi : i < sL.length) (hc : sL[i] < SB) :
    ∑ s : Fin SB, Xof es sL sR ⟨sL[i], hc⟩ s
      = (rowSumR (es.map toR) i : ℝ) / 108000 + (sumInt (fun e => if e.1 = i then e.2.2.2.1 else 0) es : ℝ) / 204000 * s17 := by
  rw [sum_Xof_row es sL sR (fun e he => by rw [getD_of_lt (hR e he)]; exact hSR _ (List.getElem_mem _))]
  have hmap : (es.map fun e => if sL.getD e.1 0 = (⟨sL[i], hc⟩ : Fin SB).val then entryVal e.2.2.1 e.2.2.2.1 else 0)
      = es.map fun e => if e.1 = i then entryVal e.2.2.1 e.2.2.2.1 else 0 := by
    apply List.map_congr_left
    intro e he
    simp only
    have hiff := getD_eq_iff sL hndL i e.1 hi (hL e he)
    by_cases h : e.1 = i
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
  rw [hmap, sum_entryVal_key es (fun e => e.1) i]
  unfold rowSumR toR
  rfl

/-- column marginal -/
lemma sum_Xof_col_eq (es : List EntQ) (sL sR : List Nat) (hndR : sR.Nodup)
    (hL : ∀ e ∈ es, e.1 < sL.length) (hR : ∀ e ∈ es, e.2.1 < sR.length) (hSL : ∀ st ∈ sL, st < SB)
    (j : Nat) (hj : j < sR.length) (hs : sR[j] < SB) :
    ∑ c : Fin SB, Xof es sL sR c ⟨sR[j], hs⟩
      = (colSumR (es.map toR) j : ℝ) / 108000 + (sumInt (fun e => if e.2.1 = j then e.2.2.2.1 else 0) es : ℝ) / 204000 * s17 := by
  rw [sum_Xof_col es sL sR (fun e he => by rw [getD_of_lt (hL e he)]; exact hSL _ (List.getElem_mem _))]
  have hmap : (es.map fun e => if sR.getD e.2.1 0 = (⟨sR[j], hs⟩ : Fin SB).val then entryVal e.2.2.1 e.2.2.2.1 else 0)
      = es.map fun e => if e.2.1 = j then entryVal e.2.2.1 e.2.2.2.1 else 0 := by
    apply List.map_congr_left
    intro e he
    simp only
    have hiff := getD_eq_iff sR hndR j e.2.1 hj (hR e he)
    by_cases h : e.2.1 = j
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
  rw [hmap, sum_entryVal_key es (fun e => e.2.1) j, sumR_col_map]

/-- a state that is not in the column has zero row -/
lemma sum_Xof_row_zero (es : List EntQ) (sL sR : List Nat) (hL : ∀ e ∈ es, e.1 < sL.length)
    (hR : ∀ e ∈ es, e.2.1 < sR.length) (hSR : ∀ st ∈ sR, st < SB) (c : Fin SB) (hc : c.val ∉ sL) :
    ∑ s : Fin SB, Xof es sL sR c s = 0 := by
  rw [sum_Xof_row es sL sR (fun e he => by rw [getD_of_lt (hR e he)]; exact hSR _ (List.getElem_mem _))]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  rw [if_neg]
  intro h
  apply hc
  rw [← h, getD_of_lt (hL e he)]
  exact List.getElem_mem _

lemma sum_Xof_col_zero (es : List EntQ) (sL sR : List Nat) (hL : ∀ e ∈ es, e.1 < sL.length)
    (hR : ∀ e ∈ es, e.2.1 < sR.length) (hSL : ∀ st ∈ sL, st < SB) (s : Fin SB) (hs : s.val ∉ sR) :
    ∑ c : Fin SB, Xof es sL sR c s = 0 := by
  rw [sum_Xof_col es sL sR (fun e he => by rw [getD_of_lt (hL e he)]; exact hSL _ (List.getElem_mem _))]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  rw [if_neg]
  intro h
  apply hs
  rw [← h, getD_of_lt (hR e he)]
  exact List.getElem_mem _

/-- support: a positive coupling value sits on a compatible pair of column states -/
lemma Xof_pos_support (es : List EntQ) (sL sR : List Nat)
    (hnn : ∀ e ∈ es, nonnegQ17 (17 * e.2.2.1) (9 * e.2.2.2.1) = true)
    (hcomp : ∀ e ∈ es, compat (sL.getD e.1 0) (sR.getD e.2.1 0) = true)
    (hL : ∀ e ∈ es, e.1 < sL.length) (hR : ∀ e ∈ es, e.2.1 < sR.length)
    (c s : Fin SB) (hpos : 0 < Xof es sL sR c s) :
    compat c.val s.val = true ∧ c.val ∈ sL ∧ s.val ∈ sR := by
  unfold Xof at hpos
  by_contra hcon
  have hz : (es.map fun e => if sL.getD e.1 0 = c.val ∧ sR.getD e.2.1 0 = s.val
      then entryVal e.2.2.1 e.2.2.2.1 else 0).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply hcon
    refine ⟨by rw [← h1, ← h2]; exact hcomp e he, ?_, ?_⟩
    · rw [← h1, getD_of_lt (hL e he)]; exact List.getElem_mem _
    · rw [← h2, getD_of_lt (hR e he)]; exact List.getElem_mem _
  rw [hz] at hpos
  exact lt_irrefl _ hpos

/-! ### The kernel -/

/-- the transition kernel of a coupling: rows with zero law get a point mass -/
noncomputable def Kof (law : Fin SB → ℝ) (X : Fin SB → Fin SB → ℝ) (c s : Fin SB) : ℝ :=
  if 0 < law c then X c s / law c else if s = c then 1 else 0

lemma Kof_nonneg (law : Fin SB → ℝ) (X : Fin SB → Fin SB → ℝ) (hX : ∀ c s, 0 ≤ X c s) (c s : Fin SB) :
    0 ≤ Kof law X c s := by
  unfold Kof
  split
  · exact div_nonneg (hX c s) (le_of_lt (by assumption))
  · split <;> norm_num

lemma Kof_sum (law : Fin SB → ℝ) (X : Fin SB → Fin SB → ℝ) (hrow : ∀ c, ∑ s, X c s = law c) (c : Fin SB) :
    ∑ s, Kof law X c s = 1 := by
  unfold Kof
  by_cases h : 0 < law c
  · simp only [h, if_true]
    rw [← Finset.sum_div, hrow c, div_self (ne_of_gt h)]
  · simp only [h, if_false]
    rw [Finset.sum_ite_eq' Finset.univ c]
    simp

/-- marginal consistency: `∑_c law c · K c s = ∑_c X c s` when zero-law rows carry no mass -/
lemma Kof_step (law : Fin SB → ℝ) (X : Fin SB → Fin SB → ℝ) (hX : ∀ c s, 0 ≤ X c s)
    (hlaw : ∀ c, 0 ≤ law c) (hrow : ∀ c, ∑ s, X c s = law c) (s : Fin SB) :
    ∑ c, law c * Kof law X c s = ∑ c, X c s := by
  apply Finset.sum_congr rfl
  intro c _
  unfold Kof
  by_cases h : 0 < law c
  · simp only [h, if_true]; field_simp
  · simp only [h, if_false]
    have hl : law c = 0 := le_antisymm (not_lt.mp h) (hlaw c)
    have hz : X c s = 0 := by
      have := hrow c
      rw [hl] at this
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => hX c s)).mp this s (Finset.mem_univ _)
    rw [hl, hz]; simp

/-! ### The marginal package of a `ℚ(√17)` collision record -/

/-- the `v1` sum of a row, as an integer -/
def rowSum1 (es : List EntQ) (i : Nat) : Int := sumInt (fun e => if e.1 = i then e.2.2.2.1 else 0) es
def colSum1 (es : List EntQ) (j : Nat) : Int := sumInt (fun e => if e.2.1 = j then e.2.2.2.1 else 0) es

/-- from the integer marginal facts, the real coupling has the real laws as marginals -/
theorem Xof_marginals (mL mR : Nat) (pL pR : List Nat) (es : List EntQ)
    (h32L : pL.length ≤ 32) (h32R : pR.length ≤ 32)
    (hL : ∀ e ∈ es, e.1 < (stsOf pL).length) (hR : ∀ e ∈ es, e.2.1 < (stsOf pR).length)
    (hrow0 : ∀ i (hi : i < (stsOf pL).length), rowSumR (es.map toR) i = lawE0 mL pL (stsOf pL)[i])
    (hrow1 : ∀ i (hi : i < (stsOf pL).length), rowSum1 es i = lawE1 mL (stsOf pL)[i])
    (hcol0 : ∀ j (hj : j < (stsOf pR).length), colSumR (es.map toR) j = lawE0 mR pR (stsOf pR)[j])
    (hcol1 : ∀ j (hj : j < (stsOf pR).length), colSum1 es j = lawE1 mR (stsOf pR)[j]) :
    (∀ c, ∑ s, Xof es (stsOf pL) (stsOf pR) c s = lawR mL pL c)
      ∧ (∀ s, ∑ c, Xof es (stsOf pL) (stsOf pR) c s = lawR mR pR s) := by
  have hSL := states_lt_of_cols pL h32L
  have hSR := states_lt_of_cols pR h32R
  have hndL := stsOf_nodup pL h32L
  have hndR := stsOf_nodup pR h32R
  constructor
  · intro c
    by_cases hc : c.val ∈ stsOf pL
    · obtain ⟨i, hi, hci⟩ := List.getElem_of_mem hc
      have hc' : c = ⟨(stsOf pL)[i], hci ▸ c.isLt⟩ := Fin.ext hci.symm
      rw [hc', sum_Xof_row_eq es _ _ hndL hL hR hSR i hi, hrow0 i hi]
      have := hrow1 i hi; unfold rowSum1 at this; rw [this]
      unfold lawR; rw [if_pos (List.getElem_mem hi)]
    · rw [sum_Xof_row_zero es _ _ hL hR hSR c hc]
      unfold lawR; rw [if_neg hc]
  · intro s
    by_cases hs : s.val ∈ stsOf pR
    · obtain ⟨j, hj, hsj⟩ := List.getElem_of_mem hs
      have hs' : s = ⟨(stsOf pR)[j], hsj ▸ s.isLt⟩ := Fin.ext hsj.symm
      rw [hs', sum_Xof_col_eq es _ _ hndR hL hR hSL j hj, hcol0 j hj]
      have := hcol1 j hj; unfold colSum1 at this; rw [this]
      unfold lawR; rw [if_pos (List.getElem_mem hj)]
    · rw [sum_Xof_col_zero es _ _ hL hR hSL s hs]
      unfold lawR; rw [if_neg hs]

/-! ### Squares of the coupling: one entry per cell -/

/-- the cell predicate of an entry -/
def cellIs (sL sR : List Nat) (e : EntQ) (c s : Fin SB) : Prop := sL.getD e.1 0 = c.val ∧ sR.getD e.2.1 0 = s.val

instance (sL sR : List Nat) (e : EntQ) (c s : Fin SB) : Decidable (cellIs sL sR e c s) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- distinct entries occupy distinct cells (from distinct packed indices and injectivity of `getD`) -/
lemma cell_inj (sL sR : List Nat) (hndL : sL.Nodup) (hndR : sR.Nodup) (e e' : EntQ)
    (hL : e.1 < sL.length) (hL' : e'.1 < sL.length) (hR : e.2.1 < sR.length) (hR' : e'.2.1 < sR.length)
    (c s : Fin SB) (h : cellIs sL sR e c s) (h' : cellIs sL sR e' c s) : idxQ e = idxQ e' := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  rw [getD_of_lt hL] at h1; rw [getD_of_lt hL'] at h1'
  rw [getD_of_lt hR] at h2; rw [getD_of_lt hR'] at h2'
  have e1 : e.1 = e'.1 := hndL.getElem_inj_iff.mp (h1.trans h1'.symm)
  have e2 : e.2.1 = e'.2.1 := hndR.getElem_inj_iff.mp (h2.trans h2'.symm)
  unfold idxQ; rw [e1, e2]

/-- with at most one entry per cell, the square of a cell sum is the sum of squares -/
lemma sq_cell_sum (sL sR : List Nat) (hndL : sL.Nodup) (hndR : sR.Nodup) (g : EntQ → ℝ) :
    ∀ (es : List EntQ), (es.map idxQ).Nodup → (∀ e ∈ es, e.1 < sL.length ∧ e.2.1 < sR.length) →
      ∀ c s : Fin SB,
      ((es.map fun e => if cellIs sL sR e c s then g e else 0).sum) ^ 2
        = (es.map fun e => if cellIs sL sR e c s then g e ^ 2 else 0).sum := by
  intro es
  induction es with
  | nil => intro _ _ c s; simp
  | cons e es ih =>
    intro hnd hb c s
    have hnd' := (List.nodup_cons.mp hnd).2
    have hnot := (List.nodup_cons.mp hnd).1
    have hb' := fun e' he' => hb e' (List.mem_cons_of_mem e he')
    simp only [List.map_cons, List.sum_cons]
    by_cases hc : cellIs sL sR e c s
    · rw [if_pos hc, if_pos hc]
      have hz : (es.map fun e' => if cellIs sL sR e' c s then g e' else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx
        rw [if_neg]
        intro hc'
        apply hnot
        rw [cell_inj sL sR hndL hndR e e' (hb e (List.mem_cons_self ..)).1 (hb' e' he').1
          (hb e (List.mem_cons_self ..)).2 (hb' e' he').2 c s hc hc']
        exact List.mem_map.mpr ⟨e', he', rfl⟩
      have hz2 : (es.map fun e' => if cellIs sL sR e' c s then g e' ^ 2 else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx
        rw [if_neg]
        intro hc'
        apply hnot
        rw [cell_inj sL sR hndL hndR e e' (hb e (List.mem_cons_self ..)).1 (hb' e' he').1
          (hb e (List.mem_cons_self ..)).2 (hb' e' he').2 c s hc hc']
        exact List.mem_map.mpr ⟨e', he', rfl⟩
      rw [hz, hz2]; ring
    · rw [if_neg hc, if_neg hc, zero_add, zero_add]
      exact ih hnd' hb' c s

/-- summing a cell-indicator sum over all cells picks each entry exactly once -/
lemma sum_cells (sL sR : List Nat) (g : EntQ → ℝ) (es : List EntQ)
    (hL : ∀ e ∈ es, sL.getD e.1 0 < SB) (hR : ∀ e ∈ es, sR.getD e.2.1 0 < SB) :
    ∑ c : Fin SB, ∑ s : Fin SB, (es.map fun e => if cellIs sL sR e c s then g e else 0).sum
      = (es.map g).sum := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have hL' := fun e' he' => hL e' (List.mem_cons_of_mem e he')
    have hR' := fun e' he' => hR e' (List.mem_cons_of_mem e he')
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih hL' hR']
    refine congrArg₂ (· + ·) ?_ rfl
    have hl := hL e (List.mem_cons_self ..)
    have hr := hR e (List.mem_cons_self ..)
    rw [Finset.sum_eq_single ⟨sL.getD e.1 0, hl⟩]
    · rw [Finset.sum_eq_single ⟨sR.getD e.2.1 0, hr⟩]
      · show (if cellIs sL sR e ⟨sL.getD e.1 0, hl⟩ ⟨sR.getD e.2.1 0, hr⟩ then g e else 0) = g e
        rw [if_pos ⟨rfl, rfl⟩]
      · intro b _ hb
        show (if cellIs sL sR e ⟨sL.getD e.1 0, hl⟩ b then g e else 0) = 0
        rw [if_neg]; rintro ⟨-, h2⟩; exact hb (Fin.ext h2.symm)
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro b _ hb
      apply Finset.sum_eq_zero
      intro s _
      show (if cellIs sL sR e b s then g e else 0) = 0
      rw [if_neg]; rintro ⟨h1, -⟩; exact hb (Fin.ext h1.symm)
    · intro h; exact absurd (Finset.mem_univ _) h

/-! ### The collision sum -/

lemma sumInt_cast (f : EntQ → Int) : ∀ es : List EntQ, (sumInt f es : ℝ) = (es.map fun e => (f e : ℝ)).sum := by
  intro es; induction es with
  | nil => simp [sumInt]
  | cons e es ih => simp only [sumInt, List.map_cons, List.sum_cons, Int.cast_add, ih]

/-- a natural number as a packed state index (identity below `SB`) -/
def toFin (x : Nat) : Fin SB := ⟨x % SB, Nat.mod_lt _ (by decide)⟩
lemma toFin_val (x : Nat) (hx : x < SB) : (toFin x).val = x := Nat.mod_eq_of_lt hx

/-- `law c · K(c,s)² = X(c,s)²/law c` (both sides vanish on zero-law rows) -/
lemma lawK_sq (law : Fin SB → ℝ) (X : Fin SB → Fin SB → ℝ) (hX : ∀ c s, 0 ≤ X c s) (hlaw : ∀ c, 0 ≤ law c)
    (hrow : ∀ c, ∑ s, X c s = law c) (c s : Fin SB) :
    law c * (Kof law X c s) ^ 2 = X c s ^ 2 / law c := by
  unfold Kof
  by_cases h : 0 < law c
  · simp only [h, if_true]; field_simp
  · simp only [h, if_false]
    have hl : law c = 0 := le_antisymm (not_lt.mp h) (hlaw c)
    have hz : X c s = 0 := by
      have := hrow c
      rw [hl] at this
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => hX c s)).mp this s (Finset.mem_univ _)
    rw [hl, hz]; simp

/-- `Σ_c Σ_s law c · K(c,s)²` is the entry sum of `val²/law(row)` -/
lemma lawK_sq_sum (law : Fin SB → ℝ) (sL sR : List Nat) (hndL : sL.Nodup) (hndR : sR.Nodup)
    (hSL : ∀ st ∈ sL, st < SB) (hSR : ∀ st ∈ sR, st < SB)
    (es : List EntQ) (hnd : (es.map idxQ).Nodup)
    (hb : ∀ e ∈ es, e.1 < sL.length ∧ e.2.1 < sR.length)
    (hlaw : ∀ c, 0 ≤ law c)
    (hrow : ∀ c, ∑ s, Xof es sL sR c s = law c)
    (hnn : ∀ e ∈ es, nonnegQ17 (17 * e.2.2.1) (9 * e.2.2.2.1) = true) :
    ∑ c, ∑ s, law c * (Kof law (Xof es sL sR) c s) ^ 2
      = (es.map fun e => entryVal e.2.2.1 e.2.2.2.1 ^ 2 / law (toFin (sL.getD e.1 0))).sum := by
  have hX := Xof_nonneg es sL sR hnn
  have hgL : ∀ e ∈ es, sL.getD e.1 0 < SB := fun e he => by rw [getD_of_lt (hb e he).1]; exact hSL _ (List.getElem_mem _)
  have hgR : ∀ e ∈ es, sR.getD e.2.1 0 < SB := fun e he => by rw [getD_of_lt (hb e he).2]; exact hSR _ (List.getElem_mem _)
  have step1 : ∀ c s, law c * (Kof law (Xof es sL sR) c s) ^ 2
      = (es.map fun e => if cellIs sL sR e c s then entryVal e.2.2.1 e.2.2.2.1 ^ 2 / law (toFin (sL.getD e.1 0)) else 0).sum := by
    intro c s
    rw [lawK_sq law _ hX hlaw hrow c s]
    change ((es.map fun e => if cellIs sL sR e c s then entryVal e.2.2.1 e.2.2.2.1 else 0).sum) ^ 2 / law c = _
    rw [sq_cell_sum sL sR hndL hndR _ es hnd hb c s, div_eq_mul_inv, ← List.sum_map_mul_right]
    congr 1
    apply List.map_congr_left
    intro e he
    by_cases hc : cellIs sL sR e c s
    · rw [if_pos hc, if_pos hc, div_eq_mul_inv]
      have : toFin (sL.getD e.1 0) = c := Fin.ext (by rw [toFin_val _ (hgL e he)]; exact hc.1)
      rw [this]
    · rw [if_neg hc, if_neg hc, zero_mul]
  rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun s _ => step1 c s))]
  exact sum_cells sL sR _ es hgL hgR

/-! ### Per-entry algebra: `val²/law(row)` against `dqSem` -/

/-- the real Perron root `ρ = (5 + √17)/2` -/
noncomputable def rhoR : ℝ := (5 + s17) / 2

/-- the common denominator of the collision sum -/
def denOf (mL : Nat) (lc : Nat) : Nat := (if mL == UTYPE then 12 else lc) * XD * XD

lemma denOf_pos (mL lc : Nat) (hlc : 0 < lc) : 0 < denOf mL lc := by
  unfold denOf XD; split <;> positivity

lemma s17_pow_three : s17 ^ 3 = 17 * s17 := by rw [pow_succ, s17_sq]
lemma s17_pow_four : s17 ^ 4 = 289 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, s17_sq]; norm_num

/-- for an entry in a row of a non-uniform column -/
lemma entry_sq_div_law_nonU (mL : Nat) (pL : List Nat) (lc : Nat) (e : EntQ)
    (hU : (mL == UTYPE) = false) (hst : (stsOf pL).getD e.1 0 ∈ stsOf pL)
    (hdvd : cntOf mL pL ((stsOf pL).getD e.1 0) ∣ lc) (hlc : 0 < lc)
    (hSB : (stsOf pL).getD e.1 0 < SB) :
    entryVal e.2.2.1 e.2.2.2.1 ^ 2 / lawR mL pL (toFin ((stsOf pL).getD e.1 0))
      = (((dqSem mL pL lc e).1 : ℝ) + ((dqSem mL pL lc e).2 : ℝ) * s17) / denOf mL lc := by
  unfold lawR dqSem denOf
  rw [toFin_val _ hSB, if_pos hst]
  simp only [hU, Bool.false_eq_true, ↓reduceIte, lawE0, lawE1]
  set cnt := cntOf mL pL ((stsOf pL).getD e.1 0) with hcnt
  obtain ⟨q, hq⟩ := hdvd
  rcases Nat.eq_zero_or_pos cnt with h0 | hpos
  · rw [h0] at hq; omega
  have hlcq : (lc / cnt : Nat) = q := by rw [hq, Nat.mul_div_cancel_left _ hpos]
  have hdivI : ((lc : Int) / (cnt : Int)) = ((lc / cnt : Nat) : Int) := by norm_cast
  rw [hdivI, hlcq, entryVal_eq]
  have hcntR : (0 : ℝ) < cnt := by exact_mod_cast hpos
  have hqpos : 0 < q := Nat.pos_of_ne_zero (fun h => by rw [h, Nat.mul_zero] at hq; omega)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hqpos)
  have hqR : (lc : ℝ) = cnt * q := by exact_mod_cast hq
  have hXD : (XD : ℝ) = 1836000 := by unfold XD; norm_num
  push_cast
  rw [hqR, hXD]
  field_simp
  ring_nf
  simp only [s17_sq, s17_pow_three, s17_pow_four]
  ring

/-- for an entry in a row of the uniform column -/
lemma entry_sq_div_law_U (mL : Nat) (pL : List Nat) (lc : Nat) (e : EntQ)
    (hU : (mL == UTYPE) = true) (hst : (stsOf pL).getD e.1 0 ∈ stsOf pL)
    (hSB : (stsOf pL).getD e.1 0 < SB) :
    entryVal e.2.2.1 e.2.2.2.1 ^ 2 / lawR mL pL (toFin ((stsOf pL).getD e.1 0))
      = (((dqSem mL pL lc e).1 : ℝ) + ((dqSem mL pL lc e).2 : ℝ) * s17) / denOf mL lc := by
  unfold lawR dqSem denOf
  rw [toFin_val _ hSB, if_pos hst]
  simp only [hU, ↓reduceIte, lawE0, lawE1, entryVal_eq]
  have hXD : (XD : ℝ) = 1836000 := by unfold XD; norm_num
  have h17 := s17_sq
  have hs := s17_pos
  have hlt : s17 < 5 := by nlinarith
  by_cases ha : isABA ((stsOf pL).getD e.1 0) = true
  · simp only [ha, ↓reduceIte]
    push_cast
    rw [hXD]
    rw [div_eq_div_iff (by positivity) (by norm_num)]
    ring_nf
    simp only [s17_sq, s17_pow_three, s17_pow_four]
    ring
  · simp only [ha, ↓reduceIte, Bool.false_eq_true]
    push_cast
    rw [hXD]
    rw [div_eq_div_iff (ne_of_gt (by linarith)) (by norm_num)]
    ring_nf
    simp only [s17_sq, s17_pow_three, s17_pow_four]
    ring

/-- summing the per-entry identity -/
lemma sum_entry_sq_div_law (mL : Nat) (pL : List Nat) (lc : Nat) (es : List EntQ)
    (h : ∀ e ∈ es, entryVal e.2.2.1 e.2.2.2.1 ^ 2 / lawR mL pL (toFin ((stsOf pL).getD e.1 0))
      = (((dqSem mL pL lc e).1 : ℝ) + ((dqSem mL pL lc e).2 : ℝ) * s17) / denOf mL lc) :
    (es.map fun e => entryVal e.2.2.1 e.2.2.2.1 ^ 2 / lawR mL pL (toFin ((stsOf pL).getD e.1 0))).sum
      = ((sumInt (fun e => (dqSem mL pL lc e).1) es : ℝ) + (sumInt (fun e => (dqSem mL pL lc e).2) es : ℝ) * s17)
          / denOf mL lc := by
  induction es with
  | nil => simp [sumInt]
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons, sumInt, Int.cast_add]
    rw [h e (List.mem_cons_self ..), ih (fun e' he' => h e' (List.mem_cons_of_mem e he'))]
    ring

/-- the sign test gives `ρ · (q0 + q1√17)/den < 1` -/
lemma collision_lt_one (q0 q1 : Int) (den : Nat) (hden : 0 < den)
    (h : negQ17 (5 * q0 + 17 * q1 - 2 * den) (q0 + 5 * q1) = true) :
    rhoR * (((q0 : ℝ) + (q1 : ℝ) * s17) / den) < 1 := by
  have hs := negQ17_sound _ _ h
  push_cast at hs
  have hdenR : (0 : ℝ) < den := by exact_mod_cast hden
  have h17 := s17_mul_self
  rw [← mul_div_assoc, div_lt_one hdenR]
  unfold rhoR
  have hexp : (5 + s17) / 2 * ((q0 : ℝ) + (q1 : ℝ) * s17)
      = (5 * (q0 : ℝ) + 17 * (q1 : ℝ) + ((q0 : ℝ) + 5 * (q1 : ℝ)) * s17) / 2 := by
    linear_combination ((q1 : ℝ) / 2) * s17_sq
  rw [hexp]
  linarith

/-- the strong sign test gives `(18/17)·ρ · (q0 + q1√17)/den < 1` -/
lemma collision_strong_lt_one (q0 q1 : Int) (den : Nat) (hden : 0 < den)
    (h : negQ17 (18 * (5 * q0 + 17 * q1) - 34 * den) (18 * (q0 + 5 * q1)) = true) :
    (18 / 17) * rhoR * (((q0 : ℝ) + (q1 : ℝ) * s17) / den) < 1 := by
  have hs := negQ17_sound _ _ h
  push_cast at hs
  have hdenR : (0 : ℝ) < den := by exact_mod_cast hden
  rw [← mul_div_assoc, div_lt_one hdenR]
  unfold rhoR
  have hexp : 18 / 17 * ((5 + s17) / 2) * ((q0 : ℝ) + (q1 : ℝ) * s17)
      = (18 * (5 * (q0 : ℝ) + 17 * (q1 : ℝ)) + 18 * ((q0 : ℝ) + 5 * (q1 : ℝ)) * s17) / 34 := by
    linear_combination (9 * (q1 : ℝ) / 17) * s17_sq
  rw [hexp]
  linarith

/-! ### The seam package -/

/-- the per-seam properties consumed by the entropy capstone, at packed states -/
structure SeamOK (mL : Nat) (pL : List Nat) (mR : Nat) (pR : List Nat) (K : Fin SB → Fin SB → ℝ) : Prop where
  nonneg : ∀ c s, 0 ≤ K c s
  rowsum : ∀ c, ∑ s, K c s = 1
  step : ∀ s, ∑ c, lawR mL pL c * K c s = lawR mR pR s
  support : ∀ c s, 0 < lawR mL pL c → 0 < K c s → compat c.val s.val = true ∧ c.val ∈ stsOf pL ∧ s.val ∈ stsOf pR
  collision : (∑ c, ∑ s, lawR mL pL c * K c s ^ 2) * rhoR < 1

/-- a `ℚ(√17)` collision record yields a seam package (and the strong bound if the left column is uniform) -/
theorem bridge_one (mL mR M ne blob : Nat) (h : checkRecord 1 mL mR M ne blob = true) :
    let cols := colours mL mR M
    let pL := cols.map Prod.fst
    let pR := cols.map Prod.snd
    ∃ K, SeamOK mL pL mR pR K
      ∧ ((mL == UTYPE) = true → (18 / 17) * rhoR * (∑ c, ∑ s, lawR mL pL c * K c s ^ 2) < 1) := by
  intro cols pL pR
  obtain ⟨-, -, h32, hLn27, hRn27, -, -, hnd, hent, hrow0, hrow1, hcol0, hcol1, hcLf, -, hfin⟩ :=
    checkRecord_one_spec mL mR M ne blob h
  set es := entriesQ false ne blob with hes
  set lc := (stsOf pL).foldl (fun l st => Nat.lcm l (cntOf mL pL st)) 1 with hlc
  have hpL32 : pL.length ≤ 32 := by simpa [pL] using h32
  have hpR32 : pR.length ≤ 32 := by simpa [pR] using h32
  have hSL := states_lt_of_cols pL hpL32
  have hSR := states_lt_of_cols pR hpR32
  have hndL := stsOf_nodup pL hpL32
  have hndR := stsOf_nodup pR hpR32
  have hL : ∀ e ∈ es, e.1 < (stsOf pL).length := fun e he => (hent e he).1
  have hR : ∀ e ∈ es, e.2.1 < (stsOf pR).length := fun e he => (hent e he).2.1
  have hnn : ∀ e ∈ es, nonnegQ17 (17 * e.2.2.1) (9 * e.2.2.2.1) = true := fun e he => (hent e he).2.2.2.2.2
  have hcomp : ∀ e ∈ es, compat ((stsOf pL).getD e.1 0) ((stsOf pR).getD e.2.1 0) = true :=
    fun e he => (hent e he).2.2.2.2.1
  obtain ⟨hrowX, hcolX⟩ := Xof_marginals mL mR pL pR es hpL32 hpR32 hL hR hrow0 hrow1 hcol0 hcol1
  have hX := Xof_nonneg es (stsOf pL) (stsOf pR) hnn
  have hlawL := lawR_nonneg mL pL
  set X := Xof es (stsOf pL) (stsOf pR) with hXdef
  set law := lawR mL pL with hlawdef
  -- the collision sum
  have hsum : ∑ c, ∑ s, law c * (Kof law X c s) ^ 2
      = ((sumInt (fun e => (dqSem mL pL lc e).1) es : ℝ) + (sumInt (fun e => (dqSem mL pL lc e).2) es : ℝ) * s17)
          / denOf mL lc := by
    rw [lawK_sq_sum law (stsOf pL) (stsOf pR) hndL hndR hSL hSR es hnd (fun e he => ⟨hL e he, hR e he⟩) hlawL hrowX hnn]
    apply sum_entry_sq_div_law
    intro e he
    have hst : (stsOf pL).getD e.1 0 ∈ stsOf pL := by rw [getD_of_lt (hL e he)]; exact List.getElem_mem _
    have hSB : (stsOf pL).getD e.1 0 < SB := hSL _ hst
    by_cases hu : (mL == UTYPE) = true
    · exact entry_sq_div_law_U mL pL lc e hu hst hSB
    · have hu' : (mL == UTYPE) = false := by simpa using hu
      obtain ⟨-, -, hdvd, hlcpos⟩ := hcLf hu'
      exact entry_sq_div_law_nonU mL pL lc e hu' hst (hdvd _ hst) hlcpos hSB
  have hden : 0 < denOf mL lc := by
    by_cases hu : (mL == UTYPE) = true
    · unfold denOf XD; rw [hu]; simp
    · have hu' : (mL == UTYPE) = false := by simpa using hu
      exact denOf_pos mL lc (hcLf hu').2.2.2
  have hdenI : ((denOf mL lc : Nat) : Int) = ((if mL == UTYPE then 12 else lc : Nat) : Int) * (XD : Int) * (XD : Int) := by
    unfold denOf; push_cast; rfl
  refine ⟨Kof law X, ⟨Kof_nonneg law X hX, Kof_sum law X hrowX, fun s => ?_, fun c s hl hk => ?_, ?_⟩, fun hu => ?_⟩
  · rw [Kof_step law X hX hlawL hrowX s]; exact hcolX s
  · unfold Kof at hk
    rw [if_pos hl] at hk
    have hXpos : 0 < X c s := by
      by_contra hcon; push Not at hcon
      have : X c s = 0 := le_antisymm hcon (hX c s)
      rw [this, zero_div] at hk; exact lt_irrefl _ hk
    exact Xof_pos_support es (stsOf pL) (stsOf pR) hnn hcomp hL hR c s hXpos
  · rw [hsum, mul_comm]
    have := hfin.1
    rw [← hdenI] at this
    exact collision_lt_one _ _ _ hden this
  · rw [hsum]
    have := hfin.2 hu
    rw [← hdenI] at this
    exact collision_strong_lt_one _ _ _ hden this

/-! ### Rational collision records (format 0) -/

lemma map_toR_toQ (es : List EntR) : (es.map toQ).map toR = es := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.map_cons, ih]; rfl

lemma map_idxQ_toQ (es : List EntR) : (es.map toQ).map idxQ = es.map idxR := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.map_cons, ih]; rfl

lemma rowSum1_toQ (es : List EntR) (key : EntQ → Nat) (i : Nat) :
    sumInt (fun e => if key e = i then e.2.2.2.1 else 0) (es.map toQ) = 0 := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.map_cons, sumInt, ih]; unfold toQ; simp

lemma nonnegQ17_zero (P : Int) (hP : 0 ≤ P) : nonnegQ17 P 0 = true := by
  unfold nonnegQ17 negQ17
  by_cases h0 : P = 0
  · subst h0; decide
  · have hP' : ¬ P < 0 := not_lt.mpr hP
    simp [h0, hP']

/-- the rational collision inequality in reals -/
lemma collision_lt_one_rat (q den : Nat) (hden : 0 < den) (h1 : 5 * q < 2 * den)
    (h2 : 17 * q * q < (2 * den - 5 * q) * (2 * den - 5 * q)) :
    ((q : ℝ) / den) * rhoR < 1 := by
  have hdenR : (0 : ℝ) < den := by exact_mod_cast hden
  have h1R : (5 : ℝ) * q < 2 * den := by exact_mod_cast h1
  have hsub : ((2 * den - 5 * q : Nat) : ℝ) = 2 * den - 5 * q := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h2R : (17 : ℝ) * q * q < (2 * den - 5 * q) * (2 * den - 5 * q) := by
    have := h2; rw [← hsub]; exact_mod_cast this
  have hq : (0 : ℝ) ≤ q := by positivity
  have hs := s17_pos
  have h17 := s17_mul_self
  -- √17 q < 2 den − 5 q
  have key : s17 * q < 2 * den - 5 * q := by
    by_contra hc; push Not at hc
    have hnn : 0 ≤ s17 * (q : ℝ) := by positivity
    have := mul_le_mul hc hc (by linarith) hnn
    nlinarith
  unfold rhoR
  rw [div_mul_eq_mul_div, div_lt_one hdenR]
  nlinarith

/-- the increments of a rational entry (non-uniform left column): no irrational part -/
lemma dqSem_toQ_snd (mL : Nat) (pL : List Nat) (lc : Nat) (hLU : (mL == UTYPE) = false) (e0 : EntR) :
    (dqSem mL pL lc (toQ e0)).2 = 0 := by
  unfold dqSem toQ
  rw [if_neg (by rw [hLU]; decide)]
  dsimp only
  generalize cntOf mL pL _ = cnt
  simp only [Int.mul_zero]

lemma dqSem_toQ_fst (mL : Nat) (pL : List Nat) (lc : Nat) (hLU : (mL == UTYPE) = false) (e0 : EntR) :
    (dqSem mL pL lc (toQ e0)).1
      = ((108 * (lc / cntOf mL pL ((stsOf pL).getD e0.1 0)) * (289 * e0.2.2.1 * e0.2.2.1) : Nat) : Int) := by
  unfold dqSem toQ
  rw [if_neg (by rw [hLU]; decide)]
  dsimp only
  generalize cntOf mL pL _ = cnt
  generalize e0.2.2.1 = v
  have hdiv : ((lc : Int) / (cnt : Int)) = ((lc / cnt : Nat) : Int) := by norm_cast
  rw [hdiv]
  push_cast
  ring

/-- a rational collision record yields a seam package -/
theorem bridge_zero (mL mR M ne blob : Nat) (h : checkRecord 0 mL mR M ne blob = true) :
    let cols := colours mL mR M
    let pL := cols.map Prod.fst
    let pR := cols.map Prod.snd
    ∃ K, SeamOK mL pL mR pR K := by
  intro cols pL pR
  obtain ⟨-, -, h32, hLn27, hRn27, hLU, hRU, -, -, hnd0, hent0, hrow, hcol, hs108, -, hr108, -, hdvd, hlcpos, hq⟩ :=
    checkRecord_zero_spec mL mR M ne blob h
  set es0 := entriesR false ne blob with hes0
  set lc := (stsOf pL).foldl (fun l st => Nat.lcm l (cntOf mL pL st)) 1 with hlc
  set es := es0.map toQ with hes
  have hpL32 : pL.length ≤ 32 := by simpa [pL] using h32
  have hpR32 : pR.length ≤ 32 := by simpa [pR] using h32
  have hSL := states_lt_of_cols pL hpL32
  have hSR := states_lt_of_cols pR hpR32
  have hndL := stsOf_nodup pL hpL32
  have hndR := stsOf_nodup pR hpR32
  have hmem : ∀ e ∈ es, ∃ e0 ∈ es0, e = toQ e0 := fun e he => by
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he; exact ⟨e0, he0, rfl⟩
  have hL : ∀ e ∈ es, e.1 < (stsOf pL).length := fun e he => by
    obtain ⟨e0, he0, rfl⟩ := hmem e he; exact (hent0 e0 he0).1
  have hR : ∀ e ∈ es, e.2.1 < (stsOf pR).length := fun e he => by
    obtain ⟨e0, he0, rfl⟩ := hmem e he; exact (hent0 e0 he0).2.1
  have hnn : ∀ e ∈ es, nonnegQ17 (17 * e.2.2.1) (9 * e.2.2.2.1) = true := fun e he => by
    obtain ⟨e0, he0, rfl⟩ := hmem e he
    show nonnegQ17 (17 * e0.2.2.1) (9 * 0) = true
    rw [Int.mul_zero]; exact nonnegQ17_zero _ (by positivity)
  have hcomp : ∀ e ∈ es, compat ((stsOf pL).getD e.1 0) ((stsOf pR).getD e.2.1 0) = true := fun e he => by
    obtain ⟨e0, he0, rfl⟩ := hmem e he; exact (hent0 e0 he0).2.2.2
  have hnd : (es.map idxQ).Nodup := by rw [hes, map_idxQ_toQ]; exact hnd0
  have hrow0 : ∀ i (hi : i < (stsOf pL).length), rowSumR (es.map toR) i = lawE0 mL pL (stsOf pL)[i] := by
    intro i hi; rw [hes, map_toR_toQ, hrow i hi]; unfold lawE0; rw [hLU]; rfl
  have hrow1 : ∀ i (hi : i < (stsOf pL).length), rowSum1 es i = lawE1 mL (stsOf pL)[i] := by
    intro i hi; unfold rowSum1; rw [hes, rowSum1_toQ]; unfold lawE1; rw [hLU]; rfl
  have hcol0 : ∀ j (hj : j < (stsOf pR).length), colSumR (es.map toR) j = lawE0 mR pR (stsOf pR)[j] := by
    intro j hj; rw [hes, map_toR_toQ, hcol j hj]; unfold lawE0; rw [hRU]; rfl
  have hcol1 : ∀ j (hj : j < (stsOf pR).length), colSum1 es j = lawE1 mR (stsOf pR)[j] := by
    intro j hj; unfold colSum1; rw [hes, rowSum1_toQ]; unfold lawE1; rw [hRU]; rfl
  obtain ⟨hrowX, hcolX⟩ := Xof_marginals mL mR pL pR es hpL32 hpR32 hL hR hrow0 hrow1 hcol0 hcol1
  have hX := Xof_nonneg es (stsOf pL) (stsOf pR) hnn
  have hlawL := lawR_nonneg mL pL
  set X := Xof es (stsOf pL) (stsOf pR) with hXdef
  set law := lawR mL pL with hlawdef
  -- the collision sum, rational form
  have hsum : ∑ c, ∑ s, law c * (Kof law X c s) ^ 2
      = ((sumInt (fun e => (dqSem mL pL lc e).1) es : ℝ) + (sumInt (fun e => (dqSem mL pL lc e).2) es : ℝ) * s17)
          / denOf mL lc := by
    rw [lawK_sq_sum law (stsOf pL) (stsOf pR) hndL hndR hSL hSR es hnd (fun e he => ⟨hL e he, hR e he⟩) hlawL hrowX hnn]
    apply sum_entry_sq_div_law
    intro e he
    have hst : (stsOf pL).getD e.1 0 ∈ stsOf pL := by rw [getD_of_lt (hL e he)]; exact List.getElem_mem _
    exact entry_sq_div_law_nonU mL pL lc e hLU hst (hdvd _ hst) hlcpos (hSL _ hst)
  have hq1 : sumInt (fun e => (dqSem mL pL lc e).2) es = 0 := by
    rw [hes]
    have : ∀ l : List EntR, sumInt (fun e => (dqSem mL pL lc e).2) (l.map toQ) = 0 := by
      intro l; induction l with
      | nil => rfl
      | cons e0 l ih => simp only [List.map_cons, sumInt, ih, Int.add_zero, dqSem_toQ_snd mL pL lc hLU e0]
    exact this es0
  have hq0 : (sumInt (fun e => (dqSem mL pL lc e).1) es : ℝ)
      = (sumR (fun e => 108 * (lc / cntOf mL pL ((stsOf pL).getD e.1 0)) * (289 * e.2.2.1 * e.2.2.1)) es0 : ℝ) := by
    rw [hes]
    have : ∀ l : List EntR, sumInt (fun e => (dqSem mL pL lc e).1) (l.map toQ)
        = ((sumR (fun e => 108 * (lc / cntOf mL pL ((stsOf pL).getD e.1 0)) * (289 * e.2.2.1 * e.2.2.1)) l : Nat) : Int) := by
      intro l; induction l with
      | nil => rfl
      | cons e0 l ih =>
        simp only [List.map_cons, sumInt, sumR, ih, dqSem_toQ_fst mL pL lc hLU e0]
        push_cast; ring
    rw [this es0]; exact Int.cast_natCast _
  have hdenR : denOf mL lc = lc * XD * XD := by unfold denOf; rw [hLU]; rfl
  refine ⟨Kof law X, ⟨Kof_nonneg law X hX, Kof_sum law X hrowX, fun s => ?_, fun c s hl hk => ?_, ?_⟩⟩
  · rw [Kof_step law X hX hlawL hrowX s]; exact hcolX s
  · unfold Kof at hk
    rw [if_pos hl] at hk
    have hXpos : 0 < X c s := by
      by_contra hcon; push Not at hcon
      have : X c s = 0 := le_antisymm hcon (hX c s)
      rw [this, zero_div] at hk; exact lt_irrefl _ hk
    exact Xof_pos_support es (stsOf pL) (stsOf pR) hnn hcomp hL hR c s hXpos
  · rw [hsum, hq1, hq0, hdenR]
    simp only [Int.cast_zero, zero_mul, add_zero]
    have hd : 0 < lc * XD * XD := by unfold XD; positivity
    have := collision_lt_one_rat _ _ hd hq.1 hq.2
    push_cast at this ⊢
    exact this

end Grid3.Three.Cert
