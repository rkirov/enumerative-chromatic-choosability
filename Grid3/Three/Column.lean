import Grid3.Three.Sig

/-!
# Concrete columns

A column of the grid is three lists `Lc : Fin 3 → Finset ℕ` of three colours each. Its colours
carry *patterns* (`patOf`: bit `r` set iff the colour lies in row `r`, so patterns are `1..7`),
the pattern multiplicities pack into the column's type `packType Lc` (the checker's `mult`
packing), and `validType (packType Lc) = true`.

A concrete state is a proper colouring `s : Fin 3 → Fin C` of the column from its lists
(`IsCol`); its signature `sigC` mirrors the canonical `sigOf`, and the concrete law `lawC` is the
type's law at that signature. Everything a seam needs from a column is stated here, independently
of the seams to its left and right.
-/

open Finset

namespace Grid3.Three.Col

open Cert

variable (Lc : Fin 3 → Finset ℕ)

/-! ### Colours and patterns -/

/-- all colours of the column -/
def colours : Finset ℕ := Lc 0 ∪ Lc 1 ∪ Lc 2

theorem mem_colours (c : ℕ) : c ∈ colours Lc ↔ ∃ r, c ∈ Lc r := by
  unfold colours
  simp only [Finset.mem_union]
  constructor
  · rintro ((h | h) | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  · rintro ⟨r, hr⟩
    fin_cases r
    · exact Or.inl (Or.inl hr)
    · exact Or.inl (Or.inr hr)
    · exact Or.inr hr

/-- the pattern of a colour: bit `r` set iff the colour is in row `r` (patterns are `1..7`) -/
def patOf (c : ℕ) : ℕ :=
  (if c ∈ Lc 0 then 1 else 0) + (if c ∈ Lc 1 then 2 else 0) + (if c ∈ Lc 2 then 4 else 0)

theorem patOf_le (c : ℕ) : patOf Lc c ≤ 7 := by
  unfold patOf; split_ifs <;> omega

theorem patOf_testBit_zero (c : ℕ) : (patOf Lc c).testBit 0 = true ↔ c ∈ Lc 0 := by
  unfold patOf
  by_cases h0 : c ∈ Lc 0 <;> by_cases h1 : c ∈ Lc 1 <;> by_cases h2 : c ∈ Lc 2 <;>
    simp [h0, h1, h2] <;> decide

theorem patOf_testBit_one (c : ℕ) : (patOf Lc c).testBit 1 = true ↔ c ∈ Lc 1 := by
  unfold patOf
  by_cases h0 : c ∈ Lc 0 <;> by_cases h1 : c ∈ Lc 1 <;> by_cases h2 : c ∈ Lc 2 <;>
    simp [h0, h1, h2] <;> decide

theorem patOf_testBit_two (c : ℕ) : (patOf Lc c).testBit 2 = true ↔ c ∈ Lc 2 := by
  unfold patOf
  by_cases h0 : c ∈ Lc 0 <;> by_cases h1 : c ∈ Lc 1 <;> by_cases h2 : c ∈ Lc 2 <;>
    simp [h0, h1, h2] <;> decide

theorem patOf_testBit (c : ℕ) (r : Fin 3) : (patOf Lc c).testBit r.val = true ↔ c ∈ Lc r := by
  fin_cases r
  · exact patOf_testBit_zero Lc c
  · exact patOf_testBit_one Lc c
  · exact patOf_testBit_two Lc c

theorem patOf_pos (c : ℕ) (hc : c ∈ colours Lc) : 0 < patOf Lc c := by
  obtain ⟨r, hr⟩ := (mem_colours Lc c).1 hc
  have h := (patOf_testBit Lc c r).2 hr
  rcases Nat.eq_zero_or_pos (patOf Lc c) with h0 | h0
  · rw [h0, Nat.zero_testBit] at h; exact absurd h (by decide)
  · exact h0

theorem patOf_eq_zero (c : ℕ) (hc : c ∉ colours Lc) : patOf Lc c = 0 := by
  unfold patOf
  rw [if_neg, if_neg, if_neg]
  all_goals intro h; exact hc ((mem_colours Lc c).2 ⟨_, h⟩)

/-! ### The packed type -/

/-- number of colours of pattern index `p` (pattern `p + 1`) -/
def cnt (p : ℕ) : ℕ := ((colours Lc).filter fun c => patOf Lc c = p + 1).card

/-- the packed column type -/
def packType : ℕ := ∑ p ∈ range 7, cnt Lc p * 4 ^ p

theorem packType_eq : packType Lc = cnt Lc 0 + 4 * cnt Lc 1 + 16 * cnt Lc 2 + 64 * cnt Lc 3
    + 256 * cnt Lc 4 + 1024 * cnt Lc 5 + 4096 * cnt Lc 6 := by
  unfold packType
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- every pattern `1..7` has a row -/
theorem exists_row (p : ℕ) (hp : p < 7) : ∃ r : Fin 3, (p + 1).testBit r.val = true := by
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩

theorem cnt_le (h3 : ∀ r, (Lc r).card = 3) (p : ℕ) (hp : p < 7) : cnt Lc p ≤ 3 := by
  obtain ⟨r, hr⟩ := exists_row p hp
  rw [← h3 r]
  apply Finset.card_le_card
  intro c hc
  rw [Finset.mem_filter] at hc
  rw [← patOf_testBit Lc c r, hc.2]
  exact hr

/-- the base-4 digit of an explicit seven-digit sum -/
theorem digit4_of_sum (d : ℕ → ℕ) (hd : ∀ q < 7, d q < 4) (q : ℕ) (hq : q < 7) :
    (d 0 + 4 * d 1 + 16 * d 2 + 64 * d 3 + 256 * d 4 + 1024 * d 5 + 4096 * d 6) / 4 ^ q % 4
      = d q := by
  have h0 := hd 0 (by decide); have h1 := hd 1 (by decide); have h2 := hd 2 (by decide)
  have h3 := hd 3 (by decide); have h4 := hd 4 (by decide); have h5 := hd 5 (by decide)
  have h6 := hd 6 (by decide)
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp only [Nat.reducePow]; omega)

theorem mult_packType (h3 : ∀ r, (Lc r).card = 3) (p : ℕ) (hp : p < 7) :
    mult (packType Lc) p = cnt Lc p := by
  unfold mult
  rw [packType_eq]
  exact digit4_of_sum (cnt Lc) (fun q hq => by have := cnt_le Lc h3 q hq; omega) p hp

theorem packType_lt (h3 : ∀ r, (Lc r).card = 3) : packType Lc < 16384 := by
  rw [packType_eq]
  have := cnt_le Lc h3
  have h0 := this 0 (by decide); have h1 := this 1 (by decide); have h2 := this 2 (by decide)
  have h3' := this 3 (by decide); have h4 := this 4 (by decide); have h5 := this 5 (by decide)
  have h6 := this 6 (by decide)
  omega

/-- the colours of row `r` are exactly the colours whose pattern has bit `r` -/
theorem row_eq_filter (r : Fin 3) :
    Lc r = (colours Lc).filter fun c => (patOf Lc c).testBit r.val = true := by
  ext c
  rw [Finset.mem_filter, patOf_testBit]
  constructor
  · intro h; exact ⟨(mem_colours Lc c).2 ⟨r, h⟩, h⟩
  · intro h; exact h.2

/-- the row sum of the multiplicities over the patterns containing row `r` -/
theorem sum_cnt_row (h3 : ∀ r, (Lc r).card = 3) (r : Fin 3) :
    ∑ p ∈ (range 7).filter (fun p => (p + 1).testBit r.val = true), cnt Lc p = 3 := by
  have key : (Lc r).card = ∑ p ∈ (range 7).filter (fun p => (p + 1).testBit r.val = true), cnt Lc p := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun c => patOf Lc c - 1)
      (t := (range 7).filter (fun p => (p + 1).testBit r.val = true))]
    · apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mem_filter, Finset.mem_range] at hp
      unfold cnt
      congr 1
      ext c
      rw [Finset.mem_filter, Finset.mem_filter]
      constructor
      · intro ⟨hc, hpc⟩
        have hpos := patOf_pos Lc c ((mem_colours Lc c).2 ⟨r, hc⟩)
        exact ⟨(mem_colours Lc c).2 ⟨r, hc⟩, by omega⟩
      · intro ⟨hc, hpc⟩
        refine ⟨?_, by omega⟩
        rw [← patOf_testBit Lc c r, hpc]; exact hp.2
    · intro c hc
      rw [Finset.mem_coe] at hc
      have hpos := patOf_pos Lc c ((mem_colours Lc c).2 ⟨r, hc⟩)
      have hle := patOf_le Lc c
      show patOf Lc c - 1 ∈ ((range 7).filter (fun p => (p + 1).testBit r.val = true) : Set ℕ)
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [show patOf Lc c - 1 + 1 = patOf Lc c by omega]
      exact (patOf_testBit Lc c r).2 hc
  rw [← key]; exact h3 r

theorem row0_sum (h3 : ∀ r, (Lc r).card = 3) : cnt Lc 0 + cnt Lc 2 + cnt Lc 4 + cnt Lc 6 = 3 := by
  have := sum_cnt_row Lc h3 0
  simp +decide only [Finset.sum_filter, Finset.sum_range_succ, Finset.sum_range_zero,
    Fin.val_zero, if_true, if_false] at this
  omega

theorem row1_sum (h3 : ∀ r, (Lc r).card = 3) : cnt Lc 1 + cnt Lc 2 + cnt Lc 5 + cnt Lc 6 = 3 := by
  have := sum_cnt_row Lc h3 1
  simp +decide only [Finset.sum_filter, Finset.sum_range_succ, Finset.sum_range_zero,
    Fin.val_one, if_true, if_false] at this
  omega

theorem row2_sum (h3 : ∀ r, (Lc r).card = 3) : cnt Lc 3 + cnt Lc 4 + cnt Lc 5 + cnt Lc 6 = 3 := by
  have := sum_cnt_row Lc h3 2
  simp +decide only [Finset.sum_filter, Finset.sum_range_succ, Finset.sum_range_zero,
    Fin.val_two, if_true, if_false] at this
  omega

theorem validType_packType (h3 : ∀ r, (Lc r).card = 3) : validType (packType Lc) = true := by
  have hm := mult_packType Lc h3
  have m0 := hm 0 (by decide); have m1 := hm 1 (by decide); have m2 := hm 2 (by decide)
  have m3 := hm 3 (by decide); have m4 := hm 4 (by decide); have m5 := hm 5 (by decide)
  have m6 := hm 6 (by decide)
  have r0 := row0_sum Lc h3; have r1 := row1_sum Lc h3; have r2 := row2_sum Lc h3
  unfold validType rowSum3
  show ((List.foldl _ 0 [0, 1, 2, 3, 4, 5, 6] == 3) && (List.foldl _ 0 [0, 1, 2, 3, 4, 5, 6] == 3)
    && (List.foldl _ 0 [0, 1, 2, 3, 4, 5, 6] == 3)) = true
  simp +decide only [List.foldl, if_true, if_false, m0, m1, m2, m3, m4, m5, m6,
    Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨by simpa using r0, by simpa using r1⟩, by simpa using r2⟩

/-! ### Concrete states and the concrete law -/

variable {C : ℕ}

/-- a proper colouring of the column from its lists -/
def IsCol (s : Fin 3 → Fin C) : Prop := (∀ r, (s r).val ∈ Lc r) ∧ s 0 ≠ s 1 ∧ s 1 ≠ s 2

instance (s : Fin 3 → Fin C) : Decidable (IsCol Lc s) := by unfold IsCol; infer_instance

/-- the signature of a concrete state, mirroring `sigOf` -/
def sigC (s : Fin 3 → Fin C) : ℕ :=
  (((patOf Lc (s 0).val - 1) * 7 + (patOf Lc (s 1).val - 1)) * 7 + (patOf Lc (s 2).val - 1)) * 2
    + (if s 0 = s 2 then 1 else 0)

/-- the concrete law: the type's law at the state's signature -/
noncomputable def lawC (s : Fin 3 → Fin C) : ℝ :=
  if IsCol Lc s then lawSig (packType Lc) (sigC Lc s) else 0

theorem lawC_nonneg (s : Fin 3 → Fin C) : 0 ≤ lawC Lc s := by
  unfold lawC; split_ifs
  · exact lawSig_nonneg _ _
  · exact le_refl _

theorem lawC_of_not (s : Fin 3 → Fin C) (h : ¬ IsCol Lc s) : lawC Lc s = 0 := by
  unfold lawC; rw [if_neg h]

theorem isCol_of_lawC_pos (s : Fin 3 → Fin C) (h : 0 < lawC Lc s) : IsCol Lc s := by
  by_contra hn; rw [lawC_of_not Lc s hn] at h; exact lt_irrefl _ h

end Grid3.Three.Col
