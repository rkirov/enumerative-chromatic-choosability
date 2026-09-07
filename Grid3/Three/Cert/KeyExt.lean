import Grid3.Three.Cert.Keys

/-!
# Every valid key extends to a valid maximal key

`exists_maximal`: for a valid packed key `(mL, mR, M)` there is a valid *maximal* key
`(mL, mR, M')` with `M ≤ M'` entrywise (`keyLE`). This is the key-level half of the maximal
extension step described in `Grid3/Three/README.md`: a concrete seam's partial block
matching gives a valid key; extending it to a maximal one only adds prohibitions, so the
certified coupling of the maximal key (`Complete.lean`) applies to the concrete seam.

The extension is greedy: while some intersecting pair `(p, q)` has a spare left colour and a spare
right colour, add one match there (`M + 4 ^ (7 p + q)`, which changes exactly that base-4 digit);
the total number of matches is bounded by `21`, so this terminates. Mathlib-free.
-/

namespace Grid3.Three.Cert

/-! ### Bumping one base-4 digit -/

theorem digit_add_pow_self (M i : Nat) (h : digit M i < 3) :
    digit (M + 4 ^ i) i = digit M i + 1 := by
  unfold digit at *
  have hA : 0 < 4 ^ i := Nat.pow_pos (by decide)
  rw [Nat.add_div_right M hA]
  omega

/-- no carry out of a digit below three -/
theorem div_add_pow_succ (M i : Nat) (h : digit M i < 3) :
    (M + 4 ^ i) / 4 ^ (i + 1) = M / 4 ^ (i + 1) := by
  unfold digit at h
  have hA : 0 < 4 ^ i := Nat.pow_pos (by decide)
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, Nat.add_div_right M hA]
  omega

theorem digit_add_pow_ne (M i j : Nat) (h : digit M i < 3) (hij : i ≠ j) :
    digit (M + 4 ^ i) j = digit M j := by
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · -- `i < j`: no carry out of digit `i`
    have hsplit : (4 : Nat) ^ j = 4 ^ (i + 1) * 4 ^ (j - i - 1) := by
      rw [← Nat.pow_add]; congr 1; omega
    unfold digit
    rw [hsplit, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, div_add_pow_succ M i h]
  · -- `j < i`: the added `4 ^ i` is a multiple of `4 * 4 ^ j`
    unfold digit
    have hj : 0 < 4 ^ j := Nat.pow_pos (by decide)
    have hsplit : (4 : Nat) ^ i = 4 ^ j * (4 * 4 ^ (i - j - 1)) := by
      rw [← Nat.pow_succ', ← Nat.pow_add]; congr 1; omega
    rw [hsplit, Nat.add_mul_div_left _ _ hj, Nat.add_mul_mod_self_left]

/-- the cell index of `(p, q)` -/
theorem cellIdx_inj {p q p' q' : Nat} (hq : q < 7) (hq' : q' < 7) :
    7 * p + q = 7 * p' + q' ↔ p = p' ∧ q = q' := by omega

theorem mcount_eq_digit_cell (M p q : Nat) : mcount M p q = digit M (7 * p + q) := rfl

/-- the effect of one added match on every cell -/
theorem mcount_bump (M p q p' q' : Nat) (hq : q < 7) (hq' : q' < 7) (h : mcount M p q < 3) :
    mcount (M + 4 ^ (7 * p + q)) p' q'
      = mcount M p' q' + (if p' = p ∧ q' = q then 1 else 0) := by
  simp only [mcount_eq_digit_cell] at h ⊢
  by_cases hpq : p' = p ∧ q' = q
  · obtain ⟨rfl, rfl⟩ := hpq
    rw [if_pos ⟨rfl, rfl⟩, digit_add_pow_self _ _ h]
  · rw [if_neg hpq, Nat.add_zero]
    apply digit_add_pow_ne _ _ _ h
    intro heq
    obtain ⟨h1, h2⟩ := (cellIdx_inj hq hq').1 heq
    exact hpq ⟨h1.symm, h2.symm⟩

theorem sumRow_bump (M p q p' : Nat) (hq : q < 7) (h : mcount M p q < 3) :
    sumRow (M + 4 ^ (7 * p + q)) p' = sumRow M p' + (if p' = p then 1 else 0) := by
  rw [sumRow_eq, sumRow_eq]
  rw [mcount_bump M p q p' 0 hq (by decide) h, mcount_bump M p q p' 1 hq (by decide) h,
    mcount_bump M p q p' 2 hq (by decide) h, mcount_bump M p q p' 3 hq (by decide) h,
    mcount_bump M p q p' 4 hq (by decide) h, mcount_bump M p q p' 5 hq (by decide) h,
    mcount_bump M p q p' 6 hq (by decide) h]
  by_cases hp : p' = p
  · subst hp
    rcases lt7 hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp; try omega)
  · simp [hp]

theorem sumCol_bump (M p q q' : Nat) (hp : p < 7) (hq : q < 7) (hq' : q' < 7) (h : mcount M p q < 3) :
    sumCol (M + 4 ^ (7 * p + q)) q' = sumCol M q' + (if q' = q then 1 else 0) := by
  rw [sumCol_eq, sumCol_eq]
  rw [mcount_bump M p q 0 q' hq, mcount_bump M p q 1 q' hq, mcount_bump M p q 2 q' hq,
    mcount_bump M p q 3 q' hq, mcount_bump M p q 4 q' hq, mcount_bump M p q 5 q' hq,
    mcount_bump M p q 6 q' hq] <;> try assumption
  by_cases hq' : q' = q
  · subst hq'
    rcases lt7 hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp; try omega)
  · simp [hq']

/-! ### Reading and building the key predicates -/

theorem validKey_of {mL mR M : Nat}
    (h1 : ∀ p < 7, ∀ q < 7, inter p q = false → mcount M p q = 0)
    (h2 : ∀ p < 7, sumRow M p ≤ mult mL p) (h3 : ∀ q < 7, sumCol M q ≤ mult mR q) :
    validKey mL mR M = true := by
  simp only [validKey, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨fun p hp q hq => ?_, h2⟩, h3⟩
  cases hi : inter p q
  · exact Or.inr (h1 p hp q hq hi)
  · exact Or.inl rfl

theorem keyMax_of {mL mR M : Nat} (hv : validKey mL mR M = true)
    (h : ∀ p < 7, ∀ q < 7, inter p q = true → sumRow M p < mult mL p → sumCol M q = mult mR q) :
    keyMax mL mR M = true := by
  simp only [keyMax, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq]
  intro p hp q hq
  cases hi : inter p q
  · exact Or.inl (Or.inl rfl)
  · by_cases hs : sumRow M p < mult mL p
    · exact Or.inr (h p hp q hq hi hs)
    · exact Or.inl (Or.inr (by have := validKey_row hv p hp; omega))

/-- a non-maximal key has an intersecting pair with spare colours on both sides -/
theorem keyMax_false {mL mR M : Nat} (hv : validKey mL mR M = true)
    (h : keyMax mL mR M = false) :
    ∃ p < 7, ∃ q < 7, inter p q = true ∧ sumRow M p < mult mL p ∧ sumCol M q < mult mR q := by
  apply Classical.byContradiction
  intro hne
  have hmax : keyMax mL mR M = true := keyMax_of hv fun p hp q hq hi hs => by
    have hc := validKey_col hv q hq
    apply Classical.byContradiction
    intro hc'
    exact hne ⟨p, hp, q, hq, hi, hs, Nat.lt_of_le_of_ne hc hc'⟩
  rw [h] at hmax
  exact Bool.false_ne_true hmax

/-! ### The greedy extension -/

/-- entrywise order on the `7 × 7` cells -/
def keyLE (M M' : Nat) : Prop := ∀ p < 7, ∀ q < 7, mcount M p q ≤ mcount M' p q

theorem keyLE_refl (M : Nat) : keyLE M M := fun _ _ _ _ => Nat.le_refl _
theorem keyLE_trans {M M' M'' : Nat} (h : keyLE M M') (h' : keyLE M' M'') : keyLE M M'' :=
  fun p hp q hq => Nat.le_trans (h p hp q hq) (h' p hp q hq)

/-- the total number of matches -/
def total (M : Nat) : Nat := (List.range 7).foldl (fun acc p => acc + sumRow M p) 0

theorem total_eq (M : Nat) : total M = sumRow M 0 + sumRow M 1 + sumRow M 2 + sumRow M 3
    + sumRow M 4 + sumRow M 5 + sumRow M 6 := by
  show List.foldl _ 0 [0, 1, 2, 3, 4, 5, 6] = _
  simp only [List.foldl]; omega

theorem total_le {mL mR M : Nat} (hv : validKey mL mR M = true) : total M ≤ 21 := by
  rw [total_eq]
  have := validKey_row hv
  have h0 := this 0 (by decide); have h1 := this 1 (by decide); have h2 := this 2 (by decide)
  have h3 := this 3 (by decide); have h4 := this 4 (by decide); have h5 := this 5 (by decide)
  have h6 := this 6 (by decide)
  have m0 := mult_lt mL 0; have m1 := mult_lt mL 1; have m2 := mult_lt mL 2
  have m3 := mult_lt mL 3; have m4 := mult_lt mL 4; have m5 := mult_lt mL 5
  have m6 := mult_lt mL 6
  omega

theorem pow49 : (16384 : Nat) ^ 7 = 4 ^ 49 := by decide

/-- adding a match at a cell below three keeps the matrix packed in `49` digits -/
theorem bump_lt (M i : Nat) (hi : i < 49) (hM : M < 4 ^ 49) (h : digit M i < 3) :
    M + 4 ^ i < 4 ^ 49 := by
  have hsplit : (4 : Nat) ^ 49 = 4 ^ (i + 1) * 4 ^ (49 - i - 1) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hpos : 0 < 4 ^ 49 := Nat.pow_pos (by decide)
  have h0 : (M + 4 ^ i) / 4 ^ 49 = 0 := by
    rw [hsplit, ← Nat.div_div_eq_div_mul, div_add_pow_succ M i h, Nat.div_div_eq_div_mul,
      ← hsplit]
    exact Nat.div_eq_of_lt hM
  have := (Nat.div_lt_iff_lt_mul hpos).1 (by rw [h0]; exact Nat.zero_lt_one)
  rwa [Nat.one_mul] at this

/-- one greedy step -/
theorem bump_step {mL mR M p q : Nat} (hp : p < 7) (hq : q < 7) (hM : M < 16384 ^ 7)
    (hv : validKey mL mR M = true) (hi : inter p q = true)
    (hs : sumRow M p < mult mL p) (hc : sumCol M q < mult mR q) :
    M + 4 ^ (7 * p + q) < 16384 ^ 7 ∧ validKey mL mR (M + 4 ^ (7 * p + q)) = true
      ∧ total (M + 4 ^ (7 * p + q)) = total M + 1 ∧ keyLE M (M + 4 ^ (7 * p + q)) := by
  have hlt3 : mcount M p q < 3 := by
    have := validKey_row hv p hp
    have := mult_lt mL p
    rw [sumRow_eq] at hs
    rcases lt7 hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hcell : ∀ p' q', q' < 7 → mcount (M + 4 ^ (7 * p + q)) p' q'
      = mcount M p' q' + (if p' = p ∧ q' = q then 1 else 0) :=
    fun p' q' hq' => mcount_bump M p q p' q' hq hq' hlt3
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pow49] at hM ⊢
    exact bump_lt M _ (by omega) hM hlt3
  · apply validKey_of
    · intro p' hp' q' hq' hi'
      rw [hcell p' q' hq']
      by_cases hpq : p' = p ∧ q' = q
      · obtain ⟨rfl, rfl⟩ := hpq
        rw [hi'] at hi; exact absurd hi (by decide)
      · rw [if_neg hpq, Nat.add_zero]
        exact validKey_inter hv p' hp' q' hq' hi'
    · intro p' hp'
      rw [sumRow_bump M p q p' hq hlt3]
      by_cases hp' : p' = p
      · subst hp'; rw [if_pos rfl]; omega
      · rw [if_neg hp', Nat.add_zero]; exact validKey_row hv p' (by assumption)
    · intro q' hq'
      rw [sumCol_bump M p q q' hp hq hq' hlt3]
      by_cases hq'' : q' = q
      · subst hq''; rw [if_pos rfl]; omega
      · rw [if_neg hq'', Nat.add_zero]; exact validKey_col hv q' hq'
  · rw [total_eq, total_eq]
    rw [sumRow_bump M p q 0 hq hlt3, sumRow_bump M p q 1 hq hlt3, sumRow_bump M p q 2 hq hlt3,
      sumRow_bump M p q 3 hq hlt3, sumRow_bump M p q 4 hq hlt3, sumRow_bump M p q 5 hq hlt3,
      sumRow_bump M p q 6 hq hlt3]
    rcases lt7 hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp; try omega)
  · intro p' hp' q' hq'
    rw [hcell p' q' hq']
    exact Nat.le_add_right _ _

theorem exists_maximal_aux (mL mR : Nat) : ∀ k M, 21 ≤ total M + k → M < 16384 ^ 7 →
    validKey mL mR M = true →
    ∃ M', M' < 16384 ^ 7 ∧ validKey mL mR M' = true ∧ keyMax mL mR M' = true ∧ keyLE M M'
  | 0, M, hk, hM, hv => by
    cases hmax : keyMax mL mR M
    · obtain ⟨p, hp, q, hq, hi, hs, hc⟩ := keyMax_false hv hmax
      obtain ⟨-, hv', ht', -⟩ := bump_step hp hq hM hv hi hs hc
      have := total_le hv'
      omega
    · exact ⟨M, hM, hv, hmax, keyLE_refl M⟩
  | k + 1, M, hk, hM, hv => by
    cases hmax : keyMax mL mR M
    · obtain ⟨p, hp, q, hq, hi, hs, hc⟩ := keyMax_false hv hmax
      obtain ⟨hM', hv', ht', hle⟩ := bump_step hp hq hM hv hi hs hc
      obtain ⟨M'', h1, h2, h3, h4⟩ := exists_maximal_aux mL mR k _ (by omega) hM' hv'
      exact ⟨M'', h1, h2, h3, keyLE_trans hle h4⟩
    · exact ⟨M, hM, hv, hmax, keyLE_refl M⟩

/-- **Maximal extension at the key level**: every valid key lies below a valid maximal key. -/
theorem exists_maximal (mL mR M : Nat) (hM : M < 16384 ^ 7) (hv : validKey mL mR M = true) :
    ∃ M', M' < 16384 ^ 7 ∧ validKey mL mR M' = true ∧ keyMax mL mR M' = true ∧ keyLE M M' :=
  exists_maximal_aux mL mR 21 M (by omega) hM hv

end Grid3.Three.Cert
