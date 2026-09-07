import Grid3.Three.Cert.KeysCore

/-!
# Completeness of the seam-key enumeration

`enumKeys_complete`: every packed key `(mL, mR, M)` with `M < 16384 ^ 7` that is valid
(`validKey`) and maximal (`keyMax`) occurs in `enumKeys mL mR`. The proof follows the enumerator
row by row (`enumRows_complete`), keeping the base-8 residual and the dead mask in closed form
(`resOf`, `dpre`), with the two bitwise tests reduced to `Nat.testBit` facts (`land_G8_eq`,
`land_eq_zero`). The row table `rowVecsLit` is identified with the structural generator `comps`
by a kernel check (`rowVecsLit_eq`), and `comps_complete` is the structural completeness of the
generator. Mathlib-free.
-/

namespace Grid3.Three.Cert

/-! ### Digits -/

theorem digit_lt (r q : Nat) : digit r q < 4 := Nat.mod_lt _ (by decide)
theorem digit8_lt (t q : Nat) : digit8 t q < 8 := Nat.mod_lt _ (by decide)
theorem rowOf_lt (M p : Nat) : rowOf M p < 16384 := Nat.mod_lt _ (by decide)

theorem lt7 {q : Nat} (h : q < 7) :
    q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 := by omega

/-- `mult` and `digit` are the same base-4 digit -/
theorem mult_eq_digit (m q : Nat) : mult m q = digit m q := rfl

/-- the base-4 digit expansion of a row vector -/
theorem digit_expand (r : Nat) (h : r < 16384) :
    r = digit r 0 + 4 * digit r 1 + 16 * digit r 2 + 64 * digit r 3 + 256 * digit r 4
      + 1024 * digit r 5 + 4096 * digit r 6 := by
  show r = r / 1 % 4 + 4 * (r / 4 % 4) + 16 * (r / 16 % 4) + 64 * (r / 64 % 4) + 256 * (r / 256 % 4)
      + 1024 * (r / 1024 % 4) + 4096 * (r / 4096 % 4)
  omega

/-- the base-8 digit of an explicit seven-digit sum -/
theorem digit8_of_sum (d : Nat → Nat) (hd : ∀ q < 7, d q < 8) (q : Nat) (hq : q < 7) :
    digit8 (d 0 + 8 * d 1 + 64 * d 2 + 512 * d 3 + 4096 * d 4 + 32768 * d 5 + 262144 * d 6) q
      = d q := by
  have h0 := hd 0 (by decide); have h1 := hd 1 (by decide); have h2 := hd 2 (by decide)
  have h3 := hd 3 (by decide); have h4 := hd 4 (by decide); have h5 := hd 5 (by decide)
  have h6 := hd 6 (by decide)
  rcases lt7 hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (unfold digit8; simp only [Nat.reducePow]; omega)

theorem sum_lt_two_pow (d : Nat → Nat) (hd : ∀ q < 7, d q < 8) :
    d 0 + 8 * d 1 + 64 * d 2 + 512 * d 3 + 4096 * d 4 + 32768 * d 5 + 262144 * d 6 < 2 ^ 21 := by
  have h0 := hd 0 (by decide); have h1 := hd 1 (by decide); have h2 := hd 2 (by decide)
  have h3 := hd 3 (by decide); have h4 := hd 4 (by decide); have h5 := hd 5 (by decide)
  have h6 := hd 6 (by decide)
  simp only [Nat.reducePow]; omega

/-- `mcount` reads the base-4 digit of the packed row -/
theorem mcount_eq_digit (M p q : Nat) (hq : q < 7) : mcount M p q = digit (rowOf M p) q := by
  unfold mcount digit rowOf
  have h1 : (16384 : Nat) ^ p = 4 ^ (7 * p) := by rw [Nat.pow_mul]
  have h2 : (16384 : Nat) = 4 ^ q * 4 ^ (7 - q) := by
    rw [← Nat.pow_add, show q + (7 - q) = 7 by omega] <;> decide
  have h3 : (4 : Nat) ∣ 4 ^ (7 - q) := ⟨4 ^ (6 - q), by rw [← Nat.pow_succ']; congr 1; omega⟩
  rw [h1, h2, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ h3, Nat.div_div_eq_div_mul,
    ← Nat.pow_add]

/-- the digits of `r % 4 ^ n` below `n` are those of `r` -/
theorem digit_mod_pow (r n q : Nat) (hq : q < n) : digit (r % 4 ^ n) q = digit r q := by
  unfold digit
  have h2 : (4 : Nat) ^ n = 4 ^ q * 4 ^ (n - q) := by rw [← Nat.pow_add]; congr 1; omega
  have h3 : (4 : Nat) ∣ 4 ^ (n - q) := ⟨4 ^ (n - q - 1), by rw [← Nat.pow_succ']; congr 1; omega⟩
  rw [h2, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ h3]

/-! ### The explicit sums -/

theorem sumRow_eq (M p : Nat) : sumRow M p = mcount M p 0 + mcount M p 1 + mcount M p 2
    + mcount M p 3 + mcount M p 4 + mcount M p 5 + mcount M p 6 := by
  show List.foldl _ 0 [0, 1, 2, 3, 4, 5, 6] = _
  simp only [List.foldl]; omega

theorem sumCol_eq (M q : Nat) : sumCol M q = mcount M 0 q + mcount M 1 q + mcount M 2 q
    + mcount M 3 q + mcount M 4 q + mcount M 5 q + mcount M 6 q := by
  show List.foldl _ 0 [0, 1, 2, 3, 4, 5, 6] = _
  simp only [List.foldl]; omega

theorem digitSum_eq (r : Nat) : digitSum r = digit r 0 + digit r 1 + digit r 2 + digit r 3
    + digit r 4 + digit r 5 + digit r 6 := by
  show List.foldl _ 0 [0, 1, 2, 3, 4, 5, 6] = _
  simp only [List.foldl]; omega

theorem toBase8_eq (r : Nat) : toBase8 r = digit r 0 + 8 * digit r 1 + 64 * digit r 2
    + 512 * digit r 3 + 4096 * digit r 4 + 32768 * digit r 5 + 262144 * digit r 6 := by
  show List.foldl _ 0 [0, 1, 2, 3, 4, 5, 6] = _
  simp only [List.foldl, Nat.reducePow]; omega

/-- partial digit sums -/
def dsum (r : Nat) : Nat → Nat
  | 0 => 0
  | q + 1 => dsum r q + digit r q

theorem dsum_seven (r : Nat) : dsum r 7 = digitSum r := by
  rw [digitSum_eq]; simp only [dsum]; omega

theorem dsum_congr (a b : Nat) : ∀ n, (∀ q < n, digit a q = digit b q) → dsum a n = dsum b n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [dsum]
    rw [dsum_congr a b n (fun q hq => h q (by omega)), h n (by omega)]

/-! ### Completeness of the row generator -/

theorem comps_complete (p : Nat) : ∀ (n rem r : Nat), r < 4 ^ n →
    (∀ q < n, inter p q = false → digit r q = 0) → dsum r n ≤ rem → r ∈ comps p n rem
  | 0, rem, r, hr, _, _ => by
    have : r = 0 := by simpa using hr
    subst this; simp [comps]
  | n + 1, rem, r, hr, hz, hs => by
    have hpos : 0 < 4 ^ n := Nat.pow_pos (by decide)
    have hu : r / 4 ^ n < 4 := by
      rw [Nat.div_lt_iff_lt_mul hpos, Nat.mul_comm, ← Nat.pow_succ]; exact hr
    have hdn : digit r n = r / 4 ^ n := Nat.mod_eq_of_lt hu
    have hv : r % 4 ^ n < 4 ^ n := Nat.mod_lt _ hpos
    have hsplit : r % 4 ^ n + r / 4 ^ n * 4 ^ n = r := Nat.mod_add_div' r (4 ^ n)
    have hds : dsum r (n + 1) = dsum r n + digit r n := rfl
    have hvd : ∀ q < n, digit (r % 4 ^ n) q = digit r q := fun q hq => digit_mod_pow r n q hq
    have hvz : ∀ q < n, inter p q = false → digit (r % 4 ^ n) q = 0 :=
      fun q hq hi => by rw [hvd q hq]; exact hz q (by omega) hi
    have hvs : dsum (r % 4 ^ n) n = dsum r n := dsum_congr _ _ n hvd
    by_cases hi : inter p n = true
    · simp only [comps, hi, if_true]
      refine List.mem_flatMap.2 ⟨r / 4 ^ n, List.mem_range.2 (by omega), ?_⟩
      refine List.mem_map.2 ⟨r % 4 ^ n, ?_, hsplit⟩
      exact comps_complete p n (rem - r / 4 ^ n) (r % 4 ^ n) hv hvz (by omega)
    · have hi' : inter p n = false := by simpa using hi
      simp only [comps, hi', Bool.false_eq_true, if_false]
      have hz0 : digit r n = 0 := hz n (by omega) hi'
      have hr' : r < 4 ^ n := by
        have : r / 4 ^ n = 0 := by omega
        rw [this, Nat.zero_mul, Nat.add_zero] at hsplit; rw [← hsplit]; exact hv
      exact comps_complete p n rem r hr' (fun q hq => hz q (by omega)) (by omega)

/-! ### Bitwise tests via `testBit` -/

/-- a bit of a base-8 packed number is a bit of one of its digits -/
theorem testBit_eq_digit8 (t i : Nat) : t.testBit i = (digit8 t (i / 3)).testBit (i % 3) := by
  have h8 : (8 : Nat) ^ (i / 3) = 2 ^ (3 * (i / 3)) := by rw [Nat.pow_mul]
  show t.testBit i = (t / 8 ^ (i / 3) % 2 ^ 3).testBit (i % 3)
  rw [Nat.testBit_mod_two_pow, h8, Nat.testBit_div_two_pow]
  have : i % 3 + 3 * (i / 3) = i := Nat.mod_add_div i 3
  rw [this]
  simp [Nat.mod_lt i (by decide : 0 < 3)]

theorem testBit_small_two (d : Nat) (hd : d < 8) : d.testBit 2 = decide (4 ≤ d) := by
  revert d; decide

theorem digit8_G8 (q : Nat) (hq : q < 7) : digit8 G8 q = 4 := by
  rcases lt7 hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem G8_lt : G8 < 2 ^ 21 := by decide

/-- all guard bits set when every base-8 digit is at least four -/
theorem land_G8_eq (t : Nat) (_ht : t < 2 ^ 21) (h : ∀ q < 7, 4 ≤ digit8 t q) :
    t &&& G8 = G8 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < 21
  · have hq : i / 3 < 7 := by omega
    rw [testBit_eq_digit8 t, testBit_eq_digit8 G8, digit8_G8 _ hq]
    have hj : i % 3 < 3 := Nat.mod_lt _ (by decide)
    have hd := digit8_lt t (i / 3)
    have h4 := h _ hq
    rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with hj | hj | hj <;> rw [hj]
    · rw [show Nat.testBit 4 0 = false by decide, Bool.and_false]
    · rw [show Nat.testBit 4 1 = false by decide, Bool.and_false]
    · rw [show Nat.testBit 4 2 = true by decide, Bool.and_true, testBit_small_two _ hd,
        decide_eq_true h4]
  · have hG : G8.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le G8_lt (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hG, Bool.and_false]

/-- no common bits when every set digit of `dead` meets a zero digit of `res` -/
theorem land_eq_zero (res dead : Nat) (hres : res < 2 ^ 21)
    (h : ∀ i < 21, dead.testBit i = true → digit8 res (i / 3) = 0) : res &&& dead = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.zero_testBit]
  by_cases hi : i < 21
  · cases hd : dead.testBit i
    · rw [Bool.and_false]
    · rw [testBit_eq_digit8 res, h i hi hd, Nat.zero_testBit, Bool.false_and]
  · have : res.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hres (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [this, Bool.false_and]

/-- a set bit of the column mask of pattern `p` lies in a column intersecting `p` -/
theorem colMask8_testBit : ∀ p < 7, ∀ i < 21, (colMask8 p).testBit i = true → inter p (i / 3) = true := by
  decide

/-! ### The tables -/

theorem rowVecsLit_eq : ∀ p < 7, ∀ cap < 4, rowVecsLit p cap = (comps p 7 cap).map (tagRow p cap) := by
  decide +kernel

/-- the row of a key is in the table -/
theorem tagRow_mem (p cap r : Nat) (hp : p < 7) (hcap : cap < 4) (hr : r < 16384)
    (hz : ∀ q < 7, inter p q = false → digit r q = 0) (hs : digitSum r ≤ cap) :
    tagRow p cap r ∈ rowVecsLit p cap := by
  rw [rowVecsLit_eq p hp cap hcap]
  exact List.mem_map.2 ⟨r, comps_complete p 7 cap r hr hz (by rw [dsum_seven]; exact hs), rfl⟩

/-! ### Reading the key predicates -/

theorem validKey_inter {mL mR M : Nat} (h : validKey mL mR M = true) :
    ∀ p < 7, ∀ q < 7, inter p q = false → mcount M p q = 0 := by
  intro p hp q hq hi
  simp only [validKey, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq] at h
  match h.1.1 p hp q hq with
  | Or.inl h' => rw [hi] at h'; exact absurd h' (by decide)
  | Or.inr h' => exact h'

theorem validKey_row {mL mR M : Nat} (h : validKey mL mR M = true) :
    ∀ p < 7, sumRow M p ≤ mult mL p := by
  intro p hp
  simp only [validKey, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq] at h
  exact h.1.2 p hp

theorem validKey_col {mL mR M : Nat} (h : validKey mL mR M = true) :
    ∀ q < 7, sumCol M q ≤ mult mR q := by
  intro q hq
  simp only [validKey, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq] at h
  exact h.2 q hq

theorem keyMax_spec {mL mR M : Nat} (h : keyMax mL mR M = true) :
    ∀ p < 7, ∀ q < 7, inter p q = true → sumRow M p < mult mL p → sumCol M q = mult mR q := by
  intro p hp q hq hi hlt
  simp only [keyMax, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
  match h p hp q hq with
  | Or.inl (Or.inl h') => rw [hi] at h'; exact absurd h' (by decide)
  | Or.inl (Or.inr h') => omega
  | Or.inr h' => exact h'

/-! ### The invariants -/

/-- the column sum of the first `p` rows -/
def cpre (M q : Nat) : Nat → Nat
  | 0 => 0
  | p + 1 => cpre M q p + mcount M p q

theorem cpre_seven (M q : Nat) : cpre M q 7 = sumCol M q := by
  rw [sumCol_eq]; simp only [cpre]; omega

theorem cpre_le_seven (M q p : Nat) (hp : p ≤ 7) : cpre M q p ≤ cpre M q 7 := by
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp only [cpre]; omega)

/-- the base-8 residual after the first `p` rows -/
def resOf (M mR p : Nat) : Nat :=
  (mult mR 0 - cpre M 0 p) + 8 * (mult mR 1 - cpre M 1 p) + 64 * (mult mR 2 - cpre M 2 p)
    + 512 * (mult mR 3 - cpre M 3 p) + 4096 * (mult mR 4 - cpre M 4 p)
    + 32768 * (mult mR 5 - cpre M 5 p) + 262144 * (mult mR 6 - cpre M 6 p)

/-- the dead mask after the first `p` rows -/
def dpre (M mL : Nat) : Nat → Nat
  | 0 => 0
  | p + 1 => dpre M mL p ||| (if sumRow M p < mult mL p then colMask8 p else 0)

theorem mult_lt (m q : Nat) : mult m q < 4 := Nat.mod_lt _ (by decide)

theorem resOf_digit (M mR p q : Nat) (hq : q < 7) :
    digit8 (resOf M mR p) q = mult mR q - cpre M q p := by
  unfold resOf
  exact digit8_of_sum (fun q => mult mR q - cpre M q p) (fun q _ => by have := mult_lt mR q; omega) q hq

theorem resOf_lt (M mR p : Nat) : resOf M mR p < 2 ^ 21 := by
  unfold resOf
  exact sum_lt_two_pow (fun q => mult mR q - cpre M q p) (fun q _ => by have := mult_lt mR q; omega)

/-- a set bit of the dead mask comes from a spare row meeting that column -/
theorem dpre_testBit (M mL : Nat) : ∀ p, p ≤ 7 → ∀ i < 21, (dpre M mL p).testBit i = true →
    ∃ j < p, sumRow M j < mult mL j ∧ inter j (i / 3) = true
  | 0, _, i, _, h => by simp [dpre] at h
  | p + 1, hp, i, hi, h => by
    simp only [dpre, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨j, hj, hs, hi⟩ := dpre_testBit M mL p (by omega) i hi h
      exact ⟨j, by omega, hs, hi⟩
    · by_cases hs : sumRow M p < mult mL p
      · rw [if_pos hs] at h
        exact ⟨p, by omega, hs, colMask8_testBit p (by omega) i hi h⟩
      · rw [if_neg hs] at h; simp at h

/-! ### The main induction -/

theorem enumRows_complete (mL mR M : Nat) (hM : M < 16384 ^ 7) (hv : validKey mL mR M = true)
    (hmax : keyMax mL mR M = true) :
    ∀ n p, p + n = 7 →
      M / 16384 ^ p ∈ enumRows (rowLists mL n p) (resOf M mR p) (dpre M mL p)
  | 0, p, hp => by
    have hp7 : p = 7 := by omega
    subst hp7
    have h0 : M / 16384 ^ 7 = 0 := Nat.div_eq_of_lt hM
    rw [h0]
    have hz : resOf M mR 7 &&& dpre M mL 7 = 0 := by
      apply land_eq_zero _ _ (resOf_lt M mR 7)
      intro i hi hb
      obtain ⟨j, hj, hs, hij⟩ := dpre_testBit M mL 7 (Nat.le_refl _) i hi hb
      have hq : i / 3 < 7 := by omega
      rw [resOf_digit _ _ _ _ hq, cpre_seven, keyMax_spec hmax j hj _ hq hij hs, Nat.sub_self]
    simp [rowLists, enumRows, hz]
  | n + 1, p, hp => by
    have hp7 : p < 7 := by omega
    -- the current row and the rest
    have hr16 : rowOf M p < 16384 := rowOf_lt M p
    have hrest : M / 16384 ^ p = rowOf M p + 16384 * (M / 16384 ^ (p + 1)) := by
      rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]; exact (Nat.mod_add_div _ _).symm
    -- the row's digits are the key's counts
    have hdig : ∀ q < 7, digit (rowOf M p) q = mcount M p q :=
      fun q hq => (mcount_eq_digit M p q hq).symm
    have hds : digitSum (rowOf M p) = sumRow M p := by
      rw [digitSum_eq, sumRow_eq, hdig 0 (by decide), hdig 1 (by decide), hdig 2 (by decide),
        hdig 3 (by decide), hdig 4 (by decide), hdig 5 (by decide), hdig 6 (by decide)]
    have hrow := validKey_row hv p hp7
    have hcol := validKey_col hv
    -- the tagged row is in the table
    have hmem : tagRow p (mult mL p) (rowOf M p) ∈ rowVecsLit p (mult mL p) :=
      tagRow_mem p (mult mL p) (rowOf M p) hp7 (mult_lt mL p) hr16
        (fun q hq hi => by rw [hdig q hq]; exact validKey_inter hv p hp7 q hq hi) (by omega)
    -- the residual arithmetic
    have hcp : ∀ q < 7, cpre M q p + mcount M p q ≤ mult mR q := fun q hq => by
      have h1 : cpre M q (p + 1) ≤ cpre M q 7 := cpre_le_seven M q (p + 1) (by omega)
      have h2 := hcol q hq
      rw [cpre_seven] at h1
      simp only [cpre] at h1; omega
    have hb8 : toBase8 (rowOf M p) = mcount M p 0 + 8 * mcount M p 1 + 64 * mcount M p 2
        + 512 * mcount M p 3 + 4096 * mcount M p 4 + 32768 * mcount M p 5
        + 262144 * mcount M p 6 := by
      rw [toBase8_eq, hdig 0 (by decide), hdig 1 (by decide), hdig 2 (by decide),
        hdig 3 (by decide), hdig 4 (by decide), hdig 5 (by decide), hdig 6 (by decide)]
    have hc := fun q hq => hcp q hq
    have hc0 := hc 0 (by decide); have hc1 := hc 1 (by decide); have hc2 := hc 2 (by decide)
    have hc3 := hc 3 (by decide); have hc4 := hc 4 (by decide); have hc5 := hc 5 (by decide)
    have hc6 := hc 6 (by decide)
    have hm0 := mult_lt mR 0; have hm1 := mult_lt mR 1; have hm2 := mult_lt mR 2
    have hm3 := mult_lt mR 3; have hm4 := mult_lt mR 4; have hm5 := mult_lt mR 5
    have hm6 := mult_lt mR 6
    -- the fits test passes
    have hfitsum : resOf M mR p + G8 - toBase8 (rowOf M p)
        = (mult mR 0 - cpre M 0 p + 4 - mcount M p 0)
          + 8 * (mult mR 1 - cpre M 1 p + 4 - mcount M p 1)
          + 64 * (mult mR 2 - cpre M 2 p + 4 - mcount M p 2)
          + 512 * (mult mR 3 - cpre M 3 p + 4 - mcount M p 3)
          + 4096 * (mult mR 4 - cpre M 4 p + 4 - mcount M p 4)
          + 32768 * (mult mR 5 - cpre M 5 p + 4 - mcount M p 5)
          + 262144 * (mult mR 6 - cpre M 6 p + 4 - mcount M p 6) := by
      rw [hb8]; unfold resOf G8; omega
    have hfits : (resOf M mR p + G8 - toBase8 (rowOf M p)) &&& G8 = G8 := by
      rw [hfitsum]
      apply land_G8_eq _ (sum_lt_two_pow (fun q => mult mR q - cpre M q p + 4 - mcount M p q)
        (fun q hq => by have := hcp q hq; have := mult_lt mR q; omega))
      intro q hq
      rw [digit8_of_sum (fun q => mult mR q - cpre M q p + 4 - mcount M p q)
        (fun q hq => by have := hcp q hq; have := mult_lt mR q; omega) q hq]
      have := hcp q hq; omega
    -- the updated residual and dead mask
    have hres' : resOf M mR p - toBase8 (rowOf M p) = resOf M mR (p + 1) := by
      rw [hb8]; unfold resOf; simp only [cpre]; omega
    have hdead' : dpre M mL p ||| (tagRow p (mult mL p) (rowOf M p)).2.2 = dpre M mL (p + 1) := by
      simp only [tagRow, dpre, hds]
    -- assemble
    have ih := enumRows_complete mL mR M hM hv hmax n (p + 1) (by omega)
    rw [← hres', ← hdead'] at ih
    show M / 16384 ^ p ∈ enumRows (rowVecsLit p (mult mL p) :: rowLists mL n (p + 1)) _ _
    simp only [enumRows]
    refine List.mem_flatMap.2 ⟨tagRow p (mult mL p) (rowOf M p), hmem, ?_⟩
    have hfits' : ((resOf M mR p + G8 - (tagRow p (mult mL p) (rowOf M p)).2.1) &&& G8 == G8) = true := by
      simp only [tagRow]; exact beq_iff_eq.2 hfits
    rw [if_pos hfits']
    exact List.mem_map.2 ⟨M / 16384 ^ (p + 1), ih, hrest.symm⟩

/-- the initial residual is the right type itself, repacked in base 8 -/
theorem resOf_zero (M mR : Nat) : resOf M mR 0 = toBase8 mR := by
  rw [toBase8_eq]; unfold resOf; simp only [cpre, Nat.sub_zero, mult_eq_digit]

/-- **Completeness**: every valid maximal key is enumerated. -/
theorem enumKeys_complete (mL mR M : Nat) (hM : M < 16384 ^ 7) (hv : validKey mL mR M = true)
    (hmax : keyMax mL mR M = true) : M ∈ enumKeys mL mR := by
  have h := enumRows_complete mL mR M hM hv hmax 7 0 rfl
  rw [resOf_zero] at h
  simpa [enumKeys, dpre] using h

/-! ### The valid types -/

/-- one quarter of the type range, starting at `s` -/
def validTypesFrom (s : Nat) : List Nat := (List.range' s 4096).filter validType

set_option maxRecDepth 100000 in
theorem range_split : List.range 16384
    = List.range' 0 4096 ++ List.range' 4096 4096 ++ List.range' 8192 4096 ++ List.range' 12288 4096 := by
  decide +kernel

theorem validTypes_split : validTypes
    = validTypesFrom 0 ++ validTypesFrom 4096 ++ validTypesFrom 8192 ++ validTypesFrom 12288 := by
  unfold validTypes validTypesFrom
  rw [range_split, List.filter_append, List.filter_append, List.filter_append]

theorem validType_mem_validTypes (m : Nat) (hm : m < 16384) (h : validType m = true) :
    m ∈ validTypes :=
  List.mem_filter.2 ⟨List.mem_range.2 hm, h⟩

end Grid3.Three.Cert
