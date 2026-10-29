/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.K5.BitSound

/-!
# Height five at `k = 5`: a faster check of the state-bit certificates

`bitOK5` and `ptOK5` of `BitLP`, arranged for the kernel:

* every operation is a primitive `Nat` operation or a recursor (no instances to unfold);
* the code vectors are enumerated code by code and cut as soon as a prefix fails `bvalid5`
  (`prunedAll`);
* the pins are filtered row by row (`filtRow`, `filt5_eq`): the test of a pin on one row at one
  code is the same closed term at every visit, so the kernel evaluates it once;
* the multipliers of the pins that fire are summed for all fifteen patterns at once: a pin
  contributes `λ · spr(em)`, its pattern mask spread into fifteen 40-bit lanes (`spr`, the same
  closed term at every code vector, so the kernel evaluates it once); lane `i` of the sum is
  `firedL F i` as long as `Σ λ < 2⁴⁰` (`lamS`, checked once per class).

`bitOK5_of_fast` and `ptOK5_of_fast` turn the fast checks into the original ones. Nothing is
trusted: the fast check is a kernel computation, and its soundness is proved here.
-/

namespace GridGen.Five.K5

open Finset GridGen.Five GridGen.Five.Ex5

/-! ### Primitive helpers -/

/-- Bit `a` of `S`. -/
def tbit (S a : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight S a) 1) 1

theorem tbit_eq (S a : ℕ) : tbit S a = S.testBit a := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  unfold tbit
  have e : Nat.land (Nat.shiftRight S a) 1 = S / 2 ^ a % 2 := by
    show (S >>> a) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [e]
  by_cases h : S / 2 ^ a % 2 = 1
  · rw [h]; simp
  · simp only [h, decide_false]
    cases hb : Nat.beq (S / 2 ^ a % 2) 1
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) h

/-- Evaluate `x` once and pass the value on (as `forceN` of `ExactDefs`). -/
def fNb (x : ℕ) (k : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (n + 1)) x

theorem fNb_eq (x : ℕ) (k : ℕ → Bool) : fNb x k = k x := by
  cases x <;> rfl

/-- `L.getD n 0` by a recursor. -/
def getR (L : List ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun a _ ih n => Nat.casesOn (motive := fun _ => ℕ) n a ih) L

theorem getR_eq : ∀ (L : List ℕ) (n : ℕ), getR L n = L.getD n 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | a :: L, n + 1 => by
    show getR L n = _
    rw [getR_eq L n]; rfl

/-- `f` holds at `0, …, 14`. -/
def all15 (f : ℕ → Bool) : Bool :=
  f 0 && f 1 && f 2 && f 3 && f 4 && f 5 && f 6 && f 7 && f 8 && f 9 && f 10 && f 11 && f 12 &&
    f 13 && f 14

theorem all15_eq (f : ℕ → Bool) : all15 f = (List.range 15).all f := by
  simp only [all15, List.range_succ, List.range_zero, List.nil_append, List.all_append,
    List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc]

/-! ### Codes -/

def kHr (c : ℕ) : ℕ := cond (Nat.beq c 0) 1 0
def kMr (c : ℕ) : ℕ := cond (Nat.beq c 2 || Nat.beq c 4) 1 0
def kXr (c : ℕ) : ℕ := cond (Nat.beq c 3 || Nat.beq c 4) 1 0

theorem beq_eq_decide (a b : ℕ) : Nat.beq a b = decide (a = b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_eq]

theorem blt_eq_decide (a b : ℕ) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_eq]

theorem ble_eq_decide (a b : ℕ) : Nat.ble a b = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_eq]

theorem kHr_eq (c : ℕ) : kHr c = kH c := by
  unfold kHr kH; rw [beq_eq_decide]; by_cases h : c = 0 <;> simp [h]

theorem kMr_eq (c : ℕ) : kMr c = kM c := by
  unfold kMr kM; rw [beq_eq_decide, beq_eq_decide]
  by_cases h2 : c = 2 <;> by_cases h4 : c = 4 <;> simp [h2, h4]

theorem kXr_eq (c : ℕ) : kXr c = kX c := by
  unfold kXr kX; rw [beq_eq_decide, beq_eq_decide]
  by_cases h3 : c = 3 <;> by_cases h4 : c = 4 <;> simp [h3, h4]

/-- The intersection bound of one consecutive pair. -/
def capR (cp ci : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.add (Nat.add 3 (kHr cp)) (kXr cp)) (kHr ci)) (kMr ci)

/-- `bvalid5` with primitive operations (the same conjuncts in the same order). -/
def bvalidR (m2 m3 m4 m5 c1 c2 c3 c4 c5 : ℕ) : Bool :=
  Nat.beq (kMr c1) 0 && Nat.beq (kXr c5) 0 &&
  (Nat.beq (kMr c2) 0 || Nat.blt 0 m2) && (Nat.beq (kMr c3) 0 || Nat.blt 0 m3) &&
  (Nat.beq (kMr c4) 0 || Nat.blt 0 m4) && (Nat.beq (kMr c5) 0 || Nat.blt 0 m5) &&
  (Nat.beq (kXr c1) 0 || Nat.blt 0 m2) && (Nat.beq (kXr c2) 0 || Nat.blt 0 m3) &&
  (Nat.beq (kXr c3) 0 || Nat.blt 0 m4) && (Nat.beq (kXr c4) 0 || Nat.blt 0 m5) &&
  Nat.ble m2 (capR c1 c2) && Nat.ble m3 (capR c2 c3) && Nat.ble m4 (capR c3 c4) &&
  Nat.ble m5 (capR c4 c5)

theorem nat_beq_eq (a b : ℕ) : Nat.beq a b = (a == b) := rfl

theorem bvalidR_eq (m2 m3 m4 m5 c1 c2 c3 c4 c5 : ℕ) :
    bvalidR m2 m3 m4 m5 c1 c2 c3 c4 c5 = bvalid5 m2 m3 m4 m5 c1 c2 c3 c4 c5 := by
  simp only [bvalidR, bvalid5, capR, kMr_eq, kXr_eq, kHr_eq, nat_beq_eq, blt_eq_decide,
    ble_eq_decide, Nat.add_eq]

def minR (a b : ℕ) : ℕ := cond (Nat.ble a b) a b

theorem minR_eq (a b : ℕ) : minR a b = min a b := by
  unfold minR
  by_cases h : a ≤ b
  · rw [Nat.ble_eq_true_of_le h, min_eq_left h]; rfl
  · have : Nat.ble a b = false := by
      rw [Bool.eq_false_iff]; intro hh; exact h (Nat.ble_eq.mp hh)
    rw [this, min_eq_right (by omega)]; rfl

def kapPr (n1 n2 n3 n4 n5 a b c d : ℕ) : ℕ :=
  Nat.add (Nat.mul (Nat.mul (Nat.mul (Nat.mul n1 n2) n3) n4) n5) <|
  Nat.add (Nat.mul (Nat.mul (Nat.sub (Nat.add a b) n2) n4) n5) <|
  Nat.add (Nat.mul (Nat.mul a c) n5) <| Nat.add (Nat.mul (Nat.mul a n3) d) <|
  Nat.add (Nat.mul (Nat.mul n1 (Nat.sub (Nat.add b c) n3)) n5) <|
  Nat.add (Nat.mul (Nat.mul n1 b) d) <| Nat.add (Nat.mul (Nat.mul n1 n2) (Nat.sub (Nat.add c d) n4)) <|
  Nat.sub (Nat.add (minR (Nat.sub (Nat.add a b) n2) (Nat.sub (Nat.add b c) n3))
    (minR (Nat.sub (Nat.add b c) n3) (Nat.sub (Nat.add c d) n4))) (Nat.sub (Nat.add b c) n3)

def kapMr (n1 n2 n3 n4 n5 a b c d : ℕ) : ℕ :=
  Nat.add (Nat.mul (Nat.mul (Nat.mul a n3) n4) n5) <|
  Nat.add (Nat.mul (Nat.mul (Nat.mul n1 b) n4) n5) <|
  Nat.add (Nat.mul (Nat.mul (Nat.mul n1 n2) c) n5) <|
  Nat.add (Nat.mul (Nat.mul (Nat.mul n1 n2) n3) d) <|
  Nat.add (Nat.mul (minR (Nat.sub (Nat.add a b) n2) (Nat.sub (Nat.add b c) n3)) n5) <|
  Nat.add (Nat.mul (Nat.sub (Nat.add a b) n2) d) <|
  Nat.add (Nat.mul a (Nat.sub (Nat.add c d) n4))
    (Nat.mul n1 (minR (Nat.sub (Nat.add b c) n3) (Nat.sub (Nat.add c d) n4)))

theorem kapPr_eq (n1 n2 n3 n4 n5 a b c d : ℕ) :
    kapPr n1 n2 n3 n4 n5 a b c d = kapP n1 n2 n3 n4 n5 a b c d := by
  simp only [kapPr, kapP, minR_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
  ring

theorem kapMr_eq (n1 n2 n3 n4 n5 a b c d : ℕ) :
    kapMr n1 n2 n3 n4 n5 a b c d = kapM n1 n2 n3 n4 n5 a b c d := by
  simp only [kapMr, kapM, minR_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
  ring

def nEr (m cp ci : ℕ) : ℕ := Nat.sub (capR cp ci) m

theorem nEr_eq (m cp ci : ℕ) : nEr m cp ci = nE5 m cp ci := by
  simp only [nEr, capR, nE5, kHr_eq, kXr_eq, kMr_eq, Nat.add_eq, Nat.sub_eq]

/-- The size-vector index from the five `kH`. -/
def nidxR (a b c d e : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 16 a) (Nat.mul 8 b)) (Nat.mul 4 c)) (Nat.mul 2 d)) e

theorem nidxR_eq (a b c d e : ℕ) : nidxR a b c d e = nidx (4 + a) (4 + b) (4 + c) (4 + d) (4 + e) := by
  simp only [nidxR, nidx, Nat.add_eq, Nat.mul_eq]; omega

/-! ### Fired pins, fifteen lanes at once -/

/-- The lane width. -/
def BL : ℕ := 1099511627776

/-- A list of lanes, packed. -/
def packB : List ℕ → ℕ
  | [] => 0
  | y :: ys => y + BL * packB ys

theorem packB_lane : ∀ (L : List ℕ), (∀ y ∈ L, y < BL) → ∀ k, packB L / BL ^ k % BL = L.getD k 0
  | [], _, k => by simp [packB]
  | y :: L, h, 0 => by
    have hy := h y List.mem_cons_self
    simp only [packB, pow_zero, Nat.div_one, List.getD_cons_zero]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy]
  | y :: L, h, k + 1 => by
    have hy := h y List.mem_cons_self
    have ih := packB_lane L (fun x hx => h x (List.mem_cons_of_mem y hx)) k
    have hB : 0 < BL := by decide
    simp only [packB, List.getD_cons_succ]
    rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hy,
      zero_add, ih]

theorem packB_lin (a : ℕ) : ∀ (xs ys : List ℕ), xs.length = ys.length →
    a * packB xs + packB ys = packB (List.zipWith (fun x y => a * x + y) xs ys)
  | [], [], _ => by simp [packB]
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)
  | x :: xs, y :: ys, h => by
    simp only [List.length_cons, add_left_inj] at h
    simp only [packB, List.zipWith_cons_cons]
    rw [← packB_lin a xs ys h]
    ring

/-- The fifteen bits of a pattern mask. -/
def bitsL (em : ℕ) : List ℕ :=
  [cond (tbit em 0) 1 0, cond (tbit em 1) 1 0, cond (tbit em 2) 1 0, cond (tbit em 3) 1 0,
    cond (tbit em 4) 1 0, cond (tbit em 5) 1 0, cond (tbit em 6) 1 0, cond (tbit em 7) 1 0,
    cond (tbit em 8) 1 0, cond (tbit em 9) 1 0, cond (tbit em 10) 1 0, cond (tbit em 11) 1 0,
    cond (tbit em 12) 1 0, cond (tbit em 13) 1 0, cond (tbit em 14) 1 0]

/-- A pattern mask spread into fifteen lanes. -/
def spr (em : ℕ) : ℕ := packB (bitsL em)

/-- The packed multipliers of the pins. -/
def firedP (F : List BPin5) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun q _ acc => Nat.add (Nat.mul q.lam (spr q.em)) acc) F

/-- The fifteen lanes of `firedL`. -/
def lanesL (F : List BPin5) : List ℕ :=
  [firedL F 0, firedL F 1, firedL F 2, firedL F 3, firedL F 4, firedL F 5, firedL F 6, firedL F 7,
    firedL F 8, firedL F 9, firedL F 10, firedL F 11, firedL F 12, firedL F 13, firedL F 14]

theorem firedL_cons (q : BPin5) (F : List BPin5) (i : ℕ) :
    firedL (q :: F) i = cond (tbit q.em i) q.lam 0 + firedL F i := by
  simp only [firedL, List.map_cons, List.sum_cons, tbit_eq]
  cases q.em.testBit i <;> rfl

theorem mul_cond (a : ℕ) (b : Bool) (y : ℕ) : a * cond b 1 0 + y = cond b a 0 + y := by
  cases b <;> simp

theorem firedP_eq : ∀ F : List BPin5, firedP F = packB (lanesL F)
  | [] => by simp [firedP, packB, lanesL, firedL]
  | q :: F => by
    show q.lam * spr q.em + firedP F = _
    rw [firedP_eq F, spr, packB_lin q.lam (bitsL q.em) (lanesL F) rfl]
    simp only [bitsL, lanesL, List.zipWith_cons_cons, List.zipWith_nil_left, mul_cond, firedL_cons]

/-- The multipliers. -/
def lamS (P : List BPin5) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun q _ acc => Nat.add q.lam acc) P

theorem firedL_le_lamS : ∀ (F : List BPin5) (i : ℕ), firedL F i ≤ lamS F
  | [], _ => by simp [firedL, lamS]
  | q :: F, i => by
    rw [firedL_cons]
    have := firedL_le_lamS F i
    show _ ≤ Nat.add q.lam (lamS F)
    cases tbit q.em i <;> simp <;> omega

/-- Lane `i` of a packed number. -/
def laneR (X i : ℕ) : ℕ := Nat.mod (Nat.div X (Nat.pow BL i)) BL

theorem laneR_fired {F : List BPin5} (hF : lamS F < BL) {i : ℕ} (hi : i < 15) :
    laneR (firedP F) i = firedL F i := by
  have hl : ∀ y ∈ lanesL F, y < BL := by
    intro y hy
    simp only [lanesL, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> exact lt_of_le_of_lt (firedL_le_lamS F _) hF
  show firedP F / BL ^ i % BL = _
  rw [firedP_eq, packB_lane _ hl]
  interval_cases i <;> rfl

/-! ### The check at one code vector -/

/-- The check of pattern `i`. -/
def stI (D K FP DP DM : ℕ) (Rl : List ℕ) (i : ℕ) : Bool :=
  Nat.blt 0 (getR Rl (getR ORBL i)) &&
    Nat.ble (Nat.add (Nat.mul (Nat.add D K) (Nat.mul (getR NUL (getR ORBL i)) (getR Rl (getR ORBL i))))
      DM) (Nat.add DP (Nat.mul (laneR FP i) (Nat.mul (getR NUL (getR ORBL i)) (getR Rl (getR ORBL i)))))

theorem stI_eq {C : BitCert5} {F : List BPin5} (hF : lamS F < BL) {P M : ℕ} {Rl : List ℕ}
    {i : ℕ} (hi : i < 15) :
    stI C.D C.K (firedP F) (Nat.mul (Nat.mul C.D 1000000000) P) (Nat.mul (Nat.mul C.D 1000000000) M)
      Rl i = (decide (0 < Rl.getD (ORBL.getD i 0) 0) &&
        decide ((C.D + C.K) * NUL.getD (ORBL.getD i 0) 0 * Rl.getD (ORBL.getD i 0) 0
          + C.D * 1000000000 * M
          ≤ C.D * 1000000000 * P + firedL F i * NUL.getD (ORBL.getD i 0) 0
            * Rl.getD (ORBL.getD i 0) 0)) := by
  unfold stI
  rw [laneR_fired hF hi]
  simp only [getR_eq, Nat.add_eq, Nat.mul_eq]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, decide_eq_true_eq, Nat.mul_assoc]

/-! ### Pins filtered row by row -/

/-- The row conditions of a pin. -/
def pconds (q : BPin5) : List (ℕ × ℕ) := q.blk.conds ++ peelConds q.peels

/-- The conditions of a pin on row `r` hold at code `c` (the same closed term at every visit). -/
def rowOKp (q : BPin5) (r c : ℕ) : Bool := (pconds q).all (fun rk => !(Nat.beq rk.1 r) || evk rk.2 c)

/-- The pins whose conditions on row `r` hold at code `c`. -/
def filtRow (r c : ℕ) (P : List BPin5) : List BPin5 :=
  List.rec (motive := fun _ => List BPin5) [] (fun q _ acc => cond (rowOKp q r c) (q :: acc) acc) P

theorem filtRow_eq (r c : ℕ) : ∀ P : List BPin5, filtRow r c P = P.filter (fun q => rowOKp q r c)
  | [] => rfl
  | q :: P => by
    show cond (rowOKp q r c) (q :: filtRow r c P) (filtRow r c P) = _
    rw [filtRow_eq r c P, List.filter_cons]
    cases rowOKp q r c <;> rfl

theorem rows_all (c1 c2 c3 c4 c5 : ℕ) : ∀ L : List (ℕ × ℕ), (∀ rk ∈ L, rk.1 < 5) →
    (L.all (fun rk => !(Nat.beq rk.1 4) || evk rk.2 c5) &&
      (L.all (fun rk => !(Nat.beq rk.1 3) || evk rk.2 c4) &&
      (L.all (fun rk => !(Nat.beq rk.1 2) || evk rk.2 c3) &&
      (L.all (fun rk => !(Nat.beq rk.1 1) || evk rk.2 c2) &&
      L.all (fun rk => !(Nat.beq rk.1 0) || evk rk.2 c1)))))
      = L.all (fun rk => evk rk.2 (crow (c1, c2, c3, c4, c5) rk.1))
  | [], _ => rfl
  | (r, k) :: L, h => by
    have ih := rows_all c1 c2 c3 c4 c5 L (fun rk hrk => h rk (List.mem_cons_of_mem _ hrk))
    have hr : r < 5 := h (r, k) List.mem_cons_self
    simp only [List.all_cons]
    rw [← ih]
    interval_cases r <;>
    · simp only [Nat.beq, crow, Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or,
        Bool.true_and]
      cases evk k c1 <;> cases evk k c2 <;> cases evk k c3 <;> cases evk k c4 <;>
        cases evk k c5 <;> simp

theorem filt5_eq {P : List BPin5} (hP : P.all (BPin5.okb RM) = true) {c1 c2 c3 c4 c5 : ℕ}
    (h1 : c1 < 5) (h2 : c2 < 5) (h3 : c3 < 5) (h4 : c4 < 5) (h5 : c5 < 5) :
    filtRow 4 c5 (filtRow 3 c4 (filtRow 2 c3 (filtRow 1 c2 (filtRow 0 c1 P))))
      = P.filter (fun q => q.bm.testBit (cidx (c1, c2, c3, c4, c5))) := by
  simp only [filtRow_eq, List.filter_filter]
  refine List.filter_congr fun q hq => ?_
  have hq' := List.all_eq_true.mp hP q hq
  rw [bm_testBit RM_ok hq' h1 h2 h3 h4 h5]
  simp only [rowOKp, pconds]
  refine rows_all c1 c2 c3 c4 c5 _ fun rk hrk => ?_
  simp only [BPin5.okb, Bool.and_eq_true] at hq'
  rcases List.mem_append.mp hrk with hm | hm
  · exact (blk_conds_ok q.blk hq'.1.1.1 rk hm).1
  · exact (peelConds_ok q.peels (bpeelOK_all hq'.1.1.2) rk hm).1

/-- The check at one code vector, with the pins that fire given. -/
def bitAtG (m2 m3 m4 m5 : ℕ) (C : BitCert5) (F : List BPin5) (c1 c2 c3 c4 c5 : ℕ) : Bool :=
  !(bvalidR m2 m3 m4 m5 c1 c2 c3 c4 c5) ||
    fNb (firedP F) fun FP =>
    fNb (Nat.mul (Nat.mul C.D 1000000000) (kapPr (Nat.add 4 (kHr c1)) (Nat.add 4 (kHr c2))
      (Nat.add 4 (kHr c3)) (Nat.add 4 (kHr c4)) (Nat.add 4 (kHr c5))
      (nEr m2 c1 c2) (nEr m3 c2 c3) (nEr m4 c3 c4) (nEr m5 c4 c5))) fun DP =>
    fNb (Nat.mul (Nat.mul C.D 1000000000) (kapMr (Nat.add 4 (kHr c1)) (Nat.add 4 (kHr c2))
      (Nat.add 4 (kHr c3)) (Nat.add 4 (kHr c4)) (Nat.add 4 (kHr c5))
      (nEr m2 c1 c2) (nEr m3 c2 c3) (nEr m4 c3 c4) (nEr m5 c4 c5))) fun DM =>
    all15 (stI C.D C.K FP DP DM
      (patCerts.getD (nidxR (kHr c1) (kHr c2) (kHr c3) (kHr c4) (kHr c5)) default).R)

theorem lamS_le_filter (p : BPin5 → Bool) : ∀ P : List BPin5, lamS (P.filter p) ≤ lamS P
  | [] => le_rfl
  | q :: P => by
    have := lamS_le_filter p P
    rw [List.filter_cons]
    show _ ≤ Nat.add q.lam (lamS P)
    split
    · show Nat.add q.lam (lamS (P.filter p)) ≤ _; simp only [Nat.add_eq]; omega
    · simp only [Nat.add_eq]; omega

theorem bitAtG_sound {m2 m3 m4 m5 : ℕ} {C : BitCert5} (hC : lamS C.pins < BL)
    {c1 c2 c3 c4 c5 : ℕ} {F : List BPin5}
    (hF : F = C.pins.filter (fun q => q.bm.testBit (cidx (c1, c2, c3, c4, c5))))
    (h : bitAtG m2 m3 m4 m5 C F c1 c2 c3 c4 c5 = true) :
    bitAt5 m2 m3 m4 m5 C c1 c2 c3 c4 c5 = true := by
  unfold bitAtG at h
  unfold bitAt5
  rw [bvalidR_eq] at h
  cases hv : bvalid5 m2 m3 m4 m5 c1 c2 c3 c4 c5
  · rfl
  rw [hv] at h
  simp only [Bool.not_true, Bool.false_or, fNb_eq] at h ⊢
  have hF' : lamS F < BL := by rw [hF]; exact lt_of_le_of_lt (lamS_le_filter _ _) hC
  rw [all15_eq, List.all_eq_true] at h
  unfold stOK5
  rw [List.all_eq_true]
  intro i hi
  have hi' : i < 15 := List.mem_range.mp hi
  have := h i hi
  rw [stI_eq hF' hi'] at this
  rw [hF, kapPr_eq, kapMr_eq, nidxR_eq] at this
  simp only [nEr_eq, kHr_eq, Nat.add_eq] at this
  exact this

theorem all5k_mono' {p q : ℕ → Bool} (h : ∀ i, i ≤ 4 → p i = true → q i = true)
    (hp : all5k p = true) : all5k q = true := by
  simp only [all5k, Bool.and_eq_true] at hp ⊢
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hp
  exact ⟨⟨⟨⟨h _ (by omega) h0, h _ (by omega) h1⟩, h _ (by omega) h2⟩, h _ (by omega) h3⟩,
    h _ (by omega) h4⟩

theorem all5k_of {q : ℕ → Bool} (h : ∀ i, i ≤ 4 → q i = true) : all5k q = true :=
  all5k_mono' (p := fun _ => true) (fun i hi _ => h i hi) rfl

/-! ### Code vectors pruned by prefix -/

/-- The conditions of one consecutive pair (`bvalidR`, regrouped). -/
def pairR (m cp ci : ℕ) : Bool :=
  (Nat.beq (kMr ci) 0 || Nat.blt 0 m) && (Nat.beq (kXr cp) 0 || Nat.blt 0 m) && Nat.ble m (capR cp ci)

/-- **`f` at every admissible code vector**, the enumeration cut as soon as a prefix fails. -/
def prunedAll (m2 m3 m4 m5 : ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℕ → Bool) : Bool :=
  all5k (fun c1 => !(Nat.beq (kMr c1) 0) || all5k (fun c2 => !(pairR m2 c1 c2) ||
    all5k (fun c3 => !(pairR m3 c2 c3) || all5k (fun c4 => !(pairR m4 c3 c4) ||
    all5k (fun c5 => !(Nat.beq (kXr c5) 0 && pairR m5 c4 c5) || f c1 c2 c3 c4 c5)))))

theorem prunedAll_spec {m2 m3 m4 m5 : ℕ} {f : ℕ → ℕ → ℕ → ℕ → ℕ → Bool}
    (h : prunedAll m2 m3 m4 m5 f = true) {c1 c2 c3 c4 c5 : ℕ} (h1 : c1 ≤ 4) (h2 : c2 ≤ 4)
    (h3 : c3 ≤ 4) (h4 : c4 ≤ 4) (h5 : c5 ≤ 4) (hv : bvalidR m2 m3 m4 m5 c1 c2 c3 c4 c5 = true) :
    f c1 c2 c3 c4 c5 = true := by
  have e1 : Nat.beq (kMr c1) 0 = true ∧ pairR m2 c1 c2 = true ∧ pairR m3 c2 c3 = true ∧
      pairR m4 c3 c4 = true ∧ (Nat.beq (kXr c5) 0 && pairR m5 c4 c5) = true := by
    simp only [bvalidR, Bool.and_eq_true] at hv
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, b2⟩, b3⟩, b4⟩, b5⟩, x2⟩, x3⟩, x4⟩, x5⟩, l2⟩, l3⟩, l4⟩, l5⟩ := hv
    simp only [pairR, Bool.and_eq_true]
    exact ⟨a1, ⟨⟨b2, x2⟩, l2⟩, ⟨⟨b3, x3⟩, l3⟩, ⟨⟨b4, x4⟩, l4⟩, a2, ⟨⟨b5, x5⟩, l5⟩⟩
  obtain ⟨g1, g2, g3, g4, g5⟩ := e1
  have k1 := all5k_spec h h1
  rw [g1, Bool.not_true, Bool.false_or] at k1
  have k2 := all5k_spec k1 h2
  rw [g2, Bool.not_true, Bool.false_or] at k2
  have k3 := all5k_spec k2 h3
  rw [g3, Bool.not_true, Bool.false_or] at k3
  have k4 := all5k_spec k3 h4
  rw [g4, Bool.not_true, Bool.false_or] at k4
  have k5 := all5k_spec k4 h5
  rw [g5, Bool.not_true, Bool.false_or] at k5
  exact k5

/-- **The fast certificate check.** -/
def bitOKF (m2 m3 m4 m5 : ℕ) (C : BitCert5) : Bool :=
  pinsOK5 RM m2 m3 m4 m5 C && Nat.blt (lamS C.pins) BL &&
    prunedAll m2 m3 m4 m5 (fun c1 c2 c3 c4 c5 => bitAtG m2 m3 m4 m5 C
      (filtRow 4 c5 (filtRow 3 c4 (filtRow 2 c3 (filtRow 1 c2 (filtRow 0 c1 C.pins)))))
      c1 c2 c3 c4 c5)

theorem bitOK5_of_fast {m2 m3 m4 m5 : ℕ} {C : BitCert5}
    (h : bitOKF m2 m3 m4 m5 C = true) : bitOK5 RM m2 m3 m4 m5 C = true := by
  simp only [bitOKF, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨hp, hL⟩, hall⟩ := h
  have hP : C.pins.all (BPin5.okb RM) = true := by
    simp only [pinsOK5, Bool.and_eq_true] at hp; exact hp.1.2
  simp only [bitOK5, hp, Bool.true_and]
  refine all5k_of fun c1 h1 => all5k_of fun c2 h2 => all5k_of fun c3 h3 =>
    all5k_of fun c4 h4 => all5k_of fun c5 h5 => ?_
  cases hv : bvalidR m2 m3 m4 m5 c1 c2 c3 c4 c5
  · unfold bitAt5; rw [← bvalidR_eq, hv]; rfl
  · exact bitAtG_sound hL (filt5_eq hP (Nat.lt_succ_of_le h1) (Nat.lt_succ_of_le h2)
      (Nat.lt_succ_of_le h3) (Nat.lt_succ_of_le h4) (Nat.lt_succ_of_le h5))
      (prunedAll_spec hall h1 h2 h3 h4 h5 hv)

/-! ### Pointwise classes -/

/-- **The fast pointwise check** at one code vector. -/
def ptAtF (m2 m3 m4 m5 : ℕ) (NM : List ℕ) (c1 c2 c3 c4 c5 : ℕ) : Bool :=
  !(bvalidR m2 m3 m4 m5 c1 c2 c3 c4 c5) ||
    Nat.ble (Nat.add (getR NM (nidxR (kHr c1) (kHr c2) (kHr c3) (kHr c4) (kHr c5)))
      (Nat.mul 1000000000 (kapMr (Nat.add 4 (kHr c1)) (Nat.add 4 (kHr c2))
      (Nat.add 4 (kHr c3)) (Nat.add 4 (kHr c4)) (Nat.add 4 (kHr c5))
      (nEr m2 c1 c2) (nEr m3 c2 c3) (nEr m4 c3 c4) (nEr m5 c4 c5))))
      (Nat.mul 1000000000 (kapPr (Nat.add 4 (kHr c1)) (Nat.add 4 (kHr c2))
      (Nat.add 4 (kHr c3)) (Nat.add 4 (kHr c4)) (Nat.add 4 (kHr c5))
      (nEr m2 c1 c2) (nEr m3 c2 c3) (nEr m4 c3 c4) (nEr m5 c4 c5)))

theorem ptAtF_eq (m2 m3 m4 m5 : ℕ) (NM : List ℕ) (c1 c2 c3 c4 c5 : ℕ) :
    ptAtF m2 m3 m4 m5 NM c1 c2 c3 c4 c5 = ptAt5 m2 m3 m4 m5 NM c1 c2 c3 c4 c5 := by
  unfold ptAtF ptAt5
  rw [bvalidR_eq, getR_eq, kapPr_eq, kapMr_eq, nidxR_eq]
  simp only [nEr_eq, kHr_eq, Nat.add_eq, Nat.mul_eq, ble_eq_decide]

/-- The fast pointwise check of a class. -/
def ptOKF (NM : List ℕ) (m2 m3 m4 m5 : ℕ) : Bool :=
  prunedAll m2 m3 m4 m5 (ptAtF m2 m3 m4 m5 NM)

theorem ptOK5_of_fast {NM : List ℕ} {m2 m3 m4 m5 : ℕ} (h : ptOKF NM m2 m3 m4 m5 = true) :
    ptOK5 NM m2 m3 m4 m5 = true := by
  unfold ptOK5
  refine all5k_of fun c1 h1 => all5k_of fun c2 h2 => all5k_of fun c3 h3 =>
    all5k_of fun c4 h4 => all5k_of fun c5 h5 => ?_
  rw [← ptAtF_eq]
  cases hv : bvalidR m2 m3 m4 m5 c1 c2 c3 c4 c5
  · unfold ptAtF; rw [hv]; rfl
  · exact prunedAll_spec h h1 h2 h3 h4 h5 hv

/-- The fast pointwise checks of a list of lists of classes. -/
theorem ptOK5_of_flatten {NM : List ℕ} {Ls : List (List (ℕ × ℕ × ℕ × ℕ))}
    (h : ∀ l ∈ Ls, l.all (fun x => ptOKF NM x.1 x.2.1 x.2.2.1 x.2.2.2) = true) :
    ∀ x ∈ List.flatten Ls, ptOK5 NM x.1 x.2.1 x.2.2.1 x.2.2.2 = true := by
  intro x hx
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.mp hx
  exact ptOK5_of_fast (List.all_eq_true.mp (h l hl) x hx)

end GridGen.Five.K5
