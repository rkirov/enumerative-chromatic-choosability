/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.K5.ExactDisp

/-!
# Height five at `k = 5`: a faster check of the exact certificates

The check `enumX` of `ExactDefs` with the same leaves, arranged for the kernel:

* every operation is a primitive `Nat` operation or a recursor (no instances to unfold);
* the penalty is carried down the enumeration as a bit mask of the pins still alive
  (`pinMask`: one mask per row and atom, the same closed term at every visit, so the kernel
  evaluates it once), and summed at the leaf (`sumL`);
* the five ray tests and the separable `Q` test read one packed linear form (`packD`) with five
  96-bit lanes, after a size check (`sumC c ≤ 2⁴⁰`); the `Q` test is rewritten as
  `D · L·c ≥ e · L·u + 5 · Σ_{j ≥ 1} (e uⱼ - D cⱼ)⁺`, since `U - L = (0, 5, …, 5)`;
* a pattern is checked in one enumeration of all five rows.

`patF_sound`: a passing fast check gives `XPass`, the hypothesis of `exact_seam55`. Nothing is
trusted: the fast check is a kernel computation, and its soundness is proved here.
-/

namespace GridGen.Five.K5

open Finset GridGen.Five GridGen.Five.Ex5

/-! ### Bits -/

/-- Bit `a` of `S`. -/
def tb (S a : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight S a) 1) 1

theorem Nat.beq_eq_false_of_ne' {a b : ℕ} (h : ¬a = b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem tb_eq (S a : ℕ) : tb S a = S.testBit a := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  unfold tb
  have e : Nat.land (Nat.shiftRight S a) 1 = S / 2 ^ a % 2 := by
    show (S >>> a) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [e]
  by_cases h : S / 2 ^ a % 2 = 1
  · rw [h]; simp
  · simp only [h, decide_false]
    exact Nat.beq_eq_false_of_ne' h

/-! ### Choices and the penalty mask -/

/-- `f` on all choices (a recursor, `= allC`). -/
def allR (f : Ch → Bool) (L : List Ch) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ r => cond (f x) r false) L

theorem allR_eq (f : Ch → Bool) : ∀ L : List Ch, allR f L = allC f L
  | [] => rfl
  | x :: L => by
    show cond (f x) (allR f L) false = (f x && allC f L)
    rw [allR_eq f L]; cases f x <;> rfl

/-- A pin's conditions on row `k` hold at atom `a` (rows `≥ 4` read row `4`, as in `penL`). -/
def okRow (cs : List (ℕ × ℕ)) (k a : ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun ks _ b => cond (Nat.beq (Nat.sub 4 ks.1) (Nat.sub 4 k)) (cond (tb ks.2 a) b false) b) cs

/-- The pins (first pin = bit `0`) whose conditions on row `k` hold at atom `a`. -/
def pinMask (cps : List (List (ℕ × ℕ) × ℕ)) (k a : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun cp _ acc => Nat.add (Nat.mul 2 acc) (cond (okRow cp.1 k a) 1 0)) cps

/-- All pins. -/
def fullM (cps : List (List (ℕ × ℕ) × ℕ)) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun _ _ acc => Nat.add (Nat.mul 2 acc) 1) cps

/-- The multipliers of the pins in a mask. -/
def sumL (cps : List (List (ℕ × ℕ) × ℕ)) (al : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun cp _ ih al => cond (Nat.beq (Nat.land al 1) 1) (Nat.add cp.2 (ih (Nat.shiftRight al 1)))
      (ih (Nat.shiftRight al 1))) cps al

/-- The mask after the rows `j < k`, with the atoms of `used` (last row first). -/
def alOf (cps : List (List (ℕ × ℕ) × ℕ)) (used : List ℕ) (k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (fullM cps)
    (fun j acc => acc &&& pinMask cps j (used.getD (k - 1 - j) 0)) k

theorem two_mul_add_div (x b : ℕ) (hb : b ≤ 1) : (2 * x + b) / 2 = x := by omega
theorem two_mul_add_mod (x b : ℕ) (hb : b ≤ 1) : (2 * x + b) % 2 = b := by omega

theorem cond_le_one (b : Bool) : (cond b 1 0 : ℕ) ≤ 1 := by cases b <;> simp

theorem two_mul_add_cond_mod (x : ℕ) (b : Bool) : (2 * x + cond b 1 0) % 2 = 1 ↔ b = true := by
  cases b <;> simp

theorem pinMask_cons (cp : List (ℕ × ℕ) × ℕ) (cps : List (List (ℕ × ℕ) × ℕ)) (k a : ℕ) :
    pinMask (cp :: cps) k a = 2 * pinMask cps k a + cond (okRow cp.1 k a) 1 0 := rfl

theorem fullM_cons (cp : List (ℕ × ℕ) × ℕ) (cps : List (List (ℕ × ℕ) × ℕ)) :
    fullM (cp :: cps) = 2 * fullM cps + 1 := rfl

theorem sumL_cons (cp : List (ℕ × ℕ) × ℕ) (cps : List (List (ℕ × ℕ) × ℕ)) (al : ℕ) :
    sumL (cp :: cps) al = (if al % 2 = 1 then cp.2 else 0) + sumL cps (al / 2) := by
  show cond (Nat.beq (Nat.land al 1) 1) (Nat.add cp.2 (sumL cps (Nat.shiftRight al 1)))
      (sumL cps (Nat.shiftRight al 1)) = _
  have e1 : Nat.land al 1 = al % 2 := Nat.and_one_is_mod al
  have e2 : Nat.shiftRight al 1 = al / 2 := by
    show al >>> 1 = _; rw [Nat.shiftRight_eq_div_pow]
  rw [e1, e2]
  by_cases h : al % 2 = 1
  · rw [h]; simp [Nat.add_eq]
  · have : Nat.beq (al % 2) 1 = false := Nat.beq_eq_false_of_ne' h
    rw [this]; simp [h]

/-- The conditions of a pin hold on the atoms of `used` (as in `penL`). -/
def firesU (cs : List (ℕ × ℕ)) (used : List ℕ) : Bool :=
  cs.all (fun ks => ks.2.testBit (used.getD (4 - ks.1) 0))

/-- The five rows. -/
def rows5 (cs : List (ℕ × ℕ)) (used : List ℕ) : Bool :=
  okRow cs 0 (used.getD 4 0) && okRow cs 1 (used.getD 3 0) && okRow cs 2 (used.getD 2 0) &&
    okRow cs 3 (used.getD 1 0) && okRow cs 4 (used.getD 0 0)

theorem okRow_cons (ks : ℕ × ℕ) (cs : List (ℕ × ℕ)) (k a : ℕ) :
    okRow (ks :: cs) k a = if 4 - ks.1 = 4 - k then (ks.2.testBit a && okRow cs k a)
      else okRow cs k a := by
  show cond (Nat.beq (Nat.sub 4 ks.1) (Nat.sub 4 k)) (cond (tb ks.2 a) (okRow cs k a) false)
    (okRow cs k a) = _
  rw [tb_eq]
  by_cases h : 4 - ks.1 = 4 - k
  · have : Nat.beq (Nat.sub 4 ks.1) (Nat.sub 4 k) = true := Nat.beq_eq_true_eq _ _ ▸ h
    rw [this]; simp only [h, ↓reduceIte]; cases ks.2.testBit a <;> rfl
  · have : Nat.beq (Nat.sub 4 ks.1) (Nat.sub 4 k) = false := Nat.beq_eq_false_of_ne' h
    rw [this]; simp only [h, ↓reduceIte]; rfl

theorem rows5_eq (used : List ℕ) : ∀ cs : List (ℕ × ℕ), rows5 cs used = firesU cs used
  | [] => rfl
  | ks :: cs => by
    have ih := rows5_eq used cs
    unfold rows5 at ih ⊢
    simp only [okRow_cons, firesU, List.all_cons] at ih ⊢
    rw [← ih]
    obtain ⟨r, S⟩ := ks
    simp only
    rcases Nat.lt_or_ge r 4 with h | h
    · interval_cases r <;> simp <;> (try (cases S.testBit _ <;> simp))
    · have e : 4 - r = 0 := by omega
      simp only [e]
      simp; try (cases S.testBit _ <;> simp)

/-- The penalty from the mask of the five rows. -/
theorem sumL_alOf5 (used : List ℕ) : ∀ cps : List (List (ℕ × ℕ) × ℕ),
    sumL cps (alOf cps used 5) = penL cps used
  | [] => rfl
  | cp :: cps => by
    have ih := sumL_alOf5 used cps
    have ea : alOf (cp :: cps) used 5 = (2 * fullM cps + 1)
        &&& (2 * pinMask cps 0 (used.getD 4 0) + cond (okRow cp.1 0 (used.getD 4 0)) 1 0)
        &&& (2 * pinMask cps 1 (used.getD 3 0) + cond (okRow cp.1 1 (used.getD 3 0)) 1 0)
        &&& (2 * pinMask cps 2 (used.getD 2 0) + cond (okRow cp.1 2 (used.getD 2 0)) 1 0)
        &&& (2 * pinMask cps 3 (used.getD 1 0) + cond (okRow cp.1 3 (used.getD 1 0)) 1 0)
        &&& (2 * pinMask cps 4 (used.getD 0 0) + cond (okRow cp.1 4 (used.getD 0 0)) 1 0) := rfl
    have eb : alOf cps used 5 = fullM cps &&& pinMask cps 0 (used.getD 4 0)
        &&& pinMask cps 1 (used.getD 3 0) &&& pinMask cps 2 (used.getD 2 0)
        &&& pinMask cps 3 (used.getD 1 0) &&& pinMask cps 4 (used.getD 0 0) := rfl
    rw [sumL_cons, ea]
    simp only [Nat.and_div_two, two_mul_add_div _ _ (cond_le_one _),
      two_mul_add_div _ _ (le_refl 1)]
    rw [← eb, ih]
    have hb : ((2 * fullM cps + 1)
        &&& (2 * pinMask cps 0 (used.getD 4 0) + cond (okRow cp.1 0 (used.getD 4 0)) 1 0)
        &&& (2 * pinMask cps 1 (used.getD 3 0) + cond (okRow cp.1 1 (used.getD 3 0)) 1 0)
        &&& (2 * pinMask cps 2 (used.getD 2 0) + cond (okRow cp.1 2 (used.getD 2 0)) 1 0)
        &&& (2 * pinMask cps 3 (used.getD 1 0) + cond (okRow cp.1 3 (used.getD 1 0)) 1 0)
        &&& (2 * pinMask cps 4 (used.getD 0 0) + cond (okRow cp.1 4 (used.getD 0 0)) 1 0)) % 2 = 1
        ↔ rows5 cp.1 used = true := by
      simp only [Nat.and_mod_two_eq_one, two_mul_add_cond_mod, two_mul_add_mod _ _ (le_refl 1),
        rows5, Bool.and_eq_true, true_and]
    have hpen : penL (cp :: cps) used = (if firesU cp.1 used then cp.2 else 0) + penL cps used := by
      unfold penL firesU; rfl
    rw [hpen, ← rows5_eq]
    by_cases h : rows5 cp.1 used = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (hb.mpr h)), ite_eq_left_of_eq_true _ _ (eq_true h)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h' => h (hb.mp h')), ite_eq_right_of_eq_false _ _ (eq_false h)]

/-! ### Venn digits -/

/-- The packed Venn data, unpacked with shifts and masks. -/
def unpackF (P : ℕ) : Ex5.V5 :=
  ⟨Nat.land P 15, Nat.land (Nat.shiftRight P 4) 15, Nat.land (Nat.shiftRight P 8) 15,
    Nat.land (Nat.shiftRight P 12) 15, Nat.land (Nat.shiftRight P 16) 15,
    Nat.land (Nat.shiftRight P 20) 15, Nat.land (Nat.shiftRight P 24) 15,
    Nat.land (Nat.shiftRight P 28) 15, Nat.land (Nat.shiftRight P 32) 15,
    Nat.land (Nat.shiftRight P 36) 15, Nat.land (Nat.shiftRight P 40) 15,
    Nat.land (Nat.shiftRight P 44) 15, Nat.land (Nat.shiftRight P 48) 15,
    Nat.land (Nat.shiftRight P 52) 15, Nat.land (Nat.shiftRight P 56) 15,
    Nat.land (Nat.shiftRight P 60) 15, Nat.land (Nat.shiftRight P 64) 15,
    Nat.land (Nat.shiftRight P 68) 15, Nat.land (Nat.shiftRight P 72) 15,
    Nat.land (Nat.shiftRight P 76) 15, Nat.land (Nat.shiftRight P 80) 15,
    Nat.land (Nat.shiftRight P 84) 15, Nat.land (Nat.shiftRight P 88) 15,
    Nat.land (Nat.shiftRight P 92) 15, Nat.land (Nat.shiftRight P 96) 15,
    Nat.land (Nat.shiftRight P 100) 15, Nat.land (Nat.shiftRight P 104) 15,
    Nat.land (Nat.shiftRight P 108) 15, Nat.land (Nat.shiftRight P 112) 15,
    Nat.land (Nat.shiftRight P 116) 15, Nat.land (Nat.shiftRight P 120) 15⟩

theorem digit_shift (P i : ℕ) : Nat.land (Nat.shiftRight P (4 * i)) 15 = digit P i := by
  show (P >>> (4 * i)) &&& (2 ^ 4 - 1) = Nat.mod (Nat.div P (Nat.pow 16 i)) 16
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  rfl

theorem unpackF_eq (P : ℕ) : unpackF P = unpack P := by
  simp only [unpackF, unpack, ← digit_shift]
  rfl

/-! ### The cone test, packed -/

/-- The sum of the orbit counts. -/
def sumC (c : C11) : ℕ :=
  Nat.add c.c0 <| Nat.add c.c1 <| Nat.add c.c2 <| Nat.add c.c3 <| Nat.add c.c4 <| Nat.add c.c5 <|
    Nat.add c.c6 <| Nat.add c.c7 <| Nat.add c.c8 <| Nat.add c.c9 c.c10

/-- The dot product, with primitive operations. -/
def dotR (a b : C11) : ℕ :=
  Nat.add (Nat.mul a.c0 b.c0) <| Nat.add (Nat.mul a.c1 b.c1) <| Nat.add (Nat.mul a.c2 b.c2) <|
  Nat.add (Nat.mul a.c3 b.c3) <| Nat.add (Nat.mul a.c4 b.c4) <| Nat.add (Nat.mul a.c5 b.c5) <|
  Nat.add (Nat.mul a.c6 b.c6) <| Nat.add (Nat.mul a.c7 b.c7) <| Nat.add (Nat.mul a.c8 b.c8) <|
  Nat.add (Nat.mul a.c9 b.c9) (Nat.mul a.c10 b.c10)

theorem dotR_eq (a b : C11) : dotR a b = dot11 a b := by
  simp only [dotR, dot11, Nat.add_eq, Nat.mul_eq]; ring

/-- The lower edges of `Q` as an orbit vector. -/
def QL : C11 := ⟨1000000, 976588, 979400, 948370, 955997, 917963, 925589, 956703, 953806, 936105,
  933215⟩

/-- Lane `d` of the packed form: the rays `1, …, 4` and `QL`. -/
def lrow (d : ℕ) : C11 :=
  match d with
  | 0 => FC 1
  | 1 => FC 2
  | 2 => FC 3
  | 3 => FC 4
  | _ => QL

/-- The packed linear form: `Σ_d (lrow d · c) 2^(96 d)`. -/
def packD (c : C11) : ℕ :=
  Nat.add (Nat.mul c.c0 39402006196394479212279060943047386327578524756517438095686275486852815458151016580440836337601866696414964141012430094805) <|
  Nat.add (Nat.mul c.c1 38479526427324491664961183568343192920905588201386841911064873652167562533736559002193626823561871898110880662807077978571) <|
  Nat.add (Nat.mul c.c2 38590324868748752940506112287693930525519806972219773959117934465671079050588680431878072700113213690943514556701444407756) <|
  Nat.add (Nat.mul c.c3 37367680616474632250549093026718836377638339430166629801427514046755617242231402996734005121092498094985159947229404856767) <|
  Nat.add (Nat.mul c.c4 37668199717734532943501145424485875021724793006557282902872864700789961685668627431426414689429173656442585208869170971074) <|
  Nat.add (Nat.mul c.c5 36169583814060865321141323620655434774166477994093192052531529647856653212238203942052029414450630830521758805723533279666) <|
  Nat.add (Nat.mul c.c6 36470063513314569619614163739382373274639126490744574688530212353597593409953656879533827568521051507063543260735309087157) <|
  Nat.add (Nat.mul c.c7 37696017534109187445825014441487737066567680082114109681987815786844194309943674394770147615632397750652616472265106653634) <|
  Nat.add (Nat.mul c.c8 37581869922158232639547042001966629674292570182225516332720904010716134455737041387782837856724170425273623169684991902145) <|
  Nat.add (Nat.mul c.c9 36884415010475853963010490344214481551736572457294986476312810662249266393824881240628606806676254515012448501210101580217) <|
    Nat.mul c.c10 36770543212568273918087003858109311775111774987395957324528895059338533607669109817015625722591472183605327715747084894648

/-- Lane `d` of a packed number. -/
def laneW (X d : ℕ) : ℕ := Nat.mod (Nat.div X (Nat.pow 79228162514264337593543950336 d))
  79228162514264337593543950336

/-- The negative parts `(e uⱼ - D cⱼ)⁺`, `j ≥ 1`. -/
def negQ (D e : ℕ) (u c : C11) : ℕ :=
  Nat.add (Nat.sub (Nat.mul e u.c1) (Nat.mul D c.c1)) <|
  Nat.add (Nat.sub (Nat.mul e u.c2) (Nat.mul D c.c2)) <|
  Nat.add (Nat.sub (Nat.mul e u.c3) (Nat.mul D c.c3)) <|
  Nat.add (Nat.sub (Nat.mul e u.c4) (Nat.mul D c.c4)) <|
  Nat.add (Nat.sub (Nat.mul e u.c5) (Nat.mul D c.c5)) <|
  Nat.add (Nat.sub (Nat.mul e u.c6) (Nat.mul D c.c6)) <|
  Nat.add (Nat.sub (Nat.mul e u.c7) (Nat.mul D c.c7)) <|
  Nat.add (Nat.sub (Nat.mul e u.c8) (Nat.mul D c.c8)) <|
  Nat.add (Nat.sub (Nat.mul e u.c9) (Nat.mul D c.c9)) (Nat.sub (Nat.mul e u.c10) (Nat.mul D c.c10))

/-- **The packed cone test.** -/
def okcF (D : ℕ) (u c : C11) (e : ℕ) : Bool :=
  Nat.ble (sumC c) 1099511627776 && Nat.ble (Nat.mul e (dotR u (FC 0))) (Nat.mul D (sumC c)) &&
  (match packD c with
   | X => Nat.ble (Nat.mul e (dotR u (FC 1))) (Nat.mul D (laneW X 0)) &&
     Nat.ble (Nat.mul e (dotR u (FC 2))) (Nat.mul D (laneW X 1)) &&
     Nat.ble (Nat.mul e (dotR u (FC 3))) (Nat.mul D (laneW X 2)) &&
     Nat.ble (Nat.mul e (dotR u (FC 4))) (Nat.mul D (laneW X 3)) &&
     Nat.ble (Nat.add (Nat.mul e (dotR u QL)) (Nat.mul 5 (negQ D e u c))) (Nat.mul D (laneW X 4)))

theorem packD_eq (c : C11) : packD c = dotR c (lrow 0) + 79228162514264337593543950336 *
    (dotR c (lrow 1) + 79228162514264337593543950336 * (dotR c (lrow 2) +
      79228162514264337593543950336 * (dotR c (lrow 3) + 79228162514264337593543950336 *
        dotR c (lrow 4)))) := by
  simp only [packD, dotR, lrow, FC, QL, Nat.add_eq, Nat.mul_eq]
  ring

theorem lrow_le (c : C11) (hc : sumC c ≤ 1099511627776) (d : ℕ) :
    dotR c (lrow d) < 2 ^ 96 := by
  have hs : c.c0 + c.c1 + c.c2 + c.c3 + c.c4 + c.c5 + c.c6 + c.c7 + c.c8 + c.c9 + c.c10
      ≤ 1099511627776 := by
    simp only [sumC, Nat.add_eq] at hc; omega
  have key : ∀ r : C11, r.c0 ≤ 41910174805 → r.c1 ≤ 41910174805 → r.c2 ≤ 41910174805 →
      r.c3 ≤ 41910174805 → r.c4 ≤ 41910174805 → r.c5 ≤ 41910174805 → r.c6 ≤ 41910174805 →
      r.c7 ≤ 41910174805 → r.c8 ≤ 41910174805 → r.c9 ≤ 41910174805 → r.c10 ≤ 41910174805 →
      dotR c r < 2 ^ 96 := by
    intro r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simp only [dotR, Nat.add_eq, Nat.mul_eq]
    have := Nat.mul_le_mul_left c.c0 h0
    have := Nat.mul_le_mul_left c.c1 h1
    have := Nat.mul_le_mul_left c.c2 h2
    have := Nat.mul_le_mul_left c.c3 h3
    have := Nat.mul_le_mul_left c.c4 h4
    have := Nat.mul_le_mul_left c.c5 h5
    have := Nat.mul_le_mul_left c.c6 h6
    have := Nat.mul_le_mul_left c.c7 h7
    have := Nat.mul_le_mul_left c.c8 h8
    have := Nat.mul_le_mul_left c.c9 h9
    have := Nat.mul_le_mul_left c.c10 h10
    have hs' := Nat.mul_le_mul_right 41910174805 hs
    norm_num at hs' ⊢
    nlinarith
  rcases d with _ | _ | _ | _ | d <;>
    refine key _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num [lrow, FC, QL]

theorem lane_gen (B y0 y1 y2 y3 y4 : ℕ) (hB : 0 < B) (h0 : y0 < B) (h1 : y1 < B) (h2 : y2 < B)
    (h3 : y3 < B) (h4 : y4 < B) :
    let X := y0 + B * (y1 + B * (y2 + B * (y3 + B * y4)))
    X / B ^ 0 % B = y0 ∧ X / B ^ 1 % B = y1 ∧ X / B ^ 2 % B = y2 ∧ X / B ^ 3 % B = y3 ∧
      X / B ^ 4 % B = y4 := by
  intro X
  have d1 : X / B = y1 + B * (y2 + B * (y3 + B * y4)) := by
    simp only [X]; rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt h0, zero_add]
  have d2 : X / B / B = y2 + B * (y3 + B * y4) := by
    rw [d1, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt h1, zero_add]
  have d3 : X / B / B / B = y3 + B * y4 := by
    rw [d2, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt h2, zero_add]
  have d4 : X / B / B / B / B = y4 := by
    rw [d3, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt h3, zero_add]
  have p2 : ∀ Y : ℕ, Y / B ^ 2 = Y / B / B := fun Y => by rw [pow_two, Nat.div_div_eq_div_mul]
  have p3 : ∀ Y : ℕ, Y / B ^ 3 = Y / B / B / B := fun Y => by
    rw [pow_succ, ← Nat.div_div_eq_div_mul, p2]
  have p4 : ∀ Y : ℕ, Y / B ^ 4 = Y / B / B / B / B := fun Y => by
    rw [pow_succ, ← Nat.div_div_eq_div_mul, p3]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [pow_zero, Nat.div_one]; simp only [X]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
  · rw [pow_one, d1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
  · rw [p2, d2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]
  · rw [p3, d3, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h3]
  · rw [p4, d4, Nat.mod_eq_of_lt h4]

theorem lane_of (y0 y1 y2 y3 y4 : ℕ) (h0 : y0 < 2 ^ 96) (h1 : y1 < 2 ^ 96) (h2 : y2 < 2 ^ 96)
    (h3 : y3 < 2 ^ 96) (h4 : y4 < 2 ^ 96) :
    let X := y0 + 79228162514264337593543950336 * (y1 + 79228162514264337593543950336 *
      (y2 + 79228162514264337593543950336 * (y3 + 79228162514264337593543950336 * y4)))
    laneW X 0 = y0 ∧ laneW X 1 = y1 ∧ laneW X 2 = y2 ∧ laneW X 3 = y3 ∧ laneW X 4 = y4 := by
  have hW : (2 : ℕ) ^ 96 = 79228162514264337593543950336 := by norm_num
  rw [hW] at h0 h1 h2 h3 h4
  exact lane_gen _ _ _ _ _ _ (by norm_num) h0 h1 h2 h3 h4

/-- The difference of the two accumulators of `qterm`. -/
theorem qterm_diff (L U a b : ℕ) (acc : ℕ × ℕ) :
    ((qterm L U a b acc).1 : ℤ) - (qterm L U a b acc).2
      = (acc.1 : ℤ) - acc.2 + L * ((a : ℤ) - b) - ((U : ℤ) - L) * ((b - a : ℕ) : ℤ) := by
  unfold qterm
  by_cases h : b ≤ a
  · have hb : Nat.ble b a = true := Nat.ble_eq.mpr h
    rw [hb]
    simp only [Bool.cond_true, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
    have : b - a = 0 := by omega
    rw [this]; push_cast [h]; ring
  · have hb : Nat.ble b a = false := by
      rw [Bool.eq_false_iff]; intro hh; exact h (Nat.ble_eq.mp hh)
    rw [hb]
    simp only [Bool.cond_false, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
    push_cast [show a ≤ b by omega]; ring

theorem qtest_of (D : ℕ) (u c : C11) (e : ℕ)
    (h : e * dot11 u QL + 5 * negQ D e u c ≤ D * dot11 c QL) : qtestQ D u c e = true := by
  unfold qtestQ
  rw [Nat.ble_eq]
  have key : ((qacc D u c e).1 : ℤ) - (qacc D u c e).2
      = (D : ℤ) * dot11 c QL - e * dot11 u QL - 5 * negQ D e u c := by
    simp only [qacc, qterm_diff]
    simp only [negQ, dot11, QL, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
    push_cast
    ring
  have h' : (e : ℤ) * dot11 u QL + 5 * negQ D e u c ≤ D * dot11 c QL := by exact_mod_cast h
  have : ((qacc D u c e).2 : ℤ) ≤ (qacc D u c e).1 := by linarith
  exact_mod_cast this

theorem okcF_sound {D : ℕ} {u c : C11} {e : ℕ} (h : okcF D u c e = true) : okcC D u c e = true := by
  unfold okcF at h
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨hs, h0⟩, ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hq⟩⟩ := h
  obtain ⟨l0, l1, l2, l3, l4⟩ := lane_of _ _ _ _ _ (lrow_le c hs 0) (lrow_le c hs 1)
    (lrow_le c hs 2) (lrow_le c hs 3) (lrow_le c hs 4)
  rw [← packD_eq] at l0 l1 l2 l3 l4
  rw [l0] at h1; rw [l1] at h2; rw [l2] at h3; rw [l3] at h4; rw [l4] at hq
  simp only [dotR_eq, lrow, Nat.mul_eq, Nat.add_eq] at h0 h1 h2 h3 h4 hq
  have hs0 : sumC c = dot11 c (FC 0) := by
    simp only [sumC, dot11, FC, Nat.add_eq]; ring
  rw [hs0] at h0
  unfold okcC
  simp only [Bool.and_eq_true, Nat.ble_eq]
  exact ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, qtest_of D u c e hq⟩

/-! ### The enumeration -/

/-- **The fast enumeration**: rows `k, k+1, …`, with the packed Venn data `P`, the atoms `used`
and the mask `al` of the pins alive. -/
def enumF (D K : ℕ) (u : C11) (cps : List (List (ℕ × ℕ) × ℕ)) (L : List (List Ch)) :
    ℕ → List ℕ → ℕ → ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → List ℕ → ℕ → ℕ → Bool)
    (fun P _ al _ => forceN (Nat.sub (Nat.add D K) (sumL cps al)) fun e =>
      okcF D u (clsV (unpackF P)) e)
    (fun C _ ih P used al k => allR (fun c => cond (Nat.blt (Ex5.cnt c.1 used) c.2.1)
      (forceN (Nat.land al (pinMask cps k c.1)) fun al' =>
        ih (Nat.sub P c.2.2.1) (c.1 :: used) al' (Nat.succ k)) true) C) L

theorem alOf_succ (cps : List (List (ℕ × ℕ) × ℕ)) (a : ℕ) (used : List ℕ) (k : ℕ) :
    alOf cps (a :: used) (k + 1) = Nat.land (alOf cps used k) (pinMask cps k a) := by
  have hc : ∀ m ≤ k, alOf cps (a :: used) (k + 1) = alOf cps (a :: used) (k + 1) →
      (Nat.rec (motive := fun _ => ℕ) (fullM cps)
        (fun j acc => Nat.land acc (pinMask cps j ((a :: used).getD (k + 1 - 1 - j) 0))) m : ℕ)
      = Nat.rec (motive := fun _ => ℕ) (fullM cps)
        (fun j acc => Nat.land acc (pinMask cps j (used.getD (k - 1 - j) 0))) m := by
    intro m hm _
    induction m with
    | zero => rfl
    | succ m ih =>
      show Nat.land _ _ = Nat.land _ _
      rw [ih (by omega)]
      congr 2
      have e : k + 1 - 1 - m = (k - 1 - m) + 1 := by omega
      rw [e]; rfl
  show Nat.land (Nat.rec (motive := fun _ => ℕ) (fullM cps)
      (fun j acc => Nat.land acc (pinMask cps j ((a :: used).getD (k + 1 - 1 - j) 0))) k : ℕ)
      (pinMask cps k ((a :: used).getD (k + 1 - 1 - k) 0)) = _
  rw [hc k le_rfl rfl]
  have e : k + 1 - 1 - k = 0 := by omega
  rw [e]; rfl

theorem enumF_sound {D K : ℕ} {u : C11} {cps : List (List (ℕ × ℕ) × ℕ)} :
    ∀ (L : List (List Ch)) (P : ℕ) (used : List ℕ) (k : ℕ), k + L.length = 5 →
      enumF D K u cps L P used (alOf cps used k) k = true → enumX D K u cps L P used = true
  | [], P, used, k, hk, h => by
    simp only [List.length_nil, add_zero] at hk
    subst hk
    change forceN (Nat.sub (Nat.add D K) (sumL cps (alOf cps used 5))) (fun e =>
      okcF D u (clsV (unpackF P)) e) = true at h
    rw [forceN_eq, sumL_alOf5, unpackF_eq] at h
    show forceN (penL cps used) (fun pen => okc55 D u P (Nat.sub (Nat.add D K) pen)) = true
    rw [forceN_eq, okc55_eq]
    exact okcF_sound h
  | C :: Cs, P, used, k, hk, h => by
    have h' : allR (fun c => cond (Nat.blt (Ex5.cnt c.1 used) c.2.1)
        (forceN (Nat.land (alOf cps used k) (pinMask cps k c.1)) fun al' =>
          enumF D K u cps Cs (Nat.sub P c.2.2.1) (c.1 :: used) al' (Nat.succ k)) true) C = true := h
    rw [allR_eq, allC_iff] at h'
    unfold enumX
    rw [allC_iff]
    intro x hx
    have hx' := h' x hx
    by_cases hc : Nat.blt (Ex5.cnt x.1 used) x.2.1 = true
    · rw [hc] at hx' ⊢
      rw [Bool.cond_true, forceN_eq, ← alOf_succ] at hx'
      simp only [Bool.not_true, Bool.false_or]
      exact enumF_sound Cs _ _ (k + 1) (by simp at hk; omega) hx'
    · simp only [Bool.not_eq_true] at hc
      rw [hc]; rfl

/-! ### Patterns and certificates -/

/-- `pdOk` with the block of each row evaluated once, so that the corrections `vecP b m` are the
same closed terms in every pattern (and evaluated once). -/
def pdOkF (sp : Spec5) (pd : PatD) : Bool :=
  Nat.blt pd.p 15 && Nat.beq pd.chs.length 5 &&
  Nat.beq pd.eqc (eqcOf sp.ppins (canons.getD pd.p (0, 1, 0, 1, 0))) &&
  (List.range 5).all (fun k =>
    (pd.chs.getD k []).contains (0, 5, 0, 0) &&
    (!repB (canons.getD pd.p (0, 1, 0, 1, 0)) k ||
      forceN (blkOf (canons.getD pd.p (0, 1, 0, 1, 0)) k) fun b =>
        sp.atoms.all (fun a => Nat.beq (Nat.land a.1 b) 0 ||
          (pd.chs.getD k []).contains (a.1, a.2, vecP b a.1, pincOf sp.rpins b a.1))))

theorem pdOkF_eq (sp : Spec5) (pd : PatD) : pdOkF sp pd = pdOk sp pd := by
  simp only [pdOkF, pdOk, forceN_eq]

/-- **The fast check of one pattern**: its cheap part, and all its column types. -/
def patF (sp : XSpec) (pc : PatD × List (List (ℕ × ℕ) × ℕ)) : Bool :=
  pdOkF sp.toSpec5 pc.1 &&
    decide (compileX (canons.getD pc.1.p (0, 1, 0, 1, 0)) sp.pins = pc.2) &&
    enumF sp.D sp.K (urow55 pc.1.p) pc.2 pc.1.chs sp.vennP [] (fullM pc.2) 0

theorem subOK_of {sp : XSpec} {pc : PatD × List (List (ℕ × ℕ) × ℕ)}
    (h5 : pc.1.chs.length = 5)
    (h : enumX sp.D sp.K (urow55 pc.1.p) pc.2 pc.1.chs sp.vennP [] = true) {i j : ℕ}
    (hi : i < (pc.1.chs.getD 0 []).length) (hj : j < (pc.1.chs.getD 1 []).length) :
    subOK sp pc i j = true := by
  have hL := five_lists h5
  rw [hL] at h
  unfold subOK
  by_cases c0 : Nat.blt (Ex5.cnt ((pc.1.chs.getD 0 []).getD i ch0).1 [])
      ((pc.1.chs.getD 0 []).getD i ch0).2.1 = true
  · by_cases c1 : Nat.blt (Ex5.cnt ((pc.1.chs.getD 1 []).getD j ch0).1
        [((pc.1.chs.getD 0 []).getD i ch0).1]) ((pc.1.chs.getD 1 []).getD j ch0).2.1 = true
    · rw [c0, c1]
      simp only [Bool.not_true, Bool.false_or]
      have m0 : (pc.1.chs.getD 0 []).getD i ch0 ∈ pc.1.chs.getD 0 [] := by
        rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
      have m1 : (pc.1.chs.getD 1 []).getD j ch0 ∈ pc.1.chs.getD 1 [] := by
        rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
      have e1 := enumX_step h m0 c0
      have e2 := enumX_step e1 m1 c1
      rw [hL]
      exact e2
    · simp only [Bool.not_eq_true] at c1
      rw [c1]; simp
  · simp only [Bool.not_eq_true] at c0
    rw [c0]; simp

theorem pdOk_len {sp : XSpec} {pc : PatD × List (List (ℕ × ℕ) × ℕ)} (h : hdrOK sp pc = true) :
    pc.1.chs.length = 5 := by
  simp only [hdrOK, pdOk, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨-, hlen⟩, -⟩, -⟩, -⟩ := h
  exact hlen

/-- **A certificate passes** when its scalar conditions and the fast checks of its patterns do. -/
theorem xpass_fast {sp : XSpec} (hspec : specOkX sp = true) (hpat : sp.pds.all (patF sp) = true) :
    XPass sp := by
  refine ⟨hspec, fun pc hpc => ?_⟩
  have h := List.all_eq_true.mp hpat pc hpc
  simp only [patF, pdOkF_eq, Bool.and_eq_true] at h
  obtain ⟨⟨hpd, hcx⟩, hen⟩ := h
  have hhdr : hdrOK sp pc = true := by
    simp only [hdrOK, hpd, hcx, Bool.and_self]
  refine ⟨hhdr, fun i hi j hj => subOK_of (pdOk_len hhdr) ?_ hi hj⟩
  exact enumF_sound pc.1.chs _ [] 0 (by rw [pdOk_len hhdr]) hen

end GridGen.Five.K5
