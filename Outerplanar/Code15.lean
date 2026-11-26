/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.SevenMarks

/-!
# The codes of the fifteen-face centroid and their scales

A term of the centroid face gives each side a pure type `PT k r` (`Outerplanar/FifteenTerm.lean`).
Ten **codes** (`C15`) matter: the constant `I`, the one- to four-mark tables `L1 L2 T3 T4`, the
ball parts `B5 B6 B7` and the hexagon parts `H6 H7`. A code has a hexagon scale, a matching scale
(for `I L1 L2`) and a ball scale (all but `H6 H7`), and belongs to some of the list classes of the
closings `U1a … U3` (`Outerplanar/Sq15Sound.lean`).

The scales are **exponent vectors** (`Sc`): `A^{a/3} q^{b/3} K^{c/3}` with `A = 17/16`,
`q = 32/27`, `K = 59/56`, stored as natural numbers for the numerator and the denominator. A
product of scales adds the vectors (`Sc.val_add`), and **`Sc.ge1`** decides `≥ 1` by an integer
power inequality (the cube of the scale; `Sc.ge1_sound`), so the kernel needs no logarithms.

The capabilities of a code (`cap_hex15`, `cap_M15`, `cap_B15`, `cap_I15`, `cap_ABf`, `cap_BAHf`,
`cap_Bf5`, `cap_Bf6`, `cap_H7f`) are read off the pure types.

Formalized by Claude (milestone M5 of `ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`).
-/

namespace Outerplanar.F15

open Finset Outerplanar Outerplanar.SqMulti

/-! ### Exponent vectors -/

/-- `κ_K = (59/56)^{1/3}`. -/
noncomputable def κK : ℝ := (59 / 56 : ℝ) ^ ((1 : ℝ) / 3)

theorem κK_cube : κK ^ 3 = 59 / 56 := rpow_third_cube (by norm_num)

theorem κK_pos : 0 < κK := Real.rpow_pos_of_pos (by norm_num) _

/-- An exponent vector: the scale `κA^ap κq^qp κK^kp / (κA^an κq^qn κK^kn)`. -/
structure Sc where
  ap : ℕ
  qp : ℕ
  kp : ℕ
  an : ℕ
  qn : ℕ
  kn : ℕ
  deriving DecidableEq

namespace Sc

/-- The product of two scales. -/
def add (s t : Sc) : Sc :=
  ⟨s.ap + t.ap, s.qp + t.qp, s.kp + t.kp, s.an + t.an, s.qn + t.qn, s.kn + t.kn⟩

/-- The numerator of the scale. -/
noncomputable def num (s : Sc) : ℝ := κA ^ s.ap * κq ^ s.qp * κK ^ s.kp

/-- The denominator of the scale. -/
noncomputable def den (s : Sc) : ℝ := κA ^ s.an * κq ^ s.qn * κK ^ s.kn

/-- The value of a scale. -/
noncomputable def val (s : Sc) : ℝ := s.num / s.den

/-- **The decision `scale ≥ 1`** (cubed, cross-multiplied). -/
def ge1 (s : Sc) : Bool :=
  Nat.ble (16 ^ s.ap * 27 ^ s.qp * 56 ^ s.kp * (17 ^ s.an * 32 ^ s.qn * 59 ^ s.kn))
    (17 ^ s.ap * 32 ^ s.qp * 59 ^ s.kp * (16 ^ s.an * 27 ^ s.qn * 56 ^ s.kn))

theorem num_pos (s : Sc) : 0 < s.num := by
  unfold num; have := κA_pos; have := κq_pos; have := κK_pos; positivity

theorem den_pos (s : Sc) : 0 < s.den := by
  unfold den; have := κA_pos; have := κq_pos; have := κK_pos; positivity

theorem val_pos (s : Sc) : 0 < s.val := div_pos s.num_pos s.den_pos

theorem val_add (s t : Sc) : (s.add t).val = s.val * t.val := by
  unfold val num den add
  simp only [pow_add]
  have := κA_pos; have := κq_pos; have := κK_pos
  field_simp

theorem num_cube (s : Sc) :
    s.num ^ 3 = (17 / 16) ^ s.ap * (32 / 27) ^ s.qp * (59 / 56) ^ s.kp := by
  unfold num
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm s.ap, mul_comm s.qp,
    mul_comm s.kp, pow_mul, pow_mul, pow_mul, κA_cube, κq_cube, κK_cube]

theorem den_cube (s : Sc) :
    s.den ^ 3 = (17 / 16) ^ s.an * (32 / 27) ^ s.qn * (59 / 56) ^ s.kn := by
  unfold den
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm s.an, mul_comm s.qn,
    mul_comm s.kn, pow_mul, pow_mul, pow_mul, κA_cube, κq_cube, κK_cube]

/-- **`ge1` is sound.** -/
theorem ge1_sound {s : Sc} (h : s.ge1 = true) : 1 ≤ s.val := by
  have hle := Nat.le_of_ble_eq_true h
  have hR : ((16 ^ s.ap * 27 ^ s.qp * 56 ^ s.kp * (17 ^ s.an * 32 ^ s.qn * 59 ^ s.kn) : ℕ) : ℝ)
      ≤ ((17 ^ s.ap * 32 ^ s.qp * 59 ^ s.kp * (16 ^ s.an * 27 ^ s.qn * 56 ^ s.kn) : ℕ) : ℝ) := by
    exact_mod_cast hle
  push_cast at hR
  have hc : s.den ^ 3 ≤ s.num ^ 3 := by
    rw [num_cube, den_cube]
    simp only [div_pow]
    rw [div_mul_div_comm, div_mul_div_comm, div_mul_div_comm, div_mul_div_comm,
      div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hd := s.den_pos
  have hn := s.num_pos
  rw [val, le_div_iff₀ hd, one_mul]
  exact (pow_le_pow_iff_left₀ hd.le hn.le (by norm_num : (3 : ℕ) ≠ 0)).mp hc

/-- The unit scale. -/
def one : Sc := ⟨0, 0, 0, 0, 0, 0⟩

/-- `A = 17/16`. -/
def A : Sc := ⟨3, 0, 0, 0, 0, 0⟩

/-- `κ_A = A^{1/3}`. -/
def kA : Sc := ⟨1, 0, 0, 0, 0, 0⟩

/-- `κ_q = q^{1/3}`. -/
def kq : Sc := ⟨0, 1, 0, 0, 0, 0⟩

/-- `A^{4/3}`. -/
def a5 : Sc := ⟨4, 0, 0, 0, 0, 0⟩

/-- `D₆ = A^{4/3}/K`. -/
def d6 : Sc := ⟨4, 0, 0, 0, 0, 3⟩

/-- `1/K = 56/59`. -/
def kInv : Sc := ⟨0, 0, 0, 0, 0, 3⟩

/-- `1/A = 16/17`. -/
def aInv : Sc := ⟨0, 0, 0, 3, 0, 0⟩

theorem val_one : one.val = 1 := by simp [val, num, den, one]

theorem val_A : A.val = 17 / 16 := by simp [val, num, den, A, κA_cube]

theorem val_kA : kA.val = κA := by simp [val, num, den, kA]

theorem val_kq : kq.val = κq := by simp [val, num, den, kq]

theorem val_a5 : a5.val = Outerplanar.a5 := by
  simp only [val, num, den, a5, pow_zero, mul_one, div_one, Outerplanar.a5]
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, κA_cube]

theorem val_d6 : d6.val = Outerplanar.d6 := by
  simp only [val, num, den, d6, pow_zero, mul_one, one_mul, Outerplanar.d6, Outerplanar.a5]
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, κA_cube, κK_cube]
  ring

theorem val_kInv : kInv.val = 56 / 59 := by
  simp only [val, num, den, kInv, pow_zero, mul_one, one_mul, κK_cube]; norm_num

theorem val_aInv : aInv.val = 16 / 17 := by
  simp only [val, num, den, aInv, pow_zero, mul_one, κA_cube]; norm_num

end Sc

/-! ### Codes -/

/-- The codes of the pure types at the fifteen-face centroid. -/
inductive C15
  | I | L1 | L2 | T3 | T4 | B5 | B6 | H6 | B7 | H7
  deriving DecidableEq

namespace C15

/-- The marks of a code. -/
def marks : C15 → ℕ
  | I => 0 | L1 => 1 | L2 => 2 | T3 => 3 | T4 => 4 | B5 => 5 | B6 => 6 | H6 => 6 | B7 => 7
  | H7 => 7

/-- In the matching class `M`. -/
def isM : C15 → Bool
  | I => true | L1 => true | L2 => true | _ => false

/-- In the ball class `B`. -/
def hasB : C15 → Bool
  | H6 => false | H7 => false | _ => true

/-- The hexagon scale. -/
def hV : C15 → Sc
  | L1 => Sc.A | L2 => Sc.A | T3 => Sc.A | T4 => Sc.A | H6 => Sc.a5 | H7 => Sc.d6 | _ => Sc.one

/-- The matching scale. -/
def mV : C15 → Sc
  | L1 => Sc.kq | L2 => Sc.kA | _ => Sc.one

/-- The ball scale. -/
def bV : C15 → Sc
  | L1 => Sc.A | L2 => Sc.A | T3 => Sc.A | _ => Sc.one

/-- In `AB_f`. -/
def inABf : C15 → Bool
  | L1 => true | L2 => true | T3 => true | _ => false

/-- In `BAH_f`. -/
def inBAHf : C15 → Bool
  | L1 => true | L2 => true | T3 => true | T4 => true | _ => false

/-- In `B_f5`. -/
def inBf5 : C15 → Bool
  | I => true | L1 => true | L2 => true | T3 => true | T4 => true | B5 => true | _ => false

/-- In `B_f6`. -/
def inBf6 : C15 → Bool
  | H6 => false | B7 => false | H7 => false | _ => true

/-- In `H7_f`. -/
def inH7f : C15 → Bool
  | I => false | B5 => false | B6 => false | B7 => false | _ => true

end C15

open C15

/-- The code of the pure type `(k, r)`. -/
def code15 (k : ℕ) (r : Fin 3) : C15 :=
  if r = 0 then .I
  else if r = 1 then
    (if k ≤ 1 then .L1 else if k = 2 then .L2 else if k = 3 then .T3 else if k = 4 then .T4
      else if k = 5 then .B5 else if k = 6 then .B6 else .B7)
  else if k ≤ 6 then .H6 else .H7

theorem code15_marks (k : ℕ) (r : Fin 3) (h1 : r = 1 → 1 ≤ k) (h2 : r = 2 → 6 ≤ k) :
    (code15 k r).marks ≤ if r = 0 then 0 else k := by
  rcases r_cases3 r with rfl | rfl | rfl
  · simp [code15, C15.marks]
  · have := h1 rfl
    simp only [code15, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte]
    split_ifs <;> simp only [C15.marks] <;> omega
  · have := h2 rfl
    simp only [code15, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]
    split_ifs <;> simp only [C15.marks] <;> omega

/-! ### Capabilities -/

section Caps

variable {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {w : ℝ} {k : ℕ} {r : Fin 3}

theorem cap_hex15 (hw : 0 < w) (h0 : ∀ c d, 0 ≤ Y c d) (h : PT k r S T Y w) :
    Hex S T Y (w * (code15 k r).hV.val) := by
  rcases r_cases3 r with rfl | rfl | rfl
  · simpa [code15, C15.hV, Sc.val_one] using pt_hex hw h0 h
  · unfold code15
    simp only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte]
    split_ifs with h1 h2 h3 h4 h5 h6
    · simp only [C15.hV, Sc.val_A]; exact pt_hexA hw h0 rfl (by omega) h
    · simp only [C15.hV, Sc.val_A]; exact pt_hexA hw h0 rfl (by omega) h
    · simp only [C15.hV, Sc.val_A]; exact pt_hexA hw h0 rfl (by omega) h
    · simp only [C15.hV, Sc.val_A]; exact pt_hexA hw h0 rfl (by omega) h
    · simp only [C15.hV, Sc.val_one, mul_one]; exact pt_hex hw h0 h
    · simp only [C15.hV, Sc.val_one, mul_one]; exact pt_hex hw h0 h
    · simp only [C15.hV, Sc.val_one, mul_one]; exact pt_hex hw h0 h
  · have hk := pt_ge6 hw rfl h
    unfold code15
    simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]
    split_ifs with h6
    · simp only [C15.hV, Sc.val_a5]; exact pt_hex6 rfl (by omega) h
    · simp only [C15.hV, Sc.val_d6]; exact pt_hexD hw rfl h

theorem cap_M15 (hw : 0 < w) (hM : (code15 k r).isM = true) (h : PT k r S T Y w) :
    BijGe S T Y (w * (code15 k r).mV.val) 1 := by
  rcases r_cases3 r with rfl | rfl | rfl
  · simpa [code15, C15.mV, Sc.val_one] using (h.1 rfl).bijGe hw.le
  · have hk := pt_ge1 hw (by decide) h
    unfold code15 at hM ⊢
    simp only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte] at hM ⊢
    split_ifs at hM ⊢ with h1 h2
    · obtain rfl : k = 1 := by omega
      simpa [C15.mV, Sc.val_kq, msc] using pt_bij15 hw (Or.inr (by norm_num)) h
    · subst h2
      simpa [C15.mV, Sc.val_kA, msc] using pt_bij15 hw (Or.inr le_rfl) h
    all_goals simp [C15.isM] at hM
  · unfold code15 at hM
    simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte] at hM
    split_ifs at hM <;> simp [C15.isM] at hM

theorem cap_pos15 (hw : 0 < w) (h0 : ∀ c d, 0 ≤ Y c d) (h : PT k r S T Y w) :
    ∀ c ∈ S, ∀ d ∈ T, c ≠ d → 0 < Y c d := fun c hc d hd hcd =>
  lt_of_lt_of_le (mul_pos (fl_pos _) hw) (pt_floor hw h0 h c hc d hd hcd)

theorem cap_hasPot15 (hS : S.card = 3) (hT : T.card = 3) (hw : 0 < w) (h0 : ∀ c d, 0 ≤ Y c d)
    (hM : (code15 k r).isM = true) (h : PT k r S T Y w) :
    HasPot S T Y (w * (code15 k r).mV.val) := by
  have := BijGe.hasPot hS hT (mul_pos hw (Sc.val_pos _)) one_pos (cap_pos15 hw h0 h)
    (cap_M15 hw hM h)
  rwa [Real.one_rpow, mul_one] at this

theorem cap_B15 (hw : 0 < w) (hB : (code15 k r).hasB = true) (h : PT k r S T Y w) :
    InBall S T Y (w * (code15 k r).bV.val) := by
  rcases r_cases3 r with rfl | rfl | rfl
  · simpa [code15, C15.bV, Sc.val_one] using pt_ball hw (by decide) h
  · unfold code15
    simp only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte]
    split_ifs with h1 h2 h3 h4 h5 h6
    · simp only [C15.bV, Sc.val_A]; exact pt_ballA hw rfl (by omega) h
    · simp only [C15.bV, Sc.val_A]; exact pt_ballA hw rfl (by omega) h
    · simp only [C15.bV, Sc.val_A]; exact pt_ballA hw rfl (by omega) h
    · simp only [C15.bV, Sc.val_one, mul_one]; exact pt_ball hw (by decide) h
    · simp only [C15.bV, Sc.val_one, mul_one]; exact pt_ball hw (by decide) h
    · simp only [C15.bV, Sc.val_one, mul_one]; exact pt_ball hw (by decide) h
    · simp only [C15.bV, Sc.val_one, mul_one]; exact pt_ball hw (by decide) h
  · unfold code15 at hB
    simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte] at hB
    split_ifs at hB <;> simp [C15.hasB] at hB

theorem cap_I15 (hI : code15 k r = .I) (h : PT k r S T Y w) : Dominant S T Y w := by
  rcases r_cases3 r with rfl | rfl | rfl
  · exact h.1 rfl
  · unfold code15 at hI
    simp only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte] at hI
    split_ifs at hI
  · unfold code15 at hI
    simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte] at hI
    split_ifs at hI

/-- The code `I` lies in the ball classes with floors. -/
theorem dom_Bf5 (hw : 0 < w) (h : Dominant S T Y w) : ClsBf5 S T Y w :=
  ⟨h.le (by nlinarith), h.inBall hw.le⟩

theorem dom_Bf6 (hw : 0 < w) (h : Dominant S T Y w) : ClsBf6 S T Y w :=
  ⟨h.le (by nlinarith), h.inBall hw.le⟩

theorem code15_one {r : Fin 3} (hr : r ≠ 0) (hr2 : r ≠ 2) : r = 1 := by
  rcases r_cases3 r with rfl | rfl | rfl
  · exact absurd rfl hr
  · rfl
  · exact absurd rfl hr2

theorem cap_ABf (hw : 0 < w) (hc : (code15 k r).inABf = true) (h : PT k r S T Y w) :
    ClsABf S T Y w := by
  rcases r_cases3 r with rfl | rfl | rfl
  · simp [code15, C15.inABf] at hc
  · unfold code15 at hc
    simp only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte] at hc
    split_ifs at hc <;> simp [C15.inABf] at hc
    all_goals exact clsABf' h rfl (by omega) hw
  · unfold code15 at hc
    simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte] at hc
    split_ifs at hc <;> simp [C15.inABf] at hc

theorem cap_BAHf (hw : 0 < w) (h0 : ∀ c d, 0 ≤ Y c d) (hc : (code15 k r).inBAHf = true)
    (h : PT k r S T Y w) : ClsBAHf S T Y w := by
  rcases r_cases3 r with rfl | rfl | rfl
  · simp [code15, C15.inBAHf] at hc
  · unfold code15 at hc
    simp only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte] at hc
    split_ifs at hc <;> simp [C15.inBAHf] at hc
    all_goals exact clsBAHf' h rfl (by omega) hw h0
  · unfold code15 at hc
    simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte] at hc
    split_ifs at hc <;> simp [C15.inBAHf] at hc

theorem cap_Bf5 (hw : 0 < w) (hc : (code15 k r).inBf5 = true) (h : PT k r S T Y w) :
    ClsBf5 S T Y w := by
  rcases r_cases3 r with rfl | rfl | rfl
  · exact dom_Bf5 hw (h.1 rfl)
  · unfold code15 at hc
    simp only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte] at hc
    split_ifs at hc <;> simp [C15.inBf5] at hc
    all_goals exact clsBf5' h rfl (by omega) hw
  · unfold code15 at hc
    simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte] at hc
    split_ifs at hc <;> simp [C15.inBf5] at hc

theorem cap_Bf6 (hw : 0 < w) (hc : (code15 k r).inBf6 = true) (h : PT k r S T Y w) :
    ClsBf6 S T Y w := by
  rcases r_cases3 r with rfl | rfl | rfl
  · exact dom_Bf6 hw (h.1 rfl)
  · unfold code15 at hc
    simp only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte] at hc
    split_ifs at hc <;> simp [C15.inBf6] at hc
    all_goals exact clsBf6' h rfl (by omega) hw
  · unfold code15 at hc
    simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte] at hc
    split_ifs at hc <;> simp [C15.inBf6] at hc

theorem cap_H7f (hw : 0 < w) (h0 : ∀ c d, 0 ≤ Y c d) (hk : k ≤ 7)
    (hc : (code15 k r).inH7f = true) (h : PT k r S T Y w) : ClsH7f S T Y w := by
  rcases r_cases3 r with rfl | rfl | rfl
  · simp [code15, C15.inH7f] at hc
  · unfold code15 at hc
    simp only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte] at hc
    split_ifs at hc <;> simp [C15.inH7f] at hc
    all_goals exact clsH7f' h hk (Or.inr ⟨rfl, by omega⟩) hw h0
  · exact clsH7f' h hk (Or.inl rfl) hw h0

end Caps

end Outerplanar.F15
