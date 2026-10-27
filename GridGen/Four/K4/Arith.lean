/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.K4.Defs

/-!
# Height four at `k = 4`: kernel arithmetic

The classification certificate (`GridGen/Four/K4/Classify.lean`, Codex's (OpenAI) argument in
`ai_research_notes/cx/h4k4b/NOTE.md`) is checked by kernel evaluation. The kernel evaluates
`Nat.add`, `Nat.mul`, `Nat.ble`, … on literals natively, but `Int` arithmetic only by unfolding
(measured 2026-10-26: about `100 µs` per `Int` operation against `10 µs` per `Nat` operation).
So the checker computes with **pairs of naturals** `⟨p, n⟩`, read as `p - n` (`Zp.val`), calling the
`Nat` primitives directly. Every operation commutes with `val` (`val_add`, `val_mul`, …), so a
checked inequality between pairs is an inequality between integers.

`V5` carries the five valuations of the checker (the rays `F₀, …, F₃` of `K` and the tail box).
-/

namespace GridGen.Four.K4

/-- A signed integer as a difference of two naturals. -/
structure Zp where
  p : ℕ
  n : ℕ

namespace Zp

/-- The integer a pair stands for. -/
def val (a : Zp) : ℤ := (a.p : ℤ) - a.n

def add (a b : Zp) : Zp := ⟨Nat.add a.p b.p, Nat.add a.n b.n⟩
def sub (a b : Zp) : Zp := ⟨Nat.add a.p b.n, Nat.add a.n b.p⟩
def neg (a : Zp) : Zp := ⟨a.n, a.p⟩
def mul (a b : Zp) : Zp :=
  ⟨Nat.add (Nat.mul a.p b.p) (Nat.mul a.n b.n), Nat.add (Nat.mul a.p b.n) (Nat.mul a.n b.p)⟩
/-- Multiplication by a natural. -/
def smul (c : ℕ) (a : Zp) : Zp := ⟨Nat.mul c a.p, Nat.mul c a.n⟩
/-- A natural. -/
def ofN (a : ℕ) : Zp := ⟨a, 0⟩
/-- `a ≤ b`. -/
def le (a b : Zp) : Bool := Nat.ble (Nat.add a.p b.n) (Nat.add b.p a.n)
def min (a b : Zp) : Zp := cond (le a b) a b
/-- `min 0 a`. -/
def negPart (a : Zp) : Zp := ⟨0, Nat.sub a.n a.p⟩
/-- `0 ≤ a`. -/
def nonneg (a : Zp) : Bool := Nat.ble a.n a.p

@[simp] theorem val_mk (p n : ℕ) : (⟨p, n⟩ : Zp).val = (p : ℤ) - n := rfl

@[simp] theorem val_add (a b : Zp) : (add a b).val = a.val + b.val := by
  simp only [add, val, Nat.add_eq]; push_cast; ring

@[simp] theorem val_sub (a b : Zp) : (sub a b).val = a.val - b.val := by
  simp only [sub, val, Nat.add_eq]; push_cast; ring

@[simp] theorem val_neg (a : Zp) : (neg a).val = -a.val := by
  simp only [neg, val]; ring

@[simp] theorem val_mul (a b : Zp) : (mul a b).val = a.val * b.val := by
  simp only [mul, val, Nat.add_eq, Nat.mul_eq]; push_cast; ring

@[simp] theorem val_smul (c : ℕ) (a : Zp) : (smul c a).val = c * a.val := by
  simp only [smul, val, Nat.mul_eq]; push_cast; ring

@[simp] theorem val_ofN (a : ℕ) : (ofN a).val = a := by simp [ofN, val]

theorem le_iff (a b : Zp) : le a b = true ↔ a.val ≤ b.val := by
  simp only [le, Nat.ble_eq, Nat.add_eq, val]
  omega

@[simp] theorem val_min (a b : Zp) : (min a b).val = Min.min a.val b.val := by
  unfold min
  cases h : le a b
  · have : ¬ a.val ≤ b.val := fun h' => by rw [(le_iff a b).mpr h'] at h; exact absurd h (by decide)
    simp only [Bool.cond_false]; omega
  · have := (le_iff a b).mp h
    simp only [Bool.cond_true]; omega

@[simp] theorem val_negPart (a : Zp) : (negPart a).val = Min.min 0 a.val := by
  simp only [negPart, val, Nat.sub_eq]
  omega

theorem nonneg_iff (a : Zp) : nonneg a = true ↔ 0 ≤ a.val := by
  simp only [nonneg, Nat.ble_eq, val]
  omega

end Zp

/-- Five values, one per valuation. -/
structure V5 where
  a : Zp
  b : Zp
  c : Zp
  d : Zp
  e : Zp

namespace V5

/-- The value at a valuation. -/
def get (v : V5) : Fin 5 → Zp
  | 0 => v.a
  | 1 => v.b
  | 2 => v.c
  | 3 => v.d
  | 4 => v.e

/-- Every value is nonnegative. -/
def nonneg (v : V5) : Bool :=
  v.a.nonneg && v.b.nonneg && v.c.nonneg && v.d.nonneg && v.e.nonneg

theorem nonneg_get {v : V5} (h : v.nonneg = true) (k : Fin 5) : 0 ≤ (v.get k).val := by
  simp only [nonneg, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he⟩ := h
  fin_cases k
  · exact (Zp.nonneg_iff _).mp ha
  · exact (Zp.nonneg_iff _).mp hb
  · exact (Zp.nonneg_iff _).mp hc
  · exact (Zp.nonneg_iff _).mp hd
  · exact (Zp.nonneg_iff _).mp he

/-- Componentwise minimum. -/
def min (u v : V5) : V5 :=
  ⟨Zp.min u.a v.a, Zp.min u.b v.b, Zp.min u.c v.c, Zp.min u.d v.d, Zp.min u.e v.e⟩

theorem get_min (u v : V5) (k : Fin 5) :
    ((min u v).get k).val = Min.min (u.get k).val (v.get k).val := by
  fin_cases k <;> simp [min, get]

/-- The zero vector. -/
def zero : V5 := ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩

theorem get_zero (k : Fin 5) : (zero.get k).val = 0 := by
  fin_cases k <;> rfl

end V5

end GridGen.Four.K4
