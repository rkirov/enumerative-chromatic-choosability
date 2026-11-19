/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Square
import Outerplanar.LoadedCert

/-!
# Squares with one loaded edge: from tables to the covering statement

`Outerplanar/Square.lean` reduces the ball closure of squares to the covering statement
`SqCover`. This file derives `SqCover` from two finite checks on data:

* for each pattern `Q` of a list of patterns (given by 36-bit codes, `patOfCode`) and each loaded
  edge `e`, a certificate checked by `checkCase` (`Outerplanar/LoadedCert.lean`), which gives
  `SqOK Q e` (`sqOK_of_check`);
* a table with one entry for every pattern in normal form (four subsets of `Fin 3`, as numbers
  below `8`, and a permutation, as a number below `6`): either a rule of `NormCons` that the
  pattern violates, or three renumberings and a pattern of the list above it (`covOK`).

`sqCover_of_table` puts the two together.
-/

namespace Outerplanar

/-- The pattern with code `c`: nine bits for each of the four edges. -/
def patOfCode (c : ℕ) : Pat :=
  ⟨fun a s => bitAt c (3 * a.val + s.val), fun s t => bitAt c (9 + 3 * s.val + t.val),
    fun t b => bitAt c (18 + 3 * t.val + b.val), fun a b => bitAt c (27 + 3 * a.val + b.val)⟩

/-- `p 0 && p 1 && p 2` on `Fin 3`. -/
def all3F (p : Fin 3 → Bool) : Bool := p 0 && p 1 && p 2

theorem all3F_apply {p : Fin 3 → Bool} (h : all3F p = true) (x : Fin 3) : p x = true := by
  simp only [all3F, Bool.and_eq_true] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  fin_cases x
  exacts [h0, h1, h2]

/-! ### Certificates give `SqOK` -/

/-- `C` is the face of the pattern `P` with loaded edge `e`. -/
def sqCaseOK (P : Pat) (e : Fin 3) (C : GCase) : Bool :=
  all3F fun x => all3F fun y =>
    (sqB₁ P e x y == C.B₁ x y) && (sqEl P e x y == C.El x y) && (sqB₂ P e x y == C.B₂ x y)
      && (P.e03 x y == C.Er x y)

theorem sqOK_of_check {P : Pat} {e : Fin 3} {C : GCase} {L : List Inst}
    (hC : sqCaseOK P e C = true) (h : checkCase 3 C L = true) : SqOK P e := by
  have hall : ∀ x y, sqB₁ P e x y = C.B₁ x y ∧ sqEl P e x y = C.El x y ∧
      sqB₂ P e x y = C.B₂ x y ∧ P.e03 x y = C.Er x y := fun x y => by
    have h1 := all3F_apply (all3F_apply hC x) y
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    exact ⟨h1.1.1.1, h1.1.1.2, h1.1.2, h1.2⟩
  have h1 : sqB₁ P e = C.B₁ := funext fun x => funext fun y => (hall x y).1
  have h2 : sqEl P e = C.El := funext fun x => funext fun y => (hall x y).2.1
  have h3 : sqB₂ P e = C.B₂ := funext fun x => funext fun y => (hall x y).2.2.1
  have h4 : P.e03 = C.Er := funext fun x => funext fun y => (hall x y).2.2.2
  unfold SqOK
  rw [h1, h2, h3, h4]
  exact checkCase_sound h

/-! ### The covering table -/

/-- `P` is below `Q`, as a check. -/
def patLEb (P Q : Pat) : Bool :=
  all3F fun x => all3F fun y =>
    (!P.e01 x y || Q.e01 x y) && (!P.e12 x y || Q.e12 x y) && (!P.e23 x y || Q.e23 x y)
      && (P.e03 x y == Q.e03 x y)

theorem patLE_of_b {P Q : Pat} (h : patLEb P Q = true) : PatLE P Q := by
  have hall : ∀ x y, (P.e01 x y = true → Q.e01 x y = true) ∧
      (P.e12 x y = true → Q.e12 x y = true) ∧ (P.e23 x y = true → Q.e23 x y = true) ∧
      P.e03 x y = Q.e03 x y := fun x y => by
    have h1 := all3F_apply (all3F_apply h x) y
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h1
    obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := h1
    refine ⟨fun hp => ?_, fun hp => ?_, fun hp => ?_, a4⟩
    · rcases a1 with a | a
      · rw [hp] at a; cases a
      · exact a
    · rcases a2 with a | a
      · rw [hp] at a; cases a
      · exact a
    · rcases a3 with a | a
      · rw [hp] at a; cases a
      · exact a
  exact ⟨fun x y => (hall x y).1, fun x y => (hall x y).2.1, fun x y => (hall x y).2.2.1,
    funext fun x => funext fun y => (hall x y).2.2.2⟩

/-- The subset of `Fin 3` with code `k`. -/
def bitsOf (k : ℕ) (a : Fin 3) : Bool := bitAt k a.val

/-- An element of `Fin 3` from a number. -/
def finOf3 (n : ℕ) : Fin 3 := ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩

/-- The rule `rule` of `NormCons` fails at the index `x`. -/
def violates (d0 d1 d2 dr : Fin 3 → Bool) (ρ : Fin 3 → Fin 3) (rule : ℕ) (x : Fin 3) : Bool :=
  if rule = 0 then d0 (ρ x) && d1 (ρ x) && d2 (ρ x) && !(decide (ρ x = x) && dr x)
  else if rule = 1 then d0 x && d1 x && dr x && !(decide (ρ x = x) && d2 x)
  else if rule = 2 then d0 x && d2 (ρ x) && dr x && !(decide (ρ x = x) && d1 x)
  else d1 (ρ x) && d2 (ρ x) && dr x && !(decide (ρ x = x) && d0 x)

theorem not_violates {d0 d1 d2 dr : Fin 3 → Bool} {ρ : Fin 3 → Fin 3}
    (h : NormCons d0 d1 d2 dr ρ) (rule : ℕ) (x : Fin 3) :
    violates d0 d1 d2 dr ρ rule x = false := by
  unfold violates
  split_ifs
  · cases h0 : d0 (ρ x) <;> cases h1 : d1 (ρ x) <;> cases h2 : d2 (ρ x) <;> simp
    exact h.c1 x h0 h1 h2
  · cases h0 : d0 x <;> cases h1 : d1 x <;> cases hr : dr x <;> simp
    exact h.c2 x h0 h1 hr
  · cases h0 : d0 x <;> cases h2 : d2 (ρ x) <;> cases hr : dr x <;> simp
    exact h.c3 x h0 h2 hr
  · cases h1 : d1 (ρ x) <;> cases h2 : d2 (ρ x) <;> cases hr : dr x <;> simp
    exact h.c4 x h1 h2 hr

/-- The check of one entry of the covering table `tbl` (16 bits per entry), for the pattern in
normal form with codes `k0`, `k1`, `k2`, `kr`, `r`; `qs` is the list of codes of patterns.
An odd entry names a violated rule; an even one three renumberings and a pattern of the list. -/
def covOK (tbl : ℕ) (qs : List ℕ) (k0 k1 k2 kr r : ℕ) : Bool :=
  if dig 16 tbl (k0 + 8 * k1 + 64 * k2 + 512 * kr + 4096 * r) % 2 = 1 then
    violates (bitsOf k0) (bitsOf k1) (bitsOf k2) (bitsOf kr) (perm6 r)
      (dig 16 tbl (k0 + 8 * k1 + 64 * k2 + 512 * kr + 4096 * r) / 2 % 4)
      (finOf3 (dig 16 tbl (k0 + 8 * k1 + 64 * k2 + 512 * kr + 4096 * r) / 8 % 4))
  else
    decide (dig 16 tbl (k0 + 8 * k1 + 64 * k2 + 512 * kr + 4096 * r) / 2 % 8 < 6) &&
    decide (dig 16 tbl (k0 + 8 * k1 + 64 * k2 + 512 * kr + 4096 * r) / 16 % 8 < 6) &&
    decide (dig 16 tbl (k0 + 8 * k1 + 64 * k2 + 512 * kr + 4096 * r) / 128 % 8 < 6) &&
    decide (dig 16 tbl (k0 + 8 * k1 + 64 * k2 + 512 * kr + 4096 * r) / 1024 < qs.length) &&
    patLEb (normPat (bitsOf k0) (bitsOf k1) (bitsOf k2) (bitsOf kr) (perm6 r)
        (perm6 (dig 16 tbl (k0 + 8 * k1 + 64 * k2 + 512 * kr + 4096 * r) / 2 % 8))
        (perm6 (dig 16 tbl (k0 + 8 * k1 + 64 * k2 + 512 * kr + 4096 * r) / 16 % 8))
        (perm6 (dig 16 tbl (k0 + 8 * k1 + 64 * k2 + 512 * kr + 4096 * r) / 128 % 8)))
      (patOfCode (qs.getD (dig 16 tbl (k0 + 8 * k1 + 64 * k2 + 512 * kr + 4096 * r) / 1024) 0))

/-- `p 0 && … && p 7`. -/
def all8 (p : ℕ → Bool) : Bool := p 0 && p 1 && p 2 && p 3 && p 4 && p 5 && p 6 && p 7

theorem all8_lt {p : ℕ → Bool} (h : all8 p = true) {x : ℕ} (hx : x < 8) : p x = true := by
  simp only [all8, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  interval_cases x
  exacts [h0, h1, h2, h3, h4, h5, h6, h7]

/-- The check of the `512` entries with given `kr` and `r`. -/
def covChunk (tbl : ℕ) (qs : List ℕ) (kr r : ℕ) : Bool :=
  all8 fun k2 => all8 fun k1 => all8 fun k0 => covOK tbl qs k0 k1 k2 kr r

theorem exists_bits (d : Fin 3 → Bool) : ∃ k, k < 8 ∧ bitsOf k = d := by
  refine ⟨(if d 0 = true then 1 else 0) + (if d 1 = true then 2 else 0)
    + (if d 2 = true then 4 else 0), ?_, ?_⟩
  · split_ifs <;> norm_num
  · funext a
    fin_cases a <;> cases h0 : d 0 <;> cases h1 : d 1 <;> cases h2 : d 2 <;>
      simp [bitsOf, bitAt, h0, h1, h2]

theorem exists_perm6 : ∀ ρ : Fin 3 → Fin 3, Function.Injective ρ →
    ∃ r : Fin 6, perm6 r.val = ρ := by
  decide +kernel

/-- **The covering statement from the two finite checks.** -/
theorem sqCover_of_table {tbl : ℕ} {qs : List ℕ}
    (hQ : ∀ q, q < qs.length → ∀ e, SqOK (patOfCode (qs.getD q 0)) e)
    (htbl : ∀ kr, kr < 8 → ∀ r, r < 6 → covChunk tbl qs kr r = true) : SqCover := by
  intro d0 d1 d2 dr ρ hρ hcons
  obtain ⟨k0, hk0, rfl⟩ := exists_bits d0
  obtain ⟨k1, hk1, rfl⟩ := exists_bits d1
  obtain ⟨k2, hk2, rfl⟩ := exists_bits d2
  obtain ⟨kr, hkr, rfl⟩ := exists_bits dr
  obtain ⟨r, rfl⟩ := exists_perm6 ρ hρ.1
  have h := all8_lt (all8_lt (all8_lt (htbl kr hkr r.val r.isLt) hk2) hk1) hk0
  unfold covOK at h
  split_ifs at h with hodd
  · rw [not_violates hcons] at h
    cases h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hp, hp0⟩, hp1⟩, hq⟩, hle⟩ := h
    exact ⟨_, _, _, perm6_bij ⟨_, hp⟩, perm6_bij ⟨_, hp0⟩, perm6_bij ⟨_, hp1⟩, _, hQ _ hq,
      patLE_of_b hle⟩

end Outerplanar
