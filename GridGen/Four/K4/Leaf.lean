/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.K4.Arith
import GridGen.Four.K4.Init
import GridGen.Four.Exact

/-!
# Height four at `k = 4`: the value of one column type

Codex's (OpenAI) classification (`ai_research_notes/cx/h4k4b/NOTE.md`) is a statement about the
seam vector `dvec Y B = ∑_{s ∈ sts Y} (cnt (B ∖ s) - H_{class s})`. Summed over the whole product
`Y₁ × ⋯ × Y₄`, with improper tuples contributing zero, it is `∑_s gvec B s` (`dot_dvec`).

The contribution `gvec B s` of a proper state depends only on its **type**: the membership masks
`mv B sᵢ` of its four colours in the lists of `B` (bit `j` set when the colour lies in `Bⱼ₊₁`) and
the three non-consecutive equalities `e₁₃, e₂₄, e₁₄`. Indeed `cnt A = cls (datC A)` is a polynomial
in the fifteen intersection sizes of the successor lists (`cnt_eq_cls`), and those are the Venn
sizes of `B` minus the number of distinct colours of `s` in the intersection (`datZ_val`).

`leafV I m₁ m₂ m₃ m₄ e₁₃ e₂₄ e₁₄` computes the five valuations of a type in `Nat`-pair arithmetic:
the dot products with the rays `F₀, …, F₃`, and twice the minimum of the dot product over the
eight corners of the tail box (`famW 4`). `leafV_sound`: it is a lower bound — an equality for
`F₀, …, F₃` — of `⟪gvec B s, w⟫` for every `w` of the valuation's family.
-/

namespace GridGen.Four.K4

open Finset GridGen.Four

/-! ### The seam vector of one state -/

instance (t : T4) : Decidable (Proper t) := by unfold Proper; infer_instance

/-- The contribution of one tuple to the seam vector (zero if improper). -/
def gvec (B : Col) (s : T4) : Q := if Proper s then cnt (ers B s) - hrow s else 0

/-- A sum over the product of the four lists. -/
def sumP (g : T4 → ℤ) (Y : Col) : ℤ :=
  ∑ a ∈ Y.1, ∑ b ∈ Y.2.1, ∑ c ∈ Y.2.2.1, ∑ d ∈ Y.2.2.2, g (a, b, c, d)

theorem sts_eq_filter (A B C D : Finset ℕ) :
    sts A B C D = (A ×ˢ B ×ˢ C ×ˢ D).filter Proper := by
  ext t
  simp only [mem_sts, Finset.mem_filter, Finset.mem_product, Proper]
  tauto

theorem sum_sts_eq_sumP (Y : Col) (f : T4 → ℤ) :
    ∑ s ∈ stsC Y, f s = sumP (fun s => if Proper s then f s else 0) Y := by
  unfold stsC sumP
  rw [sts_eq_filter, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_product]

/-- **The seam value as a sum over the product.** -/
theorem dot_dvec (Y B : Col) (w : Q) :
    dot (dvec Y B) w = sumP (fun s => dot (gvec B s) w) Y := by
  unfold dvec
  rw [dot_sum, sum_sts_eq_sumP]
  congr 1
  funext s
  unfold gvec
  split_ifs <;> simp [dot_zero]

/-! ### Class counts from intersection sizes -/

/-- The fifteen intersection sizes of the lists of a column. -/
def datC (A : Col) : Dat :=
  ⟨A.1.card, A.2.1.card, A.2.2.1.card, A.2.2.2.card, (A.1 ∩ A.2.1).card,
    (A.2.1 ∩ A.2.2.1).card, (A.2.2.1 ∩ A.2.2.2).card, (A.1 ∩ A.2.2.1).card,
    (A.2.1 ∩ A.2.2.2).card, (A.1 ∩ A.2.2.2).card, (A.1 ∩ A.2.1 ∩ A.2.2.1).card,
    (A.2.1 ∩ A.2.2.1 ∩ A.2.2.2).card, (A.1 ∩ A.2.1 ∩ A.2.2.2).card,
    (A.1 ∩ A.2.2.1 ∩ A.2.2.2).card, (A.1 ∩ A.2.1 ∩ A.2.2.1 ∩ A.2.2.2).card⟩

theorem Q_ext {d e : Q} (h : ∀ w : Q, dot d w = dot e w) : d = e := by
  obtain ⟨d1, d2, d3, d4⟩ := d
  obtain ⟨e1, e2, e3, e4⟩ := e
  have h1 := h (1, 0, 0, 0)
  have h2 := h (0, 1, 0, 0)
  have h3 := h (0, 0, 1, 0)
  have h4 := h (0, 0, 0, 1)
  simp only [dot, mul_one, mul_zero, add_zero, zero_add] at h1 h2 h3 h4
  rw [h1, h2, h3, h4]

/-- **The class counts of a column**, from the intersection sizes of its lists. -/
theorem cnt_eq_cls (A : Col) : cnt A = cls (datC A) := by
  obtain ⟨A₁, A₂, A₃, A₄⟩ := A
  obtain ⟨f1, f2, f3, f4, f5, f6, -, f8, f9, f10, f11⟩ := inter_forms A₁ A₂ A₃ A₄
  have hN := card_sts_formula A₁ A₂ A₃ A₄
  have h13 := card_eq13 A₁ A₂ A₃ A₄
  have h24 := card_eq24 A₁ A₂ A₃ A₄
  have h1324 := card_eq1324 A₁ A₂ A₃ A₄
  have h14 := card_eq14 A₁ A₂ A₃ A₄
  rw [f1, f2, f3] at h13
  rw [f4, f5, f6] at h24
  rw [show A₁ ∩ A₃ ∩ (A₂ ∩ A₄) = A₁ ∩ A₂ ∩ A₃ ∩ A₄ from f6] at h1324
  rw [f9, f11, f8, f10] at h14
  refine Q_ext fun w => ?_
  rw [dot_cnt_split]
  simp only [stsC]
  rw [hN, h13, h24, h1324, h14]
  simp only [cls, datC, dot]
  ring

/-! ### Masks -/

/-- A boolean as `0` or `1`. -/
def bn (b : Bool) : ℕ := cond b 1 0

/-- A membership vector as a four-bit mask: bit `j` for row `j + 1`. -/
def mIdx (r : Mem) : ℕ := Nat.add (Nat.add (bn r.1) (Nat.mul 2 (bn r.2.1)))
  (Nat.add (Nat.mul 4 (bn r.2.2.1)) (Nat.mul 8 (bn r.2.2.2)))

/-- `m ⊇ J` for masks. -/
def sup (m J : ℕ) : Bool := Nat.beq (Nat.land m J) J

/-- The mask of a colour in the lists of a column. -/
def mv (B : Col) (c : ℕ) : ℕ := mIdx (memv B.1 B.2.1 B.2.2.1 B.2.2.2 c)

theorem bn_eq_bi (b : Bool) : ((bn b : ℕ) : ℤ) = bi b := by cases b <;> rfl

theorem sup_bits :
    (∀ a b c d : Bool, sup (mIdx (a, b, c, d)) 1 = a) ∧
    (∀ a b c d : Bool, sup (mIdx (a, b, c, d)) 2 = b) ∧
    (∀ a b c d : Bool, sup (mIdx (a, b, c, d)) 4 = c) ∧
    (∀ a b c d : Bool, sup (mIdx (a, b, c, d)) 8 = d) ∧
    (∀ a b c d : Bool, sup (mIdx (a, b, c, d)) 3 = (a && b)) ∧
    (∀ a b c d : Bool, sup (mIdx (a, b, c, d)) 6 = (b && c)) ∧
    (∀ a b c d : Bool, sup (mIdx (a, b, c, d)) 12 = (c && d)) ∧
    (∀ a b c d : Bool, sup (mIdx (a, b, c, d)) 5 = (a && c)) ∧
    (∀ a b c d : Bool, sup (mIdx (a, b, c, d)) 10 = (b && d)) ∧
    (∀ a b c d : Bool, sup (mIdx (a, b, c, d)) 9 = (a && d)) ∧
    (∀ a b c d : Bool, sup (mIdx (a, b, c, d)) 7 = (a && b && c)) ∧
    (∀ a b c d : Bool, sup (mIdx (a, b, c, d)) 14 = (b && c && d)) ∧
    (∀ a b c d : Bool, sup (mIdx (a, b, c, d)) 11 = (a && b && d)) ∧
    (∀ a b c d : Bool, sup (mIdx (a, b, c, d)) 13 = (a && c && d)) ∧
    (∀ a b c d : Bool, sup (mIdx (a, b, c, d)) 15 = (a && b && c && d)) := by
  decide

/-! ### The data vector of a type -/

/-- Venn sizes as naturals, in the order of `Venn`. -/
structure VN where
  (x1 x2 x3 x4 x12 x23 x34 x13 x24 x14 x123 x234 x124 x134 x1234 : ℕ)

/-- The integer Venn sizes. -/
def VN.toVenn (v : VN) : Venn :=
  ⟨v.x1, v.x2, v.x3, v.x4, v.x12, v.x23, v.x34, v.x13, v.x24, v.x14, v.x123, v.x234, v.x124,
    v.x134, v.x1234⟩

/-- Intersection sizes as signed pairs. -/
structure DZ where
  (n1 n2 n3 n4 e12 e23 e34 a13 a24 a14 t123 t234 a124 a134 q : Zp)

/-- Their values. -/
def DZ.val (d : DZ) : Dat :=
  ⟨d.n1.val, d.n2.val, d.n3.val, d.n4.val, d.e12.val, d.e23.val, d.e34.val, d.a13.val, d.a24.val,
    d.a14.val, d.t123.val, d.t234.val, d.a124.val, d.a134.val, d.q.val⟩

/-- **The data vector of a type**: each intersection size is the Venn size minus the number of
distinct colours of the column lying in the intersection. Row 3 repeats row 1 when `e₁₃`, row 4
repeats row 2 when `e₂₄` and row 1 when `e₁₄`. -/
def datZ (v : VN) (m1 m2 m3 m4 : ℕ) (e13 e24 e14 : Bool) : DZ :=
  ⟨⟨v.x1, bn (sup m1 1)⟩, ⟨v.x2, bn (sup m2 2)⟩, ⟨v.x3, bn (sup m3 4)⟩, ⟨v.x4, bn (sup m4 8)⟩,
    ⟨v.x12, Nat.add (bn (sup m1 3)) (bn (sup m2 3))⟩,
    ⟨v.x23, Nat.add (bn (sup m2 6)) (bn (sup m3 6))⟩,
    ⟨v.x34, Nat.add (bn (sup m3 12)) (bn (sup m4 12))⟩,
    ⟨v.x13, Nat.add (bn (sup m1 5)) (bn (!e13 && sup m3 5))⟩,
    ⟨v.x24, Nat.add (bn (sup m2 10)) (bn (!e24 && sup m4 10))⟩,
    ⟨v.x14, Nat.add (bn (sup m1 9)) (bn (!e14 && sup m4 9))⟩,
    ⟨v.x123, Nat.add (Nat.add (bn (sup m1 7)) (bn (sup m2 7))) (bn (!e13 && sup m3 7))⟩,
    ⟨v.x234, Nat.add (Nat.add (bn (sup m2 14)) (bn (sup m3 14))) (bn (!e24 && sup m4 14))⟩,
    ⟨v.x124, Nat.add (Nat.add (bn (sup m1 11)) (bn (sup m2 11))) (bn (!e24 && !e14 && sup m4 11))⟩,
    ⟨v.x134, Nat.add (Nat.add (bn (sup m1 13)) (bn (!e13 && sup m3 13))) (bn (!e14 && sup m4 13))⟩,
    ⟨v.x1234, Nat.add (Nat.add (bn (sup m1 15)) (bn (sup m2 15)))
      (Nat.add (bn (!e13 && sup m3 15)) (bn (!e24 && !e14 && sup m4 15)))⟩⟩

theorem bi_true : bi true = 1 := rfl
theorem bi_false : bi false = 0 := rfl

/-- The data vector of a type is the integer `dat` of the existing exact certificates, for
consistent equality bits. -/
theorem datZ_val (v : VN) (r1 r2 r3 r4 : Mem) (e13 e24 e14 : Bool)
    (h13 : e13 = true → r3 = r1) (h24 : e24 = true → r4 = r2) (h14 : e14 = true → r4 = r1)
    (n1 : ¬ (e13 = true ∧ e14 = true)) (n2 : ¬ (e24 = true ∧ e14 = true)) :
    (datZ v (mIdx r1) (mIdx r2) (mIdx r3) (mIdx r4) e13 e24 e14).val
      = dat v.toVenn r1 r2 r3 r4 e13 e24 e14 := by
  obtain ⟨s1, s2, s4, s8, s3, s6, s12, s5, s10, s9, s7, s14, s11, s13, s15⟩ := sup_bits
  obtain ⟨a1, b1, c1, d1⟩ := r1
  obtain ⟨a2, b2, c2, d2⟩ := r2
  cases e13 <;> cases e24 <;> cases e14 <;>
    first
      | exact absurd ⟨rfl, rfl⟩ n1
      | exact absurd ⟨rfl, rfl⟩ n2
      | skip
  all_goals (try obtain rfl := h13 rfl); (try obtain rfl := h24 rfl); (try obtain rfl := h14 rfl)
  all_goals
    try obtain ⟨a3, b3, c3, d3⟩ := r3
    try obtain ⟨a4, b4, c4, d4⟩ := r4
    simp only [datZ, DZ.val, dat, VN.toVenn, Zp.val_mk, Nat.add_eq, s1, s2, s4, s8, s3, s6, s12,
      s5, s10, s9, s7, s14, s11, s13, s15, Bool.true_and, Bool.false_and, Bool.not_true,
      Bool.not_false, Dat.mk.injEq]
    push_cast [bn_eq_bi, bi_false]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring


/-! ### The class counts and the valuations of a type -/

/-- The class counts `(A, B, C, D)` from signed intersection sizes, as in `cls`. -/
def clsZ (d : DZ) : Zp × Zp × Zp × Zp :=
  let N := Zp.sub (Zp.mul d.n4 (Zp.sub (Zp.mul d.n3 (Zp.sub (Zp.mul d.n1 d.n2) d.e12))
      (Zp.sub (Zp.mul d.n1 d.e23) d.t123)))
    (Zp.sub (Zp.mul d.n1 (Zp.sub (Zp.mul d.n2 d.e34) d.t234)) (Zp.sub (Zp.mul d.e12 d.e34) d.q))
  let N13 := Zp.add (Zp.sub (Zp.sub (Zp.mul (Zp.mul d.a13 d.n2) d.n4) (Zp.mul d.t123 d.n4))
    (Zp.mul d.n2 d.a134)) d.q
  let N24 := Zp.add (Zp.sub (Zp.sub (Zp.mul (Zp.mul d.a24 d.n1) d.n3) (Zp.mul d.a124 d.n3))
    (Zp.mul d.n1 d.t234)) d.q
  let N1324 := Zp.sub (Zp.mul d.a13 d.a24) d.q
  let N14 := Zp.sub (Zp.sub (Zp.mul d.a14 (Zp.sub (Zp.mul d.n2 d.n3) d.e23))
    (Zp.sub (Zp.mul d.a124 d.n3) d.q)) (Zp.sub (Zp.mul d.n2 d.a134) d.q)
  (N1324, Zp.sub (Zp.add N13 N24) (Zp.add N1324 N1324), N14,
    Zp.sub (Zp.add N N1324) (Zp.add (Zp.add N13 N24) N14))

/-- The value of four signed pairs. -/
def Q4val (z : Zp × Zp × Zp × Zp) : Q := (z.1.val, z.2.1.val, z.2.2.1.val, z.2.2.2.val)

theorem clsZ_val (d : DZ) : Q4val (clsZ d) = cls d.val := by
  simp only [Q4val, clsZ, cls, DZ.val]
  simp only [Zp.val_add, Zp.val_sub, Zp.val_mul, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | ring

/-- The uniform transfer row of a class, from the equality bits. -/
def hrowN (e13 e24 e14 : Bool) : ℕ × ℕ × ℕ × ℕ :=
  cond (e13 && e24) (7, 20, 6, 8) (cond (e13 || e24) (5, 19, 7, 8)
    (cond e14 (3, 14, 11, 8) (4, 16, 8, 9)))

theorem hrow_eq (s : T4) :
    hrow s = ((((hrowN (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))).1 : ℕ) : ℤ),
      (((hrowN (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))).2.1 : ℕ) : ℤ),
      (((hrowN (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))).2.2.1 : ℕ) : ℤ),
      (((hrowN (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))).2.2.2 : ℕ) : ℤ)) := by
  unfold hrow hrowN
  by_cases h1 : r1 s = r3 s <;> by_cases h2 : r2 s = r4 s <;> by_cases h3 : r1 s = r4 s <;>
    (first | have e1 := eq_false h1 | have e1 := eq_true h1) <;>
    (first | have e2 := eq_false h2 | have e2 := eq_true h2) <;>
    (first | have e3 := eq_false h3 | have e3 := eq_true h3) <;>
    (try simp only [e1, e2, e3, decide_true, decide_false, and_self, and_true, true_and, and_false, false_and, or_true,
      true_or, or_false, false_or, if_true, if_false, Bool.and_self, Bool.and_true,
      Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_true, Bool.true_or, Bool.or_false,
      Bool.false_or, cond_true, cond_false]) <;> rfl

/-- Class counts minus a transfer row. -/
def subH (c : Zp × Zp × Zp × Zp) (h : ℕ × ℕ × ℕ × ℕ) : Zp × Zp × Zp × Zp :=
  (Zp.sub c.1 (Zp.ofN h.1), Zp.sub c.2.1 (Zp.ofN h.2.1), Zp.sub c.2.2.1 (Zp.ofN h.2.2.1),
    Zp.sub c.2.2.2 (Zp.ofN h.2.2.2))

theorem subH_val (c : Zp × Zp × Zp × Zp) (h : ℕ × ℕ × ℕ × ℕ) :
    Q4val (subH c h) = Q4val c - ((h.1 : ℤ), (h.2.1 : ℤ), (h.2.2.1 : ℤ), (h.2.2.2 : ℤ)) := by
  simp [subH, Q4val]

/-- The seam vector of a type. -/
def leafD (v : VN) (m1 m2 m3 m4 : ℕ) (e13 e24 e14 : Bool) : Zp × Zp × Zp × Zp :=
  subH (clsZ (datZ v m1 m2 m3 m4 e13 e24 e14)) (hrowN e13 e24 e14)

/-- The dot product with a weight of naturals. -/
def dotN (d : Zp × Zp × Zp × Zp) (w0 w1 w2 w3 : ℕ) : Zp :=
  Zp.add (Zp.add (Zp.smul w0 d.1) (Zp.smul w1 d.2.1)) (Zp.add (Zp.smul w2 d.2.2.1) (Zp.smul w3 d.2.2.2))

theorem dotN_val (d : Zp × Zp × Zp × Zp) (w0 w1 w2 w3 : ℕ) :
    (dotN d w0 w1 w2 w3).val = dot (Q4val d) (w0, w1, w2, w3) := by
  simp only [dotN, Zp.val_add, Zp.val_smul, Q4val, dot]; ring

/-- Twice the minimum of the dot product over the corners of the tail box. -/
def tailZ (d : Zp × Zp × Zp × Zp) : Zp :=
  Zp.add (dotN d 20000 18906 17184 17814)
    (Zp.add (Zp.smul 2 (Zp.negPart d.2.1))
      (Zp.add (Zp.smul 4 (Zp.negPart d.2.2.1)) (Zp.smul 4 (Zp.negPart d.2.2.2))))

/-- The five valuations of a seam vector. -/
def vals (d : Zp × Zp × Zp × Zp) : V5 :=
  ⟨dotN d 1 1 1 1, dotN d 41 39 36 37, dotN d 1579 1494 1361 1409,
    dotN d 60371 57080 51896 53789, tailZ d⟩

/-- **The valuations of one column type.** -/
def leafV (v : VN) (m1 m2 m3 m4 : ℕ) (e13 e24 e14 : Bool) : V5 :=
  vals (leafD v m1 m2 m3 m4 e13 e24 e14)

/-! ### The valuation families -/

/-- The weights each valuation bounds: the rays `F₀, …, F₃`, and twice the eight tail corners. -/
def famW : Fin 5 → List Q
  | 0 => [(1, 1, 1, 1)]
  | 1 => [(41, 39, 36, 37)]
  | 2 => [(1579, 1494, 1361, 1409)]
  | 3 => [(60371, 57080, 51896, 53789)]
  | 4 => [(20000, 18906, 17184, 17814), (20000, 18906, 17184, 17818),
      (20000, 18906, 17188, 17814), (20000, 18906, 17188, 17818),
      (20000, 18908, 17184, 17814), (20000, 18908, 17184, 17818),
      (20000, 18908, 17188, 17814), (20000, 18908, 17188, 17818)]

/-- Every weight of every family is nonnegative. -/
theorem famW_nonneg (k : Fin 5) (w : Q) (hw : w ∈ famW k) :
    0 ≤ w.1 ∧ 0 ≤ w.2.1 ∧ 0 ≤ w.2.2.1 ∧ 0 ≤ w.2.2.2 := by
  fin_cases k <;> simp only [famW, List.mem_cons, List.mem_nil_iff, or_false] at hw <;>
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The valuations bound the families. -/
theorem vals_le (d : Zp × Zp × Zp × Zp) (k : Fin 5) (w : Q) (hw : w ∈ famW k) :
    ((vals d).get k).val ≤ dot (Q4val d) w := by
  fin_cases k <;> simp only [famW, List.mem_cons, List.mem_nil_iff, or_false] at hw
  · subst hw; simp [vals, V5.get, dotN_val]
  · subst hw; simp [vals, V5.get, dotN_val]
  · subst hw; simp [vals, V5.get, dotN_val]
  · subst hw; simp [vals, V5.get, dotN_val]
  · simp only [vals, V5.get, tailZ, Zp.val_add, Zp.val_smul, Zp.val_negPart, dotN_val]
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Q4val, dot] <;> push_cast <;> omega

/-! ### Soundness of the leaf -/

theorem actDat_eq_datC (B : Col) (s : T4) :
    actDat B.1 B.2.1 B.2.2.1 B.2.2.2 s = datC (ers B s) := rfl

/-- **The seam vector of a proper state is the value of its type.** -/
theorem leafD_val (B : Col) (I : VN) (hI : I.toVenn = vennOf B.1 B.2.1 B.2.2.1 B.2.2.2) {s : T4}
    (hs : Proper s) :
    Q4val (leafD I (mv B (r1 s)) (mv B (r2 s)) (mv B (r3 s)) (mv B (r4 s)) (decide (r1 s = r3 s))
      (decide (r2 s = r4 s)) (decide (r1 s = r4 s))) = gvec B s := by
  have hp := hs
  obtain ⟨p12, p23, p34⟩ := hp
  have hd := dat_eq B.1 B.2.1 B.2.2.1 B.2.2.2 hs
  rw [actDat_eq_datC, ← hI, ← datZ_val] at hd
  · unfold gvec leafD mv
    rw [if_pos hs, cnt_eq_cls, hd, ← clsZ_val, hrow_eq, subH_val]
  · intro h; rw [of_decide_eq_true h]
  · intro h; rw [of_decide_eq_true h]
  · intro h; rw [of_decide_eq_true h]
  · rintro ⟨h1, h2⟩; exact p34 ((of_decide_eq_true h1).symm.trans (of_decide_eq_true h2))
  · rintro ⟨h1, h2⟩; exact p12 ((of_decide_eq_true h2).trans (of_decide_eq_true h1).symm)

/-- **Soundness of a leaf**: the valuations of the type of a proper state bound its contribution
at every weight of the families. -/
theorem leafV_sound (B : Col) (I : VN) (hI : I.toVenn = vennOf B.1 B.2.1 B.2.2.1 B.2.2.2)
    {s : T4} (hs : Proper s) (k : Fin 5) (w : Q) (hw : w ∈ famW k) :
    ((leafV I (mv B (r1 s)) (mv B (r2 s)) (mv B (r3 s)) (mv B (r4 s)) (decide (r1 s = r3 s))
      (decide (r2 s = r4 s)) (decide (r1 s = r4 s))).get k).val ≤ dot (gvec B s) w := by
  rw [← leafD_val B I hI hs]
  exact vals_le _ k w hw

end GridGen.Four.K4
