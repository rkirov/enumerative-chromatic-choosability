/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Seam

/-!
# Height four: exact data of one state from membership bits

For lists `B₁, …, B₄` and a proper column `s`, the successor lists are `Aᵢ = Bᵢ.erase sᵢ`, and
every intersection `⋂_{i∈I} Aᵢ` is `⋂_{i∈I} Bᵢ` with the colours `sᵢ` (`i ∈ I`) removed. So its
size is the size of `⋂_{i∈I} Bᵢ` minus the number of distinct `sᵢ` in it, a function of the
*membership bits* `[sᵢ ∈ Bⱼ]` and the *pattern bits* `[s₁ = s₃]`, `[s₂ = s₄]`, `[s₁ = s₄]`
(`dat_eq`). The successor count and the pattern counts are polynomials in these sizes
(`card_sts_formula`, `card_eq13`, …), so the weighted successor count `GB` is an explicit integer
function of the Venn sizes of `B` and the bits of `s` (`GB_cls`).

This is the computational core of the exact certificates for small mismatches at `k = 6`
(`GridGen/Four/Small6.lean`, via `Exact6.lean`).
-/

namespace GridGen.Four

open Finset

/-- Membership bits of one colour in four lists. -/
abbrev Mem := Bool × Bool × Bool × Bool

/-- The integer of a bit. -/
def bi (b : Bool) : ℤ := if b then 1 else 0

/-- The membership bits of a colour. -/
def memv (B₁ B₂ B₃ B₄ : Finset ℕ) (c : ℕ) : Mem :=
  (decide (c ∈ B₁), decide (c ∈ B₂), decide (c ∈ B₃), decide (c ∈ B₄))

/-- The fifteen Venn sizes `|⋂_{i∈I} Bᵢ|`. -/
structure Venn where
  (x1 x2 x3 x4 x12 x23 x34 x13 x24 x14 x123 x234 x124 x134 x1234 : ℤ)

/-- The fifteen intersection sizes of the successor lists. -/
structure Dat where
  (n1 n2 n3 n4 e12 e23 e34 a13 a24 a14 t123 t234 a124 a134 q : ℤ)

/-- The Venn sizes of four lists. -/
def vennOf (B₁ B₂ B₃ B₄ : Finset ℕ) : Venn :=
  ⟨B₁.card, B₂.card, B₃.card, B₄.card, (B₁ ∩ B₂).card, (B₂ ∩ B₃).card, (B₃ ∩ B₄).card,
    (B₁ ∩ B₃).card, (B₂ ∩ B₄).card, (B₁ ∩ B₄).card, (B₁ ∩ B₂ ∩ B₃).card, (B₂ ∩ B₃ ∩ B₄).card,
    (B₁ ∩ B₂ ∩ B₄).card, (B₁ ∩ B₃ ∩ B₄).card, (B₁ ∩ B₂ ∩ B₃ ∩ B₄).card⟩

/-- The intersection sizes of the successor lists of `s`. -/
def actDat (B₁ B₂ B₃ B₄ : Finset ℕ) (s : T4) : Dat :=
  let A₁ := B₁.erase (r1 s); let A₂ := B₂.erase (r2 s)
  let A₃ := B₃.erase (r3 s); let A₄ := B₄.erase (r4 s)
  ⟨A₁.card, A₂.card, A₃.card, A₄.card, (A₁ ∩ A₂).card, (A₂ ∩ A₃).card, (A₃ ∩ A₄).card,
    (A₁ ∩ A₃).card, (A₂ ∩ A₄).card, (A₁ ∩ A₄).card, (A₁ ∩ A₂ ∩ A₃).card, (A₂ ∩ A₃ ∩ A₄).card,
    (A₁ ∩ A₂ ∩ A₄).card, (A₁ ∩ A₃ ∩ A₄).card, (A₁ ∩ A₂ ∩ A₃ ∩ A₄).card⟩

/-- The intersection sizes of the successor lists, from the Venn sizes and the bits. -/
def dat (v : Venn) (r1 r2 r3 r4 : Mem) (e13 e24 e14 : Bool) : Dat :=
  ⟨v.x1 - bi r1.1, v.x2 - bi r2.2.1, v.x3 - bi r3.2.2.1, v.x4 - bi r4.2.2.2,
    v.x12 - bi (r1.1 && r1.2.1) - bi (r2.1 && r2.2.1),
    v.x23 - bi (r2.2.1 && r2.2.2.1) - bi (r3.2.1 && r3.2.2.1),
    v.x34 - bi (r3.2.2.1 && r3.2.2.2) - bi (r4.2.2.1 && r4.2.2.2),
    v.x13 - bi (r1.1 && r1.2.2.1) - bi (r3.1 && r3.2.2.1) + bi (e13 && r1.1 && r1.2.2.1),
    v.x24 - bi (r2.2.1 && r2.2.2.2) - bi (r4.2.1 && r4.2.2.2) + bi (e24 && r2.2.1 && r2.2.2.2),
    v.x14 - bi (r1.1 && r1.2.2.2) - bi (r4.1 && r4.2.2.2) + bi (e14 && r1.1 && r1.2.2.2),
    v.x123 - bi (r1.1 && r1.2.1 && r1.2.2.1) - bi (r2.1 && r2.2.1 && r2.2.2.1)
      - bi (r3.1 && r3.2.1 && r3.2.2.1) + bi (e13 && r1.1 && r1.2.1 && r1.2.2.1),
    v.x234 - bi (r2.2.1 && r2.2.2.1 && r2.2.2.2) - bi (r3.2.1 && r3.2.2.1 && r3.2.2.2)
      - bi (r4.2.1 && r4.2.2.1 && r4.2.2.2) + bi (e24 && r2.2.1 && r2.2.2.1 && r2.2.2.2),
    v.x124 - bi (r1.1 && r1.2.1 && r1.2.2.2) - bi (r2.1 && r2.2.1 && r2.2.2.2)
      - bi (r4.1 && r4.2.1 && r4.2.2.2) + bi (e24 && r2.1 && r2.2.1 && r2.2.2.2)
      + bi (e14 && r1.1 && r1.2.1 && r1.2.2.2),
    v.x134 - bi (r1.1 && r1.2.2.1 && r1.2.2.2) - bi (r3.1 && r3.2.2.1 && r3.2.2.2)
      - bi (r4.1 && r4.2.2.1 && r4.2.2.2) + bi (e13 && r1.1 && r1.2.2.1 && r1.2.2.2)
      + bi (e14 && r1.1 && r1.2.2.1 && r1.2.2.2),
    v.x1234 - bi (r1.1 && r1.2.1 && r1.2.2.1 && r1.2.2.2)
      - bi (r2.1 && r2.2.1 && r2.2.2.1 && r2.2.2.2) - bi (r3.1 && r3.2.1 && r3.2.2.1 && r3.2.2.2)
      - bi (r4.1 && r4.2.1 && r4.2.2.1 && r4.2.2.2)
      + bi (e13 && r1.1 && r1.2.1 && r1.2.2.1 && r1.2.2.2)
      + bi (e24 && r2.1 && r2.2.1 && r2.2.2.1 && r2.2.2.2)
      + bi (e14 && r1.1 && r1.2.1 && r1.2.2.1 && r1.2.2.2)⟩

/-! ### Erase chains -/

theorem card_erase_int (Y : Finset ℕ) (a : ℕ) :
    ((Y.erase a).card : ℤ) = Y.card - bi (decide (a ∈ Y)) := by
  unfold bi
  by_cases h : a ∈ Y
  · rw [Finset.card_erase_of_mem h]; simp [h]
    have : 1 ≤ Y.card := Finset.card_pos.mpr ⟨a, h⟩
    omega
  · rw [Finset.erase_eq_of_notMem h]; simp [h]

/-- Two erasures of distinct colours. -/
theorem chain2 (X : Finset ℕ) {a b : ℕ} (hab : a ≠ b) :
    (((X.erase a).erase b).card : ℤ) = X.card - bi (decide (a ∈ X)) - bi (decide (b ∈ X)) := by
  rw [card_erase_int, card_erase_int]
  have : decide (b ∈ X.erase a) = decide (b ∈ X) := by
    simp only [Finset.mem_erase, ne_eq, Ne.symm hab, not_false_eq_true, true_and]
  rw [this]

/-- Two erasures, possibly of the same colour. -/
theorem chain2' (X : Finset ℕ) (a b : ℕ) :
    (((X.erase a).erase b).card : ℤ)
      = X.card - bi (decide (a ∈ X)) - bi (decide (b ∈ X)) + bi (decide (a = b) && decide (a ∈ X)) := by
  rw [card_erase_int, card_erase_int]
  unfold bi
  by_cases hab : a = b
  · subst hab; by_cases h : a ∈ X <;> simp [h]
  · have : (b ∈ X.erase a) ↔ b ∈ X := by simp [Finset.mem_erase, Ne.symm hab]
    by_cases h : b ∈ X <;> by_cases h' : a ∈ X <;> simp [this, h, h', hab]

/-- Three erasures, rows `1, 2, 3` (or any `a ≠ b ≠ c`). -/
theorem chain3 (X : Finset ℕ) {a b c : ℕ} (hab : a ≠ b) (hbc : b ≠ c) :
    ((((X.erase a).erase b).erase c).card : ℤ) = X.card - bi (decide (a ∈ X))
      - bi (decide (b ∈ X)) - bi (decide (c ∈ X)) + bi (decide (a = c) && decide (a ∈ X)) := by
  rw [card_erase_int, chain2 X hab]
  unfold bi
  by_cases hac : a = c
  · subst hac; by_cases h : a ∈ X <;> simp [h]
  · have : (c ∈ (X.erase a).erase b) ↔ c ∈ X := by
      simp [Finset.mem_erase, Ne.symm hac, Ne.symm hbc]
    by_cases h : c ∈ X <;> simp [this, h, hac]

/-- Three erasures, rows `1, 2, 4`: `a ≠ b`. -/
theorem chain3b (X : Finset ℕ) {a b d : ℕ} (hab : a ≠ b) :
    ((((X.erase a).erase b).erase d).card : ℤ) = X.card - bi (decide (a ∈ X))
      - bi (decide (b ∈ X)) - bi (decide (d ∈ X)) + bi (decide (b = d) && decide (b ∈ X))
      + bi (decide (a = d) && decide (a ∈ X)) := by
  rw [card_erase_int, chain2 X hab]
  unfold bi
  by_cases hbd : b = d
  · subst hbd
    have hab' : ¬ a = b := hab
    by_cases h : b ∈ X <;> simp [h, hab']
  · by_cases had : a = d
    · subst had; by_cases h : a ∈ X <;> simp [h, hbd]
    · have : (d ∈ (X.erase a).erase b) ↔ d ∈ X := by
        simp [Finset.mem_erase, Ne.symm had, Ne.symm hbd]
      by_cases h : d ∈ X <;> simp [this, h, hbd, had]

/-- Three erasures, rows `1, 3, 4`: `c ≠ d`. -/
theorem chain3c (X : Finset ℕ) (a : ℕ) {c d : ℕ} (hcd : c ≠ d) :
    ((((X.erase a).erase c).erase d).card : ℤ) = X.card - bi (decide (a ∈ X))
      - bi (decide (c ∈ X)) - bi (decide (d ∈ X)) + bi (decide (a = c) && decide (a ∈ X))
      + bi (decide (a = d) && decide (a ∈ X)) := by
  rw [card_erase_int, card_erase_int, card_erase_int]
  simp only [Finset.mem_erase]
  unfold bi
  by_cases h1 : a ∈ X <;> by_cases h2 : c ∈ X <;> by_cases h3 : d ∈ X <;>
    by_cases e1 : a = c <;> by_cases e2 : a = d <;> simp_all <;> omega

/-- Four erasures of a proper column. -/
theorem chain4 (X : Finset ℕ) {a b c d : ℕ} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) :
    (((((X.erase a).erase b).erase c).erase d).card : ℤ) = X.card - bi (decide (a ∈ X))
      - bi (decide (b ∈ X)) - bi (decide (c ∈ X)) - bi (decide (d ∈ X))
      + bi (decide (a = c) && decide (a ∈ X)) + bi (decide (b = d) && decide (b ∈ X))
      + bi (decide (a = d) && decide (a ∈ X)) := by
  rw [card_erase_int, card_erase_int, card_erase_int, card_erase_int]
  simp only [Finset.mem_erase]
  unfold bi
  by_cases h1 : a ∈ X <;> by_cases h2 : b ∈ X <;> by_cases h3 : c ∈ X <;> by_cases h4 : d ∈ X <;>
    by_cases e1 : a = c <;> by_cases e2 : b = d <;> by_cases e3 : a = d <;> simp_all <;> omega

/-! ### The data of one state -/

theorem inter_erase2 (X Y : Finset ℕ) (a b : ℕ) :
    X.erase a ∩ Y.erase b = ((X ∩ Y).erase a).erase b := by
  ext x; simp only [Finset.mem_inter, Finset.mem_erase]; tauto

theorem inter_erase3 (X Y Z : Finset ℕ) (a b c : ℕ) :
    X.erase a ∩ Y.erase b ∩ Z.erase c = (((X ∩ Y ∩ Z).erase a).erase b).erase c := by
  ext x; simp only [Finset.mem_inter, Finset.mem_erase]; tauto

theorem inter_erase4 (X Y Z U : Finset ℕ) (a b c d : ℕ) :
    X.erase a ∩ Y.erase b ∩ Z.erase c ∩ U.erase d
      = ((((X ∩ Y ∩ Z ∩ U).erase a).erase b).erase c).erase d := by
  ext x; simp only [Finset.mem_inter, Finset.mem_erase]; tauto

/-- **The data of one state from its bits.** -/
theorem dat_eq (B₁ B₂ B₃ B₄ : Finset ℕ) {s : T4} (hs : Proper s) :
    actDat B₁ B₂ B₃ B₄ s = dat (vennOf B₁ B₂ B₃ B₄) (memv B₁ B₂ B₃ B₄ (r1 s))
      (memv B₁ B₂ B₃ B₄ (r2 s)) (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s))
      (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) := by
  obtain ⟨p12, p23, p34⟩ := hs
  simp only [actDat, dat, vennOf, Dat.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [card_erase_int]; rfl
  · rw [card_erase_int]; rfl
  · rw [card_erase_int]; rfl
  · rw [card_erase_int]; rfl
  · rw [inter_erase2, chain2 _ p12]; simp [memv, Finset.mem_inter, Bool.and_assoc]
  · rw [inter_erase2, chain2 _ p23]; simp [memv, Finset.mem_inter, Bool.and_assoc]
  · rw [inter_erase2, chain2 _ p34]; simp [memv, Finset.mem_inter, Bool.and_assoc]
  · rw [inter_erase2, chain2']; simp [memv, Finset.mem_inter, Bool.and_assoc]
  · rw [inter_erase2, chain2']; simp [memv, Finset.mem_inter, Bool.and_assoc]
  · rw [inter_erase2, chain2']; simp [memv, Finset.mem_inter, Bool.and_assoc]
  · rw [inter_erase3, chain3 _ p12 p23]; simp [memv, Finset.mem_inter, Bool.and_assoc]
  · rw [inter_erase3, chain3 _ p23 p34]; simp [memv, Finset.mem_inter, Bool.and_assoc]
  · rw [inter_erase3, chain3b _ p12]; simp [memv, Finset.mem_inter, Bool.and_assoc]
  · rw [inter_erase3, chain3c _ _ p34]; simp [memv, Finset.mem_inter, Bool.and_assoc]
  · rw [inter_erase4, chain4 _ p12 p23 p34]; simp [memv, Finset.mem_inter, Bool.and_assoc]

/-! ### The weighted count from the data -/

/-- The class counts `(0101, one equality, s₁ = s₄, no equality)` from the data. -/
def cls (d : Dat) : ℤ × ℤ × ℤ × ℤ :=
  let N := d.n4 * (d.n3 * (d.n1 * d.n2 - d.e12) - (d.n1 * d.e23 - d.t123))
    - (d.n1 * (d.n2 * d.e34 - d.t234) - (d.e12 * d.e34 - d.q))
  let N13 := d.a13 * d.n2 * d.n4 - d.t123 * d.n4 - d.n2 * d.a134 + d.q
  let N24 := d.a24 * d.n1 * d.n3 - d.a124 * d.n3 - d.n1 * d.t234 + d.q
  let N1324 := d.a13 * d.a24 - d.q
  let N14 := d.a14 * (d.n2 * d.n3 - d.e23) - (d.a124 * d.n3 - d.q) - (d.n2 * d.a134 - d.q)
  (N1324, N13 + N24 - 2 * N1324, N14, N - N13 - N24 + N1324 - N14)

theorem inter_forms (A₁ A₂ A₃ A₄ : Finset ℕ) :
    A₂ ∩ (A₁ ∩ A₃) = A₁ ∩ A₂ ∩ A₃ ∧ A₄ ∩ (A₁ ∩ A₃) = A₁ ∩ A₃ ∩ A₄ ∧
    A₂ ∩ A₄ ∩ (A₁ ∩ A₃) = A₁ ∩ A₂ ∩ A₃ ∩ A₄ ∧ A₁ ∩ (A₂ ∩ A₄) = A₁ ∩ A₂ ∩ A₄ ∧
    A₃ ∩ (A₂ ∩ A₄) = A₂ ∩ A₃ ∩ A₄ ∧ A₁ ∩ A₃ ∩ (A₂ ∩ A₄) = A₁ ∩ A₂ ∩ A₃ ∩ A₄ ∧
    A₁ ∩ A₃ ∩ (A₂ ∩ A₄) = A₁ ∩ A₂ ∩ A₃ ∩ A₄ ∧ A₂ ∩ (A₁ ∩ A₄) = A₁ ∩ A₂ ∩ A₄ ∧
    A₂ ∩ (A₁ ∩ A₄) ∩ A₃ = A₁ ∩ A₂ ∩ A₃ ∩ A₄ ∧ A₃ ∩ (A₁ ∩ A₄) = A₁ ∩ A₃ ∩ A₄ ∧
    A₂ ∩ (A₃ ∩ (A₁ ∩ A₄)) = A₁ ∩ A₂ ∩ A₃ ∩ A₄ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext x; simp only [Finset.mem_inter]; tauto)

/-- **The weighted successor count, by classes.** -/
theorem GB_cls (w : Wt) (B₁ B₂ B₃ B₄ : Finset ℕ) (s : T4) :
    GB w B₁ B₂ B₃ B₄ s = ((cls (actDat B₁ B₂ B₃ B₄ s)).1 : ℝ)
      + ((cls (actDat B₁ B₂ B₃ B₄ s)).2.1 : ℝ) * w.a + ((cls (actDat B₁ B₂ B₃ B₄ s)).2.2.1 : ℝ) * w.b
      + ((cls (actDat B₁ B₂ B₃ B₄ s)).2.2.2 : ℝ) * w.c := by
  set A₁ := B₁.erase (r1 s)
  set A₂ := B₂.erase (r2 s)
  set A₃ := B₃.erase (r3 s)
  set A₄ := B₄.erase (r4 s)
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
  unfold GB
  rw [G_split, hN, h13, h24, h1324, h14]
  simp only [cls, actDat]
  push_cast
  ring

/-! ### Certificates -/

/-- A pin: a row, an atom (membership vector), its multiplier, and a bound on the atom's size. -/
abbrev Pin := Fin 4 × Mem × ℤ × ℕ

/-- An exact certificate: Venn sizes, the atoms a row can lie in, pins, and the constant `K`, all
over the common denominator `D`. -/
structure Spec where
  venn : Venn
  atoms : List Mem
  pins : List Pin
  l13 : ℤ
  l24 : ℤ
  K : ℤ
  D : ℤ

/-- The row bits of a column. -/
def rowsel (r1 r2 r3 r4 : Mem) : Fin 4 → Mem
  | 0 => r1
  | 1 => r2
  | 2 => r3
  | 3 => r4

/-- The pinned multipliers that fire. -/
def pinsum : List Pin → Mem → Mem → Mem → Mem → ℤ
  | [], _, _, _, _ => 0
  | p :: L, r1, r2, r3, r4 =>
      (if rowsel r1 r2 r3 r4 p.1 = p.2.1 then p.2.2.1 else 0) + pinsum L r1 r2 r3 r4

/-- `Σ λ` and `Σ λ·|R|` over the pins. -/
def lamsum : List Pin → ℤ
  | [] => 0
  | p :: L => p.2.2.1 + lamsum L

def lamsize : List Pin → ℤ
  | [] => 0
  | p :: L => p.2.2.1 * p.2.2.2 + lamsize L

def lamnonneg : List Pin → Bool
  | [] => true
  | p :: L => decide (0 ≤ p.2.2.1) && decide (p.2.1 ≠ (false, false, false, false)) && lamnonneg L

/-- The bits of a proper column are consistent. -/
def valid (r1 r2 r3 r4 : Mem) (e13 e24 e14 : Bool) : Bool :=
  !(e13 && e14) && !(e24 && e14) && (!e13 || r1 == r3) && (!e24 || r2 == r4) && (!e14 || r1 == r4)

/-! ### Pin sums and consistent columns -/

theorem pinsum_bounds : ∀ (L : List Pin), lamnonneg L = true → ∀ r1 r2 r3 r4 : Mem,
    0 ≤ pinsum L r1 r2 r3 r4 ∧ pinsum L r1 r2 r3 r4 ≤ lamsum L
  | [], _, _, _, _, _ => by simp [pinsum, lamsum]
  | p :: L, h, r1, r2, r3, r4 => by
    simp only [lamnonneg, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hp, -⟩, hL⟩ := h
    obtain ⟨h1, h2⟩ := pinsum_bounds L hL r1 r2 r3 r4
    simp only [pinsum, lamsum]
    split_ifs <;> constructor <;> linarith

theorem valid_of (B₁ B₂ B₃ B₄ : Finset ℕ) {s : T4} (hs : Proper s) :
    valid (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s)) (memv B₁ B₂ B₃ B₄ (r3 s))
      (memv B₁ B₂ B₃ B₄ (r4 s)) (decide (r1 s = r3 s)) (decide (r2 s = r4 s))
      (decide (r1 s = r4 s)) = true := by
  obtain ⟨p12, p23, p34⟩ := hs
  unfold valid
  by_cases h13 : r1 s = r3 s <;> by_cases h24 : r2 s = r4 s <;> by_cases h14 : r1 s = r4 s
  all_goals simp only [h13, h24, h14, decide_true, decide_false, Bool.and_true, Bool.and_false,
    Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.true_or, Bool.false_or,
    Bool.or_true, Bool.or_false, beq_iff_eq]
  all_goals first
    | rfl
    | (exfalso; exact p34 (h13.symm.trans h14))
    | (exfalso; exact p12 (h14.trans h24.symm))
    | (simp only [h13, h24, h14, Bool.and_self, Bool.true_and, Bool.and_true, beq_self_eq_true])
    | skip
  all_goals simp_all

/-! ### Averaging an exact certificate -/

/-- The colours of four lists with given membership bits. -/
def atomSet (B₁ B₂ B₃ B₄ : Finset ℕ) (m : Mem) : Finset ℕ :=
  (B₁ ∪ B₂ ∪ B₃ ∪ B₄).filter (fun c => memv B₁ B₂ B₃ B₄ c = m)

/-- The rows of a column, by index. -/
def rowfun : Fin 4 → T4 → ℕ
  | 0 => r1
  | 1 => r2
  | 2 => r3
  | 3 => r4

theorem rowsel_memv (B₁ B₂ B₃ B₄ : Finset ℕ) (s : T4) (i : Fin 4) :
    rowsel (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s)) (memv B₁ B₂ B₃ B₄ (r3 s))
      (memv B₁ B₂ B₃ B₄ (r4 s)) i = memv B₁ B₂ B₃ B₄ (rowfun i s) := by
  fin_cases i <;> rfl

theorem mem_atomSet {B₁ B₂ B₃ B₄ : Finset ℕ} {m : Mem} (hm : m ≠ (false, false, false, false))
    (c : ℕ) : memv B₁ B₂ B₃ B₄ c = m ↔ c ∈ atomSet B₁ B₂ B₃ B₄ m := by
  unfold atomSet
  rw [Finset.mem_filter]
  constructor
  · intro h
    refine ⟨?_, h⟩
    by_contra hc
    simp only [Finset.mem_union, not_or] at hc
    apply hm; rw [← h]; simp [memv, hc]
  · exact fun h => h.2

theorem pins_avg {Ω : Finset T4} (u : T4 → ℝ) (hu0 : ∀ t, 0 ≤ u t) {m q : ℝ} (hm : 0 < m)
    (hq0 : 0 ≤ q)
    (hf : ∀ i : Fin 4, ∀ c, m * ∑ t ∈ Ω.filter (fun t => rowfun i t = c), u t
      ≤ (m * q) * ∑ t ∈ Ω, u t) (B₁ B₂ B₃ B₄ : Finset ℕ) :
    ∀ L : List Pin, lamnonneg L = true →
      (∀ p ∈ L, ((atomSet B₁ B₂ B₃ B₄ p.2.1).card : ℤ) ≤ p.2.2.2) →
      ∑ s ∈ Ω, u s * (pinsum L (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s))
          (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s)) : ℝ)
        ≤ q * (lamsize L : ℝ) * ∑ s ∈ Ω, u s
  | [], _, _ => by simp [pinsum, lamsize]
  | p :: L, hL, hs => by
    simp only [lamnonneg, Bool.and_eq_true, decide_eq_true_eq] at hL
    obtain ⟨⟨hp, hpm⟩, hL⟩ := hL
    have ih := pins_avg u hu0 hm hq0 hf B₁ B₂ B₃ B₄ L hL (fun p' hp' => hs p' (List.mem_cons_of_mem _ hp'))
    have hsz := hs p List.mem_cons_self
    -- the first pin
    have hfib := fibre_mem u (rowfun p.1) (hf p.1) (atomSet B₁ B₂ B₃ B₄ p.2.1)
    have e1 : ∑ s ∈ Ω, u s * (if rowfun p.1 s ∈ atomSet B₁ B₂ B₃ B₄ p.2.1 then (1 : ℝ) else 0)
        = ∑ s ∈ Ω, u s * (if rowsel (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s))
            (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s)) p.1 = p.2.1 then (1 : ℝ) else 0) := by
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [rowsel_memv]
      have hiff := mem_atomSet (B₁ := B₁) (B₂ := B₂) (B₃ := B₃) (B₄ := B₄) hpm (rowfun p.1 s)
      by_cases h : memv B₁ B₂ B₃ B₄ (rowfun p.1 s) = p.2.1
      · rw [if_pos (hiff.mp h), if_pos h]
      · rw [if_neg (fun h' => h (hiff.mpr h')), if_neg h]
    rw [e1] at hfib
    have hW0 : 0 ≤ ∑ s ∈ Ω, u s := Finset.sum_nonneg (fun s _ => hu0 s)
    have hp' : (0 : ℝ) ≤ p.2.2.1 := by exact_mod_cast hp
    have hsz' : ((atomSet B₁ B₂ B₃ B₄ p.2.1).card : ℝ) ≤ (p.2.2.2 : ℝ) := by exact_mod_cast hsz
    have b1 : ∑ s ∈ Ω, u s * (if rowsel (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s))
        (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s)) p.1 = p.2.1 then (1 : ℝ) else 0)
        ≤ q * (p.2.2.2 : ℝ) * ∑ s ∈ Ω, u s := by
      have h2 : m * q * ((atomSet B₁ B₂ B₃ B₄ p.2.1).card : ℝ) * ∑ s ∈ Ω, u s
          ≤ m * q * (p.2.2.2 : ℝ) * ∑ s ∈ Ω, u s :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsz' (mul_nonneg hm.le hq0)) hW0
      have h3 := hfib.trans h2
      have : m * (∑ s ∈ Ω, u s * (if rowsel (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s))
          (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s)) p.1 = p.2.1 then (1 : ℝ) else 0))
          ≤ m * (q * (p.2.2.2 : ℝ) * ∑ s ∈ Ω, u s) := h3.trans_eq (by ring)
      exact le_of_mul_le_mul_left this hm
    have e2 : ∑ s ∈ Ω, u s * (pinsum (p :: L) (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s))
          (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s)) : ℝ)
        = (p.2.2.1 : ℝ) * ∑ s ∈ Ω, u s * (if rowsel (memv B₁ B₂ B₃ B₄ (r1 s))
            (memv B₁ B₂ B₃ B₄ (r2 s)) (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s)) p.1
            = p.2.1 then (1 : ℝ) else 0)
          + ∑ s ∈ Ω, u s * (pinsum L (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s))
            (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s)) : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      simp only [pinsum]; push_cast; split_ifs <;> ring
    rw [e2]
    have : (p.2.2.1 : ℝ) * ∑ s ∈ Ω, u s * (if rowsel (memv B₁ B₂ B₃ B₄ (r1 s))
        (memv B₁ B₂ B₃ B₄ (r2 s)) (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s)) p.1
        = p.2.1 then (1 : ℝ) else 0) ≤ (p.2.2.1 : ℝ) * (q * (p.2.2.2 : ℝ) * ∑ s ∈ Ω, u s) :=
      mul_le_mul_of_nonneg_left b1 hp'
    simp only [lamsize]; push_cast
    nlinarith

theorem bi_cast (p : Prop) [Decidable p] : ((bi (decide p) : ℤ) : ℝ) = if p then 1 else 0 := by
  unfold bi; split_ifs <;> simp_all

end GridGen.Four
