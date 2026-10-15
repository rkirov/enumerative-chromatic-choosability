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
function of the Venn sizes of `B` and the bits of `s` (`GB_cls`). The uniform side `GU` depends on
the pattern bits only (`GU_urow`).

This is the computational core of the exact certificates for small mismatches at `k = 7`
(`GridGen/Four/Small7.lean`).
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

theorem bi_and (p q : Prop) [Decidable p] [Decidable q] :
    bi (decide (p ∧ q)) = bi (decide p && decide q) := by
  unfold bi; by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

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

/-- The uniform class coefficients at `k = 7` (`ℓ = 5`), by pattern. -/
def urow (e13 e24 e14 : Bool) : ℤ × ℤ × ℤ × ℤ :=
  if e13 && e24 then (31, 260, 105, 440)
  else if e13 || e24 then (26, 244, 109, 452)
  else if e14 then (21, 218, 134, 452)
  else (22, 226, 113, 465)

/-- **The uniform side at `k = 7`, by pattern.** -/
theorem GU_urow (w : Wt) {s : T4} (hs : Proper s) :
    GU 7 w s = ((urow (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))).1 : ℝ)
      + ((urow (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))).2.1 : ℝ) * w.a
      + ((urow (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))).2.2.1 : ℝ)
          * w.b
      + ((urow (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))).2.2.2 : ℝ)
          * w.c := by
  have hs' := hs
  obtain ⟨p12, p23, p34⟩ := hs'
  rcases canon_cases hs with h | h | h | h | h
  · rw [GU_eq_of_canon w h (by decide), GU_0101 (by norm_num) w]
    have b : r3 s = r1 s ∧ r4 s = r2 s := by
      unfold canon at h; simp only [Prod.mk.injEq] at h; split_ifs at h <;> simp_all
    simp [urow, b.1.symm, b.2.symm, vA, aff]; norm_num
  · rw [GU_eq_of_canon w h (by decide), GU_0102 (by norm_num) w]
    have b : r3 s = r1 s ∧ r4 s ≠ r2 s ∧ r4 s ≠ r1 s := by
      unfold canon at h; simp only [Prod.mk.injEq] at h; split_ifs at h <;> simp_all
    have b2 : r2 s ≠ r4 s := fun e => b.2.1 e.symm
    have b3 : r1 s ≠ r4 s := fun e => b.2.2 e.symm
    simp [urow, b.1.symm, b2, vB, aff]; norm_num
  · rw [GU_eq_of_canon w h (by decide), GU_0121 (by norm_num) w]
    have b : r3 s ≠ r1 s ∧ r4 s = r2 s := by
      unfold canon at h; simp only [Prod.mk.injEq] at h; split_ifs at h <;> simp_all
    have b1 : r1 s ≠ r3 s := fun e => b.1 e.symm
    have b3 : r1 s ≠ r4 s := fun e => p12 (e.trans b.2)
    simp [urow, b1, b.2.symm, vB, aff]; norm_num
  · rw [GU_eq_of_canon w h (by decide), GU_0120 (by norm_num) w]
    have b : r3 s ≠ r1 s ∧ r4 s ≠ r2 s ∧ r4 s = r1 s := by
      unfold canon at h; simp only [Prod.mk.injEq] at h; split_ifs at h <;> simp_all
    have b1 : r1 s ≠ r3 s := fun e => b.1 e.symm
    have b2 : r2 s ≠ r4 s := fun e => b.2.1 e.symm
    simp [urow, b1, b2, b.2.2.symm, Ne.symm p34, vC, aff]; norm_num
  · rw [GU_eq_of_canon w h (by decide), GU_0123 (by norm_num) w]
    have b : r3 s ≠ r1 s ∧ r4 s ≠ r2 s ∧ r4 s ≠ r1 s := by
      unfold canon at h; simp only [Prod.mk.injEq] at h; split_ifs at h <;> simp_all
    have b1 : r1 s ≠ r3 s := fun e => b.1 e.symm
    have b2 : r2 s ≠ r4 s := fun e => b.2.1 e.symm
    have b3 : r1 s ≠ r4 s := fun e => b.2.2 e.symm
    simp [urow, b1, b2, b3, vD, aff]; norm_num

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

/-- The numerator of the gain `y` of a column, over `D`. -/
def yNum (sp : Spec) (r1 r2 r3 r4 : Mem) (e13 e24 : Bool) : ℤ :=
  sp.K - pinsum sp.pins r1 r2 r3 r4 - bi e13 * sp.l13 - bi e24 * sp.l24

/-- The check for one column type: `(1 - y)·GB ≥ GU` on the box, `ρ = 123/125`. -/
def okc (sp : Spec) (r1 r2 r3 r4 : Mem) (e13 e24 e14 : Bool) : Bool :=
  let cA := cls (dat sp.venn r1 r2 r3 r4 e13 e24 e14)
  let cU := urow e13 e24 e14
  let Y := yNum sp r1 r2 r3 r4 e13 e24
  let d0 := (sp.D - Y) * cA.1 - sp.D * cU.1
  let d1 := (sp.D - Y) * cA.2.1 - sp.D * cU.2.1
  let d2 := (sp.D - Y) * cA.2.2.1 - sp.D * cU.2.2.1
  let d3 := (sp.D - Y) * cA.2.2.2 - sp.D * cU.2.2.2
  decide (0 ≤ 125 * d0 + min (123 * d1) (125 * d1) + min (123 * d2) (125 * d2)
    + min (123 * d3) (125 * d3))

/-- The bits of a proper column are consistent. -/
def valid (r1 r2 r3 r4 : Mem) (e13 e24 e14 : Bool) : Bool :=
  !(e13 && e14) && !(e24 && e14) && (!e13 || r1 == r3) && (!e24 || r2 == r4) && (!e14 || r1 == r4)

/-- **The certificate check** over all column types. -/
def allOk (sp : Spec) : Bool :=
  let ats := sp.atoms ++ [(false, false, false, false)]
  ats.all fun r1 => ats.all fun r2 => ats.all fun r3 => ats.all fun r4 =>
    [false, true].all fun e13 => [false, true].all fun e24 => [false, true].all fun e14 =>
      !valid r1 r2 r3 r4 e13 e24 e14 || okc sp r1 r2 r3 r4 e13 e24 e14

/-- The scalar conditions: `0 < D`, `|y| < 1`, and the averaged gain `K - q Σ λ|R| ≥ 0` with
`q = 125/492` (`k = 7`). -/
def specOk (sp : Spec) : Bool :=
  decide (0 < sp.D) && decide (sp.K < sp.D) && decide (0 ≤ sp.l13) && decide (0 ≤ sp.l24)
    && lamnonneg sp.pins && decide (0 ≤ sp.D + sp.K - lamsum sp.pins - sp.l13 - sp.l24)
    && decide (125 * (lamsize sp.pins + sp.l13 + sp.l24) ≤ 492 * sp.K)

/-! ### The bound for one state from a certificate -/

theorem rho_seven : rho 7 = 123 / 125 := by norm_num [rho]

theorem lin_min {d x : ℝ} (hx0 : 123 / 125 ≤ x) (hx1 : x ≤ 1) :
    min (123 * d) (125 * d) / 125 ≤ d * x := by
  rcases le_total 0 d with hd | hd
  · rw [min_eq_left (by linarith)]; nlinarith
  · rw [min_eq_right (by linarith)]; nlinarith

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

theorem okc_of (sp : Spec) (hok : allOk sp = true) {B₁ B₂ B₃ B₄ : Finset ℕ}
    (hat : ∀ c, memv B₁ B₂ B₃ B₄ c ∈ sp.atoms ∨ memv B₁ B₂ B₃ B₄ c = (false, false, false, false))
    {s : T4} (hs : Proper s) :
    okc sp (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s)) (memv B₁ B₂ B₃ B₄ (r3 s))
      (memv B₁ B₂ B₃ B₄ (r4 s)) (decide (r1 s = r3 s)) (decide (r2 s = r4 s))
      (decide (r1 s = r4 s)) = true := by
  have hmem : ∀ c, memv B₁ B₂ B₃ B₄ c ∈ sp.atoms ++ [(false, false, false, false)] := by
    intro c; rcases hat c with h | h
    · exact List.mem_append_left _ h
    · rw [h]; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hb : ∀ b : Bool, b ∈ [false, true] := by intro b; cases b <;> simp
  unfold allOk at hok
  simp only [List.all_eq_true] at hok
  have := hok (memv B₁ B₂ B₃ B₄ (r1 s)) (hmem _) (memv B₁ B₂ B₃ B₄ (r2 s)) (hmem _)
    (memv B₁ B₂ B₃ B₄ (r3 s)) (hmem _) (memv B₁ B₂ B₃ B₄ (r4 s)) (hmem _)
    (decide (r1 s = r3 s)) (hb _) (decide (r2 s = r4 s)) (hb _) (decide (r1 s = r4 s)) (hb _)
  rw [valid_of B₁ B₂ B₃ B₄ hs] at this
  simpa using this

/-- **The bound for one state from an exact certificate**, `k = 7`. -/
theorem exact_state (sp : Spec) (hok : allOk sp = true) (hsp : specOk sp = true)
    {B₁ B₂ B₃ B₄ : Finset ℕ} (hv : sp.venn = vennOf B₁ B₂ B₃ B₄)
    (hat : ∀ c, memv B₁ B₂ B₃ B₄ c ∈ sp.atoms ∨ memv B₁ B₂ B₃ B₄ c = (false, false, false, false))
    {w : Wt} (hw : InBox 7 w) {s : T4} (hs : Proper s) :
    GU 7 w s * (1 + (yNum sp (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s))
        (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s)) (decide (r1 s = r3 s))
        (decide (r2 s = r4 s)) : ℝ) / sp.D)
      ≤ GB w B₁ B₂ B₃ B₄ s := by
  have hc := okc_of sp hok hat hs
  simp only [specOk, Bool.and_eq_true, decide_eq_true_eq] at hsp
  obtain ⟨⟨⟨⟨⟨⟨hD, hKD⟩, h13⟩, h24⟩, hL⟩, hlow⟩, -⟩ := hsp
  set Y := yNum sp (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s))
    (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s)) (decide (r1 s = r3 s))
    (decide (r2 s = r4 s)) with hY
  -- `-D ≤ Y < D`
  have hYb : -sp.D ≤ Y ∧ Y < sp.D := by
    obtain ⟨p0, p1⟩ := pinsum_bounds sp.pins hL (memv B₁ B₂ B₃ B₄ (r1 s))
      (memv B₁ B₂ B₃ B₄ (r2 s)) (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s))
    have b13 : 0 ≤ bi (decide (r1 s = r3 s)) ∧ bi (decide (r1 s = r3 s)) ≤ 1 := by
      unfold bi; split_ifs <;> norm_num
    have b24 : 0 ≤ bi (decide (r2 s = r4 s)) ∧ bi (decide (r2 s = r4 s)) ≤ 1 := by
      unfold bi; split_ifs <;> norm_num
    rw [hY, yNum]
    constructor <;> nlinarith
  -- the integer inequality
  set cA := cls (dat sp.venn (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s))
    (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s)) (decide (r1 s = r3 s))
    (decide (r2 s = r4 s)) (decide (r1 s = r4 s))) with hcA
  set cU := urow (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) with hcU
  have hint : 0 ≤ 125 * ((sp.D - Y) * cA.1 - sp.D * cU.1)
      + min (123 * ((sp.D - Y) * cA.2.1 - sp.D * cU.2.1)) (125 * ((sp.D - Y) * cA.2.1 - sp.D * cU.2.1))
      + min (123 * ((sp.D - Y) * cA.2.2.1 - sp.D * cU.2.2.1))
          (125 * ((sp.D - Y) * cA.2.2.1 - sp.D * cU.2.2.1))
      + min (123 * ((sp.D - Y) * cA.2.2.2 - sp.D * cU.2.2.2))
          (125 * ((sp.D - Y) * cA.2.2.2 - sp.D * cU.2.2.2)) := by
    simpa [okc] using hc
  -- the real counts
  have hGB : GB w B₁ B₂ B₃ B₄ s = (cA.1 : ℝ) + (cA.2.1 : ℝ) * w.a + (cA.2.2.1 : ℝ) * w.b
      + (cA.2.2.2 : ℝ) * w.c := by
    rw [GB_cls, dat_eq B₁ B₂ B₃ B₄ hs, ← hv]
  have hGU : GU 7 w s = (cU.1 : ℝ) + (cU.2.1 : ℝ) * w.a + (cU.2.2.1 : ℝ) * w.b
      + (cU.2.2.2 : ℝ) * w.c := GU_urow w hs
  have hw' := hw
  obtain ⟨ha0, ha1, hb0, hb1, hc0, hc1⟩ := hw
  rw [rho_seven] at ha0 hb0 hc0
  have hint' : (0 : ℝ) ≤ 125 * (((sp.D - Y) * cA.1 - sp.D * cU.1 : ℤ) : ℝ)
      + min (123 * (((sp.D - Y) * cA.2.1 - sp.D * cU.2.1 : ℤ) : ℝ))
          (125 * (((sp.D - Y) * cA.2.1 - sp.D * cU.2.1 : ℤ) : ℝ))
      + min (123 * (((sp.D - Y) * cA.2.2.1 - sp.D * cU.2.2.1 : ℤ) : ℝ))
          (125 * (((sp.D - Y) * cA.2.2.1 - sp.D * cU.2.2.1 : ℤ) : ℝ))
      + min (123 * (((sp.D - Y) * cA.2.2.2 - sp.D * cU.2.2.2 : ℤ) : ℝ))
          (125 * (((sp.D - Y) * cA.2.2.2 - sp.D * cU.2.2.2 : ℤ) : ℝ)) := by
    have := (Int.cast_le (R := ℝ)).mpr hint
    push_cast at this ⊢
    simpa [Int.cast_min] using this
  have m1 := lin_min (d := (((sp.D - Y) * cA.2.1 - sp.D * cU.2.1 : ℤ) : ℝ)) ha0 ha1
  have m2 := lin_min (d := (((sp.D - Y) * cA.2.2.1 - sp.D * cU.2.2.1 : ℤ) : ℝ)) hb0 hb1
  have m3 := lin_min (d := (((sp.D - Y) * cA.2.2.2 - sp.D * cU.2.2.2 : ℤ) : ℝ)) hc0 hc1
  have key : (sp.D : ℝ) * GU 7 w s ≤ ((sp.D : ℝ) - Y) * GB w B₁ B₂ B₃ B₄ s := by
    rw [hGB, hGU]
    push_cast at m1 m2 m3 hint' ⊢
    nlinarith
  -- `GU (1 + y) ≤ GB`
  have hDpos : (0 : ℝ) < sp.D := by exact_mod_cast hD
  have hY1 : (-(sp.D : ℝ)) ≤ Y := by exact_mod_cast hYb.1
  have hGB0 : 0 ≤ GB w B₁ B₂ B₃ B₄ s := by
    unfold GB G
    exact Finset.sum_nonneg (fun t _ => (rho_pos' (by norm_num)).le.trans (gw_mem hw' t).1)
  have hYsq : (0 : ℝ) ≤ (Y : ℝ) ^ 2 := sq_nonneg _
  have hDY : (0 : ℝ) ≤ (sp.D : ℝ) + Y := by linarith
  have hfin : GU 7 w s * ((sp.D : ℝ) + Y) * sp.D ≤ GB w B₁ B₂ B₃ B₄ s * (sp.D : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left key hDY
    nlinarith [mul_nonneg hYsq hGB0]
  rw [show (1 : ℝ) + (Y : ℝ) / sp.D = ((sp.D : ℝ) + Y) / sp.D by field_simp, mul_div_assoc',
    div_le_iff₀ hDpos]
  nlinarith

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

theorem qk_seven : qk 7 = 125 / 492 := by norm_num [qk, rho]

theorem bi_cast (p : Prop) [Decidable p] : ((bi (decide p) : ℤ) : ℝ) = if p then 1 else 0 := by
  unfold bi; split_ifs <;> simp_all

/-- **The seam inequality at `k = 7` from an exact certificate** for the lists `B`. -/
theorem exact_seam (sp : Spec) (hok : allOk sp = true) (hsp : specOk sp = true)
    {B₁ B₂ B₃ B₄ : Finset ℕ} (hv : sp.venn = vennOf B₁ B₂ B₃ B₄)
    (hat : ∀ c, memv B₁ B₂ B₃ B₄ c ∈ sp.atoms ∨ memv B₁ B₂ B₃ B₄ c = (false, false, false, false))
    (hsize : ∀ p ∈ sp.pins, ((atomSet B₁ B₂ B₃ B₄ p.2.1).card : ℤ) ≤ p.2.2.2)
    {w : Wt} (hw : InBox 7 w) {X₁ X₂ X₃ X₄ : Finset ℕ}
    (hX₁ : 7 - 1 ≤ X₁.card) (hX₂ : 7 - 1 ≤ X₂.card) (hX₃ : 7 - 1 ≤ X₃.card)
    (hX₄ : 7 - 1 ≤ X₄.card) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 7 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄, GB w B₁ B₂ B₃ B₄ s := by
  have hsp' := hsp
  simp only [specOk, Bool.and_eq_true, decide_eq_true_eq] at hsp'
  obtain ⟨⟨⟨⟨⟨⟨hD, -⟩, h13⟩, h24⟩, hL⟩, -⟩, hK⟩ := hsp'
  obtain ⟨-, -, -, -, hq0, hRq, -⟩ := consts_sign (k := 7) (by norm_num)
  have hm : (0 : ℝ) < ((7 - 3 : ℕ) : ℝ) := by norm_num
  set m : ℝ := ((7 - 3 : ℕ) : ℝ) with hm_def
  set Ω := sts X₁ X₂ X₃ X₄ with hΩ
  set u : T4 → ℝ := GU 7 w with hu
  have hu0 : ∀ t, 0 ≤ u t := GU_nonneg (by norm_num) hw
  set q := qk 7 with hq
  have hR0 : 0 ≤ m * q := (mul_pos hm hq0).le
  have hR : ∀ t ∈ Ω, ∀ t' ∈ Ω, u t ≤ (m * q) * u t' := fun t ht t' ht' => by
    rw [← hRq]; exact GU_ratio (by norm_num) hw (proper_of_mem_sts ht) (proper_of_mem_sts ht')
  have hf : ∀ i : Fin 4, ∀ c, m * ∑ t ∈ Ω.filter (fun t => rowfun i t = c), u t
      ≤ (m * q) * ∑ t ∈ Ω, u t := by
    intro i c
    fin_cases i
    · exact fibre_sts1 u hu0 (fun t => r1 t = c) hX₁ hX₂ hX₃ hX₄ hR0 hR (fun _ => c)
        (fun _ _ => rfl) (fun _ h => h)
    · exact fibre_sts2 u hu0 (fun t => r2 t = c) hX₁ hX₂ hX₃ hX₄ hR0 hR (fun _ => c)
        (fun _ _ => rfl) (fun _ h => h)
    · exact fibre_sts3 u hu0 (fun t => r3 t = c) hX₁ hX₂ hX₃ hX₄ hR0 hR (fun _ => c)
        (fun _ _ => rfl) (fun _ h => h)
    · exact fibre_sts4 u hu0 (fun t => r4 t = c) hX₁ hX₂ hX₃ hX₄ hR0 hR (fun _ => c)
        (fun _ _ => rfl) (fun _ h => h)
  set Y : T4 → ℤ := fun s => yNum sp (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s))
    (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s)) (decide (r1 s = r3 s))
    (decide (r2 s = r4 s)) with hYdef
  have hDpos : (0 : ℝ) < sp.D := by exact_mod_cast hD
  have hsum : ∑ s ∈ Ω, u s * (1 + (Y s : ℝ) / sp.D) ≤ ∑ s ∈ Ω, GB w B₁ B₂ B₃ B₄ s :=
    Finset.sum_le_sum (fun s hs => exact_state sp hok hsp hv hat hw (proper_of_mem_sts hs))
  suffices h : 0 ≤ ∑ s ∈ Ω, u s * (Y s : ℝ) by
    have e : ∑ s ∈ Ω, u s * (1 + (Y s : ℝ) / sp.D)
        = ∑ s ∈ Ω, u s + (∑ s ∈ Ω, u s * (Y s : ℝ)) / sp.D := by
      rw [Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    have : 0 ≤ (∑ s ∈ Ω, u s * (Y s : ℝ)) / sp.D := div_nonneg h hDpos.le
    linarith
  set W := ∑ s ∈ Ω, u s with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun s _ => hu0 s)
  set P := ∑ s ∈ Ω, u s * (pinsum sp.pins (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s))
    (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s)) : ℝ) with hP
  set C13 := ∑ s ∈ Ω, u s * c13 s with hC13
  set C24 := ∑ s ∈ Ω, u s * c24 s with hC24
  have e : ∑ s ∈ Ω, u s * (Y s : ℝ)
      = (sp.K : ℝ) * W - P - (sp.l13 : ℝ) * C13 - (sp.l24 : ℝ) * C24 := by
    rw [hW, hP, hC13, hC24]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [hYdef, yNum]
    push_cast
    rw [bi_cast, bi_cast]
    unfold c13 c24
    ring
  rw [e]
  have bP := pins_avg u hu0 hm hq0.le hf B₁ B₂ B₃ B₄ sp.pins hL hsize
  have bC13 : m * C13 ≤ (m * q) * W := by
    rw [hC13]
    have : ∑ s ∈ Ω, u s * c13 s = ∑ s ∈ Ω.filter (fun t => r1 t = r3 t), u s := by
      rw [← sum_mul_ite]; rfl
    rw [this]
    exact fibre_sts1 u hu0 (fun t => r1 t = r3 t) hX₁ hX₂ hX₃ hX₄ hR0 hR r3
      (fun _ _ => rfl) (fun _ h => h)
  have bC24 : m * C24 ≤ (m * q) * W := by
    rw [hC24]
    have : ∑ s ∈ Ω, u s * c24 s = ∑ s ∈ Ω.filter (fun t => r2 t = r4 t), u s := by
      rw [← sum_mul_ite]; rfl
    rw [this]
    exact fibre_sts2 u hu0 (fun t => r2 t = r4 t) hX₁ hX₂ hX₃ hX₄ hR0 hR r4
      (fun _ _ => rfl) (fun _ h => h)
  have c13' : C13 ≤ q * W := le_of_mul_le_mul_left (bC13.trans_eq (by ring)) hm
  have c24' : C24 ≤ q * W := le_of_mul_le_mul_left (bC24.trans_eq (by ring)) hm
  have h13' : (0 : ℝ) ≤ sp.l13 := by exact_mod_cast h13
  have h24' : (0 : ℝ) ≤ sp.l24 := by exact_mod_cast h24
  have hK' : (125 : ℝ) * ((lamsize sp.pins : ℝ) + sp.l13 + sp.l24) ≤ 492 * sp.K := by
    exact_mod_cast hK
  have hqv : q = 125 / 492 := qk_seven
  have i1 := mul_le_mul_of_nonneg_left c13' h13'
  have i2 := mul_le_mul_of_nonneg_left c24' h24'
  have i3 : (125 / 492 : ℝ) * ((lamsize sp.pins : ℝ) + sp.l13 + sp.l24) * W ≤ (sp.K : ℝ) * W :=
    mul_le_mul_of_nonneg_right (by linarith) hW0
  rw [hqv] at bP i1 i2
  nlinarith

end GridGen.Four
