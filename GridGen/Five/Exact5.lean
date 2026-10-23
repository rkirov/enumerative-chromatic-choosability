/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Small5.Count
import GridGen.Five.Small5.Fibre

/-!
# Height five, `k = 6`: the exact-certificate checker

`GridGen/Four/Exact.lean` and `Exact6.lean` with five rows, reorganised so that a column type
costs a few milliseconds of kernel time. The mathematics is that of Four: for lists `B₁, …, B₅`
and a proper column `s`, the successor lists are `Aᵢ = Bᵢ.erase sᵢ`; the weighted successor
count `GB` is a combination of orbit counts, which are integer polynomials in the Venn sizes of
`A` (`GridGen/Five/Small5/Count.lean`), and the Venn sizes of `A` are those of `B` minus a
correction determined by the *column type*: the equality pattern of `s` and the membership
vector (atom) of each of its colours. A certificate gives multipliers (pins) for the events
"row `r` lies in atom `m`" and "`sᵢ = sⱼ`"; each column type is checked to satisfy
`GU · (1 + y) ≤ GB` on the whole box (`exact_state5`), with `y` the pinned gain, and the
averaged gain is nonnegative by the fibre bounds (`exact_seam5`).

**Encoding.** A row set or an atom is a five-bit mask (bit `i` for row `i + 1`). The 31 Venn
sizes are packed into one natural number, four bits each (`packV`). Each colour of the column
(one per block of its pattern, represented by its first row) moves from its atom out of the lists
of its block, which lowers the Venn sizes by a fixed packed vector (`vecP`). A colour in no list of
its block changes nothing and may be treated as lying in no list at all (the touching reduction
R1 of `ai_research_notes/H5_K6_SYMBOLIC_2026-10-23.md`): its atom is replaced by `0`
(`ratom`). The check enumerates, block by block, the possible atoms with their packed corrections
and pin sums (`enumP`), so that each column type costs a few subtractions, the class counts
(`cls5`) and the box test (`okc`).

**The check.** For a column type with orbit-count vector `c` of `A` and uniform vector `u`
(`Vmat`), and `e = D + K - pins`, the test is `e · Σ uₒwₒ ≤ D · Σ cₒwₒ` for every `w` in the box;
both sides are linear in `w`, so it is separable: `2000·d₀ + Σ_{o ≥ 1} min(Lₒ dₒ, 2000 dₒ) ≥ 0`
with `dₒ = D cₒ - e uₒ` and `Lₒ = 2000·lo5 o`. This is the weaker form `GU (1 + y) ≤ GB` of the
symbolic note (`exact_state6` needs no more).
-/

namespace GridGen.Five.Ex5

open Finset

/-! ### Rows, masks and lists -/

/-- The rows of a mask. -/
def rowsOf (I : ℕ) : List ℕ := (List.range 5).filter (fun i => I.testBit i)

/-- Five lists as a function of the row index. -/
def bl (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (i : ℕ) : Finset ℕ :=
  match i with
  | 0 => B₁
  | 1 => B₂
  | 2 => B₃
  | 3 => B₄
  | _ => B₅

/-- The intersection of the lists of a nonempty row list (left-nested). -/
def interL (F : ℕ → Finset ℕ) : List ℕ → Finset ℕ
  | [] => ∅
  | i :: L => L.foldl (fun acc j => acc ∩ F j) (F i)

theorem mem_foldl_inter (F : ℕ → Finset ℕ) (c : ℕ) :
    ∀ (L : List ℕ) (S : Finset ℕ),
      c ∈ L.foldl (fun acc j => acc ∩ F j) S ↔ c ∈ S ∧ ∀ j ∈ L, c ∈ F j
  | [], S => by simp
  | j :: L, S => by
    rw [List.foldl_cons, mem_foldl_inter F c L]
    simp only [Finset.mem_inter, List.mem_cons, forall_eq_or_imp]
    tauto

theorem mem_interL (F : ℕ → Finset ℕ) (i : ℕ) (L : List ℕ) (c : ℕ) :
    c ∈ interL F (i :: L) ↔ ∀ j ∈ i :: L, c ∈ F j := by
  rw [interL, mem_foldl_inter]
  simp

/-- The membership vector of a colour: bit `i` for the list `Bᵢ₊₁`. -/
def memv5 (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (c : ℕ) : ℕ :=
  (if c ∈ B₁ then 1 else 0) + (if c ∈ B₂ then 2 else 0) + (if c ∈ B₃ then 4 else 0)
    + (if c ∈ B₄ then 8 else 0) + (if c ∈ B₅ then 16 else 0)

/-- A mask from five bits. -/
def mk5 (b0 b1 b2 b3 b4 : Bool) : ℕ :=
  cond b0 1 0 + cond b1 2 0 + cond b2 4 0 + cond b3 8 0 + cond b4 16 0

/-- The bit of a row. -/
def getb (b0 b1 b2 b3 b4 : Bool) (i : ℕ) : Bool :=
  match i with
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | 3 => b3
  | _ => b4

theorem land_mk5_table : ∀ I ∈ List.range 32, ∀ b0 b1 b2 b3 b4 : Bool,
    decide (Nat.land I (mk5 b0 b1 b2 b3 b4) = I) = (rowsOf I).all (getb b0 b1 b2 b3 b4) := by
  decide +kernel

theorem mk5_lt (b0 b1 b2 b3 b4 : Bool) : mk5 b0 b1 b2 b3 b4 < 32 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

theorem memv5_eq (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (c : ℕ) :
    memv5 B₁ B₂ B₃ B₄ B₅ c = mk5 (decide (c ∈ B₁)) (decide (c ∈ B₂)) (decide (c ∈ B₃))
      (decide (c ∈ B₄)) (decide (c ∈ B₅)) := by
  unfold memv5 mk5
  by_cases h1 : c ∈ B₁ <;> by_cases h2 : c ∈ B₂ <;> by_cases h3 : c ∈ B₃ <;>
    by_cases h4 : c ∈ B₄ <;> by_cases h5 : c ∈ B₅ <;> simp [h1, h2, h3, h4, h5]

theorem memv5_lt (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (c : ℕ) : memv5 B₁ B₂ B₃ B₄ B₅ c < 32 := by
  rw [memv5_eq]; exact mk5_lt _ _ _ _ _

theorem rowsOf_lt {I i : ℕ} (h : i ∈ rowsOf I) : i < 5 := by
  unfold rowsOf at h
  rw [List.mem_filter, List.mem_range] at h
  exact h.1

theorem getb_decide (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (c : ℕ) {i : ℕ} (hi : i < 5) :
    getb (decide (c ∈ B₁)) (decide (c ∈ B₂)) (decide (c ∈ B₃)) (decide (c ∈ B₄))
      (decide (c ∈ B₅)) i = decide (c ∈ bl B₁ B₂ B₃ B₄ B₅ i) := by
  interval_cases i <;> rfl

/-- **The bits of a colour**: `I ⊆ memv c` iff the colour lies in every list of `I`. -/
theorem land_memv5 (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) {I : ℕ} (hI : I < 32) (c : ℕ) :
    Nat.land I (memv5 B₁ B₂ B₃ B₄ B₅ c) = I ↔ ∀ i ∈ rowsOf I, c ∈ bl B₁ B₂ B₃ B₄ B₅ i := by
  have h := land_mk5_table I (List.mem_range.mpr hI) (decide (c ∈ B₁)) (decide (c ∈ B₂))
    (decide (c ∈ B₃)) (decide (c ∈ B₄)) (decide (c ∈ B₅))
  rw [← memv5_eq] at h
  have h' : Nat.land I (memv5 B₁ B₂ B₃ B₄ B₅ c) = I ↔
      (rowsOf I).all (getb (decide (c ∈ B₁)) (decide (c ∈ B₂)) (decide (c ∈ B₃))
        (decide (c ∈ B₄)) (decide (c ∈ B₅))) = true := by
    rw [← h, decide_eq_true_iff]
  rw [h', List.all_eq_true]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  rw [getb_decide B₁ B₂ B₃ B₄ B₅ c (rowsOf_lt hi), decide_eq_true_iff]

/-! ### Erasing the colours of a column -/

theorem interL_erase (F : ℕ → Finset ℕ) (σ : ℕ → ℕ) (i : ℕ) (L : List ℕ) :
    interL (fun j => (F j).erase (σ j)) (i :: L) = interL F (i :: L) \ ((i :: L).map σ).toFinset := by
  ext c
  rw [mem_interL, Finset.mem_sdiff, mem_interL, List.mem_toFinset, List.mem_map]
  simp only [Finset.mem_erase]
  constructor
  · intro h
    exact ⟨fun j hj => (h j hj).2, fun ⟨j, hj, e⟩ => (h j hj).1 e.symm⟩
  · rintro ⟨h, hn⟩ j hj
    exact ⟨fun e => hn ⟨j, hj, e.symm⟩, h j hj⟩

/-- `k` is the first row of its colour. -/
def repS (σ : ℕ → ℕ) (k : ℕ) : Prop := ∀ j < k, σ j ≠ σ k

instance (σ : ℕ → ℕ) (k : ℕ) : Decidable (repS σ k) := by unfold repS; infer_instance

/-- **The colours of a column in a set, counted by first rows.** -/
theorem card_inter_image (σ : ℕ → ℕ) (X : Finset ℕ) (L : List ℕ) (hL : ∀ i ∈ L, i < 5) :
    (X ∩ (L.map σ).toFinset).card
      = ((range 5).filter (fun k => repS σ k ∧ (∃ i ∈ L, σ i = σ k) ∧ σ k ∈ X)).card := by
  classical
  have himg : X ∩ (L.map σ).toFinset
      = ((range 5).filter (fun k => repS σ k ∧ (∃ i ∈ L, σ i = σ k) ∧ σ k ∈ X)).image σ := by
    ext c
    simp only [Finset.mem_inter, List.mem_toFinset, List.mem_map, Finset.mem_image,
      Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hX, i, hi, rfl⟩
      have hex : ∃ k, σ k = σ i := ⟨i, rfl⟩
      refine ⟨Nat.find hex, ⟨?_, ?_, ⟨i, hi, (Nat.find_spec hex).symm⟩, ?_⟩, Nat.find_spec hex⟩
      · exact lt_of_le_of_lt (Nat.find_min' hex rfl) (hL i hi)
      · intro j hj e
        exact Nat.find_min hex hj (e.trans (Nat.find_spec hex))
      · rw [Nat.find_spec hex]; exact hX
    · rintro ⟨k, ⟨-, -, ⟨i, hi, e⟩, hX⟩, rfl⟩
      exact ⟨hX, i, hi, e⟩
  rw [himg, Finset.card_image_of_injOn]
  intro k hk k' hk' e
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hk hk'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact hk'.2.1 k h e
  · exact hk.2.1 k' h e.symm

/-- **The Venn sizes of the punctured lists**: an intersection loses the colours of the column
that lie in it, counted by first rows. -/
theorem card_interL_erase (F : ℕ → Finset ℕ) (σ : ℕ → ℕ) (i : ℕ) (L : List ℕ)
    (hL : ∀ j ∈ i :: L, j < 5) :
    (interL (fun j => (F j).erase (σ j)) (i :: L)).card
      + ((range 5).filter (fun k => repS σ k ∧ (∃ j ∈ i :: L, σ j = σ k)
          ∧ σ k ∈ interL F (i :: L))).card
      = (interL F (i :: L)).card := by
  rw [interL_erase, ← card_inter_image σ _ _ hL]
  exact Finset.card_sdiff_add_card_inter _ _

/-! ### Venn data by masks, and packing -/

/-- The Venn size of a mask (`1 ≤ I ≤ 31`). -/
def V5.get (v : V5) (I : ℕ) : ℕ :=
  match I with
  | 1 => v.x1
  | 2 => v.x2
  | 3 => v.x3
  | 4 => v.x4
  | 5 => v.x5
  | 6 => v.x6
  | 7 => v.x7
  | 8 => v.x8
  | 9 => v.x9
  | 10 => v.x10
  | 11 => v.x11
  | 12 => v.x12
  | 13 => v.x13
  | 14 => v.x14
  | 15 => v.x15
  | 16 => v.x16
  | 17 => v.x17
  | 18 => v.x18
  | 19 => v.x19
  | 20 => v.x20
  | 21 => v.x21
  | 22 => v.x22
  | 23 => v.x23
  | 24 => v.x24
  | 25 => v.x25
  | 26 => v.x26
  | 27 => v.x27
  | 28 => v.x28
  | 29 => v.x29
  | 30 => v.x30
  | _ => v.x31

theorem V5.ext_get {v w : V5} (h : ∀ I, 1 ≤ I → I < 32 → v.get I = w.get I) : v = w := by
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31⟩ := v
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31⟩ := w
  simp only [V5.mk.injEq]
  exact ⟨h 1 (by norm_num) (by norm_num), h 2 (by norm_num) (by norm_num), h 3 (by norm_num) (by norm_num), h 4 (by norm_num) (by norm_num), h 5 (by norm_num) (by norm_num), h 6 (by norm_num) (by norm_num), h 7 (by norm_num) (by norm_num), h 8 (by norm_num) (by norm_num), h 9 (by norm_num) (by norm_num), h 10 (by norm_num) (by norm_num), h 11 (by norm_num) (by norm_num), h 12 (by norm_num) (by norm_num), h 13 (by norm_num) (by norm_num), h 14 (by norm_num) (by norm_num), h 15 (by norm_num) (by norm_num), h 16 (by norm_num) (by norm_num), h 17 (by norm_num) (by norm_num), h 18 (by norm_num) (by norm_num), h 19 (by norm_num) (by norm_num), h 20 (by norm_num) (by norm_num), h 21 (by norm_num) (by norm_num), h 22 (by norm_num) (by norm_num), h 23 (by norm_num) (by norm_num), h 24 (by norm_num) (by norm_num), h 25 (by norm_num) (by norm_num), h 26 (by norm_num) (by norm_num), h 27 (by norm_num) (by norm_num), h 28 (by norm_num) (by norm_num), h 29 (by norm_num) (by norm_num), h 30 (by norm_num) (by norm_num), h 31 (by norm_num) (by norm_num)⟩

/-- Fieldwise sum of Venn data. -/
def addV (v w : V5) : V5 := ⟨v.x1 + w.x1, v.x2 + w.x2, v.x3 + w.x3, v.x4 + w.x4, v.x5 + w.x5, v.x6 + w.x6, v.x7 + w.x7, v.x8 + w.x8, v.x9 + w.x9, v.x10 + w.x10, v.x11 + w.x11, v.x12 + w.x12, v.x13 + w.x13, v.x14 + w.x14, v.x15 + w.x15, v.x16 + w.x16, v.x17 + w.x17, v.x18 + w.x18, v.x19 + w.x19, v.x20 + w.x20, v.x21 + w.x21, v.x22 + w.x22, v.x23 + w.x23, v.x24 + w.x24, v.x25 + w.x25, v.x26 + w.x26, v.x27 + w.x27, v.x28 + w.x28, v.x29 + w.x29, v.x30 + w.x30, v.x31 + w.x31⟩

theorem addV_get (v w : V5) {I : ℕ} (h1 : 1 ≤ I) (h2 : I < 32) :
    (addV v w).get I = v.get I + w.get I := by
  interval_cases I <;> rfl

/-- The zero Venn data. -/
def zeroV : V5 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Pack a list of digits, base 16. -/
def packL : List ℕ → ℕ
  | [] => 0
  | a :: L => a + 16 * packL L

theorem digit_packL : ∀ (L : List ℕ), (∀ x ∈ L, x < 16) → ∀ i : ℕ,
    packL L / 16 ^ i % 16 = L.getD i 0
  | [], _, i => by simp [packL]
  | a :: L, h, 0 => by
    have ha := h a List.mem_cons_self
    simp only [packL, pow_zero, Nat.div_one, List.getD_cons_zero]
    omega
  | a :: L, h, i + 1 => by
    have ha := h a List.mem_cons_self
    have ih := digit_packL L (fun x hx => h x (List.mem_cons_of_mem a hx)) i
    have e : (a + 16 * packL L) / 16 = packL L := by omega
    rw [packL, pow_succ', ← Nat.div_div_eq_div_mul, e, List.getD_cons_succ, ih]

/-- The Venn data as a list. -/
def V5.toList (v : V5) : List ℕ := [v.x1, v.x2, v.x3, v.x4, v.x5, v.x6, v.x7, v.x8, v.x9, v.x10, v.x11, v.x12, v.x13, v.x14, v.x15, v.x16, v.x17, v.x18, v.x19, v.x20, v.x21, v.x22, v.x23, v.x24, v.x25, v.x26, v.x27, v.x28, v.x29, v.x30, v.x31]

/-- The packed Venn data. -/
def packV (v : V5) : ℕ := packL v.toList

theorem packL_add : ∀ L M : List ℕ, L.length = M.length →
    packL (List.zipWith (· + ·) L M) = packL L + packL M
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)
  | a :: L, b :: M, h => by
    simp only [List.zipWith_cons_cons, packL]
    rw [packL_add L M (by simpa using h)]
    ring

theorem packV_addV (v w : V5) : packV (addV v w) = packV v + packV w :=
  packL_add v.toList w.toList rfl

/-- Digit `i` of a packed number. -/
def digit (P i : ℕ) : ℕ := Nat.mod (Nat.div P (Nat.pow 16 i)) 16

/-- Unpack the Venn data. -/
def unpack (P : ℕ) : V5 := ⟨digit P 0, digit P 1, digit P 2, digit P 3, digit P 4, digit P 5, digit P 6, digit P 7, digit P 8, digit P 9, digit P 10, digit P 11, digit P 12, digit P 13, digit P 14, digit P 15, digit P 16, digit P 17, digit P 18, digit P 19, digit P 20, digit P 21, digit P 22, digit P 23, digit P 24, digit P 25, digit P 26, digit P 27, digit P 28, digit P 29, digit P 30⟩

theorem unpack_packV (v : V5) (h : ∀ x ∈ v.toList, x < 16) : unpack (packV v) = v := by
  have hd : ∀ i, digit (packV v) i = v.toList.getD i 0 := fun i => digit_packL _ h i
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31⟩ := v
  simp only [unpack, hd]
  rfl

/-! ### Column types -/

/-- `k` is the first row of its colour (Boolean). -/
def repB (c : T5) (k : ℕ) : Bool := (List.range k).all (fun j => !(Nat.beq (rowAt j c) (rowAt k c)))

/-- The block of row `k`: the mask of the rows with its colour. -/
def blkOf (c : T5) (k : ℕ) : ℕ :=
  cond (Nat.beq (r1 c) (rowAt k c)) 1 0 + cond (Nat.beq (r2 c) (rowAt k c)) 2 0
    + cond (Nat.beq (r3 c) (rowAt k c)) 4 0 + cond (Nat.beq (r4 c) (rowAt k c)) 8 0
    + cond (Nat.beq (r5 c) (rowAt k c)) 16 0

/-- The reduced atom of a colour of block `b`: `0` if the colour lies in no list of its block. -/
def ratom (a b : ℕ) : ℕ := cond (Nat.beq (Nat.land a b) 0) 0 a

/-- Digit `I` of the correction of a colour of block `b` in atom `m`: whether it lies in all
lists of `I` and `I` meets its block. -/
def digB (I b m : ℕ) : ℕ := cond (!(Nat.beq (Nat.land b I) 0) && Nat.beq (Nat.land I m) I) 1 0

/-- The correction of a colour of block `b` in atom `m`. -/
def vecV (b m : ℕ) : V5 := ⟨digB 1 b m, digB 2 b m, digB 3 b m, digB 4 b m, digB 5 b m, digB 6 b m, digB 7 b m, digB 8 b m, digB 9 b m, digB 10 b m, digB 11 b m, digB 12 b m, digB 13 b m, digB 14 b m, digB 15 b m, digB 16 b m, digB 17 b m, digB 18 b m, digB 19 b m, digB 20 b m, digB 21 b m, digB 22 b m, digB 23 b m, digB 24 b m, digB 25 b m, digB 26 b m, digB 27 b m, digB 28 b m, digB 29 b m, digB 30 b m, digB 31 b m⟩

/-- The packed correction. -/
def vecP (b m : ℕ) : ℕ := packV (vecV b m)

/-- The size of an atom in a list of atoms with sizes (`0` if unlisted). -/
def asz : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | p :: L, m => if p.1 = m then p.2 else asz L m

theorem asz_mem : ∀ (L : List (ℕ × ℕ)) (m : ℕ), asz L m ≠ 0 → (m, asz L m) ∈ L
  | [], _, h => absurd rfl h
  | p :: L, m, h => by
    by_cases hp : p.1 = m
    · have e : asz (p :: L) m = p.2 := by simp [asz, hp]
      rw [e, ← hp]; exact List.mem_cons_self
    · have e : asz (p :: L) m = asz L m := by simp [asz, hp]
      rw [e] at h ⊢
      exact List.mem_cons_of_mem _ (asz_mem L m h)

/-- The Venn size of the mask `I`, from atom sizes. -/
def vsumI (I : ℕ) (f : ℕ → ℕ) : ℕ := ∑ m ∈ range 32, if Nat.land I m = I then f m else 0

/-- The Venn data of the atom sizes. -/
def vennOfAtoms (A : List (ℕ × ℕ)) : V5 := ⟨vsumI 1 (asz A), vsumI 2 (asz A), vsumI 3 (asz A), vsumI 4 (asz A), vsumI 5 (asz A), vsumI 6 (asz A), vsumI 7 (asz A), vsumI 8 (asz A), vsumI 9 (asz A), vsumI 10 (asz A), vsumI 11 (asz A), vsumI 12 (asz A), vsumI 13 (asz A), vsumI 14 (asz A), vsumI 15 (asz A), vsumI 16 (asz A), vsumI 17 (asz A), vsumI 18 (asz A), vsumI 19 (asz A), vsumI 20 (asz A), vsumI 21 (asz A), vsumI 22 (asz A), vsumI 23 (asz A), vsumI 24 (asz A), vsumI 25 (asz A), vsumI 26 (asz A), vsumI 27 (asz A), vsumI 28 (asz A), vsumI 29 (asz A), vsumI 30 (asz A), vsumI 31 (asz A)⟩

/-- The uniform orbit counts of the `p`-th canonical pattern (rows of `Vmat`). -/
def urowOf (p : ℕ) : C11 :=
  match p with
  | 0 => ⟨21, 136, 68, 104, 336, 36, 240, 68, 156, 168, 264⟩
  | 1 => ⟨17, 126, 56, 98, 312, 43, 273, 55, 174, 138, 288⟩
  | 2 => ⟨17, 112, 71, 110, 348, 39, 252, 56, 132, 174, 270⟩
  | 3 => ⟨13, 98, 55, 114, 309, 55, 312, 43, 138, 135, 288⟩
  | 4 => ⟨14, 104, 58, 103, 323, 46, 286, 46, 144, 142, 298⟩
  | 5 => ⟨9, 86, 39, 110, 276, 71, 348, 42, 135, 135, 288⟩
  | 6 => ⟨13, 98, 55, 114, 309, 55, 312, 43, 138, 135, 288⟩
  | 7 => ⟨10, 91, 42, 104, 286, 58, 325, 45, 142, 142, 298⟩
  | 8 => ⟨17, 110, 56, 86, 276, 42, 270, 71, 174, 174, 288⟩
  | 9 => ⟨17, 126, 56, 98, 312, 43, 273, 55, 174, 138, 288⟩
  | 10 => ⟨13, 116, 44, 92, 288, 45, 284, 58, 181, 144, 298⟩
  | 11 => ⟨14, 92, 58, 90, 284, 45, 284, 58, 144, 181, 298⟩
  | 12 => ⟨10, 91, 42, 104, 286, 58, 325, 45, 142, 142, 298⟩
  | 13 => ⟨14, 104, 58, 103, 323, 46, 286, 46, 144, 142, 298⟩
  | _ => ⟨11, 96, 45, 96, 298, 48, 298, 48, 149, 149, 309⟩

/-- The pin sum of a colour of block `b` in atom `m`: the pins on a row of the block and atom `m`. -/
def pincOf : List (ℕ × ℕ × ℕ) → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | q :: Q, b, m => cond (b.testBit q.1 && Nat.beq q.2.1 m) q.2.2 0 + pincOf Q b m

/-- The equality pins that fire on a pattern. -/
def eqcOf : List (ℕ × ℕ × ℕ) → T5 → ℕ
  | [], _ => 0
  | q :: Q, c => cond (Nat.beq (rowAt q.1 c) (rowAt q.2.1 c)) q.2.2 0 + eqcOf Q c

/-! ### Certificates -/

/-- A choice for a row: atom, its size (`5` for none), packed correction and pin sum. -/
abbrev Ch := ℕ × ℕ × ℕ × ℕ

/-- The data of one pattern: its index in `canons`, its equality pins, and the choices of each
row (the empty choice `(0, 5, 0, 0)` only, for a row that is not first in its block). -/
structure PatD where
  p : ℕ
  eqc : ℕ
  chs : List (List Ch)

/-- An exact certificate for one list shape: the atoms with sizes, the packed Venn data, row pins
`(row, atom, λ)`, equality pins `(pinned row, other row, λ)`, the constant `K` over the
denominator `D`, and the data of the fifteen patterns. -/
structure Spec5 where
  atoms : List (ℕ × ℕ)
  vennP : ℕ
  rpins : List (ℕ × ℕ × ℕ)
  ppins : List (ℕ × ℕ × ℕ)
  K : ℕ
  D : ℕ
  pds : List PatD

/-- Accumulate the separable box minimum: `(positive part, negative part)`. -/
def term (Lo a b : ℕ) (acc : ℕ × ℕ) : ℕ × ℕ :=
  cond (Nat.ble b a) (Nat.add acc.1 (Nat.mul Lo (Nat.sub a b)), acc.2)
    (acc.1, Nat.add acc.2 (Nat.mul 2000 (Nat.sub b a)))

/-- The orbit counts from packed Venn data. -/
def cls5 (P : ℕ) : C11 := clsV (unpack P)

/-- **The check of one column type**: `e · Σ uₒ wₒ ≤ D · Σ cₒ wₒ` on the box. -/
def okc (D : ℕ) (u : C11) (P e : ℕ) : Bool :=
  let c := cls5 P
  let acc := term 1931 (Nat.mul D c.c10) (Nat.mul e u.c10) <|
    term 1933 (Nat.mul D c.c9) (Nat.mul e u.c9) <| term 1951 (Nat.mul D c.c8) (Nat.mul e u.c8) <|
    term 1954 (Nat.mul D c.c7) (Nat.mul e u.c7) <| term 1924 (Nat.mul D c.c6) (Nat.mul e u.c6) <|
    term 1918 (Nat.mul D c.c5) (Nat.mul e u.c5) <| term 1953 (Nat.mul D c.c4) (Nat.mul e u.c4) <|
    term 1947 (Nat.mul D c.c3) (Nat.mul e u.c3) <| term 1977 (Nat.mul D c.c2) (Nat.mul e u.c2) <|
    term 1974 (Nat.mul D c.c1) (Nat.mul e u.c1) <| term 2000 (Nat.mul D c.c0) (Nat.mul e u.c0) (0, 0)
  Nat.ble acc.2 acc.1

/-- The number of earlier choices with atom `m`. -/
def cnt (m : ℕ) (L : List ℕ) : ℕ := L.rec 0 (fun x _ r => cond (Nat.beq x m) (Nat.succ r) r)

/-- `f` holds on a list of choices. -/
def allC (f : Ch → Bool) (L : List Ch) : Bool := L.rec true (fun x _ r => f x && r)

/-- **The enumeration** of the column types of a pattern, row by row: a choice is skipped when its
atom is full; the packed Venn data and the pin sum are updated on the way. -/
def enumP (D K : ℕ) (u : C11) (eqc : ℕ) : List (List Ch) → ℕ → ℕ → List ℕ → Bool
  | [], P, pin, _ => okc D u P (Nat.sub (Nat.add D K) (Nat.add pin eqc))
  | C :: Cs, P, pin, used => allC (fun c => !(Nat.blt (cnt c.1 used) c.2.1) ||
      enumP D K u eqc Cs (Nat.sub P c.2.2.1) (Nat.add pin c.2.2.2) (c.1 :: used)) C

/-- The data of a pattern is complete: every row may take the empty choice, and the first row
of a block may take every atom meeting its block, with the right correction and pin sum; the
equality pins are those of the pattern. -/
def pdOk (sp : Spec5) (pd : PatD) : Bool :=
  let c := canons.getD pd.p (0, 1, 0, 1, 0)
  Nat.blt pd.p 15 && Nat.beq pd.chs.length 5 && Nat.beq pd.eqc (eqcOf sp.ppins c) &&
  (List.range 5).all (fun k =>
    (pd.chs.getD k []).contains (0, 5, 0, 0) &&
    (!repB c k || sp.atoms.all (fun a => Nat.beq (Nat.land a.1 (blkOf c k)) 0 ||
      (pd.chs.getD k []).contains (a.1, a.2, vecP (blkOf c k) a.1, pincOf sp.rpins (blkOf c k) a.1))))

/-- **The check of one pattern.** -/
def patOk (sp : Spec5) (pd : PatD) : Bool :=
  pdOk sp pd && enumP sp.D sp.K (urowOf pd.p) pd.eqc pd.chs sp.vennP 0 []

/-- The weight of a pin in the averaged gain, over `1000·3877·2918`: `2918` for an end row
(fibre ratio `1000/3877`), `3877` for a middle row (`1000/2918`). -/
def wq (r : ℕ) : ℕ := if r = 0 ∨ 4 ≤ r then 2918 else 3877

def rsum (A : List (ℕ × ℕ)) : List (ℕ × ℕ × ℕ) → ℕ
  | [] => 0
  | q :: Q => q.2.2 * asz A q.2.1 * wq q.1 + rsum A Q

def psum : List (ℕ × ℕ × ℕ) → ℕ
  | [] => 0
  | q :: Q => q.2.2 * wq q.1 + psum Q

def rpOk : List (ℕ × ℕ × ℕ) → Bool
  | [] => true
  | q :: Q => Nat.blt q.1 5 && !(Nat.beq q.2.1 0) && rpOk Q

def ppOk : List (ℕ × ℕ × ℕ) → Bool
  | [] => true
  | q :: Q => Nat.blt q.1 5 && Nat.blt q.2.1 5 && !(Nat.beq q.1 q.2.1) && ppOk Q

/-- **The scalar conditions**: `0 < D`, the packed Venn data of the atoms, the pins well formed,
every pattern present, and the averaged gain `K - Σ λ q |R| ≥ 0`. -/
def specOk (sp : Spec5) : Bool :=
  Nat.blt 0 sp.D && Nat.beq sp.vennP (packV (vennOfAtoms sp.atoms)) && rpOk sp.rpins &&
    ppOk sp.ppins && (List.range 15).all (fun p => sp.pds.any (fun pd => Nat.beq pd.p p)) &&
    Nat.ble (1000 * (rsum sp.atoms sp.rpins + psum sp.ppins)) (11313086 * sp.K)

/-- All patterns pass. -/
def allOk (sp : Spec5) : Bool := sp.pds.all (patOk sp)

/-! ### The Venn data of the lists from their atom sizes -/

theorem rowsOf_1 : rowsOf 1 = [0] := by decide
theorem rowsOf_2 : rowsOf 2 = [1] := by decide
theorem rowsOf_3 : rowsOf 3 = [0, 1] := by decide
theorem rowsOf_4 : rowsOf 4 = [2] := by decide
theorem rowsOf_5 : rowsOf 5 = [0, 2] := by decide
theorem rowsOf_6 : rowsOf 6 = [1, 2] := by decide
theorem rowsOf_7 : rowsOf 7 = [0, 1, 2] := by decide
theorem rowsOf_8 : rowsOf 8 = [3] := by decide
theorem rowsOf_9 : rowsOf 9 = [0, 3] := by decide
theorem rowsOf_10 : rowsOf 10 = [1, 3] := by decide
theorem rowsOf_11 : rowsOf 11 = [0, 1, 3] := by decide
theorem rowsOf_12 : rowsOf 12 = [2, 3] := by decide
theorem rowsOf_13 : rowsOf 13 = [0, 2, 3] := by decide
theorem rowsOf_14 : rowsOf 14 = [1, 2, 3] := by decide
theorem rowsOf_15 : rowsOf 15 = [0, 1, 2, 3] := by decide
theorem rowsOf_16 : rowsOf 16 = [4] := by decide
theorem rowsOf_17 : rowsOf 17 = [0, 4] := by decide
theorem rowsOf_18 : rowsOf 18 = [1, 4] := by decide
theorem rowsOf_19 : rowsOf 19 = [0, 1, 4] := by decide
theorem rowsOf_20 : rowsOf 20 = [2, 4] := by decide
theorem rowsOf_21 : rowsOf 21 = [0, 2, 4] := by decide
theorem rowsOf_22 : rowsOf 22 = [1, 2, 4] := by decide
theorem rowsOf_23 : rowsOf 23 = [0, 1, 2, 4] := by decide
theorem rowsOf_24 : rowsOf 24 = [3, 4] := by decide
theorem rowsOf_25 : rowsOf 25 = [0, 3, 4] := by decide
theorem rowsOf_26 : rowsOf 26 = [1, 3, 4] := by decide
theorem rowsOf_27 : rowsOf 27 = [0, 1, 3, 4] := by decide
theorem rowsOf_28 : rowsOf 28 = [2, 3, 4] := by decide
theorem rowsOf_29 : rowsOf 29 = [0, 2, 3, 4] := by decide
theorem rowsOf_30 : rowsOf 30 = [1, 2, 3, 4] := by decide
theorem rowsOf_31 : rowsOf 31 = [0, 1, 2, 3, 4] := by decide

theorem rowsOf_ne_nil {I : ℕ} (h1 : 1 ≤ I) (h2 : I < 32) : rowsOf I ≠ [] := by
  interval_cases I <;> decide

/-- The colours of the lists with membership vector `m`. -/
def atomSet (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (m : ℕ) : Finset ℕ :=
  (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅).filter (fun c => memv5 B₁ B₂ B₃ B₄ B₅ c = m)

/-- The certificate's atom sizes are those of the lists. -/
def AtomsMatch (sp : Spec5) (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) : Prop :=
  ∀ m, 0 < m → m < 32 → (atomSet B₁ B₂ B₃ B₄ B₅ m).card = asz sp.atoms m

theorem venn5_get (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) {I : ℕ} (h1 : 1 ≤ I) (h2 : I < 32) :
    (venn5 B₁ B₂ B₃ B₄ B₅).get I = (interL (bl B₁ B₂ B₃ B₄ B₅) (rowsOf I)).card := by
  interval_cases I
  · rw [rowsOf_1]; rfl
  · rw [rowsOf_2]; rfl
  · rw [rowsOf_3]; rfl
  · rw [rowsOf_4]; rfl
  · rw [rowsOf_5]; rfl
  · rw [rowsOf_6]; rfl
  · rw [rowsOf_7]; rfl
  · rw [rowsOf_8]; rfl
  · rw [rowsOf_9]; rfl
  · rw [rowsOf_10]; rfl
  · rw [rowsOf_11]; rfl
  · rw [rowsOf_12]; rfl
  · rw [rowsOf_13]; rfl
  · rw [rowsOf_14]; rfl
  · rw [rowsOf_15]; rfl
  · rw [rowsOf_16]; rfl
  · rw [rowsOf_17]; rfl
  · rw [rowsOf_18]; rfl
  · rw [rowsOf_19]; rfl
  · rw [rowsOf_20]; rfl
  · rw [rowsOf_21]; rfl
  · rw [rowsOf_22]; rfl
  · rw [rowsOf_23]; rfl
  · rw [rowsOf_24]; rfl
  · rw [rowsOf_25]; rfl
  · rw [rowsOf_26]; rfl
  · rw [rowsOf_27]; rfl
  · rw [rowsOf_28]; rfl
  · rw [rowsOf_29]; rfl
  · rw [rowsOf_30]; rfl
  · rw [rowsOf_31]; rfl

theorem mem_union_of_bl {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} {i c : ℕ} (h : c ∈ bl B₁ B₂ B₃ B₄ B₅ i) :
    c ∈ B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅ := by
  simp only [Finset.mem_union]
  match i with
  | 0 => tauto
  | 1 => tauto
  | 2 => tauto
  | 3 => tauto
  | _ + 4 => exact Or.inr h

theorem mem_atomSet {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} {m : ℕ} (hm : m ≠ 0) (c : ℕ) :
    c ∈ atomSet B₁ B₂ B₃ B₄ B₅ m ↔ memv5 B₁ B₂ B₃ B₄ B₅ c = m := by
  unfold atomSet
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  by_contra hc
  simp only [Finset.mem_union, not_or] at hc
  apply hm; rw [← h]; simp [memv5, hc]

/-- An intersection of lists, as the colours whose membership vector contains the mask. -/
theorem interL_eq_filter (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) {I : ℕ} (h1 : 1 ≤ I) (h2 : I < 32) :
    interL (bl B₁ B₂ B₃ B₄ B₅) (rowsOf I) = (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅).filter
      (fun c => Nat.land I (memv5 B₁ B₂ B₃ B₄ B₅ c) = I) := by
  obtain ⟨i, L, hL⟩ := List.exists_cons_of_ne_nil (rowsOf_ne_nil h1 h2)
  ext c
  rw [Finset.mem_filter, land_memv5 B₁ B₂ B₃ B₄ B₅ h2, hL, mem_interL]
  exact ⟨fun h => ⟨mem_union_of_bl (h i List.mem_cons_self), h⟩, fun h => h.2⟩

/-- **The Venn sizes from the atom sizes.** -/
theorem card_interL_atoms (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) {I : ℕ} (h1 : 1 ≤ I) (h2 : I < 32) :
    (interL (bl B₁ B₂ B₃ B₄ B₅) (rowsOf I)).card
      = vsumI I (fun m => (atomSet B₁ B₂ B₃ B₄ B₅ m).card) := by
  rw [interL_eq_filter B₁ B₂ B₃ B₄ B₅ h1 h2,
    Finset.card_eq_sum_card_fiberwise (f := memv5 B₁ B₂ B₃ B₄ B₅) (t := range 32)
      (fun c _ => Finset.mem_range.mpr (memv5_lt _ _ _ _ _ c))]
  unfold vsumI atomSet
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.filter_filter]
  split_ifs with hm
  · congr 1
    refine Finset.filter_congr fun c _ => ?_
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ hm, h⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro c - ⟨h, rfl⟩
    exact hm h

theorem vennOfAtoms_get (A : List (ℕ × ℕ)) {I : ℕ} (h1 : 1 ≤ I) (h2 : I < 32) :
    (vennOfAtoms A).get I = vsumI I (asz A) := by
  interval_cases I <;> rfl

/-- **The Venn data of lists matching a certificate.** -/
theorem venn5_eq_atoms {sp : Spec5} {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} (hA : AtomsMatch sp B₁ B₂ B₃ B₄ B₅) :
    venn5 B₁ B₂ B₃ B₄ B₅ = vennOfAtoms sp.atoms := by
  apply V5.ext_get
  intro I h1 h2
  rw [venn5_get _ _ _ _ _ h1 h2, card_interL_atoms _ _ _ _ _ h1 h2, vennOfAtoms_get _ h1 h2]
  unfold vsumI
  refine Finset.sum_congr rfl fun m hm => ?_
  split_ifs with h
  · have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · have : Nat.land I 0 = 0 := Nat.and_zero I
        omega
      · exact hm0
    exact hA m hm0 (Finset.mem_range.mp hm)
  · rfl

/-! ### The column type of a proper column -/

theorem vecV_get (b m : ℕ) {I : ℕ} (h1 : 1 ≤ I) (h2 : I < 32) : (vecV b m).get I = digB I b m := by
  interval_cases I <;> rfl

theorem zeroV_get {I : ℕ} (h1 : 1 ≤ I) (h2 : I < 32) : zeroV.get I = 0 := by
  interval_cases I <;> rfl

theorem eqv_canon {s : T5} (hs : Proper s) {i j : ℕ} (hi : i < 5) (hj : j < 5) :
    rowAt i s = rowAt j s ↔ rowAt i (canon s) = rowAt j (canon s) := by
  have hc := samePat_canon hs
  have pc := proper_canon hs
  generalize canon s = c at hc pc
  obtain ⟨h13, h24, h35, h14, h25, h15⟩ := hc
  obtain ⟨p1, p2, p3, p4⟩ := hs
  obtain ⟨q1, q2, q3, q4⟩ := pc
  interval_cases i <;> interval_cases j <;> simp only [rowAt] <;> grind

theorem repS_iff {s : T5} (hs : Proper s) {k : ℕ} (hk : k < 5) :
    repS (fun j => rowAt j s) k ↔ repB (canon s) k = true := by
  unfold repS repB
  rw [List.all_eq_true]
  refine forall_congr' fun j => ?_
  rw [List.mem_range]
  refine imp_congr_right fun hj => ?_
  rw [Bool.not_eq_true', ← Bool.not_eq_true, Nat.beq_eq]
  exact not_congr (eqv_canon hs (by omega) hk)

theorem blk_table : ∀ c ∈ canons, ∀ k ∈ List.range 5, ∀ I ∈ List.range 32,
    decide (∃ i ∈ rowsOf I, rowAt i c = rowAt k c) = !(Nat.beq (Nat.land (blkOf c k) I) 0) := by
  decide +kernel

theorem touch_table : ∀ I ∈ List.range 32, ∀ b ∈ List.range 32, ∀ a ∈ List.range 32,
    digB I b (ratom a b) = digB I b a := by
  decide +kernel

theorem blkOf_lt (c : T5) (k : ℕ) : blkOf c k < 32 := by
  unfold blkOf
  cases Nat.beq (r1 c) (rowAt k c) <;> cases Nat.beq (r2 c) (rowAt k c) <;>
    cases Nat.beq (r3 c) (rowAt k c) <;> cases Nat.beq (r4 c) (rowAt k c) <;>
    cases Nat.beq (r5 c) (rowAt k c) <;> decide

/-- **The correction of one row**: the first row `k` of a colour of the column lowers the Venn
size of `I` iff its block meets `I` and the colour lies in all lists of `I`. -/
theorem corr_k (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) {s : T5} (hs : Proper s) {k I : ℕ} (hk : k < 5)
    (h1 : 1 ≤ I) (h2 : I < 32) :
    (if repS (fun j => rowAt j s) k ∧ (∃ i ∈ rowsOf I, rowAt i s = rowAt k s) ∧
        rowAt k s ∈ interL (bl B₁ B₂ B₃ B₄ B₅) (rowsOf I) then 1 else 0)
      = cond (repB (canon s) k) (digB I (blkOf (canon s) k)
          (ratom (memv5 B₁ B₂ B₃ B₄ B₅ (rowAt k s)) (blkOf (canon s) k))) 0 := by
  rw [touch_table I (List.mem_range.mpr h2) _ (List.mem_range.mpr (blkOf_lt _ _)) _
    (List.mem_range.mpr (memv5_lt _ _ _ _ _ _))]
  have e1 := repS_iff hs hk
  have e2 : (∃ i ∈ rowsOf I, rowAt i s = rowAt k s) ↔
      (!(Nat.beq (Nat.land (blkOf (canon s) k) I) 0)) = true := by
    rw [← blk_table _ (canon_mem hs) k (List.mem_range.mpr hk) I (List.mem_range.mpr h2),
      decide_eq_true_iff]
    exact exists_congr fun i => and_congr_right fun hi => eqv_canon hs (rowsOf_lt hi) hk
  have e3 : rowAt k s ∈ interL (bl B₁ B₂ B₃ B₄ B₅) (rowsOf I) ↔
      Nat.beq (Nat.land I (memv5 B₁ B₂ B₃ B₄ B₅ (rowAt k s))) I = true := by
    obtain ⟨i, L, hL⟩ := List.exists_cons_of_ne_nil (rowsOf_ne_nil h1 h2)
    rw [Nat.beq_eq, land_memv5 B₁ B₂ B₃ B₄ B₅ h2, hL, mem_interL]
  unfold digB
  by_cases r : repB (canon s) k = true
  · rw [r, Bool.cond_true]
    by_cases a : (!(Nat.beq (Nat.land (blkOf (canon s) k) I) 0)) = true
    · by_cases b : Nat.beq (Nat.land I (memv5 B₁ B₂ B₃ B₄ B₅ (rowAt k s))) I = true
      · rw [if_pos ⟨e1.mpr r, e2.mpr a, e3.mpr b⟩, a, b]; rfl
      · rw [if_neg (fun h => b (e3.mp h.2.2))]
        simp only [Bool.not_eq_true] at b
        rw [b, Bool.and_false]; rfl
    · rw [if_neg (fun h => a (e2.mp h.2.1))]
      simp only [Bool.not_eq_true] at a
      rw [a, Bool.false_and]; rfl
  · rw [if_neg (fun h => r (e1.mp h.1))]
    simp only [Bool.not_eq_true] at r
    rw [r]; rfl

/-- The correction of row `k` of a column, as Venn data. -/
def vk (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (s : T5) (k : ℕ) : V5 :=
  if repB (canon s) k = true then
    vecV (blkOf (canon s) k) (ratom (memv5 B₁ B₂ B₃ B₄ B₅ (rowAt k s)) (blkOf (canon s) k))
  else zeroV

theorem vk_get (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (s : T5) (k : ℕ) {I : ℕ} (h1 : 1 ≤ I) (h2 : I < 32) :
    (vk B₁ B₂ B₃ B₄ B₅ s k).get I = cond (repB (canon s) k) (digB I (blkOf (canon s) k)
      (ratom (memv5 B₁ B₂ B₃ B₄ B₅ (rowAt k s)) (blkOf (canon s) k))) 0 := by
  unfold vk
  by_cases r : repB (canon s) k = true
  · rw [if_pos r, vecV_get _ _ h1 h2, r]; rfl
  · rw [if_neg r, zeroV_get h1 h2]
    simp only [Bool.not_eq_true] at r
    rw [r]; rfl

theorem bl_erase (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (s : T5) :
    bl (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s)) (B₅.erase (r5 s))
      = fun j => (bl B₁ B₂ B₃ B₄ B₅ j).erase (rowAt j s) := by
  funext j
  match j with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | _ + 4 => rfl

/-- **The Venn data of the punctured lists**: those of the lists minus the corrections of the
first rows of the colours of the column. -/
theorem venn5_erase (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) {s : T5} (hs : Proper s) :
    venn5 B₁ B₂ B₃ B₄ B₅ = addV (venn5 (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s))
      (B₄.erase (r4 s)) (B₅.erase (r5 s))) (addV (vk B₁ B₂ B₃ B₄ B₅ s 0)
        (addV (vk B₁ B₂ B₃ B₄ B₅ s 1) (addV (vk B₁ B₂ B₃ B₄ B₅ s 2)
          (addV (vk B₁ B₂ B₃ B₄ B₅ s 3) (vk B₁ B₂ B₃ B₄ B₅ s 4))))) := by
  apply V5.ext_get
  intro I h1 h2
  simp only [addV_get _ _ h1 h2, venn5_get _ _ _ _ _ h1 h2, vk_get _ _ _ _ _ _ _ h1 h2, bl_erase]
  obtain ⟨i, L, hL⟩ := List.exists_cons_of_ne_nil (rowsOf_ne_nil h1 h2)
  have hlt : ∀ j ∈ i :: L, j < 5 := fun j hj => rowsOf_lt (hL ▸ hj)
  have h := card_interL_erase (bl B₁ B₂ B₃ B₄ B₅) (fun j => rowAt j s) i L hlt
  rw [Finset.card_filter, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one] at h
  rw [hL]
  have c0 := corr_k B₁ B₂ B₃ B₄ B₅ hs (k := 0) (by norm_num) h1 h2
  have c1 := corr_k B₁ B₂ B₃ B₄ B₅ hs (k := 1) (by norm_num) h1 h2
  have c2 := corr_k B₁ B₂ B₃ B₄ B₅ hs (k := 2) (by norm_num) h1 h2
  have c3 := corr_k B₁ B₂ B₃ B₄ B₅ hs (k := 3) (by norm_num) h1 h2
  have c4 := corr_k B₁ B₂ B₃ B₄ B₅ hs (k := 4) (by norm_num) h1 h2
  rw [hL] at c0 c1 c2 c3 c4
  rw [c0, c1, c2, c3, c4] at h
  omega

/-! ### The choices of a column -/

/-- The reduced atom of row `k` of a column. -/
def raK (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (s : T5) (k : ℕ) : ℕ :=
  ratom (memv5 B₁ B₂ B₃ B₄ B₅ (rowAt k s)) (blkOf (canon s) k)

/-- The choice of row `k` taken by a column: the reduced atom of its colour if `k` is the first
row of the colour and that atom is not empty, else the empty choice. -/
def xch (sp : Spec5) (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (s : T5) (k : ℕ) : Ch :=
  if repB (canon s) k = true ∧ raK B₁ B₂ B₃ B₄ B₅ s k ≠ 0 then
    (raK B₁ B₂ B₃ B₄ B₅ s k, asz sp.atoms (raK B₁ B₂ B₃ B₄ B₅ s k),
      vecP (blkOf (canon s) k) (raK B₁ B₂ B₃ B₄ B₅ s k),
      pincOf sp.rpins (blkOf (canon s) k) (raK B₁ B₂ B₃ B₄ B₅ s k))
  else (0, 5, 0, 0)

theorem vecV_zero (b : ℕ) : vecV b 0 = zeroV := by
  apply V5.ext_get
  intro I h1 h2
  rw [vecV_get _ _ h1 h2, zeroV_get h1 h2]
  unfold digB
  have e1 : Nat.land I 0 = 0 := Nat.and_zero I
  have e2 : Nat.beq 0 I = false := by
    rw [← Bool.not_eq_true, Nat.beq_eq]; omega
  rw [e1, e2, Bool.and_false]; rfl

theorem packV_zeroV : packV zeroV = 0 := rfl

theorem packV_vk (sp : Spec5) (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (s : T5) (k : ℕ) :
    packV (vk B₁ B₂ B₃ B₄ B₅ s k) = (xch sp B₁ B₂ B₃ B₄ B₅ s k).2.2.1 := by
  unfold vk xch
  by_cases r : repB (canon s) k = true
  · rw [if_pos r]
    by_cases z : raK B₁ B₂ B₃ B₄ B₅ s k = 0
    · rw [if_neg (fun h => h.2 z)]
      unfold raK at z; rw [z, vecV_zero]; rfl
    · rw [if_pos ⟨r, z⟩]; rfl
  · rw [if_neg r, if_neg (fun h => r h.1)]; rfl

theorem ratom_spec (a b : ℕ) :
    (Nat.land a b = 0 ∧ ratom a b = 0) ∨ (Nat.land a b ≠ 0 ∧ ratom a b = a) := by
  unfold ratom
  by_cases h : Nat.land a b = 0
  · left; refine ⟨h, ?_⟩; rw [h]; rfl
  · right
    refine ⟨h, ?_⟩
    have e : Nat.beq (Nat.land a b) 0 = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; exact h
    rw [e]; rfl

theorem raK_ne_zero {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} {s : T5} {k : ℕ}
    (h : raK B₁ B₂ B₃ B₄ B₅ s k ≠ 0) :
    raK B₁ B₂ B₃ B₄ B₅ s k = memv5 B₁ B₂ B₃ B₄ B₅ (rowAt k s) ∧
      Nat.land (memv5 B₁ B₂ B₃ B₄ B₅ (rowAt k s)) (blkOf (canon s) k) ≠ 0 := by
  unfold raK at *
  rcases ratom_spec (memv5 B₁ B₂ B₃ B₄ B₅ (rowAt k s)) (blkOf (canon s) k) with h' | h'
  · exact absurd h'.2 h
  · exact ⟨h'.2, h'.1⟩

theorem xch_fst {sp : Spec5} {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} {s : T5} {k : ℕ}
    (h : (xch sp B₁ B₂ B₃ B₄ B₅ s k).1 ≠ 0) :
    repB (canon s) k = true ∧ (xch sp B₁ B₂ B₃ B₄ B₅ s k).1 = memv5 B₁ B₂ B₃ B₄ B₅ (rowAt k s) ∧
      (xch sp B₁ B₂ B₃ B₄ B₅ s k).2.1 = asz sp.atoms (xch sp B₁ B₂ B₃ B₄ B₅ s k).1 := by
  unfold xch at *
  by_cases c : repB (canon s) k = true ∧ raK B₁ B₂ B₃ B₄ B₅ s k ≠ 0
  · rw [if_pos c] at h ⊢
    exact ⟨c.1, (raK_ne_zero c.2).1, rfl⟩
  · rw [if_neg c] at h; exact absurd rfl h

theorem xch_zero {sp : Spec5} {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} {s : T5} {k : ℕ}
    (h : (xch sp B₁ B₂ B₃ B₄ B₅ s k).1 = 0) : xch sp B₁ B₂ B₃ B₄ B₅ s k = (0, 5, 0, 0) := by
  unfold xch at *
  by_cases c : repB (canon s) k = true ∧ raK B₁ B₂ B₃ B₄ B₅ s k ≠ 0
  · rw [if_pos c] at h; exact absurd h c.2
  · rw [if_neg c]

theorem mem_atomSet_self (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) {c : ℕ} (h : memv5 B₁ B₂ B₃ B₄ B₅ c ≠ 0) :
    c ∈ atomSet B₁ B₂ B₃ B₄ B₅ (memv5 B₁ B₂ B₃ B₄ B₅ c) :=
  (mem_atomSet h c).mpr rfl

/-- **The choice of every row is listed**, by the completeness of the pattern data. -/
theorem xch_mem {sp : Spec5} {pd : PatD} (hpd : pdOk sp pd = true) {B₁ B₂ B₃ B₄ B₅ : Finset ℕ}
    (hA : AtomsMatch sp B₁ B₂ B₃ B₄ B₅) {s : T5} (hp : canons.getD pd.p (0, 1, 0, 1, 0) = canon s)
    {k : ℕ} (hk : k < 5) : xch sp B₁ B₂ B₃ B₄ B₅ s k ∈ pd.chs.getD k [] := by
  unfold pdOk at hpd
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hpd
  obtain ⟨-, hrow⟩ := hpd
  obtain ⟨h0, h1⟩ := hrow k hk
  rw [hp] at h1
  rw [List.contains_iff_mem] at h0
  by_cases z : (xch sp B₁ B₂ B₃ B₄ B₅ s k).1 = 0
  · rw [xch_zero z]; exact h0
  · obtain ⟨r, e1, -⟩ := xch_fst z
    unfold xch at z ⊢
    by_cases c : repB (canon s) k = true ∧ raK B₁ B₂ B₃ B₄ B₅ s k ≠ 0
    · rw [if_pos c]
      rw [if_pos c] at z
      obtain ⟨ea, eb⟩ := raK_ne_zero c.2
      rw [ea]
      set a := memv5 B₁ B₂ B₃ B₄ B₅ (rowAt k s) with ha
      have ha0 : a ≠ 0 := by rw [← ea]; exact c.2
      have hsz : asz sp.atoms a ≠ 0 := by
        rw [← hA a (Nat.pos_of_ne_zero ha0) (memv5_lt _ _ _ _ _ _)]
        exact (Finset.card_pos.mpr ⟨_, mem_atomSet_self B₁ B₂ B₃ B₄ B₅ ha0⟩).ne'
      have hmem := asz_mem sp.atoms a hsz
      have := h1
      simp only [c.1, Bool.not_true, Bool.false_or, List.all_eq_true] at this
      have h2 := this _ hmem
      simp only [Bool.or_eq_true, List.contains_iff_mem] at h2
      rcases h2 with h2 | h2
      · exact absurd (Nat.beq_eq ▸ h2 : Nat.land a (blkOf (canon s) k) = 0) eb
      · exact h2
    · rw [if_neg c] at z; exact absurd rfl z

/-! ### Capacity -/

theorem cnt_cons (m a : ℕ) (L : List ℕ) : cnt m (a :: L) = (if a = m then 1 else 0) + cnt m L := by
  show cond (Nat.beq a m) (Nat.succ (cnt m L)) (cnt m L) = _
  by_cases h : a = m
  · rw [if_pos h, (Nat.beq_eq ▸ h : Nat.beq a m = true)]; simp [Nat.succ_eq_add_one, Nat.add_comm]
  · have e : Nat.beq a m = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; exact h
    rw [if_neg h, e]; simp

theorem cnt_range (f : ℕ → ℕ) (m : ℕ) : ∀ k : ℕ,
    cnt m ((List.range k).reverse.map f) = ((range k).filter (fun j => f j = m)).card
  | 0 => rfl
  | k + 1 => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, cnt_cons, cnt_range f m k, Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp), Nat.add_comm]
    · simp

theorem cnt_le_length (m : ℕ) : ∀ L : List ℕ, cnt m L ≤ L.length
  | [] => le_rfl
  | a :: L => by
    rw [cnt_cons, List.length_cons]
    have := cnt_le_length m L
    split_ifs <;> omega

/-- The colours of the column in an atom are at most the atom's size. -/
theorem cap_le {sp : Spec5} {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} {s : T5} (hs : Proper s) {m : ℕ}
    (hm : m ≠ 0) {n : ℕ} (hn : n ≤ 5) :
    ((range n).filter (fun j => (xch sp B₁ B₂ B₃ B₄ B₅ s j).1 = m)).card
      ≤ (atomSet B₁ B₂ B₃ B₄ B₅ m).card := by
  refine Finset.card_le_card_of_injOn (fun j => rowAt j s) ?_ ?_
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hj
    obtain ⟨-, e, -⟩ := xch_fst (hj.2 ▸ hm : (xch sp B₁ B₂ B₃ B₄ B₅ s j).1 ≠ 0)
    rw [hj.2] at e
    simp only [Finset.mem_coe]
    rw [e]; exact mem_atomSet_self _ _ _ _ _ (e ▸ hm)
  · intro j hj j' hj' e
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hj hj'
    obtain ⟨r, -, -⟩ := xch_fst (hj.2 ▸ hm : (xch sp B₁ B₂ B₃ B₄ B₅ s j).1 ≠ 0)
    obtain ⟨r', -, -⟩ := xch_fst (hj'.2 ▸ hm : (xch sp B₁ B₂ B₃ B₄ B₅ s j').1 ≠ 0)
    have q := (repS_iff hs (by omega : j < 5)).mpr r
    have q' := (repS_iff hs (by omega : j' < 5)).mpr r'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact q' j h e
    · exact q j' h e.symm

/-- **The capacity test passes** at every row. -/
theorem cap_level {sp : Spec5} {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} (hA : AtomsMatch sp B₁ B₂ B₃ B₄ B₅)
    {s : T5} (hs : Proper s) {k : ℕ} (hk : k < 5) :
    Nat.blt (cnt (xch sp B₁ B₂ B₃ B₄ B₅ s k).1
      ((List.range k).reverse.map (fun j => (xch sp B₁ B₂ B₃ B₄ B₅ s j).1)))
      (xch sp B₁ B₂ B₃ B₄ B₅ s k).2.1 = true := by
  rw [Nat.blt_eq]
  by_cases z : (xch sp B₁ B₂ B₃ B₄ B₅ s k).1 = 0
  · have := cnt_le_length (xch sp B₁ B₂ B₃ B₄ B₅ s k).1
      ((List.range k).reverse.map (fun j => (xch sp B₁ B₂ B₃ B₄ B₅ s j).1))
    rw [List.length_map, List.length_reverse, List.length_range] at this
    rw [xch_zero z]; rw [xch_zero z] at this
    show _ < 5; omega
  · obtain ⟨-, e, hsz⟩ := xch_fst z
    set m := (xch sp B₁ B₂ B₃ B₄ B₅ s k).1 with hm
    rw [cnt_range, hsz]
    have h1 := cap_le (sp := sp) (B₁ := B₁) (B₂ := B₂) (B₃ := B₃) (B₄ := B₄) (B₅ := B₅) hs z
      (n := k + 1) (by omega)
    rw [Finset.range_add_one, Finset.filter_insert, if_pos hm.symm,
      Finset.card_insert_of_notMem (by simp)] at h1
    have hm32 : m < 32 := by rw [e]; exact memv5_lt _ _ _ _ _ _
    rw [hA m (Nat.pos_of_ne_zero z) hm32] at h1
    omega

/-! ### Pins -/

/-- The first row of the colour of row `r` of a pattern. -/
def repOf (c : T5) (r : ℕ) : ℕ := ((List.range 5).find? (fun j => Nat.beq (rowAt j c) (rowAt r c))).getD 0

theorem rep_table : ∀ c ∈ canons, ∀ r ∈ List.range 5, ∀ k ∈ List.range 5,
    (repB c k && (blkOf c k).testBit r) = Nat.beq k (repOf c r) := by
  decide +kernel

theorem repOf_table : ∀ c ∈ canons, ∀ r ∈ List.range 5,
    Nat.blt (repOf c r) 5 && Nat.beq (rowAt (repOf c r) c) (rowAt r c) := by
  decide +kernel

/-- The row pins that fire on a column (actual atoms). -/
def pinAct (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (s : T5) : List (ℕ × ℕ × ℕ) → ℕ
  | [] => 0
  | q :: Q => (if memv5 B₁ B₂ B₃ B₄ B₅ (rowAt q.1 s) = q.2.1 then q.2.2 else 0)
      + pinAct B₁ B₂ B₃ B₄ B₅ s Q

/-- The pins counted by the certificate for a column (through the choices). -/
def pinK (rp : List (ℕ × ℕ × ℕ)) (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (s : T5) (k : ℕ) : ℕ :=
  if repB (canon s) k = true ∧ raK B₁ B₂ B₃ B₄ B₅ s k ≠ 0 then
    pincOf rp (blkOf (canon s) k) (raK B₁ B₂ B₃ B₄ B₅ s k) else 0

theorem xch_pin (sp : Spec5) (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (s : T5) (k : ℕ) :
    (xch sp B₁ B₂ B₃ B₄ B₅ s k).2.2.2 = pinK sp.rpins B₁ B₂ B₃ B₄ B₅ s k := by
  unfold xch pinK; split_ifs <;> rfl

theorem pinK_cons (q : ℕ × ℕ × ℕ) (Q : List (ℕ × ℕ × ℕ)) (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (s : T5)
    (k : ℕ) : pinK (q :: Q) B₁ B₂ B₃ B₄ B₅ s k =
      (if repB (canon s) k = true ∧ raK B₁ B₂ B₃ B₄ B₅ s k ≠ 0 ∧
          (blkOf (canon s) k).testBit q.1 = true ∧ q.2.1 = raK B₁ B₂ B₃ B₄ B₅ s k
        then q.2.2 else 0) + pinK Q B₁ B₂ B₃ B₄ B₅ s k := by
  unfold pinK
  by_cases c : repB (canon s) k = true ∧ raK B₁ B₂ B₃ B₄ B₅ s k ≠ 0
  · rw [if_pos c, if_pos c]
    show cond ((blkOf (canon s) k).testBit q.1 && Nat.beq q.2.1 (raK B₁ B₂ B₃ B₄ B₅ s k)) q.2.2 0
      + pincOf Q _ _ = _
    by_cases t : (blkOf (canon s) k).testBit q.1 = true
    · by_cases e : q.2.1 = raK B₁ B₂ B₃ B₄ B₅ s k
      · rw [if_pos ⟨c.1, c.2, t, e⟩, t, (Nat.beq_eq ▸ e : Nat.beq _ _ = true)]; rfl
      · have e' : Nat.beq q.2.1 (raK B₁ B₂ B₃ B₄ B₅ s k) = false := by
          rw [← Bool.not_eq_true, Nat.beq_eq]; exact e
        rw [if_neg (fun h => e h.2.2.2), t, e']; rfl
    · simp only [Bool.not_eq_true] at t
      rw [if_neg (fun h => by rw [t] at h; exact Bool.false_ne_true h.2.2.1), t]; rfl
  · rw [if_neg c, if_neg c, if_neg (fun h => c ⟨h.1, h.2.1⟩)]

/-- One pin is counted at most once, and only when it fires. -/
theorem one_pin_le (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) {s : T5} (hs : Proper s) {r : ℕ} (hr : r < 5)
    (m l : ℕ) :
    ∑ k ∈ range 5, (if repB (canon s) k = true ∧ raK B₁ B₂ B₃ B₄ B₅ s k ≠ 0 ∧
        (blkOf (canon s) k).testBit r = true ∧ m = raK B₁ B₂ B₃ B₄ B₅ s k then l else 0)
      ≤ if memv5 B₁ B₂ B₃ B₄ B₅ (rowAt r s) = m then l else 0 := by
  have hc := canon_mem hs
  set ρ := repOf (canon s) r with hρ
  have t2 := repOf_table _ hc r (List.mem_range.mpr hr)
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at t2
  rw [Finset.sum_eq_single ρ]
  · split_ifs with h1 h2
    · rfl
    · exfalso
      obtain ⟨-, hz, -, he⟩ := h1
      apply h2
      rw [he, (raK_ne_zero hz).1]
      congr 1
      exact ((eqv_canon hs t2.1 hr).mpr t2.2).symm
    · exact Nat.zero_le _
    · exact le_rfl
  · intro k hk hne
    rw [if_neg]
    rintro ⟨h1, -, h3, -⟩
    have t1 := rep_table _ hc r (List.mem_range.mpr hr) k (List.mem_range.mpr (Finset.mem_range.mp hk))
    rw [h1, h3, Bool.and_self] at t1
    exact hne (Nat.beq_eq ▸ t1.symm)
  · intro h; exact absurd (Finset.mem_range.mpr t2.1) h

/-- **The certificate counts no pin that does not fire.** -/
theorem pinK_le (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) {s : T5} (hs : Proper s) :
    ∀ rp : List (ℕ × ℕ × ℕ), rpOk rp = true →
      ∑ k ∈ range 5, pinK rp B₁ B₂ B₃ B₄ B₅ s k ≤ pinAct B₁ B₂ B₃ B₄ B₅ s rp
  | [], _ => by simp [pinK, pincOf, pinAct]
  | q :: Q, h => by
    simp only [rpOk, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨hr, -⟩, hQ⟩ := h
    simp only [pinK_cons, Finset.sum_add_distrib, pinAct]
    exact Nat.add_le_add (one_pin_le B₁ B₂ B₃ B₄ B₅ hs hr q.2.1 q.2.2) (pinK_le B₁ B₂ B₃ B₄ B₅ hs Q hQ)

/-- The equality pins that fire on a column. -/
def eqAct (s : T5) : List (ℕ × ℕ × ℕ) → ℕ
  | [] => 0
  | q :: Q => (if rowAt q.1 s = rowAt q.2.1 s then q.2.2 else 0) + eqAct s Q

theorem eqc_eq {s : T5} (hs : Proper s) :
    ∀ pp : List (ℕ × ℕ × ℕ), ppOk pp = true → eqcOf pp (canon s) = eqAct s pp
  | [], _ => rfl
  | q :: Q, h => by
    simp only [ppOk, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨⟨hi, hj⟩, -⟩, hQ⟩ := h
    show cond (Nat.beq (rowAt q.1 (canon s)) (rowAt q.2.1 (canon s))) q.2.2 0 + eqcOf Q (canon s)
      = (if rowAt q.1 s = rowAt q.2.1 s then q.2.2 else 0) + eqAct s Q
    rw [eqc_eq hs Q hQ]
    congr 1
    by_cases e : rowAt q.1 s = rowAt q.2.1 s
    · rw [if_pos e, (Nat.beq_eq ▸ (eqv_canon hs hi hj).mp e : Nat.beq _ _ = true)]; rfl
    · have e' : Nat.beq (rowAt q.1 (canon s)) (rowAt q.2.1 (canon s)) = false := by
        rw [← Bool.not_eq_true, Nat.beq_eq]; exact fun h => e ((eqv_canon hs hi hj).mpr h)
      rw [if_neg e, e']; rfl

/-! ### The enumeration -/

theorem allC_iff (f : Ch → Bool) : ∀ L : List Ch, allC f L = true ↔ ∀ x ∈ L, f x = true
  | [] => by simp [allC]
  | x :: L => by
    show (f x && allC f L) = true ↔ _
    rw [Bool.and_eq_true, allC_iff f L, List.forall_mem_cons]

theorem enumP_step {D K : ℕ} {u : C11} {eqc : ℕ} {C : List Ch} {Cs : List (List Ch)} {P pin : ℕ}
    {used : List ℕ} (h : enumP D K u eqc (C :: Cs) P pin used = true) {x : Ch} (hx : x ∈ C)
    (hc : Nat.blt (cnt x.1 used) x.2.1 = true) :
    enumP D K u eqc Cs (Nat.sub P x.2.2.1) (Nat.add pin x.2.2.2) (x.1 :: used) = true := by
  have := (allC_iff _ C).mp h x hx
  rw [hc, Bool.not_true, Bool.false_or] at this
  exact this

/-! ### The box test -/

/-- The weighted sum of an orbit-count vector. -/
noncomputable def dotC (c : C11) (w : Wt5) : ℝ :=
  c.c0 * w 0 + c.c1 * w 1 + c.c2 * w 2 + c.c3 * w 3 + c.c4 * w 4 + c.c5 * w 5 + c.c6 * w 6
    + c.c7 * w 7 + c.c8 * w 8 + c.c9 * w 9 + c.c10 * w 10

theorem term_spec (Lo a b : ℕ) (acc : ℕ × ℕ) {x : ℝ} (hx0 : (Lo : ℝ) / 2000 ≤ x) (hx1 : x ≤ 1) :
    ((term Lo a b acc).1 : ℝ) - (term Lo a b acc).2
      ≤ (acc.1 : ℝ) - acc.2 + 2000 * (((a : ℝ) - b) * x) := by
  unfold term
  by_cases h : b ≤ a
  · have e : Nat.ble b a = true := Nat.ble_eq.mpr h
    rw [e]
    simp only [cond_true, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
    push_cast [h]
    have : ((a : ℝ) - b) * ((Lo : ℝ) / 2000) ≤ ((a : ℝ) - b) * x :=
      mul_le_mul_of_nonneg_left hx0 (by have : (b : ℝ) ≤ a := by exact_mod_cast h
                                        linarith)
    nlinarith
  · have e : Nat.ble b a = false := by
      rw [← Bool.not_eq_true, Nat.ble_eq]; exact h
    rw [e]
    simp only [cond_false, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
    have h' : a ≤ b := by omega
    push_cast [h']
    have : (a : ℝ) ≤ b := by exact_mod_cast h'
    nlinarith

theorem lo2000 : ∀ o : Fin 11, ((![2000, 1974, 1977, 1947, 1953, 1918, 1924, 1954, 1951, 1933,
    1931] : Fin 11 → ℕ) o : ℚ) / 2000 = lo5 o := by decide +kernel

theorem box_edge {w : Wt5} (hw : InBox5 w) (o : Fin 11) {Lo : ℕ}
    (h : (![2000, 1974, 1977, 1947, 1953, 1918, 1924, 1954, 1951, 1933, 1931] : Fin 11 → ℕ) o = Lo) :
    (Lo : ℝ) / 2000 ≤ w o ∧ w o ≤ 1 := by
  obtain ⟨h0, h1⟩ := hw o
  refine ⟨?_, h1⟩
  have := lo2000 o
  rw [h] at this
  have e : ((Lo : ℚ) / 2000 : ℚ) = lo5 o := this
  have e' : ((Lo : ℝ) / 2000) = ((lo5 o : ℚ) : ℝ) := by rw [← e]; push_cast; ring
  rw [e']; exact h0

/-- **The box test is sound**: `e · Σ uₒ wₒ ≤ D · Σ cₒ wₒ` on the box. -/
theorem okc_sound {D : ℕ} {u : C11} {P e : ℕ} (h : okc D u P e = true) {w : Wt5} (hw : InBox5 w) :
    (e : ℝ) * dotC u w ≤ D * dotC (cls5 P) w := by
  simp only [okc] at h
  generalize cls5 P = c at h ⊢
  generalize ha0 : term 2000 (Nat.mul D c.c0) (Nat.mul e u.c0) (0, 0) = a0 at h
  generalize ha1 : term 1974 (Nat.mul D c.c1) (Nat.mul e u.c1) a0 = a1 at h
  generalize ha2 : term 1977 (Nat.mul D c.c2) (Nat.mul e u.c2) a1 = a2 at h
  generalize ha3 : term 1947 (Nat.mul D c.c3) (Nat.mul e u.c3) a2 = a3 at h
  generalize ha4 : term 1953 (Nat.mul D c.c4) (Nat.mul e u.c4) a3 = a4 at h
  generalize ha5 : term 1918 (Nat.mul D c.c5) (Nat.mul e u.c5) a4 = a5 at h
  generalize ha6 : term 1924 (Nat.mul D c.c6) (Nat.mul e u.c6) a5 = a6 at h
  generalize ha7 : term 1954 (Nat.mul D c.c7) (Nat.mul e u.c7) a6 = a7 at h
  generalize ha8 : term 1951 (Nat.mul D c.c8) (Nat.mul e u.c8) a7 = a8 at h
  generalize ha9 : term 1933 (Nat.mul D c.c9) (Nat.mul e u.c9) a8 = a9 at h
  generalize ha10 : term 1931 (Nat.mul D c.c10) (Nat.mul e u.c10) a9 = a10 at h
  have hf : (a10.2 : ℝ) ≤ a10.1 := by exact_mod_cast Nat.ble_eq.mp h
  have t0 := term_spec 2000 (Nat.mul D c.c0) (Nat.mul e u.c0) (0, 0) (box_edge hw 0 rfl).1 (box_edge hw 0 rfl).2
  rw [ha0] at t0
  have t1 := term_spec 1974 (Nat.mul D c.c1) (Nat.mul e u.c1) a0 (box_edge hw 1 rfl).1 (box_edge hw 1 rfl).2
  rw [ha1] at t1
  have t2 := term_spec 1977 (Nat.mul D c.c2) (Nat.mul e u.c2) a1 (box_edge hw 2 rfl).1 (box_edge hw 2 rfl).2
  rw [ha2] at t2
  have t3 := term_spec 1947 (Nat.mul D c.c3) (Nat.mul e u.c3) a2 (box_edge hw 3 rfl).1 (box_edge hw 3 rfl).2
  rw [ha3] at t3
  have t4 := term_spec 1953 (Nat.mul D c.c4) (Nat.mul e u.c4) a3 (box_edge hw 4 rfl).1 (box_edge hw 4 rfl).2
  rw [ha4] at t4
  have t5 := term_spec 1918 (Nat.mul D c.c5) (Nat.mul e u.c5) a4 (box_edge hw 5 rfl).1 (box_edge hw 5 rfl).2
  rw [ha5] at t5
  have t6 := term_spec 1924 (Nat.mul D c.c6) (Nat.mul e u.c6) a5 (box_edge hw 6 rfl).1 (box_edge hw 6 rfl).2
  rw [ha6] at t6
  have t7 := term_spec 1954 (Nat.mul D c.c7) (Nat.mul e u.c7) a6 (box_edge hw 7 rfl).1 (box_edge hw 7 rfl).2
  rw [ha7] at t7
  have t8 := term_spec 1951 (Nat.mul D c.c8) (Nat.mul e u.c8) a7 (box_edge hw 8 rfl).1 (box_edge hw 8 rfl).2
  rw [ha8] at t8
  have t9 := term_spec 1933 (Nat.mul D c.c9) (Nat.mul e u.c9) a8 (box_edge hw 9 rfl).1 (box_edge hw 9 rfl).2
  rw [ha9] at t9
  have t10 := term_spec 1931 (Nat.mul D c.c10) (Nat.mul e u.c10) a9 (box_edge hw 10 rfl).1 (box_edge hw 10 rfl).2
  rw [ha10] at t10
  simp only [Nat.mul_eq] at t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
  push_cast at t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
  unfold dotC
  linarith

/-! ### The bound for one column -/

theorem toList_get (v : V5) : ∀ x ∈ v.toList, ∃ I, 1 ≤ I ∧ I < 32 ∧ x = v.get I := by
  intro x hx
  simp only [V5.toList, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact ⟨1, by norm_num, by norm_num, rfl⟩
    | exact ⟨2, by norm_num, by norm_num, rfl⟩
    | exact ⟨3, by norm_num, by norm_num, rfl⟩
    | exact ⟨4, by norm_num, by norm_num, rfl⟩
    | exact ⟨5, by norm_num, by norm_num, rfl⟩
    | exact ⟨6, by norm_num, by norm_num, rfl⟩
    | exact ⟨7, by norm_num, by norm_num, rfl⟩
    | exact ⟨8, by norm_num, by norm_num, rfl⟩
    | exact ⟨9, by norm_num, by norm_num, rfl⟩
    | exact ⟨10, by norm_num, by norm_num, rfl⟩
    | exact ⟨11, by norm_num, by norm_num, rfl⟩
    | exact ⟨12, by norm_num, by norm_num, rfl⟩
    | exact ⟨13, by norm_num, by norm_num, rfl⟩
    | exact ⟨14, by norm_num, by norm_num, rfl⟩
    | exact ⟨15, by norm_num, by norm_num, rfl⟩
    | exact ⟨16, by norm_num, by norm_num, rfl⟩
    | exact ⟨17, by norm_num, by norm_num, rfl⟩
    | exact ⟨18, by norm_num, by norm_num, rfl⟩
    | exact ⟨19, by norm_num, by norm_num, rfl⟩
    | exact ⟨20, by norm_num, by norm_num, rfl⟩
    | exact ⟨21, by norm_num, by norm_num, rfl⟩
    | exact ⟨22, by norm_num, by norm_num, rfl⟩
    | exact ⟨23, by norm_num, by norm_num, rfl⟩
    | exact ⟨24, by norm_num, by norm_num, rfl⟩
    | exact ⟨25, by norm_num, by norm_num, rfl⟩
    | exact ⟨26, by norm_num, by norm_num, rfl⟩
    | exact ⟨27, by norm_num, by norm_num, rfl⟩
    | exact ⟨28, by norm_num, by norm_num, rfl⟩
    | exact ⟨29, by norm_num, by norm_num, rfl⟩
    | exact ⟨30, by norm_num, by norm_num, rfl⟩
    | exact ⟨31, by norm_num, by norm_num, rfl⟩

theorem interL_subset (F : ℕ → Finset ℕ) (i : ℕ) (L : List ℕ) : interL F (i :: L) ⊆ F i :=
  fun c hc => (mem_interL F i L c).mp hc i List.mem_cons_self

theorem bl_card_le {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6)
    (hB₃ : B₃.card = 6) (hB₄ : B₄.card = 6) (hB₅ : B₅.card = 6) (i : ℕ) :
    (bl B₁ B₂ B₃ B₄ B₅ i).card ≤ 6 := by
  match i with
  | 0 => exact hB₁.le
  | 1 => exact hB₂.le
  | 2 => exact hB₃.le
  | 3 => exact hB₄.le
  | _ + 4 => exact hB₅.le

theorem venn5_erase_lt {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6)
    (hB₃ : B₃.card = 6) (hB₄ : B₄.card = 6) (hB₅ : B₅.card = 6) (s : T5) :
    ∀ x ∈ (venn5 (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))
      (B₅.erase (r5 s))).toList, x < 16 := by
  intro x hx
  obtain ⟨I, h1, h2, rfl⟩ := toList_get _ x hx
  rw [venn5_get _ _ _ _ _ h1 h2, bl_erase]
  obtain ⟨i, L, hL⟩ := List.exists_cons_of_ne_nil (rowsOf_ne_nil h1 h2)
  rw [hL]
  have h3 := Finset.card_le_card (interL_subset (fun j => (bl B₁ B₂ B₃ B₄ B₅ j).erase (rowAt j s)) i L)
  have h4 := Finset.card_le_card (Finset.erase_subset (rowAt i s) (bl B₁ B₂ B₃ B₄ B₅ i))
  have h5 := bl_card_le hB₁ hB₂ hB₃ hB₄ hB₅ i
  omega

theorem urow_table : ∀ p ∈ List.range 15, urowOf p = ⟨Vmat (orb (canons.getD p (0, 1, 0, 1, 0))) 0, Vmat (orb (canons.getD p (0, 1, 0, 1, 0))) 1, Vmat (orb (canons.getD p (0, 1, 0, 1, 0))) 2, Vmat (orb (canons.getD p (0, 1, 0, 1, 0))) 3, Vmat (orb (canons.getD p (0, 1, 0, 1, 0))) 4, Vmat (orb (canons.getD p (0, 1, 0, 1, 0))) 5, Vmat (orb (canons.getD p (0, 1, 0, 1, 0))) 6, Vmat (orb (canons.getD p (0, 1, 0, 1, 0))) 7, Vmat (orb (canons.getD p (0, 1, 0, 1, 0))) 8, Vmat (orb (canons.getD p (0, 1, 0, 1, 0))) 9, Vmat (orb (canons.getD p (0, 1, 0, 1, 0))) 10⟩ := by
  decide +kernel

theorem G_dotC (w : Wt5) (A B C D E : Finset ℕ) :
    G w A B C D E = dotC ⟨corb A B C D E 0, corb A B C D E 1, corb A B C D E 2, corb A B C D E 3, corb A B C D E 4, corb A B C D E 5, corb A B C D E 6, corb A B C D E 7, corb A B C D E 8, corb A B C D E 9, corb A B C D E 10⟩ w := by
  rw [G_eq_sum_orb]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, dotC, corb]
  norm_num
  ring

theorem GU_dotC {w : Wt5} {s : T5} (hs : Proper s) {p : ℕ} (hp : p < 15)
    (hc : canons.getD p (0, 1, 0, 1, 0) = canon s) : GU 6 w s = dotC (urowOf p) w := by
  rw [GU_six w hs, urow_table p (List.mem_range.mpr hp), hc, ← orb_congr (samePat_canon hs)]
  simp only [rowV, Fin.sum_univ_succ, Fin.sum_univ_zero, dotC]
  norm_num
  ring

theorem canon_index {s : T5} (hs : Proper s) : ∃ p < 15, canons.getD p (0, 1, 0, 1, 0) = canon s := by
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem (canon_mem hs)
  refine ⟨i, by simpa [canons] using hi, ?_⟩
  rw [List.getD_eq_getElem _ _ hi, e]

theorem five_lists {L : List (List Ch)} (h : L.length = 5) :
    L = [L.getD 0 [], L.getD 1 [], L.getD 2 [], L.getD 3 [], L.getD 4 []] := by
  match L, h with
  | [a, b, c, d, e], _ => rfl

/-- **The bound for one column from an exact certificate.** -/
theorem exact_state5 (sp : Spec5) (hok : allOk sp = true) (hsp : specOk sp = true)
    {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6)
    (hB₄ : B₄.card = 6) (hB₅ : B₅.card = 6) (hA : AtomsMatch sp B₁ B₂ B₃ B₄ B₅)
    {w : Wt5} (hw : InBox5 w) {s : T5} (hs : Proper s) :
    ((sp.D : ℝ) + sp.K - pinAct B₁ B₂ B₃ B₄ B₅ s sp.rpins - eqAct s sp.ppins) * GU 6 w s
      ≤ sp.D * GB w B₁ B₂ B₃ B₄ B₅ s := by
  -- the pattern and its data
  obtain ⟨p, hp, hpc⟩ := canon_index hs
  have hsp' := hsp
  simp only [specOk, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, List.all_eq_true,
    List.mem_range, List.any_eq_true] at hsp'
  obtain ⟨⟨⟨⟨⟨hD, hvenn⟩, hrp⟩, hpp⟩, hall⟩, -⟩ := hsp'
  obtain ⟨pd, hpd, hpdp⟩ := hall p hp
  have hpat := List.all_eq_true.mp hok pd hpd
  simp only [patOk, Bool.and_eq_true] at hpat
  obtain ⟨hpdok, henum⟩ := hpat
  have hpd' := hpdok
  simp only [pdOk, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hpd'
  obtain ⟨⟨⟨-, hlen⟩, heqc⟩, -⟩ := hpd'
  subst hpdp
  -- the choices of the column
  set x : ℕ → Ch := xch sp B₁ B₂ B₃ B₄ B₅ s with hx
  have hmem : ∀ k < 5, x k ∈ pd.chs.getD k [] := fun k hk =>
    xch_mem hpdok hA hpc hk
  rw [five_lists hlen] at henum
  have e0 := enumP_step henum (hmem 0 (by norm_num)) (cap_level hA hs (k := 0) (by norm_num))
  have e1 := enumP_step e0 (hmem 1 (by norm_num)) (cap_level hA hs (k := 1) (by norm_num))
  have e2 := enumP_step e1 (hmem 2 (by norm_num)) (cap_level hA hs (k := 2) (by norm_num))
  have e3 := enumP_step e2 (hmem 3 (by norm_num)) (cap_level hA hs (k := 3) (by norm_num))
  have e4 := enumP_step e3 (hmem 4 (by norm_num)) (cap_level hA hs (k := 4) (by norm_num))
  simp only [enumP] at e4
  -- the packed Venn data of the successor lists
  set VA := venn5 (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))
    (B₅.erase (r5 s)) with hVA
  have hP : sp.vennP = packV VA + (x 0).2.2.1 + (x 1).2.2.1 + (x 2).2.2.1 + (x 3).2.2.1
      + (x 4).2.2.1 := by
    rw [hvenn, ← venn5_eq_atoms hA, venn5_erase B₁ B₂ B₃ B₄ B₅ hs]
    simp only [packV_addV, packV_vk sp]
    ring
  have hP' : Nat.sub (Nat.sub (Nat.sub (Nat.sub (Nat.sub sp.vennP (x 0).2.2.1) (x 1).2.2.1)
      (x 2).2.2.1) (x 3).2.2.1) (x 4).2.2.1 = packV VA := by
    simp only [Nat.sub_eq]; omega
  rw [hP'] at e4
  have hok' := okc_sound e4 hw
  have hcls : cls5 (packV VA) = ⟨corb (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s))
      (B₄.erase (r4 s)) (B₅.erase (r5 s)) 0, corb (B₁.erase (r1 s)) (B₂.erase (r2 s))
      (B₃.erase (r3 s)) (B₄.erase (r4 s)) (B₅.erase (r5 s)) 1, corb (B₁.erase (r1 s))
      (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s)) (B₅.erase (r5 s)) 2,
      corb (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))
      (B₅.erase (r5 s)) 3, corb (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s))
      (B₄.erase (r4 s)) (B₅.erase (r5 s)) 4, corb (B₁.erase (r1 s)) (B₂.erase (r2 s))
      (B₃.erase (r3 s)) (B₄.erase (r4 s)) (B₅.erase (r5 s)) 5, corb (B₁.erase (r1 s))
      (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s)) (B₅.erase (r5 s)) 6,
      corb (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))
      (B₅.erase (r5 s)) 7, corb (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s))
      (B₄.erase (r4 s)) (B₅.erase (r5 s)) 8, corb (B₁.erase (r1 s)) (B₂.erase (r2 s))
      (B₃.erase (r3 s)) (B₄.erase (r4 s)) (B₅.erase (r5 s)) 9, corb (B₁.erase (r1 s))
      (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s)) (B₅.erase (r5 s)) 10⟩ := by
    rw [cls5, unpack_packV VA (venn5_erase_lt hB₁ hB₂ hB₃ hB₄ hB₅ s), hVA, clsV_venn5]
  rw [hcls, ← G_dotC, ← GU_dotC hs hp hpc] at hok'
  -- the pins
  have hpin := pinK_le B₁ B₂ B₃ B₄ B₅ hs sp.rpins hrp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add] at hpin
  simp only [← xch_pin sp] at hpin
  have heq := eqc_eq hs sp.ppins hpp
  rw [← hpc, ← heqc] at heq
  -- `e ≥ D + K - pins`
  have hGU := GU_nonneg hw s
  set e := Nat.sub (Nat.add sp.D sp.K) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add
    (Nat.add 0 (x 0).2.2.2) (x 1).2.2.2) (x 2).2.2.2) (x 3).2.2.2) (x 4).2.2.2) pd.eqc) with he
  have he' : (sp.D : ℝ) + sp.K - pinAct B₁ B₂ B₃ B₄ B₅ s sp.rpins - eqAct s sp.ppins ≤ e := by
    have : (sp.D + sp.K : ℕ) ≤ e + ((x 0).2.2.2 + (x 1).2.2.2 + (x 2).2.2.2 + (x 3).2.2.2
        + (x 4).2.2.2 + pd.eqc) := by
      simp only [he, Nat.sub_eq, Nat.add_eq]; omega
    have h2 : ((sp.D + sp.K : ℕ) : ℝ) ≤ e + ((x 0).2.2.2 + (x 1).2.2.2 + (x 2).2.2.2
        + (x 3).2.2.2 + (x 4).2.2.2 + pd.eqc : ℕ) := by exact_mod_cast this
    have h3 : (((x 0).2.2.2 + (x 1).2.2.2 + (x 2).2.2.2 + (x 3).2.2.2 + (x 4).2.2.2 : ℕ) : ℝ)
        ≤ pinAct B₁ B₂ B₃ B₄ B₅ s sp.rpins := by exact_mod_cast hpin
    have h4 : (pd.eqc : ℝ) = eqAct s sp.ppins := by exact_mod_cast heq
    push_cast at h2 h3
    linarith
  calc ((sp.D : ℝ) + sp.K - pinAct B₁ B₂ B₃ B₄ B₅ s sp.rpins - eqAct s sp.ppins) * GU 6 w s
      ≤ e * GU 6 w s := mul_le_mul_of_nonneg_right he' hGU
    _ ≤ sp.D * GB w B₁ B₂ B₃ B₄ B₅ s := by unfold GB; exact hok'

/-! ### Averaging -/

theorem qrow_wq (r : ℕ) : qrow r = 1000 * (wq r : ℝ) / 11313086 := by
  unfold qrow wq
  split_ifs <;> norm_num

theorem sum_ite_mul {Ω : Finset T5} (u : T5 → ℝ) (P : T5 → Prop) [DecidablePred P] (l : ℝ) :
    ∑ t ∈ Ω, u t * (if P t then l else 0) = l * ∑ t ∈ Ω.filter P, u t := by
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> ring

/-- **The averaged row pins.** -/
theorem pin_avg (sp : Spec5) {w : Wt5} (hw : InBox5 w) {X₁ X₂ X₃ X₄ X₅ : Finset ℕ}
    (hX₁ : 5 ≤ X₁.card) (hX₂ : 5 ≤ X₂.card) (hX₃ : 5 ≤ X₃.card) (hX₄ : 5 ≤ X₄.card)
    (hX₅ : 5 ≤ X₅.card) {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} (hA : AtomsMatch sp B₁ B₂ B₃ B₄ B₅) :
    ∀ rp : List (ℕ × ℕ × ℕ), rpOk rp = true →
      ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s * (pinAct B₁ B₂ B₃ B₄ B₅ s rp : ℝ)
        ≤ 1000 * (rsum sp.atoms rp : ℝ) / 11313086 * ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s
  | [], _ => by simp [pinAct, rsum]
  | q :: Q, h => by
    simp only [rpOk, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨hr, hm⟩, hQ⟩ := h
    have hm' : q.2.1 ≠ 0 := by
      intro e; rw [e] at hm; simp at hm
    have ih := pin_avg sp hw hX₁ hX₂ hX₃ hX₄ hX₅ hA Q hQ
    have hW : 0 ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s := Finset.sum_nonneg fun s _ => GU_nonneg hw s
    have hfirst : ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s *
        ((if memv5 B₁ B₂ B₃ B₄ B₅ (rowAt q.1 s) = q.2.1 then q.2.2 else 0 : ℕ) : ℝ)
        ≤ q.2.2 * (qrow q.1 * asz sp.atoms q.2.1 * ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s) := by
      simp only [Nat.cast_ite, Nat.cast_zero]
      rw [sum_ite_mul]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      by_cases h32 : q.2.1 < 32
      · have e : (sts X₁ X₂ X₃ X₄ X₅).filter
            (fun s => memv5 B₁ B₂ B₃ B₄ B₅ (rowAt q.1 s) = q.2.1)
            = (sts X₁ X₂ X₃ X₄ X₅).filter (fun s => rowAt q.1 s ∈ atomSet B₁ B₂ B₃ B₄ B₅ q.2.1) :=
          Finset.filter_congr fun s _ => (mem_atomSet hm' _).symm
        rw [e]
        have hf := fibre_set hw hX₁ hX₂ hX₃ hX₄ hX₅ hr (atomSet B₁ B₂ B₃ B₄ B₅ q.2.1)
        rw [hA q.2.1 (Nat.pos_of_ne_zero hm') h32] at hf
        exact hf
      · have e : (sts X₁ X₂ X₃ X₄ X₅).filter
            (fun s => memv5 B₁ B₂ B₃ B₄ B₅ (rowAt q.1 s) = q.2.1) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro s _ e
          have := memv5_lt B₁ B₂ B₃ B₄ B₅ (rowAt q.1 s)
          omega
        rw [e, Finset.sum_empty]
        have : 0 ≤ qrow q.1 := by unfold qrow; split_ifs <;> norm_num
        exact mul_nonneg (mul_nonneg this (Nat.cast_nonneg _)) hW
    have hsplit : ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s * (pinAct B₁ B₂ B₃ B₄ B₅ s (q :: Q) : ℝ)
        = ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s *
            ((if memv5 B₁ B₂ B₃ B₄ B₅ (rowAt q.1 s) = q.2.1 then q.2.2 else 0 : ℕ) : ℝ)
          + ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s * (pinAct B₁ B₂ B₃ B₄ B₅ s Q : ℝ) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [pinAct, Nat.cast_add, mul_add]
    rw [hsplit]
    have hq := qrow_wq q.1
    rw [hq] at hfirst
    have e : 1000 * (rsum sp.atoms (q :: Q) : ℝ) / 11313086 * ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s
        = q.2.2 * (1000 * (wq q.1 : ℝ) / 11313086 * asz sp.atoms q.2.1
            * ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s)
          + 1000 * (rsum sp.atoms Q : ℝ) / 11313086 * ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s := by
      simp only [rsum]; push_cast; ring
    rw [e]
    exact add_le_add hfirst ih

/-- **The averaged equality pins.** -/
theorem eq_avg {w : Wt5} (hw : InBox5 w) {X₁ X₂ X₃ X₄ X₅ : Finset ℕ}
    (hX₁ : 5 ≤ X₁.card) (hX₂ : 5 ≤ X₂.card) (hX₃ : 5 ≤ X₃.card) (hX₄ : 5 ≤ X₄.card)
    (hX₅ : 5 ≤ X₅.card) :
    ∀ pp : List (ℕ × ℕ × ℕ), ppOk pp = true →
      ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s * (eqAct s pp : ℝ)
        ≤ 1000 * (psum pp : ℝ) / 11313086 * ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s
  | [], _ => by simp [eqAct, psum]
  | q :: Q, h => by
    simp only [ppOk, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨⟨hi, hj⟩, hne⟩, hQ⟩ := h
    have hne' : q.1 ≠ q.2.1 := by
      intro e; rw [e] at hne; simp at hne
    have ih := eq_avg hw hX₁ hX₂ hX₃ hX₄ hX₅ Q hQ
    have hfirst : ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s *
        ((if rowAt q.1 s = rowAt q.2.1 s then q.2.2 else 0 : ℕ) : ℝ)
        ≤ q.2.2 * (qrow q.1 * ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s) := by
      simp only [Nat.cast_ite, Nat.cast_zero]
      rw [sum_ite_mul]
      exact mul_le_mul_of_nonneg_left (fibre_pair hw hX₁ hX₂ hX₃ hX₄ hX₅ hi hj hne')
        (Nat.cast_nonneg _)
    have hsplit : ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s * (eqAct s (q :: Q) : ℝ)
        = ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s *
            ((if rowAt q.1 s = rowAt q.2.1 s then q.2.2 else 0 : ℕ) : ℝ)
          + ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s * (eqAct s Q : ℝ) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [eqAct, Nat.cast_add, mul_add]
    rw [hsplit]
    rw [qrow_wq q.1] at hfirst
    have e : 1000 * (psum (q :: Q) : ℝ) / 11313086 * ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s
        = q.2.2 * (1000 * (wq q.1 : ℝ) / 11313086 * ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s)
          + 1000 * (psum Q : ℝ) / 11313086 * ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s := by
      simp only [psum]; push_cast; ring
    rw [e]
    exact add_le_add hfirst ih

/-- **The seam inequality from an exact certificate** for lists with the certificate's atom
sizes. -/
theorem exact_seam5 (sp : Spec5) (hok : allOk sp = true) (hsp : specOk sp = true)
    {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6)
    (hB₄ : B₄.card = 6) (hB₅ : B₅.card = 6) (hA : AtomsMatch sp B₁ B₂ B₃ B₄ B₅)
    {w : Wt5} (hw : InBox5 w) {X₁ X₂ X₃ X₄ X₅ : Finset ℕ}
    (hX₁ : 5 ≤ X₁.card) (hX₂ : 5 ≤ X₂.card) (hX₃ : 5 ≤ X₃.card) (hX₄ : 5 ≤ X₄.card)
    (hX₅ : 5 ≤ X₅.card) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GB w B₁ B₂ B₃ B₄ B₅ s := by
  have hsp' := hsp
  simp only [specOk, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hsp'
  obtain ⟨⟨⟨⟨⟨hD, -⟩, hrp⟩, hpp⟩, -⟩, hK⟩ := hsp'
  set W := ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun s _ => GU_nonneg hw s
  have hsum : ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, ((sp.D : ℝ) + sp.K - pinAct B₁ B₂ B₃ B₄ B₅ s sp.rpins
        - eqAct s sp.ppins) * GU 6 w s
      ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, (sp.D : ℝ) * GB w B₁ B₂ B₃ B₄ B₅ s :=
    Finset.sum_le_sum fun s hs =>
      exact_state5 sp hok hsp hB₁ hB₂ hB₃ hB₄ hB₅ hA hw (proper_of_mem_sts hs)
  have e : ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, ((sp.D : ℝ) + sp.K - pinAct B₁ B₂ B₃ B₄ B₅ s sp.rpins
        - eqAct s sp.ppins) * GU 6 w s
      = ((sp.D : ℝ) + sp.K) * W - ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s * (pinAct B₁ B₂ B₃ B₄ B₅ s sp.rpins : ℝ)
        - ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s * (eqAct s sp.ppins : ℝ) := by
    rw [hW, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [e, ← Finset.mul_sum] at hsum
  have hp := pin_avg sp hw hX₁ hX₂ hX₃ hX₄ hX₅ hA sp.rpins hrp
  have hq := eq_avg hw hX₁ hX₂ hX₃ hX₄ hX₅ sp.ppins hpp
  have hK' : (1000 : ℝ) * ((rsum sp.atoms sp.rpins : ℝ) + psum sp.ppins) ≤ 11313086 * sp.K := by
    exact_mod_cast hK
  have hD' : (0 : ℝ) < sp.D := by exact_mod_cast hD
  have h1 : 1000 * (rsum sp.atoms sp.rpins : ℝ) / 11313086 * W + 1000 * (psum sp.ppins : ℝ) / 11313086 * W
      ≤ (sp.K : ℝ) * W := by
    have : 1000 * (rsum sp.atoms sp.rpins : ℝ) / 11313086 * W + 1000 * (psum sp.ppins : ℝ) / 11313086 * W
        = (1000 * ((rsum sp.atoms sp.rpins : ℝ) + psum sp.ppins)) / 11313086 * W := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by rw [div_le_iff₀ (by norm_num)]; linarith) hW0
  have h2 : (sp.D : ℝ) * W ≤ sp.D * ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GB w B₁ B₂ B₃ B₄ B₅ s := by
    nlinarith
  exact le_of_mul_le_mul_left h2 hD'

end GridGen.Five.Ex5
