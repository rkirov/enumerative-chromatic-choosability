/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.K4.Box

/-!
# Height four at `k = 4`: regions of column types

A **region** is a set of column types given by the equality bits `e₁₃, e₂₄, e₁₄` and, for each
row, a set `rsᵢ` of possible masks (a 16-bit set: bit `m` for the mask `m`). Its intersection sizes
lie in a box (`rbox`): the size for `J` is the Venn size `I_J` minus the number `δ_J` of counted rows
of `J` (a row repeating an earlier row of `J` is not counted) whose mask contains `J`, and
`δ_J` lies between the number of counted rows all of whose possible masks contain `J` and the number
of those some of whose possible masks do (`allJ`, `anyJ`). With sizes `nᵢ = 4 - [own bit]`, the
box valuations `boxV` bound every state of the region (`regionV_sound`), provided each row's
possible masks agree on the row's own bit (`Unif`). An empty box has no states (`regionV` is
`none`).

The seam vector of a state has `|dₖ| ≤ 256` (`gvec_bound`), since its class counts count proper
colourings of four lists of at most four colours.
-/

namespace GridGen.Four.K4

open Finset GridGen.Four

/-! ### Mask sets -/

/-- The set of masks containing `J`, as a 16-bit set. -/
def upJ : ℕ → ℕ
  | 0 => 65535 | 1 => 43690 | 2 => 52428 | 3 => 34952 | 4 => 61680 | 5 => 41120 | 6 => 49344
  | 7 => 32896 | 8 => 65280 | 9 => 43520 | 10 => 52224 | 11 => 34816 | 12 => 61440
  | 13 => 40960 | 14 => 49152 | _ => 32768

theorem testBit_upJ : ∀ J < 16, ∀ m < 16, Nat.testBit (upJ J) m = sup m J := by decide

/-- Some mask of the set contains `J`. -/
def anyJ (rs J : ℕ) : Bool := !(Nat.beq (Nat.land rs (upJ J)) 0)

/-- Every mask of the set contains `J`. -/
def allJ (rs J : ℕ) : Bool := Nat.beq (Nat.land rs (upJ J)) rs

theorem sup_of_allJ {rs J m : ℕ} (hJ : J < 16) (hm : m < 16) (h : allJ rs J = true)
    (hr : Nat.testBit rs m = true) : sup m J = true := by
  unfold allJ at h
  have e : Nat.land rs (upJ J) = rs := Nat.eq_of_beq_eq_true h
  have : Nat.testBit (rs &&& upJ J) m = true := by
    rw [show (rs &&& upJ J) = Nat.land rs (upJ J) from rfl, e]; exact hr
  rw [Nat.testBit_and, Bool.and_eq_true] at this
  rw [← testBit_upJ J hJ m hm]; exact this.2

theorem anyJ_of_sup {rs J m : ℕ} (hJ : J < 16) (hm : m < 16) (h : sup m J = true)
    (hr : Nat.testBit rs m = true) : anyJ rs J = true := by
  have hb : Nat.testBit (rs &&& upJ J) m = true := by
    rw [Nat.testBit_and, hr, testBit_upJ J hJ m hm, h]; rfl
  have hne : Nat.land rs (upJ J) ≠ 0 := by
    intro h0
    rw [show (rs &&& upJ J) = Nat.land rs (upJ J) from rfl, h0, Nat.zero_testBit] at hb
    exact absurd hb (by decide)
  unfold anyJ
  cases e : Nat.beq (Nat.land rs (upJ J)) 0
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) hne

theorem mIdx_lt (r : Mem) : mIdx r < 16 := by
  obtain ⟨a, b, c, d⟩ := r
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem mv_lt (B : Col) (c : ℕ) : mv B c < 16 := mIdx_lt _

/-- A counted row's term lies between its `allJ` and `anyJ` bounds. -/
theorem term_bounds {rs J m : ℕ} (hJ : J < 16) (hm : m < 16) (hr : Nat.testBit rs m = true) :
    bn (allJ rs J) ≤ bn (sup m J) ∧ bn (sup m J) ≤ bn (anyJ rs J) := by
  constructor
  · cases h : allJ rs J
    · exact Nat.zero_le _
    · rw [sup_of_allJ hJ hm h hr]
  · cases h : sup m J
    · exact Nat.zero_le _
    · rw [anyJ_of_sup hJ hm h hr]

theorem term_bounds' {rs J m : ℕ} (b : Bool) (hJ : J < 16) (hm : m < 16)
    (hr : Nat.testBit rs m = true) :
    bn (b && allJ rs J) ≤ bn (b && sup m J) ∧ bn (b && sup m J) ≤ bn (b && anyJ rs J) := by
  cases b
  · exact ⟨le_refl _, le_refl _⟩
  · simpa using term_bounds hJ hm hr

/-! ### The box of a region -/

/-- The interval for one intersection: `I_J - δ_J` with `δ_J ∈ [dmin, dmax]`, clipped at `0`. -/
def ivl (I dmin dmax : ℕ) : ℕ × ℕ := (Nat.sub I dmax, Nat.sub I dmin)

/-- The same for `I_J ∈ [Il, Ih]`. -/
def ivl2v (Il Ih dmin dmax : ℕ) : ℕ × ℕ := (Nat.sub Il dmax, Nat.sub Ih dmin)

/-- **The box of a region.** Returns `(lo, hi)`. -/
def rbox (vl vh : VN) (rs1 rs2 rs3 rs4 : ℕ) (e13 e24 e14 : Bool) : X11 × X11 :=
  let i12 := ivl2v vl.x12 vh.x12 (Nat.add (bn (allJ rs1 3)) (bn (allJ rs2 3)))
    (Nat.add (bn (anyJ rs1 3)) (bn (anyJ rs2 3)))
  let i23 := ivl2v vl.x23 vh.x23 (Nat.add (bn (allJ rs2 6)) (bn (allJ rs3 6)))
    (Nat.add (bn (anyJ rs2 6)) (bn (anyJ rs3 6)))
  let i34 := ivl2v vl.x34 vh.x34 (Nat.add (bn (allJ rs3 12)) (bn (allJ rs4 12)))
    (Nat.add (bn (anyJ rs3 12)) (bn (anyJ rs4 12)))
  let i13 := ivl2v vl.x13 vh.x13 (Nat.add (bn (allJ rs1 5)) (bn (!e13 && allJ rs3 5)))
    (Nat.add (bn (anyJ rs1 5)) (bn (!e13 && anyJ rs3 5)))
  let i24 := ivl2v vl.x24 vh.x24 (Nat.add (bn (allJ rs2 10)) (bn (!e24 && allJ rs4 10)))
    (Nat.add (bn (anyJ rs2 10)) (bn (!e24 && anyJ rs4 10)))
  let i14 := ivl2v vl.x14 vh.x14 (Nat.add (bn (allJ rs1 9)) (bn (!e14 && allJ rs4 9)))
    (Nat.add (bn (anyJ rs1 9)) (bn (!e14 && anyJ rs4 9)))
  let i123 := ivl2v vl.x123 vh.x123 (Nat.add (Nat.add (bn (allJ rs1 7)) (bn (allJ rs2 7))) (bn (!e13 && allJ rs3 7)))
    (Nat.add (Nat.add (bn (anyJ rs1 7)) (bn (anyJ rs2 7))) (bn (!e13 && anyJ rs3 7)))
  let i234 := ivl2v vl.x234 vh.x234
    (Nat.add (Nat.add (bn (allJ rs2 14)) (bn (allJ rs3 14))) (bn (!e24 && allJ rs4 14)))
    (Nat.add (Nat.add (bn (anyJ rs2 14)) (bn (anyJ rs3 14))) (bn (!e24 && anyJ rs4 14)))
  let i124 := ivl2v vl.x124 vh.x124
    (Nat.add (Nat.add (bn (allJ rs1 11)) (bn (allJ rs2 11))) (bn (!e24 && !e14 && allJ rs4 11)))
    (Nat.add (Nat.add (bn (anyJ rs1 11)) (bn (anyJ rs2 11))) (bn (!e24 && !e14 && anyJ rs4 11)))
  let i134 := ivl2v vl.x134 vh.x134
    (Nat.add (Nat.add (bn (allJ rs1 13)) (bn (!e13 && allJ rs3 13))) (bn (!e14 && allJ rs4 13)))
    (Nat.add (Nat.add (bn (anyJ rs1 13)) (bn (!e13 && anyJ rs3 13))) (bn (!e14 && anyJ rs4 13)))
  let iq := ivl2v vl.x1234 vh.x1234
    (Nat.add (Nat.add (bn (allJ rs1 15)) (bn (allJ rs2 15)))
      (Nat.add (bn (!e13 && allJ rs3 15)) (bn (!e24 && !e14 && allJ rs4 15))))
    (Nat.add (Nat.add (bn (anyJ rs1 15)) (bn (anyJ rs2 15)))
      (Nat.add (bn (!e13 && anyJ rs3 15)) (bn (!e24 && !e14 && anyJ rs4 15))))
  (⟨i12.1, i23.1, i34.1, i13.1, i24.1, i14.1, i123.1, i234.1, i124.1, i134.1, iq.1⟩,
    ⟨i12.2, i23.2, i34.2, i13.2, i24.2, i14.2, i123.2, i234.2, i124.2, i134.2, iq.2⟩)

/-- Every interval of the box is nonempty. -/
def X11.leB (lo hi : X11) : Bool :=
  Nat.ble lo.e12 hi.e12 && Nat.ble lo.e23 hi.e23 && Nat.ble lo.e34 hi.e34 &&
  Nat.ble lo.a13 hi.a13 && Nat.ble lo.a24 hi.a24 && Nat.ble lo.a14 hi.a14 &&
  Nat.ble lo.t123 hi.t123 && Nat.ble lo.t234 hi.t234 && Nat.ble lo.a124 hi.a124 &&
  Nat.ble lo.a134 hi.a134 && Nat.ble lo.q hi.q

/-- The size of a successor list from the row's mask set. -/
def nOf (rs i : ℕ) : ℕ := cond (allJ rs i) 3 4

/-- **The valuations of a region**, for Venn sizes between `vl` and `vh`: `none` if its box is
empty. -/
def regionV (vl vh : VN) (rs1 rs2 rs3 rs4 : ℕ) (e13 e24 e14 : Bool) : Option V5 :=
  let b := rbox vl vh rs1 rs2 rs3 rs4 e13 e24 e14
  cond (Nat.beq rs1 0 || Nat.beq rs2 0 || Nat.beq rs3 0 || Nat.beq rs4 0) none
    (cond (X11.leB b.1 b.2)
      (some (boxV (nOf rs1 1) (nOf rs2 2) (nOf rs3 4) (nOf rs4 8) (hrowN e13 e24 e14) b.1 b.2)) none)

/-! ### The seam vector is small -/

theorem ce_bounds (t : T4) : (0 ≤ (ce t).1 ∧ (ce t).1 ≤ 1) ∧ (0 ≤ (ce t).2.1 ∧ (ce t).2.1 ≤ 1) ∧
    (0 ≤ (ce t).2.2.1 ∧ (ce t).2.2.1 ≤ 1) ∧ (0 ≤ (ce t).2.2.2 ∧ (ce t).2.2.2 ≤ 1) := by
  unfold ce; split_ifs <;> decide

theorem card_stsC_le (A : Col) :
    (stsC A).card ≤ A.1.card * A.2.1.card * A.2.2.1.card * A.2.2.2.card := by
  unfold stsC
  rw [sts_eq_filter]
  refine (Finset.card_filter_le _ _).trans ?_
  simp only [Finset.card_product]
  ring_nf; exact le_refl _

theorem cnt_bounds (A : Col) :
    (0 ≤ (cnt A).1 ∧ (cnt A).1 ≤ (stsC A).card) ∧ (0 ≤ (cnt A).2.1 ∧ (cnt A).2.1 ≤ (stsC A).card) ∧
    (0 ≤ (cnt A).2.2.1 ∧ (cnt A).2.2.1 ≤ (stsC A).card) ∧
    (0 ≤ (cnt A).2.2.2 ∧ (cnt A).2.2.2 ≤ (stsC A).card) := by
  unfold cnt
  simp only [Prod.fst_sum, Prod.snd_sum]
  have hc : ((stsC A).card : ℤ) = ∑ _t ∈ stsC A, (1 : ℤ) := by simp
  rw [hc]
  refine ⟨⟨Finset.sum_nonneg fun t _ => (ce_bounds t).1.1,
      Finset.sum_le_sum fun t _ => (ce_bounds t).1.2⟩,
    ⟨Finset.sum_nonneg fun t _ => (ce_bounds t).2.1.1,
      Finset.sum_le_sum fun t _ => (ce_bounds t).2.1.2⟩,
    ⟨Finset.sum_nonneg fun t _ => (ce_bounds t).2.2.1.1,
      Finset.sum_le_sum fun t _ => (ce_bounds t).2.2.1.2⟩,
    ⟨Finset.sum_nonneg fun t _ => (ce_bounds t).2.2.2.1,
      Finset.sum_le_sum fun t _ => (ce_bounds t).2.2.2.2⟩⟩

theorem card_erase_le4 {X : Finset ℕ} (h : X.card = 4) (a : ℕ) : (X.erase a).card ≤ 4 :=
  (Finset.card_erase_le).trans h.le

theorem stsC_ers_le (B : Col) (hB : CardsIn 4 4 B) (s : T4) : (stsC (ers B s)).card ≤ 256 := by
  obtain ⟨⟨a1, a1'⟩, ⟨a2, a2'⟩, ⟨a3, a3'⟩, ⟨a4, a4'⟩⟩ := hB
  refine (card_stsC_le _).trans ?_
  simp only [ers]
  have h1 := card_erase_le4 (le_antisymm a1' a1) (r1 s)
  have h2 := card_erase_le4 (le_antisymm a2' a2) (r2 s)
  have h3 := card_erase_le4 (le_antisymm a3' a3) (r3 s)
  have h4 := card_erase_le4 (le_antisymm a4' a4) (r4 s)
  calc _ ≤ 4 * 4 * 4 * 4 := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3) h4
    _ = 256 := by norm_num

theorem hrowN_bounds (e13 e24 e14 : Bool) :
    (hrowN e13 e24 e14).1 ≤ 20 ∧ (hrowN e13 e24 e14).2.1 ≤ 20 ∧ (hrowN e13 e24 e14).2.2.1 ≤ 20 ∧
      (hrowN e13 e24 e14).2.2.2 ≤ 20 := by
  cases e13 <;> cases e24 <;> cases e14 <;> decide


/-! ### Soundness of a region -/

/-- A row's mask set agrees on the row's own bit `i ∈ {1, 2, 4, 8}`. -/
def Unif (rs i : ℕ) : Prop := allJ rs i = true ∨ anyJ rs i = false

/-- Venn sizes below others, on the eleven larger intersections. -/
def VLe (a b : VN) : Prop :=
  a.x12 ≤ b.x12 ∧ a.x23 ≤ b.x23 ∧ a.x34 ≤ b.x34 ∧ a.x13 ≤ b.x13 ∧ a.x24 ≤ b.x24 ∧ a.x14 ≤ b.x14 ∧
    a.x123 ≤ b.x123 ∧ a.x234 ≤ b.x234 ∧ a.x124 ≤ b.x124 ∧ a.x134 ≤ b.x134 ∧ a.x1234 ≤ b.x1234

theorem VLe_refl (a : VN) : VLe a a := by
  unfold VLe; omega

theorem ivl2 {vl v vh a b c d x y : ℕ} {D : ℤ} (hl : vl ≤ v) (hh : v ≤ vh)
    (hD : D = (v : ℤ) - (x + y : ℕ)) (h0 : 0 ≤ D) (hx : a ≤ x ∧ x ≤ c) (hy : b ≤ y ∧ y ≤ d) :
    ((ivl2v vl vh (Nat.add a b) (Nat.add c d)).1 : ℤ) ≤ D ∧
      D ≤ (ivl2v vl vh (Nat.add a b) (Nat.add c d)).2 := by
  simp only [ivl2v, Nat.add_eq, Nat.sub_eq]; omega

theorem ivl3 {vl v vh a b c d e f x y z : ℕ} {D : ℤ} (hl : vl ≤ v) (hh : v ≤ vh)
    (hD : D = (v : ℤ) - (x + y + z : ℕ)) (h0 : 0 ≤ D)
    (hx : a ≤ x ∧ x ≤ d) (hy : b ≤ y ∧ y ≤ e) (hz : c ≤ z ∧ z ≤ f) :
    ((ivl2v vl vh (Nat.add (Nat.add a b) c) (Nat.add (Nat.add d e) f)).1 : ℤ) ≤ D ∧
      D ≤ (ivl2v vl vh (Nat.add (Nat.add a b) c) (Nat.add (Nat.add d e) f)).2 := by
  simp only [ivl2v, Nat.add_eq, Nat.sub_eq]; omega

theorem ivl4 {vl v vh a b c d e f g h x y z t : ℕ} {D : ℤ} (hl : vl ≤ v) (hh : v ≤ vh)
    (hD : D = (v : ℤ) - (x + y + (z + t) : ℕ))
    (h0 : 0 ≤ D) (hx : a ≤ x ∧ x ≤ e) (hy : b ≤ y ∧ y ≤ f) (hz : c ≤ z ∧ z ≤ g)
    (ht : d ≤ t ∧ t ≤ h) :
    ((ivl2v vl vh (Nat.add (Nat.add a b) (Nat.add c d)) (Nat.add (Nat.add e f) (Nat.add g h))).1 : ℤ)
        ≤ D ∧
      D ≤ (ivl2v vl vh (Nat.add (Nat.add a b) (Nat.add c d)) (Nat.add (Nat.add e f) (Nat.add g h))).2 := by
  simp only [ivl2v, Nat.add_eq, Nat.sub_eq]; omega

theorem nOf_eq {rs i m : ℕ} (hi : i < 16) (hm : m < 16) (hr : Nat.testBit rs m = true)
    (hu : Unif rs i) : (nOf rs i : ℤ) = 4 - bn (sup m i) := by
  unfold nOf
  rcases hu with h | h
  · rw [h, sup_of_allJ hi hm h hr]; rfl
  · cases e : sup m i
    · rw [show allJ rs i = false from ?_]; · rfl
      cases e' : allJ rs i
      · rfl
      · rw [anyJ_of_sup hi hm (sup_of_allJ hi hm e' hr) hr] at h; exact absurd h (by decide)
    · rw [anyJ_of_sup hi hm e hr] at h; exact absurd h (by decide)

/-- The seam vector of a proper state as class counts minus a transfer row. -/
theorem gvec_eq_cls (B : Col) (I : VN) (hI : I.toVenn = vennOf B.1 B.2.1 B.2.2.1 B.2.2.2) {s : T4}
    (hs : Proper s) :
    gvec B s = cls (datC (ers B s)) - hQ (hrowN (decide (r1 s = r3 s)) (decide (r2 s = r4 s))
      (decide (r1 s = r4 s))) := by
  unfold gvec
  rw [if_pos hs, cnt_eq_cls, hrow_eq]
  rfl

/-- The intersection sizes of the successor lists as the data vector of the type. -/
theorem datC_eq_datZ (B : Col) (I : VN) (hI : I.toVenn = vennOf B.1 B.2.1 B.2.2.1 B.2.2.2)
    {s : T4} (hs : Proper s) :
    datC (ers B s) = (datZ I (mv B (r1 s)) (mv B (r2 s)) (mv B (r3 s)) (mv B (r4 s))
      (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))).val := by
  obtain ⟨p12, p23, p34⟩ := hs
  have hd := dat_eq B.1 B.2.1 B.2.2.1 B.2.2.2 ⟨p12, p23, p34⟩
  rw [actDat_eq_datC, ← hI, ← datZ_val] at hd
  · exact hd
  · intro h; rw [of_decide_eq_true h]
  · intro h; rw [of_decide_eq_true h]
  · intro h; rw [of_decide_eq_true h]
  · rintro ⟨h1, h2⟩; exact p34 ((of_decide_eq_true h1).symm.trans (of_decide_eq_true h2))
  · rintro ⟨h1, h2⟩; exact p12 ((of_decide_eq_true h2).trans (of_decide_eq_true h1).symm)

/-- **Soundness of a region**: a proper state whose masks lie in the row sets is bounded by the
box valuations of the region (which is then nonempty). -/
theorem regionV_sound (B : Col) (hB : CardsIn 4 4 B) (I : VN)
    (hI : I.toVenn = vennOf B.1 B.2.1 B.2.2.1 B.2.2.2) {vl vh : VN} (hl : VLe vl I) (hh : VLe I vh)
    {s : T4} (hs : Proper s)
    {rs1 rs2 rs3 rs4 : ℕ} (h1 : Nat.testBit rs1 (mv B (r1 s)) = true)
    (h2 : Nat.testBit rs2 (mv B (r2 s)) = true) (h3 : Nat.testBit rs3 (mv B (r3 s)) = true)
    (h4 : Nat.testBit rs4 (mv B (r4 s)) = true) (u1 : Unif rs1 1) (u2 : Unif rs2 2)
    (u3 : Unif rs3 4) (u4 : Unif rs4 8) :
    ∃ x, regionV vl vh rs1 rs2 rs3 rs4 (decide (r1 s = r3 s)) (decide (r2 s = r4 s))
        (decide (r1 s = r4 s)) = some x ∧
      ∀ k w, w ∈ famW k → (x.get k).val ≤ dot (gvec B s) w := by
  have hd := datC_eq_datZ B I hI hs
  have hg := gvec_eq_cls B I hI hs
  set D := datC (ers B s) with hDdef
  set m1 := mv B (r1 s)
  set m2 := mv B (r2 s)
  set m3 := mv B (r3 s)
  set m4 := mv B (r4 s)
  have l1 : m1 < 16 := mv_lt _ _
  have l2 : m2 < 16 := mv_lt _ _
  have l3 : m3 < 16 := mv_lt _ _
  have l4 : m4 < 16 := mv_lt _ _
  -- the list sizes
  obtain ⟨⟨a1, a1'⟩, ⟨a2, a2'⟩, ⟨a3, a3'⟩, ⟨a4, a4'⟩⟩ := hB
  have hx : I.x1 = 4 ∧ I.x2 = 4 ∧ I.x3 = 4 ∧ I.x4 = 4 := by
    have e := congrArg (fun V : Venn => (V.x1, V.x2, V.x3, V.x4)) hI
    simp only [VN.toVenn, vennOf, Prod.mk.injEq] at e
    omega
  -- the box
  have nn : ∀ (X : Finset ℕ), (0 : ℤ) ≤ X.card := fun X => Nat.cast_nonneg _
  have F := fun (f : Dat → ℤ) => congrArg f hd
  obtain ⟨l12, l23, l34, l13, l24, l14, l123, l234, l124, l134, l1234⟩ := hl
  obtain ⟨u12, u23, u34, u13, u24, u14, u123, u234, u124, u134, u1234⟩ := hh
  have hbox : InBox (nOf rs1 1) (nOf rs2 2) (nOf rs3 4) (nOf rs4 8)
      (rbox vl vh rs1 rs2 rs3 rs4 (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))).1
      (rbox vl vh rs1 rs2 rs3 rs4 (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))).2
      D := by
    have f12 := ivl2 l12 u12 (F Dat.e12) (nn _) (term_bounds (J := 3) (by decide) l1 h1)
      (term_bounds (J := 3) (by decide) l2 h2)
    have f23 := ivl2 l23 u23 (F Dat.e23) (nn _) (term_bounds (J := 6) (by decide) l2 h2)
      (term_bounds (J := 6) (by decide) l3 h3)
    have f34 := ivl2 l34 u34 (F Dat.e34) (nn _) (term_bounds (J := 12) (by decide) l3 h3)
      (term_bounds (J := 12) (by decide) l4 h4)
    have f13 := ivl2 l13 u13 (F Dat.a13) (nn _) (term_bounds (J := 5) (by decide) l1 h1)
      (term_bounds' (J := 5) (!decide (r1 s = r3 s)) (by decide) l3 h3)
    have f24 := ivl2 l24 u24 (F Dat.a24) (nn _) (term_bounds (J := 10) (by decide) l2 h2)
      (term_bounds' (J := 10) (!decide (r2 s = r4 s)) (by decide) l4 h4)
    have f14 := ivl2 l14 u14 (F Dat.a14) (nn _) (term_bounds (J := 9) (by decide) l1 h1)
      (term_bounds' (J := 9) (!decide (r1 s = r4 s)) (by decide) l4 h4)
    have f123 := ivl3 l123 u123 (F Dat.t123) (nn _) (term_bounds (J := 7) (by decide) l1 h1)
      (term_bounds (J := 7) (by decide) l2 h2)
      (term_bounds' (J := 7) (!decide (r1 s = r3 s)) (by decide) l3 h3)
    have f234 := ivl3 l234 u234 (F Dat.t234) (nn _) (term_bounds (J := 14) (by decide) l2 h2)
      (term_bounds (J := 14) (by decide) l3 h3)
      (term_bounds' (J := 14) (!decide (r2 s = r4 s)) (by decide) l4 h4)
    have f124 := ivl3 l124 u124 (F Dat.a124) (nn _) (term_bounds (J := 11) (by decide) l1 h1)
      (term_bounds (J := 11) (by decide) l2 h2)
      (term_bounds' (J := 11) (!decide (r2 s = r4 s) && !decide (r1 s = r4 s)) (by decide) l4 h4)
    have f134 := ivl3 l134 u134 (F Dat.a134) (nn _) (term_bounds (J := 13) (by decide) l1 h1)
      (term_bounds' (J := 13) (!decide (r1 s = r3 s)) (by decide) l3 h3)
      (term_bounds' (J := 13) (!decide (r1 s = r4 s)) (by decide) l4 h4)
    have fq := ivl4 l1234 u1234 (F Dat.q) (nn _) (term_bounds (J := 15) (by decide) l1 h1)
      (term_bounds (J := 15) (by decide) l2 h2)
      (term_bounds' (J := 15) (!decide (r1 s = r3 s)) (by decide) l3 h3)
      (term_bounds' (J := 15) (!decide (r2 s = r4 s) && !decide (r1 s = r4 s)) (by decide) l4 h4)
    have n1 := congrArg Dat.n1 hd
    have n2 := congrArg Dat.n2 hd
    have n3 := congrArg Dat.n3 hd
    have n4 := congrArg Dat.n4 hd
    simp only [datZ, DZ.val, Zp.val_mk] at n1 n2 n3 n4
    rw [hx.1] at n1
    rw [hx.2.1] at n2
    rw [hx.2.2.1] at n3
    rw [hx.2.2.2] at n4
    refine ⟨?_, ?_, ?_, ?_, f12.1, f12.2, f23.1, f23.2, f34.1, f34.2, f13.1, f13.2, f24.1, f24.2,
      f14.1, f14.2, f123.1, f123.2, f234.1, f234.2, f124.1, f124.2, f134.1, f134.2, fq.1, fq.2⟩
    · rw [n1, nOf_eq (by decide) l1 h1 u1]; push_cast; ring
    · rw [n2, nOf_eq (by decide) l2 h2 u2]; push_cast; ring
    · rw [n3, nOf_eq (by decide) l3 h3 u3]; push_cast; ring
    · rw [n4, nOf_eq (by decide) l4 h4 u4]; push_cast; ring
  -- the seam vector is small
  have hb : |(cls D - hQ (hrowN (decide (r1 s = r3 s)) (decide (r2 s = r4 s))
      (decide (r1 s = r4 s)))).2.1| ≤ 256 ∧
      |(cls D - hQ (hrowN (decide (r1 s = r3 s)) (decide (r2 s = r4 s))
      (decide (r1 s = r4 s)))).2.2.1| ≤ 256 ∧
      |(cls D - hQ (hrowN (decide (r1 s = r3 s)) (decide (r2 s = r4 s))
      (decide (r1 s = r4 s)))).2.2.2| ≤ 256 := by
    rw [hDdef, ← cnt_eq_cls]
    have hc := cnt_bounds (ers B s)
    have hn : ((stsC (ers B s)).card : ℤ) ≤ 256 := by
      exact_mod_cast stsC_ers_le B ⟨⟨a1, a1'⟩, ⟨a2, a2'⟩, ⟨a3, a3'⟩, ⟨a4, a4'⟩⟩ s
    have hh := hrowN_bounds (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))
    simp only [hQ, Prod.snd_sub, Prod.fst_sub, abs_le]
    omega
  -- conclude
  refine ⟨boxV (nOf rs1 1) (nOf rs2 2) (nOf rs3 4) (nOf rs4 8)
      (hrowN (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)))
      (rbox vl vh rs1 rs2 rs3 rs4 (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))).1
      (rbox vl vh rs1 rs2 rs3 rs4 (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))).2,
      ?_, fun k w hw => ?_⟩
  · have hle : X11.leB (rbox vl vh rs1 rs2 rs3 rs4 (decide (r1 s = r3 s)) (decide (r2 s = r4 s))
        (decide (r1 s = r4 s))).1 (rbox vl vh rs1 rs2 rs3 rs4 (decide (r1 s = r3 s))
        (decide (r2 s = r4 s)) (decide (r1 s = r4 s))).2 = true := by
      obtain ⟨-, -, -, -, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
        b18, b19, b20, b21, b22⟩ := hbox
      simp only [X11.leB, Bool.and_eq_true, Nat.ble_eq]
      omega
    have hz : ∀ (rs m : ℕ), Nat.testBit rs m = true → Nat.beq rs 0 = false := by
      intro rs m h
      cases e : Nat.beq rs 0
      · rfl
      · rw [Nat.eq_of_beq_eq_true e, Nat.zero_testBit] at h; exact absurd h (by decide)
    simp only [regionV, hle, hz _ _ h1, hz _ _ h2, hz _ _ h3, hz _ _ h4, Bool.or_false,
      cond_false, cond_true]
  · rw [hg]
    exact boxV_sound _ _ _ _ _ _ _ D hbox hb k w hw

end GridGen.Four.K4
