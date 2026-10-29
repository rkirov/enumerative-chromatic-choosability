/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.K5.ExactDefs

/-!
# Height five at `k = 5`: soundness of the exact certificates

* `okcC_sound`: the cone test bounds `e · GU ≤ D · GB` at every weight of the cone (the five
  rays exactly, `Q` by the separable minimum).
* The pins of a certificate are pins of `GridGen/Five/K5/Pins.lean` with the atom unions `DS S`
  as colour sets (`XPin.toPin`), whose sizes are the certificate's (`card_DS`).
* `exact_state55`: for a column of the lists, `(D + K - pen) · GU ≤ D · GB`, where `pen` sums the
  multipliers of the pins that fire on the column; the type's penalty is at most `pen`, since a
  condition on a reduced atom can only fire on the actual atom (`penL_le`).
* `exact_seam55`: averaging with `pin_sum5`.
-/

namespace GridGen.Five.K5

open Finset GridGen.Five GridGen.Five.Ex5

/-! ### The cone test -/

theorem FC_eq : ∀ k < 5, FC k = ⟨Fv k 0, Fv k 1, Fv k 2, Fv k 3, Fv k 4, Fv k 5, Fv k 6, Fv k 7,
    Fv k 8, Fv k 9, Fv k 10⟩ := by decide

theorem dotC_rayW (c : C11) {k : ℕ} (hk : k < 5) :
    dotC c (rayW k) = (dot11 c (FC k) : ℝ) / Fv k 0 := by
  rw [FC_eq k hk]
  unfold dotC dot11 rayW
  push_cast
  ring

theorem qterm_spec (L U a b : ℕ) (acc : ℕ × ℕ) {x : ℝ} (hx0 : (L : ℝ) / 1000000 ≤ x)
    (hx1 : x ≤ (U : ℝ) / 1000000) :
    ((qterm L U a b acc).1 : ℝ) - (qterm L U a b acc).2
      ≤ (acc.1 : ℝ) - acc.2 + 1000000 * (((a : ℝ) - b) * x) := by
  unfold qterm
  by_cases h : b ≤ a
  · have h' : Nat.ble b a = true := Nat.ble_eq.mpr h
    simp only [h', cond_true, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
    push_cast [h]
    have hba : (0 : ℝ) ≤ (a : ℝ) - b := by have : (b : ℝ) ≤ a := by exact_mod_cast h
                                           linarith
    have : (L : ℝ) ≤ 1000000 * x := by rw [div_le_iff₀ (by norm_num)] at hx0; linarith
    nlinarith
  · have h' : Nat.ble b a = false := by rw [← Bool.not_eq_true, Nat.ble_eq]; exact h
    simp only [h', cond_false, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
    have hab : a ≤ b := by omega
    push_cast [hab]
    have : 1000000 * x ≤ (U : ℝ) := by rw [le_div_iff₀ (by norm_num)] at hx1; linarith
    have hba : (0 : ℝ) ≤ (b : ℝ) - a := by have : (a : ℝ) ≤ b := by exact_mod_cast hab
                                           linarith
    nlinarith

theorem q_edge {w : Wt5} (hw : InQ w) (j : Fin 11) {L U : ℕ} (hL : qL j = L) (hU : qU j = U) :
    (L : ℝ) / 1000000 ≤ w j ∧ w j ≤ (U : ℝ) / 1000000 := by
  rw [← hL, ← hU]; exact hw j

/-- **The cone test is sound.** -/
theorem okcC_sound {D : ℕ} {u c : C11} {e : ℕ} (h : okcC D u c e = true) {w : Wt5}
    (hw : InCone5 w) : (e : ℝ) * dotC u w ≤ D * dotC c w := by
  simp only [okcC, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨r0, r1⟩, r2⟩, r3⟩, r4⟩, hq⟩ := h
  rcases hw with hw | ⟨k, hk, rfl⟩
  · simp only [qtestQ, qacc, Nat.ble_eq] at hq
    generalize ha0 : qterm 1000000 1000000 (Nat.mul D c.c0) (Nat.mul e u.c0) (0, 0) = a0 at hq
    generalize ha1 : qterm 976588 976593 (Nat.mul D c.c1) (Nat.mul e u.c1) a0 = a1 at hq
    generalize ha2 : qterm 979400 979405 (Nat.mul D c.c2) (Nat.mul e u.c2) a1 = a2 at hq
    generalize ha3 : qterm 948370 948375 (Nat.mul D c.c3) (Nat.mul e u.c3) a2 = a3 at hq
    generalize ha4 : qterm 955997 956002 (Nat.mul D c.c4) (Nat.mul e u.c4) a3 = a4 at hq
    generalize ha5 : qterm 917963 917968 (Nat.mul D c.c5) (Nat.mul e u.c5) a4 = a5 at hq
    generalize ha6 : qterm 925589 925594 (Nat.mul D c.c6) (Nat.mul e u.c6) a5 = a6 at hq
    generalize ha7 : qterm 956703 956708 (Nat.mul D c.c7) (Nat.mul e u.c7) a6 = a7 at hq
    generalize ha8 : qterm 953806 953811 (Nat.mul D c.c8) (Nat.mul e u.c8) a7 = a8 at hq
    generalize ha9 : qterm 936105 936110 (Nat.mul D c.c9) (Nat.mul e u.c9) a8 = a9 at hq
    generalize ha10 : qterm 933215 933220 (Nat.mul D c.c10) (Nat.mul e u.c10) a9 = a10 at hq
    have hf : (a10.2 : ℝ) ≤ a10.1 := by exact_mod_cast hq
    have t0 := qterm_spec 1000000 1000000 (Nat.mul D c.c0) (Nat.mul e u.c0) (0, 0)
      (q_edge hw 0 rfl rfl).1 (q_edge hw 0 rfl rfl).2
    rw [ha0] at t0
    have t1 := qterm_spec 976588 976593 (Nat.mul D c.c1) (Nat.mul e u.c1) a0
      (q_edge hw 1 rfl rfl).1 (q_edge hw 1 rfl rfl).2
    rw [ha1] at t1
    have t2 := qterm_spec 979400 979405 (Nat.mul D c.c2) (Nat.mul e u.c2) a1
      (q_edge hw 2 rfl rfl).1 (q_edge hw 2 rfl rfl).2
    rw [ha2] at t2
    have t3 := qterm_spec 948370 948375 (Nat.mul D c.c3) (Nat.mul e u.c3) a2
      (q_edge hw 3 rfl rfl).1 (q_edge hw 3 rfl rfl).2
    rw [ha3] at t3
    have t4 := qterm_spec 955997 956002 (Nat.mul D c.c4) (Nat.mul e u.c4) a3
      (q_edge hw 4 rfl rfl).1 (q_edge hw 4 rfl rfl).2
    rw [ha4] at t4
    have t5 := qterm_spec 917963 917968 (Nat.mul D c.c5) (Nat.mul e u.c5) a4
      (q_edge hw 5 rfl rfl).1 (q_edge hw 5 rfl rfl).2
    rw [ha5] at t5
    have t6 := qterm_spec 925589 925594 (Nat.mul D c.c6) (Nat.mul e u.c6) a5
      (q_edge hw 6 rfl rfl).1 (q_edge hw 6 rfl rfl).2
    rw [ha6] at t6
    have t7 := qterm_spec 956703 956708 (Nat.mul D c.c7) (Nat.mul e u.c7) a6
      (q_edge hw 7 rfl rfl).1 (q_edge hw 7 rfl rfl).2
    rw [ha7] at t7
    have t8 := qterm_spec 953806 953811 (Nat.mul D c.c8) (Nat.mul e u.c8) a7
      (q_edge hw 8 rfl rfl).1 (q_edge hw 8 rfl rfl).2
    rw [ha8] at t8
    have t9 := qterm_spec 936105 936110 (Nat.mul D c.c9) (Nat.mul e u.c9) a8
      (q_edge hw 9 rfl rfl).1 (q_edge hw 9 rfl rfl).2
    rw [ha9] at t9
    have t10 := qterm_spec 933215 933220 (Nat.mul D c.c10) (Nat.mul e u.c10) a9
      (q_edge hw 10 rfl rfl).1 (q_edge hw 10 rfl rfl).2
    rw [ha10] at t10
    simp only [Nat.mul_eq] at t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
    push_cast at t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
    unfold dotC
    linarith
  · have hF0 : (0 : ℝ) < Fv k 0 := by exact_mod_cast Fv_pos k (by omega)
    rw [dotC_rayW u hk, dotC_rayW c hk, mul_div_assoc', mul_div_assoc',
      div_le_div_iff_of_pos_right hF0]
    have hr : e * dot11 u (FC k) ≤ D * dot11 c (FC k) := by
      interval_cases k
      exacts [r0, r1, r2, r3, r4]
    exact_mod_cast hr

/-! ### The uniform rows -/

theorem urow55_table : ∀ p ∈ List.range 15, urow55 p = ⟨Vmat5 (orb (canons.getD p (0, 1, 0, 1, 0))) 0,
    Vmat5 (orb (canons.getD p (0, 1, 0, 1, 0))) 1, Vmat5 (orb (canons.getD p (0, 1, 0, 1, 0))) 2,
    Vmat5 (orb (canons.getD p (0, 1, 0, 1, 0))) 3, Vmat5 (orb (canons.getD p (0, 1, 0, 1, 0))) 4,
    Vmat5 (orb (canons.getD p (0, 1, 0, 1, 0))) 5, Vmat5 (orb (canons.getD p (0, 1, 0, 1, 0))) 6,
    Vmat5 (orb (canons.getD p (0, 1, 0, 1, 0))) 7, Vmat5 (orb (canons.getD p (0, 1, 0, 1, 0))) 8,
    Vmat5 (orb (canons.getD p (0, 1, 0, 1, 0))) 9, Vmat5 (orb (canons.getD p (0, 1, 0, 1, 0))) 10⟩ := by
  decide +kernel

theorem GU_dotC55 {w : Wt5} {s : T5} (hs : Proper s) {p : ℕ} (hp : p < 15)
    (hc : canons.getD p (0, 1, 0, 1, 0) = canon s) : GU 5 w s = dotC (urow55 p) w := by
  rw [GU_five w hs, urow55_table p (List.mem_range.mpr hp), hc, ← orb_congr (samePat_canon hs)]
  simp only [rowV5, Fin.sum_univ_succ, Fin.sum_univ_zero, dotC]
  norm_num
  ring

theorem bl_card_le5 {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5)
    (hB₃ : B₃.card = 5) (hB₄ : B₄.card = 5) (hB₅ : B₅.card = 5) (i : ℕ) :
    (bl B₁ B₂ B₃ B₄ B₅ i).card ≤ 5 := by
  match i with
  | 0 => exact hB₁.le
  | 1 => exact hB₂.le
  | 2 => exact hB₃.le
  | 3 => exact hB₄.le
  | _ + 4 => exact hB₅.le

theorem venn5_erase_lt5 {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5)
    (hB₃ : B₃.card = 5) (hB₄ : B₄.card = 5) (hB₅ : B₅.card = 5) (s : T5) :
    ∀ x ∈ (venn5 (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))
      (B₅.erase (r5 s))).toList, x < 16 := by
  intro x hx
  obtain ⟨I, h1, h2, rfl⟩ := toList_get _ x hx
  rw [venn5_get _ _ _ _ _ h1 h2, bl_erase]
  obtain ⟨i, L, hL⟩ := List.exists_cons_of_ne_nil (rowsOf_ne_nil h1 h2)
  rw [hL]
  have h3 := Finset.card_le_card
    (interL_subset (fun j => (bl B₁ B₂ B₃ B₄ B₅ j).erase (rowAt j s)) i L)
  have h4 := Finset.card_le_card (Finset.erase_subset (rowAt i s) (bl B₁ B₂ B₃ B₄ B₅ i))
  have h5 := bl_card_le5 hB₁ hB₂ hB₃ hB₄ hB₅ i
  omega

/-! ### Atom unions as colour sets -/

/-- The colours of the lists whose atom lies in the set `S` (a bit mask over atom codes). -/
def DS (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (S : ℕ) : Finset ℕ :=
  (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅).filter (fun c => S.testBit (memv5 B₁ B₂ B₃ B₄ B₅ c))

theorem list_sum_range (f : ℕ → ℕ) : ∀ n, ((List.range n).map f).sum = ∑ m ∈ range n, f m
  | 0 => rfl
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f n,
      Finset.sum_range_succ]; simp

theorem memv5_zero_of {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} {c : ℕ} (h : c ∉ B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅) :
    memv5 B₁ B₂ B₃ B₄ B₅ c = 0 := by
  simp only [Finset.mem_union, not_or] at h
  simp [memv5, h]

/-- **The size of an atom union.** -/
theorem card_DS {sp : XSpec} {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} (hA : AtomsMatch sp.toSpec5 B₁ B₂ B₃ B₄ B₅)
    {S : ℕ} (hS : S.testBit 0 = false) : (DS B₁ B₂ B₃ B₄ B₅ S).card = dszX sp.atoms S := by
  rw [dszX, list_sum_range]
  rw [Finset.card_eq_sum_card_fiberwise (f := memv5 B₁ B₂ B₃ B₄ B₅) (t := range 32)
    (fun c _ => Finset.mem_range.mpr (memv5_lt _ _ _ _ _ c))]
  refine Finset.sum_congr rfl fun m hm => ?_
  by_cases hb : S.testBit m = true
  · rw [if_pos hb]
    have hm0 : m ≠ 0 := by rintro rfl; rw [hS] at hb; exact absurd hb (by decide)
    rw [show asz sp.atoms m = asz sp.toSpec5.atoms m from rfl,
      ← hA m (Nat.pos_of_ne_zero hm0) (Finset.mem_range.mp hm)]
    congr 1
    ext c
    simp only [DS, atomSet, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ hb⟩, h2⟩
  · rw [if_neg hb, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c hc e
    simp only [DS, Finset.mem_filter] at hc
    exact hb (e ▸ hc.2)

/-! ### Exact pins as pins -/

/-- The factor of a peel. -/
def XPeel.toFac (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (A : List (ℕ × ℕ)) : XPeel → Fac5
  | mem r S => Fac5.mem r (DS B₁ B₂ B₃ B₄ B₅ S) (dszX A S)
  | eq r j => Fac5.eqr r j

/-- The block of a pin. -/
def blkOfX (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (A : List (ℕ × ℕ)) (r0 : ℕ) : List ℕ → Blk5
  | [S] => Blk5.one r0 (DS B₁ B₂ B₃ B₄ B₅ S) (dszX A S)
  | [S, S'] => Blk5.two r0 (DS B₁ B₂ B₃ B₄ B₅ S) (DS B₁ B₂ B₃ B₄ B₅ S') (dszX A S) (dszX A S')
  | [S, S', S''] => Blk5.three r0 (DS B₁ B₂ B₃ B₄ B₅ S) (DS B₁ B₂ B₃ B₄ B₅ S')
      (DS B₁ B₂ B₃ B₄ B₅ S'') (dszX A S) (dszX A S') (dszX A S'')
  | _ => Blk5.none

/-- An exact pin as a pin. -/
def XPin.toPin (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (A : List (ℕ × ℕ)) (q : XPin) : Pin5 :=
  ⟨blkOfX B₁ B₂ B₃ B₄ B₅ A q.r0 q.bs, q.peels.map (XPeel.toFac B₁ B₂ B₃ B₄ B₅ A)⟩

theorem toPin_bndX (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (A : List (ℕ × ℕ)) (q : XPin) :
    (q.toPin B₁ B₂ B₃ B₄ B₅ A).bnd = xbnd A q := by
  unfold Pin5.bnd xbnd XPin.toPin
  congr 1
  · rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    cases p <;> rfl
  · simp only
    match q.bs with
    | [] => rfl
    | [S] => rfl
    | [S, S'] => rfl
    | [S, S', S''] => rfl
    | _ :: _ :: _ :: _ :: _ => rfl

theorem blkOfX_reads (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (A : List (ℕ × ℕ)) (r0 : ℕ) (bs : List ℕ)
    (hl : bs.length ≤ 3) (i : ℕ) :
    (blkOfX B₁ B₂ B₃ B₄ B₅ A r0 bs).reads i = blkReads r0 bs i := by
  match bs, hl with
  | [], _ => simp [blkOfX, Blk5.reads, blkReads]
  | [S], _ =>
    simp only [blkOfX, Blk5.reads, blkReads, List.length_singleton]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]; omega
  | [S, S'], _ =>
    simp only [blkOfX, Blk5.reads, blkReads, List.length_cons, List.length_nil]
    rw [Bool.eq_iff_iff, Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff,
      decide_eq_true_iff]; omega
  | [S, S', S''], _ =>
    simp only [blkOfX, Blk5.reads, blkReads, List.length_cons, List.length_nil]
    rw [Bool.eq_iff_iff, Bool.or_eq_true, Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff,
      decide_eq_true_iff, decide_eq_true_iff]; omega

theorem toFac_reads (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (A : List (ℕ × ℕ)) (p : XPeel) :
    (p.toFac B₁ B₂ B₃ B₄ B₅ A).reads = p.reads ∧ (p.toFac B₁ B₂ B₃ B₄ B₅ A).row = p.row := by
  cases p with
  | mem r S =>
    refine ⟨funext fun i => ?_, rfl⟩
    simp only [XPeel.toFac, Fac5.reads, XPeel.reads]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq]
  | eq r j =>
    refine ⟨funext fun i => ?_, rfl⟩
    simp only [XPeel.toFac, Fac5.reads, XPeel.reads]
    rw [Bool.eq_iff_iff, Bool.or_eq_true, Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff,
      beq_iff_eq, beq_iff_eq]

theorem peelOK_ofX {sp : XSpec} {B₁ B₂ B₃ B₄ B₅ : Finset ℕ}
    (hA : AtomsMatch sp.toSpec5 B₁ B₂ B₃ B₄ B₅) (r0 : ℕ) (bs : List ℕ) (hl : bs.length ≤ 3) :
    ∀ ps : List XPeel, xpeelOK r0 bs ps = true →
      PeelOK5 (blkOfX B₁ B₂ B₃ B₄ B₅ sp.atoms r0 bs).reads
        (ps.map (XPeel.toFac B₁ B₂ B₃ B₄ B₅ sp.atoms))
  | [], _ => trivial
  | p :: ps, h => by
    simp only [xpeelOK, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.all_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨?_, ?_, ?_, peelOK_ofX hA r0 bs hl ps h4⟩
    · rw [blkOfX_reads _ _ _ _ _ _ _ _ hl, (toFac_reads B₁ B₂ B₃ B₄ B₅ sp.atoms p).2]; exact h1
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      rw [(toFac_reads B₁ B₂ B₃ B₄ B₅ sp.atoms g').1, (toFac_reads B₁ B₂ B₃ B₄ B₅ sp.atoms p).2]
      have := h2 g' hg'
      simpa using this
    · cases p with
      | mem r S =>
        simp only [XPeel.okb, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
          Bool.not_true] at h3
        exact ⟨h3.1, (card_DS hA h3.2).le⟩
      | eq r j =>
        simp only [XPeel.okb, decide_eq_true_eq] at h3
        exact h3

theorem toPin_OKX {sp : XSpec} {B₁ B₂ B₃ B₄ B₅ : Finset ℕ}
    (hA : AtomsMatch sp.toSpec5 B₁ B₂ B₃ B₄ B₅) {q : XPin} (hq : q.okb = true) :
    (q.toPin B₁ B₂ B₃ B₄ B₅ sp.atoms).OK := by
  simp only [XPin.okb, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hq
  obtain ⟨⟨⟨hl, hr⟩, hbs⟩, hp⟩ := hq
  refine ⟨?_, peelOK_ofX hA q.r0 q.bs hl q.peels hp⟩
  have hb : ∀ S ∈ q.bs, S.testBit 0 = false := fun S hS => by
    have := hbs S hS; simpa using this
  simp only [XPin.toPin]
  match hm : q.bs, hl with
  | [], _ => trivial
  | [S], _ =>
    rw [hm] at hb hr
    exact ⟨by simp at hr; omega, (card_DS hA (hb S (by simp))).le⟩
  | [S, S'], _ =>
    rw [hm] at hb hr
    exact ⟨by simp at hr; omega, (card_DS hA (hb S (by simp))).le,
      (card_DS hA (hb S' (by simp))).le⟩
  | [S, S', S''], _ =>
    rw [hm] at hb hr
    exact ⟨by simp at hr; omega, (card_DS hA (hb S (by simp))).le,
      (card_DS hA (hb S' (by simp))).le, (card_DS hA (hb S'' (by simp))).le⟩

/-! ### Pins fire on the actual columns -/

section state

variable {sp : XSpec} {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} {w : Wt5} {s : T5}

/-- The multipliers of the pins that fire on a column. -/
def penAct (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (A : List (ℕ × ℕ)) (s : T5) (P : List XPin) : ℕ :=
  (P.map fun q => if (q.toPin B₁ B₂ B₃ B₄ B₅ A).ev s then q.lam else 0).sum

theorem repOf_facts {s : T5} (hs : Proper s) {r : ℕ} (hr : r < 5) :
    repOf (canon s) r < 5 ∧ rowAt (repOf (canon s) r) s = rowAt r s := by
  have h := repOf_table _ (canon_mem hs) r (List.mem_range.mpr hr)
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact ⟨h.1, (eqv_canon hs h.1 hr).mpr h.2⟩

/-- **A condition on a reduced atom fires on the actual colour.** -/
theorem cond_fires (hs : Proper s) {r : ℕ} (hr : r < 5) {S : ℕ} (hS : S.testBit 0 = false)
    (h : S.testBit (xch sp.toSpec5 B₁ B₂ B₃ B₄ B₅ s (repOf (canon s) r)).1 = true) :
    rowAt r s ∈ DS B₁ B₂ B₃ B₄ B₅ S := by
  obtain ⟨hk, hrow⟩ := repOf_facts hs hr
  have hne : (xch sp.toSpec5 B₁ B₂ B₃ B₄ B₅ s (repOf (canon s) r)).1 ≠ 0 := by
    intro e; rw [e, hS] at h; exact absurd h (by decide)
  obtain ⟨-, he, -⟩ := xch_fst hne
  rw [he, hrow] at h
  simp only [DS, Finset.mem_filter]
  refine ⟨?_, h⟩
  by_contra hc
  rw [memv5_zero_of hc, hS] at h
  exact absurd h (by decide)

theorem used_getD (x : ℕ → Ch) {k : ℕ} (hk : k < 5) :
    [(x 4).1, (x 3).1, (x 2).1, (x 1).1, (x 0).1].getD (4 - k) 0 = (x k).1 := by
  interval_cases k <;> rfl

theorem blkConds_mem : ∀ (r0 : ℕ) (bs : List ℕ) (rs : ℕ × ℕ), rs ∈ blkConds r0 bs →
    r0 ≤ rs.1 ∧ rs.1 < r0 + bs.length ∧ rs.2 ∈ bs
  | _, [], _, h => absurd h List.not_mem_nil
  | r0, S :: Ss, rs, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := blkConds_mem (r0 + 1) Ss rs h
      simp only [List.length_cons, List.mem_cons]
      exact ⟨by omega, by omega, Or.inr this.2.2⟩

theorem memConds_mem : ∀ (ps : List XPeel) (rs : ℕ × ℕ), rs ∈ memConds ps →
    XPeel.mem rs.1 rs.2 ∈ ps
  | [], _, h => absurd h List.not_mem_nil
  | XPeel.mem r S :: ps, rs, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (memConds_mem ps rs h)
  | XPeel.eq r j :: ps, rs, h => List.mem_cons_of_mem _ (memConds_mem ps rs h)

theorem xpeelOK_okb {r0 : ℕ} {bs : List ℕ} : ∀ {ps : List XPeel}, xpeelOK r0 bs ps = true →
    ∀ p ∈ ps, p.okb = true
  | [], _, _, h => absurd h List.not_mem_nil
  | q :: ps, h, p, hp => by
    simp only [xpeelOK, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.1.2
    · exact xpeelOK_okb h.2 p hp

/-- The conditions of a well-formed pin are on rows below five, with masks avoiding atom `0`. -/
theorem conds_ok {q : XPin} (hq : q.okb = true) :
    ∀ rs ∈ q.conds, rs.1 < 5 ∧ rs.2.testBit 0 = false := by
  simp only [XPin.okb, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hq
  obtain ⟨⟨⟨hl, hr⟩, hbs⟩, hp⟩ := hq
  intro rs hrs
  rcases List.mem_append.mp hrs with h | h
  · obtain ⟨h1, h2, h3⟩ := blkConds_mem q.r0 q.bs rs h
    exact ⟨by omega, by have := hbs _ h3; simpa using this⟩
  · have hm := xpeelOK_okb hp _ (memConds_mem q.peels rs h)
    simp only [XPeel.okb, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true] at hm
    exact hm

theorem eqsOK_iff (hs : Proper s) : ∀ ps : List XPeel, (∀ p ∈ ps, p.okb = true) →
    eqsOK (canon s) ps = true → ∀ r j, XPeel.eq r j ∈ ps → rowAt r s = rowAt j s
  | [], _, _, r, j, h => absurd h List.not_mem_nil
  | XPeel.eq r' j' :: ps, hok, h, r, j, hm => by
    simp only [eqsOK, Bool.and_eq_true, beq_iff_eq] at h
    have hk := hok _ List.mem_cons_self
    simp only [XPeel.okb, decide_eq_true_eq] at hk
    rcases List.mem_cons.mp hm with e | hm
    · cases e; exact (eqv_canon hs hk.1 hk.2.1).mpr h.1
    · exact eqsOK_iff hs ps (fun p hp => hok p (List.mem_cons_of_mem _ hp)) h.2 r j hm
  | XPeel.mem r' S' :: ps, hok, h, r, j, hm => by
    simp only [eqsOK] at h
    rcases List.mem_cons.mp hm with e | hm
    · cases e
    · exact eqsOK_iff hs ps (fun p hp => hok p (List.mem_cons_of_mem _ hp)) h r j hm

theorem mem_memConds : ∀ (ps : List XPeel) {r S : ℕ}, XPeel.mem r S ∈ ps → (r, S) ∈ memConds ps
  | [], _, _, h => absurd h List.not_mem_nil
  | XPeel.mem r' S' :: ps, r, S, h => by
    rcases List.mem_cons.mp h with e | h
    · cases e; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_memConds ps h)
  | XPeel.eq r' j' :: ps, r, S, h => by
    rcases List.mem_cons.mp h with e | h
    · cases e
    · exact mem_memConds ps h

theorem blkConds_get : ∀ (r0 : ℕ) (bs : List ℕ) (i : ℕ), i < bs.length →
    (r0 + i, bs.getD i 0) ∈ blkConds r0 bs
  | _, [], _, h => absurd h (by simp)
  | r0, S :: Ss, 0, _ => by simp [blkConds]
  | r0, S :: Ss, i + 1, h => by
    simp only [blkConds, List.getD_cons_succ]
    have := blkConds_get (r0 + 1) Ss i (by simp at h; omega)
    rw [show r0 + 1 + i = r0 + (i + 1) by ring] at this
    exact List.mem_cons_of_mem _ this

/-- **A pin whose equalities hold and whose conditions hold on the colours fires.** -/
theorem toPin_fires (hs : Proper s) {q : XPin} (hq : q.okb = true)
    (he : eqsOK (canon s) q.peels = true)
    (hc : ∀ rs ∈ q.conds, rowAt rs.1 s ∈ DS B₁ B₂ B₃ B₄ B₅ rs.2) :
    (q.toPin B₁ B₂ B₃ B₄ B₅ sp.atoms).ev s = true := by
  have hq' := hq
  simp only [XPin.okb, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hq'
  obtain ⟨⟨⟨hl, hr⟩, hbs⟩, hp⟩ := hq'
  have hpk := xpeelOK_okb hp
  unfold Pin5.ev XPin.toPin allEv5
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_map]
  constructor
  · rintro f ⟨p, hp, rfl⟩
    cases p with
    | mem r S =>
      simp only [XPeel.toFac, Fac5.ev, decide_eq_true_eq]
      exact hc (r, S) (List.mem_append_right _ (mem_memConds q.peels hp))
    | eq r j =>
      simp only [XPeel.toFac, Fac5.ev, decide_eq_true_eq]
      exact eqsOK_iff hs q.peels hpk he r j hp
  · have hb : ∀ i, i < q.bs.length → rowAt (q.r0 + i) s ∈ DS B₁ B₂ B₃ B₄ B₅ (q.bs.getD i 0) := by
      intro i hi
      exact hc (q.r0 + i, q.bs.getD i 0) (List.mem_append_left _ (blkConds_get q.r0 q.bs i hi))
    match hm : q.bs, hl with
    | [], _ => rfl
    | [S], _ =>
      have h0 := hb 0 (by rw [hm]; simp)
      simp only [hm, List.getD_cons_zero, Nat.add_zero] at h0
      simp [blkOfX, Blk5.ev, h0]
    | [S, S'], _ =>
      have h0 := hb 0 (by rw [hm]; simp)
      have h1 := hb 1 (by rw [hm]; simp)
      simp only [hm, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at h0 h1
      simp [blkOfX, Blk5.ev, h0, h1]
    | [S, S', S''], _ =>
      have h0 := hb 0 (by rw [hm]; simp)
      have h1 := hb 1 (by rw [hm]; simp)
      have h2 := hb 2 (by rw [hm]; simp)
      simp only [hm, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at h0 h1 h2
      simp [blkOfX, Blk5.ev, h0, h1, h2]

/-- **The penalty of a type is at most the penalty of the column.** -/
theorem penL_le (hs : Proper s) (x : ℕ → Ch) (hx : ∀ k, x k = xch sp.toSpec5 B₁ B₂ B₃ B₄ B₅ s k) :
    ∀ P : List XPin, P.all XPin.okb = true →
      penL (compileX (canon s) P) [(x 4).1, (x 3).1, (x 2).1, (x 1).1, (x 0).1]
        ≤ penAct B₁ B₂ B₃ B₄ B₅ sp.atoms s P
  | [], _ => le_rfl
  | q :: P, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := penL_le hs x hx P h.2
    unfold compileX penAct at *
    rw [List.filterMap_cons]
    simp only [List.map_cons, List.sum_cons]
    unfold compileOne
    by_cases he : eqsOK (canon s) q.peels = true
    · simp only [he, if_true]
      unfold penL at *
      simp only [List.map_cons, List.sum_cons]
      refine Nat.add_le_add ?_ ih
      split_ifs with hf hev
      · exact le_rfl
      · exfalso
        apply hev
        refine toPin_fires hs h.1 he fun rs hrs => ?_
        obtain ⟨hr5, hS⟩ := conds_ok h.1 rs hrs
        have := List.all_eq_true.mp hf (repOf (canon s) rs.1, rs.2)
          (List.mem_map.mpr ⟨rs, hrs, rfl⟩)
        simp only at this
        rw [used_getD x (repOf_facts hs hr5).1, hx] at this
        exact cond_fires hs hr5 hS this
      · exact Nat.zero_le _
      · exact le_rfl
    · simp only [Bool.not_eq_true] at he
      simp only [he, Bool.false_eq_true, if_false]
      exact le_trans ih (Nat.le_add_left _ _)

end state

/-! ### The split check -/

/-- The empty choice. -/
def ch0 : Ch := (0, 5, 0, 0)

/-- The check of the types of a pattern whose first two rows take the `i`-th and `j`-th
choices. -/
def subOK (sp : XSpec) (pc : PatD × List (List (ℕ × ℕ) × ℕ)) (i j : ℕ) : Bool :=
  !(Nat.blt (Ex5.cnt ((pc.1.chs.getD 0 []).getD i ch0).1 []) ((pc.1.chs.getD 0 []).getD i ch0).2.1) ||
  !(Nat.blt (Ex5.cnt ((pc.1.chs.getD 1 []).getD j ch0).1 [((pc.1.chs.getD 0 []).getD i ch0).1])
    ((pc.1.chs.getD 1 []).getD j ch0).2.1) ||
  enumX sp.D sp.K (urow55 pc.1.p) pc.2 (pc.1.chs.drop 2)
    (Nat.sub (Nat.sub sp.vennP ((pc.1.chs.getD 0 []).getD i ch0).2.2.1)
      ((pc.1.chs.getD 1 []).getD j ch0).2.2.1)
    [((pc.1.chs.getD 1 []).getD j ch0).1, ((pc.1.chs.getD 0 []).getD i ch0).1]

/-- The cheap part of the check of a pattern. -/
def hdrOK (sp : XSpec) (pc : PatD × List (List (ℕ × ℕ) × ℕ)) : Bool :=
  pdOk sp.toSpec5 pc.1 && decide (compileX (canons.getD pc.1.p (0, 1, 0, 1, 0)) sp.pins = pc.2)

/-- **A certificate passes**: the scalar conditions, and for every pattern the cheap part and all
the split checks. -/
def XPass (sp : XSpec) : Prop :=
  specOkX sp = true ∧ ∀ pc ∈ sp.pds, hdrOK sp pc = true ∧
    ∀ i < (pc.1.chs.getD 0 []).length, ∀ j < (pc.1.chs.getD 1 []).length, subOK sp pc i j = true

theorem enumX_step {D K : ℕ} {u : C11} {cps : List (List (ℕ × ℕ) × ℕ)} {C : List Ch}
    {Cs : List (List Ch)} {P : ℕ} {used : List ℕ} (h : enumX D K u cps (C :: Cs) P used = true)
    {x : Ch} (hx : x ∈ C) (hc : Nat.blt (Ex5.cnt x.1 used) x.2.1 = true) :
    enumX D K u cps Cs (Nat.sub P x.2.2.1) (x.1 :: used) = true := by
  have := (allC_iff _ C).mp h x hx
  rw [hc, Bool.not_true, Bool.false_or] at this
  exact this

theorem getD_of_mem {α : Type*} {L : List α} {x : α} (d : α) (h : x ∈ L) :
    ∃ i < L.length, L.getD i d = x := by
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem h
  exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi, e]⟩

section state2

variable {sp : XSpec} {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} {w : Wt5} {s : T5}

/-- **The bound for one column from an exact certificate.** -/
theorem exact_state55 (hpass : XPass sp) (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5)
    (hB₃ : B₃.card = 5) (hB₄ : B₄.card = 5) (hB₅ : B₅.card = 5)
    (hA : AtomsMatch sp.toSpec5 B₁ B₂ B₃ B₄ B₅) (hw : InCone5 w) (hs : Proper s) :
    ((sp.D : ℝ) + sp.K - penAct B₁ B₂ B₃ B₄ B₅ sp.atoms s sp.pins) * GU 5 w s
      ≤ sp.D * GB w B₁ B₂ B₃ B₄ B₅ s := by
  obtain ⟨hsp, hpats⟩ := hpass
  obtain ⟨p, hp, hpc⟩ := canon_index hs
  have hsp' := hsp
  simp only [specOkX, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, List.all_eq_true,
    List.mem_range, List.any_eq_true, decide_eq_true_eq] at hsp'
  obtain ⟨⟨⟨⟨hD, hvenn⟩, hpins⟩, hall⟩, -⟩ := hsp'
  obtain ⟨pc, hpcm, hpcp⟩ := hall p hp
  obtain ⟨hhdr, hsub⟩ := hpats pc hpcm
  simp only [hdrOK, Bool.and_eq_true, decide_eq_true_eq] at hhdr
  obtain ⟨hpdok, hcmp⟩ := hhdr
  have hpd' := hpdok
  simp only [pdOk, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hpd'
  obtain ⟨⟨⟨-, hlen⟩, -⟩, -⟩ := hpd'
  have hpcp' : pc.1.p = p := hpcp
  rw [hpcp'] at hcmp
  -- the choices of the column
  set x : ℕ → Ch := xch sp.toSpec5 B₁ B₂ B₃ B₄ B₅ s with hx
  have hmem : ∀ k < 5, x k ∈ pc.1.chs.getD k [] := fun k hk =>
    xch_mem hpdok hA (by rw [hpcp']; exact hpc) hk
  obtain ⟨i, hi, hie⟩ := getD_of_mem ch0 (hmem 0 (by norm_num))
  obtain ⟨j, hj, hje⟩ := getD_of_mem ch0 (hmem 1 (by norm_num))
  have hs2 := hsub i hi j hj
  have c0 := cap_level hA hs (k := 0) (by norm_num)
  have c1 := cap_level hA hs (k := 1) (by norm_num)
  simp only [List.range_zero, List.reverse_nil, List.map_nil, List.range_one,
    List.reverse_singleton, List.map_singleton] at c0 c1
  simp only [subOK, hie, hje] at hs2
  rw [← hx] at c0 c1
  simp only [c0, c1, Bool.not_true, Bool.false_or] at hs2
  have hdrop : pc.1.chs.drop 2 = [pc.1.chs.getD 2 [], pc.1.chs.getD 3 [], pc.1.chs.getD 4 []] := by
    rw [five_lists hlen]; rfl
  rw [hdrop] at hs2
  have e2 := enumX_step hs2 (hmem 2 (by norm_num)) (cap_level hA hs (k := 2) (by norm_num))
  have e3 := enumX_step e2 (hmem 3 (by norm_num)) (cap_level hA hs (k := 3) (by norm_num))
  have e4 := enumX_step e3 (hmem 4 (by norm_num)) (cap_level hA hs (k := 4) (by norm_num))
  simp only [enumX, forceN_eq, okc55_eq] at e4
  -- the packed Venn data of the successor lists
  set VA := venn5 (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))
    (B₅.erase (r5 s)) with hVA
  have hP : sp.vennP = packV VA + (x 0).2.2.1 + (x 1).2.2.1 + (x 2).2.2.1 + (x 3).2.2.1
      + (x 4).2.2.1 := by
    have : sp.toSpec5.vennP = sp.vennP := rfl
    rw [hvenn, show sp.atoms = sp.toSpec5.atoms from rfl, ← venn5_eq_atoms hA,
      venn5_erase B₁ B₂ B₃ B₄ B₅ hs]
    simp only [packV_addV, packV_vk sp.toSpec5]
    ring
  have hP' : Nat.sub (Nat.sub (Nat.sub (Nat.sub (Nat.sub sp.vennP (x 0).2.2.1) (x 1).2.2.1)
      (x 2).2.2.1) (x 3).2.2.1) (x 4).2.2.1 = packV VA := by
    simp only [Nat.sub_eq]; omega
  rw [hP'] at e4
  have hok' := okcC_sound e4 hw
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
    rw [cls5, unpack_packV VA (venn5_erase_lt5 hB₁ hB₂ hB₃ hB₄ hB₅ s), hVA, clsV_venn5]
  rw [hcls, ← G_dotC, hpcp', ← GU_dotC55 hs hp hpc] at hok'
  -- the pins
  have hpen := penL_le (sp := sp) hs x (fun _ => rfl) sp.pins (List.all_eq_true.mpr hpins)
  rw [← hcmp, hpc] at e4 hok'
  have hGU := GU_nonneg55 hw s
  set e := Nat.sub (Nat.add sp.D sp.K)
    (penL (compileX (canon s) sp.pins) [(x 4).1, (x 3).1, (x 2).1, (x 1).1, (x 0).1]) with he
  have he' : (sp.D : ℝ) + sp.K - penAct B₁ B₂ B₃ B₄ B₅ sp.atoms s sp.pins ≤ e := by
    have : sp.D + sp.K ≤ e + penAct B₁ B₂ B₃ B₄ B₅ sp.atoms s sp.pins := by
      simp only [he, Nat.sub_eq, Nat.add_eq]; omega
    have h2 : ((sp.D + sp.K : ℕ) : ℝ) ≤ ((e + penAct B₁ B₂ B₃ B₄ B₅ sp.atoms s sp.pins : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at h2
    linarith
  calc ((sp.D : ℝ) + sp.K - penAct B₁ B₂ B₃ B₄ B₅ sp.atoms s sp.pins) * GU 5 w s
      ≤ e * GU 5 w s := mul_le_mul_of_nonneg_right he' hGU
    _ ≤ sp.D * GB w B₁ B₂ B₃ B₄ B₅ s := by rw [mul_comm]; unfold GB; linarith

end state2

/-! ### Averaging -/

section seam

variable {sp : XSpec} {B₁ B₂ B₃ B₄ B₅ X₁ X₂ X₃ X₄ X₅ : Finset ℕ} {w : Wt5}

theorem sum_penAct (hw : InCone5 w) (h₁ : 4 ≤ X₁.card) (h₂ : 4 ≤ X₂.card) (h₃ : 4 ≤ X₃.card)
    (h₄ : 4 ≤ X₄.card) (h₅ : 4 ≤ X₅.card) (hA : AtomsMatch sp.toSpec5 B₁ B₂ B₃ B₄ B₅) :
    ∀ P : List XPin, P.all XPin.okb = true →
      ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 5 w s * (penAct B₁ B₂ B₃ B₄ B₅ sp.atoms s P : ℝ)
        ≤ (((P.map fun q => (q.lam : ℚ) * xbnd sp.atoms q).sum : ℚ) : ℝ)
          * ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 5 w s
  | [], _ => by simp [penAct]
  | q :: P, hP => by
    simp only [List.all_cons, Bool.and_eq_true] at hP
    have ih := sum_penAct hw h₁ h₂ h₃ h₄ h₅ hA P hP.2
    have hq := pin_sum5 hw h₁ h₂ h₃ h₄ h₅ (q.toPin B₁ B₂ B₃ B₄ B₅ sp.atoms) (toPin_OKX hA hP.1)
    rw [toPin_bndX] at hq
    have e1 : ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 5 w s * (penAct B₁ B₂ B₃ B₄ B₅ sp.atoms s (q :: P) : ℝ)
        = (q.lam : ℝ) * ∑ s ∈ (sts X₁ X₂ X₃ X₄ X₅).filter
            (fun t => (q.toPin B₁ B₂ B₃ B₄ B₅ sp.atoms).ev t = true), GU 5 w s
          + ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 5 w s * (penAct B₁ B₂ B₃ B₄ B₅ sp.atoms s P : ℝ) := by
      rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      simp only [penAct, List.map_cons, List.sum_cons]
      split_ifs <;> push_cast <;> ring
    rw [e1]
    have hl : (0 : ℝ) ≤ q.lam := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hq hl
    simp only [List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast]
    linarith

/-- **The seam inequality from an exact certificate**, for lists with its atom sizes. -/
theorem exact_seam55 (hpass : XPass sp) (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5)
    (hB₃ : B₃.card = 5) (hB₄ : B₄.card = 5) (hB₅ : B₅.card = 5)
    (hA : AtomsMatch sp.toSpec5 B₁ B₂ B₃ B₄ B₅) (hw : InCone5 w)
    (h₁ : 4 ≤ X₁.card) (h₂ : 4 ≤ X₂.card) (h₃ : 4 ≤ X₃.card) (h₄ : 4 ≤ X₄.card)
    (h₅ : 4 ≤ X₅.card) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 5 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GB w B₁ B₂ B₃ B₄ B₅ s := by
  have hsp := hpass.1
  simp only [specOkX, Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq] at hsp
  obtain ⟨⟨⟨⟨hD, -⟩, hpins⟩, -⟩, hK⟩ := hsp
  set W := ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 5 w s with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun s _ => GU_nonneg55 hw s
  have hsum : ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, ((sp.D : ℝ) + sp.K
        - penAct B₁ B₂ B₃ B₄ B₅ sp.atoms s sp.pins) * GU 5 w s
      ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, (sp.D : ℝ) * GB w B₁ B₂ B₃ B₄ B₅ s :=
    Finset.sum_le_sum fun s hs =>
      exact_state55 hpass hB₁ hB₂ hB₃ hB₄ hB₅ hA hw (proper_of_mem_sts hs)
  have e : ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, ((sp.D : ℝ) + sp.K
        - penAct B₁ B₂ B₃ B₄ B₅ sp.atoms s sp.pins) * GU 5 w s
      = ((sp.D : ℝ) + sp.K) * W
        - ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 5 w s * (penAct B₁ B₂ B₃ B₄ B₅ sp.atoms s sp.pins : ℝ) := by
    rw [hW, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [e, ← Finset.mul_sum] at hsum
  have hp := sum_penAct hw h₁ h₂ h₃ h₄ h₅ hA sp.pins hpins
  have hK' : (((sp.pins.map fun q => (q.lam : ℚ) * xbnd sp.atoms q).sum : ℚ) : ℝ) ≤ sp.K := by
    exact_mod_cast hK
  have h1 := mul_le_mul_of_nonneg_right hK' hW0
  have hD' : (0 : ℝ) < sp.D := by exact_mod_cast hD
  have h2 : (sp.D : ℝ) * W ≤ sp.D * ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GB w B₁ B₂ B₃ B₄ B₅ s := by linarith
  exact le_of_mul_le_mul_left h2 hD'

end seam

end GridGen.Five.K5
