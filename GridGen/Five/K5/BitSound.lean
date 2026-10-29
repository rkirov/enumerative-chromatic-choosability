/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.K5.RowMask

/-!
# Height five at `k = 5`: soundness of the state-bit certificates

The bit masks of `GridGen/Five/K5/BitLP.lean` describe the pin events exactly (`bm_testBit`,
`em_testBit`): a pin fires at a state with code index `ci` and canonical pattern `i` iff bit `ci`
of its code mask and bit `i` of its pattern mask are set. With the state bound `state55` the
kernel checks give `GB ≥ GU · (1 + (K - fired)/D)` at every state, and the pins average out
(`sum_fired5`): `seam_of_bit55`. A pointwise class has `V ≥ 0` at every state
(`seam_of_pt55`).
-/

namespace GridGen.Five.K5

open Finset GridGen.Five GridGen.Five.Ex5

/-! ### Masks -/

theorem foldr_land_testBit {α : Type*} (f : α → ℕ) (base : ℕ) (i : ℕ) :
    ∀ L : List α, (L.foldr (fun x acc => f x &&& acc) base).testBit i
      = (L.all (fun x => (f x).testBit i) && base.testBit i)
  | [] => by simp
  | x :: L => by
    simp only [List.foldr_cons, Nat.testBit_and, foldr_land_testBit f base i L, List.all_cons,
      Bool.and_assoc]

theorem cdig_cidx {c1 c2 c3 c4 c5 : ℕ} (h1 : c1 < 5) (h2 : c2 < 5) (h3 : c3 < 5) (h4 : c4 < 5)
    (h5 : c5 < 5) {r : ℕ} (hr : r < 5) :
    cdig r (cidx (c1, c2, c3, c4, c5)) = crow (c1, c2, c3, c4, c5) r := by
  interval_cases r <;> simp only [cdig, cidx, crow] <;> norm_num <;> omega

theorem all_congr_mem {α : Type*} {f g : α → Bool} :
    ∀ {L : List α}, (∀ x ∈ L, f x = g x) → L.all f = L.all g
  | [], _ => rfl
  | x :: L, h => by
    simp only [List.all_cons]
    rw [h x List.mem_cons_self, all_congr_mem (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- The row masks are correct. -/
def RMok (rm : List ℕ) : Prop := ∀ r < 5, ∀ k < 3, rmOK rm r k = true

theorem RM_ok : RMok RM := by
  intro r hr k hk
  interval_cases r <;> interval_cases k
  exacts [rm_ok_0_0, rm_ok_0_1, rm_ok_0_2, rm_ok_1_0, rm_ok_1_1, rm_ok_1_2, rm_ok_2_0, rm_ok_2_1,
    rm_ok_2_2, rm_ok_3_0, rm_ok_3_1, rm_ok_3_2, rm_ok_4_0, rm_ok_4_1, rm_ok_4_2]

/-- The row conditions of a well-formed pin are in range. -/
def condsOK (L : List (ℕ × ℕ)) : Prop := ∀ rk ∈ L, rk.1 < 5 ∧ rk.2 < 3

theorem peelConds_ok : ∀ ps : List BPeel5, (ps.all BPeel5.okb) = true → condsOK (peelConds ps)
  | [], _ => fun _ h => absurd h List.not_mem_nil
  | BPeel5.ev r k :: ps, h => by
    simp only [List.all_cons, Bool.and_eq_true, BPeel5.okb, decide_eq_true_eq] at h
    intro rk hrk
    rcases List.mem_cons.mp hrk with rfl | hrk
    · exact h.1
    · exact peelConds_ok ps h.2 rk hrk
  | BPeel5.eq r j :: ps, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact peelConds_ok ps h.2

theorem peelEqs_ok : ∀ ps : List BPeel5, (ps.all BPeel5.okb) = true →
    ∀ rj ∈ peelEqs ps, rj.1 < 5 ∧ rj.2 < 5
  | [], _ => fun _ h => absurd h List.not_mem_nil
  | BPeel5.ev r k :: ps, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact peelEqs_ok ps h.2
  | BPeel5.eq r j :: ps, h => by
    simp only [List.all_cons, Bool.and_eq_true, BPeel5.okb, decide_eq_true_eq] at h
    intro rj hrj
    rcases List.mem_cons.mp hrj with rfl | hrj
    · exact ⟨h.1.1, h.1.2.1⟩
    · exact peelEqs_ok ps h.2 rj hrj

theorem blk_conds_ok : ∀ b : BBlk5, b.okb = true → condsOK b.conds
  | BBlk5.none, _ => fun _ h => absurd h List.not_mem_nil
  | BBlk5.one r k, h => by
    simp only [BBlk5.okb, decide_eq_true_eq] at h
    intro rk hrk; simp only [BBlk5.conds, List.mem_singleton] at hrk; subst hrk; exact h
  | BBlk5.two r k k', h => by
    simp only [BBlk5.okb, decide_eq_true_eq] at h
    intro rk hrk; simp only [BBlk5.conds, List.mem_cons, List.not_mem_nil, or_false] at hrk
    rcases hrk with rfl | rfl
    · exact ⟨by omega, h.2.1⟩
    · exact ⟨by omega, h.2.2⟩
  | BBlk5.three r k k' k'', h => by
    simp only [BBlk5.okb, decide_eq_true_eq] at h
    intro rk hrk; simp only [BBlk5.conds, List.mem_cons, List.not_mem_nil, or_false] at hrk
    rcases hrk with rfl | rfl | rfl
    · exact ⟨by omega, h.2.1⟩
    · exact ⟨by omega, h.2.2.1⟩
    · exact ⟨by omega, h.2.2.2⟩

theorem bpeelOK_all {b : BBlk5} : ∀ {ps : List BPeel5}, bpeelOK b ps = true →
    ps.all BPeel5.okb = true
  | [], _ => rfl
  | p :: ps, h => by
    simp only [bpeelOK, Bool.and_eq_true] at h
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨h.1.2, bpeelOK_all h.2⟩

/-- **The code mask of a pin.** -/
theorem bm_testBit {rm : List ℕ} (hrm : RMok rm) {q : BPin5} (hq : q.okb rm = true)
    {c1 c2 c3 c4 c5 : ℕ} (h1 : c1 < 5) (h2 : c2 < 5) (h3 : c3 < 5) (h4 : c4 < 5) (h5 : c5 < 5) :
    q.bm.testBit (cidx (c1, c2, c3, c4, c5))
      = (q.blk.conds ++ peelConds q.peels).all
          (fun rk => evk rk.2 (crow (c1, c2, c3, c4, c5) rk.1)) := by
  simp only [BPin5.okb, Bool.and_eq_true, beq_iff_eq] at hq
  obtain ⟨⟨⟨hb, hp⟩, hbm⟩, -⟩ := hq
  have hok : condsOK (q.blk.conds ++ peelConds q.peels) := by
    intro rk hrk
    rcases List.mem_append.mp hrk with h | h
    · exact blk_conds_ok q.blk hb rk h
    · exact peelConds_ok q.peels (bpeelOK_all hp) rk h
  have hci : cidx (c1, c2, c3, c4, c5) < 3125 := by simp only [cidx]; omega
  rw [hbm, bmaskOf, foldr_land_testBit, FULLc, Nat.testBit_two_pow_sub_one,
    decide_eq_true hci, Bool.and_true]
  refine all_congr_mem fun rk hrk => ?_
  obtain ⟨hr, hk⟩ := hok rk hrk
  rw [rmOK_spec (hrm rk.1 hr rk.2 hk) hci, cdig_cidx h1 h2 h3 h4 h5 hr]

/-- **The pattern mask of a pin.** -/
theorem em_testBit {rm : List ℕ} {q : BPin5} (hq : q.okb rm = true) {i : ℕ} (hi : i < 15) :
    q.em.testBit i = (peelEqs q.peels).all (fun rj =>
      rowAt rj.1 (canons.getD i (0, 0, 0, 0, 0)) == rowAt rj.2 (canons.getD i (0, 0, 0, 0, 0))) := by
  simp only [BPin5.okb, Bool.and_eq_true, beq_iff_eq] at hq
  obtain ⟨⟨⟨-, hp⟩, -⟩, hem⟩ := hq
  rw [hem, emaskOf, foldr_land_testBit, FULLp, Nat.testBit_two_pow_sub_one,
    decide_eq_true hi, Bool.and_true]
  refine all_congr_mem fun rj hrj => ?_
  obtain ⟨hr, hj⟩ := peelEqs_ok q.peels (bpeelOK_all hp) rj hrj
  exact pmask_ok rj.1 hr rj.2 hj i hi

theorem peels_evc (c : ℕ × ℕ × ℕ × ℕ × ℕ) (p : T5) : ∀ ps : List BPeel5,
    ps.all (fun f => f.evc c p)
      = ((peelConds ps).all (fun rk => evk rk.2 (crow c rk.1))
        && (peelEqs ps).all (fun rj => rowAt rj.1 p == rowAt rj.2 p))
  | [] => rfl
  | BPeel5.ev r k :: ps => by
    rw [List.all_cons, peels_evc c p ps]
    simp only [peelConds, peelEqs, List.all_cons, BPeel5.evc, Bool.and_assoc]
  | BPeel5.eq r j :: ps => by
    rw [List.all_cons, peels_evc c p ps]
    simp only [peelConds, peelEqs, List.all_cons, BPeel5.evc]
    cases (rowAt r p == rowAt j p) <;> cases (peelConds ps).all (fun rk => evk rk.2 (crow c rk.1))
      <;> simp

theorem blk_evc (c : ℕ × ℕ × ℕ × ℕ × ℕ) :
    ∀ b : BBlk5, b.evc c = b.conds.all (fun rk => evk rk.2 (crow c rk.1))
  | BBlk5.none => rfl
  | BBlk5.one r k => by simp [BBlk5.evc, BBlk5.conds]
  | BBlk5.two r k k' => by simp [BBlk5.evc, BBlk5.conds]
  | BBlk5.three r k k' k'' => by simp [BBlk5.evc, BBlk5.conds, Bool.and_assoc]

/-- **A pin fires at a code vector and pattern iff both masks have the bits.** -/
theorem evc_masks {rm : List ℕ} (hrm : RMok rm) {q : BPin5} (hq : q.okb rm = true)
    {c1 c2 c3 c4 c5 : ℕ} (h1 : c1 < 5) (h2 : c2 < 5) (h3 : c3 < 5) (h4 : c4 < 5) (h5 : c5 < 5)
    {i : ℕ} (hi : i < 15) :
    q.evc (c1, c2, c3, c4, c5) (canons.getD i (0, 0, 0, 0, 0))
      = (q.bm.testBit (cidx (c1, c2, c3, c4, c5)) && q.em.testBit i) := by
  rw [bm_testBit hrm hq h1 h2 h3 h4 h5, em_testBit hq hi, BPin5.evc, peels_evc, blk_evc,
    List.all_append]
  cases (BBlk5.conds q.blk).all (fun rk => evk rk.2 (crow (c1, c2, c3, c4, c5) rk.1)) <;>
    cases (peelConds q.peels).all (fun rk => evk rk.2 (crow (c1, c2, c3, c4, c5) rk.1)) <;> simp

/-- The filtered multiplier sum is the fired sum. -/
theorem firedL_eq {rm : List ℕ} (hrm : RMok rm) {c1 c2 c3 c4 c5 : ℕ} (h1 : c1 < 5) (h2 : c2 < 5)
    (h3 : c3 < 5) (h4 : c4 < 5) (h5 : c5 < 5) {i : ℕ} (hi : i < 15) :
    ∀ P : List BPin5, P.all (BPin5.okb rm) = true →
      firedL (P.filter fun q => q.bm.testBit (cidx (c1, c2, c3, c4, c5))) i
        = fired P (c1, c2, c3, c4, c5) (canons.getD i (0, 0, 0, 0, 0))
  | [], _ => rfl
  | q :: P, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := firedL_eq hrm h1 h2 h3 h4 h5 hi P h.2
    have he := evc_masks hrm h.1 h1 h2 h3 h4 h5 hi
    unfold firedL at ih ⊢
    unfold fired at ih ⊢
    simp only [List.filter_cons]
    by_cases hb : q.bm.testBit (cidx (c1, c2, c3, c4, c5)) = true
    · simp only [hb, ite_true, List.map_cons, List.sum_cons, ih]
      rw [he, hb, Bool.true_and]
    · simp only [hb, Bool.false_eq_true, ite_false, List.map_cons, List.sum_cons, ih]
      rw [he]
      simp only [Bool.not_eq_true] at hb
      simp [hb]

/-! ### Pins on actual states -/

section sound

variable {w : Wt5} {X₁ X₂ X₃ X₄ X₅ B₁ B₂ B₃ B₄ B₅ : Finset ℕ} {m : List ℕ}

/-- The pin of actual lists. -/
def BPin5.toPin (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (m : List ℕ) (q : BPin5) : Pin5 :=
  ⟨q.blk.blk B₁ B₂ B₃ B₄ B₅ m, q.peels.map (BPeel5.fac B₁ B₂ B₃ B₄ B₅ m)⟩

theorem peel_reads5 (p : BPeel5) :
    (p.fac B₁ B₂ B₃ B₄ B₅ m).reads = p.reads ∧ (p.fac B₁ B₂ B₃ B₄ B₅ m).row = p.row := by
  cases p <;> exact ⟨rfl, rfl⟩

theorem blk_reads5 (b : BBlk5) : (b.blk B₁ B₂ B₃ B₄ B₅ m).reads = b.reads := by
  cases b <;> rfl

theorem peelOK_of5 (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5) (hB₃ : B₃.card = 5)
    (hB₄ : B₄.card = 5) (hB₅ : B₅.card = 5) (hm : MOK B₁ B₂ B₃ B₄ B₅ m) (b : BBlk5) :
    ∀ ps : List BPeel5, bpeelOK b ps = true →
      PeelOK5 (b.blk B₁ B₂ B₃ B₄ B₅ m).reads (ps.map (BPeel5.fac B₁ B₂ B₃ B₄ B₅ m))
  | [], _ => trivial
  | p :: ps, h => by
    simp only [bpeelOK, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.all_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨?_, ?_, ?_, peelOK_of5 hB₁ hB₂ hB₃ hB₄ hB₅ hm b ps h4⟩
    · rw [blk_reads5, (peel_reads5 p).2]; exact h1
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      rw [(peel_reads5 g').1, (peel_reads5 p).2]
      have := h2 g' hg'
      simpa using this
    · cases p with
      | ev r k =>
        simp only [BPeel5.okb, decide_eq_true_eq] at h3
        exact ⟨h3.1, dset_card hB₁ hB₂ hB₃ hB₄ hB₅ hm h3.1 k⟩
      | eq r j =>
        simp only [BPeel5.okb, decide_eq_true_eq] at h3
        exact h3

theorem blk_ok5 (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5) (hB₃ : B₃.card = 5)
    (hB₄ : B₄.card = 5) (hB₅ : B₅.card = 5) (hm : MOK B₁ B₂ B₃ B₄ B₅ m) (b : BBlk5)
    (hb : b.okb = true) : (b.blk B₁ B₂ B₃ B₄ B₅ m).ok := by
  cases b with
  | none => trivial
  | one r k =>
    simp only [BBlk5.okb, decide_eq_true_eq] at hb
    exact ⟨hb.1, dset_card hB₁ hB₂ hB₃ hB₄ hB₅ hm hb.1 k⟩
  | two r k k' =>
    simp only [BBlk5.okb, decide_eq_true_eq] at hb
    exact ⟨hb.1, dset_card hB₁ hB₂ hB₃ hB₄ hB₅ hm (by omega) k,
      dset_card hB₁ hB₂ hB₃ hB₄ hB₅ hm (by omega) k'⟩
  | three r k k' k'' =>
    simp only [BBlk5.okb, decide_eq_true_eq] at hb
    exact ⟨hb.1, dset_card hB₁ hB₂ hB₃ hB₄ hB₅ hm (by omega) k,
      dset_card hB₁ hB₂ hB₃ hB₄ hB₅ hm (by omega) k',
      dset_card hB₁ hB₂ hB₃ hB₄ hB₅ hm (by omega) k''⟩

theorem toPin_OK (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5) (hB₃ : B₃.card = 5)
    (hB₄ : B₄.card = 5) (hB₅ : B₅.card = 5) (hm : MOK B₁ B₂ B₃ B₄ B₅ m) {rm : List ℕ}
    {q : BPin5} (hq : q.okb rm = true) : (q.toPin B₁ B₂ B₃ B₄ B₅ m).OK := by
  simp only [BPin5.okb, Bool.and_eq_true] at hq
  obtain ⟨⟨⟨hb, hp⟩, -⟩, -⟩ := hq
  exact ⟨blk_ok5 hB₁ hB₂ hB₃ hB₄ hB₅ hm q.blk hb,
    peelOK_of5 hB₁ hB₂ hB₃ hB₄ hB₅ hm q.blk q.peels hp⟩

theorem toPin_bnd (q : BPin5) : (q.toPin B₁ B₂ B₃ B₄ B₅ m).bnd = q.bnd m := by
  unfold Pin5.bnd BPin5.bnd BPin5.toPin
  congr 1
  · rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    cases p <;> rfl
  · cases q.blk <;> rfl

theorem kcodes_rows (s : T5) {r : ℕ} (hr : r < 5) :
    crow (kcodes B₁ B₂ B₃ B₄ B₅ s) r < 5 := by
  rw [crow_codes _ _ _ _ _ _ hr]
  have := rcode_le (Bpv B₁ B₂ B₃ B₄ B₅ r) (bl B₁ B₂ B₃ B₄ B₅ r) (Bnx B₁ B₂ B₃ B₄ B₅ r) (rowAt r s)
  omega

/-- The event of a pin on a state is its event on the codes and the canonical pattern. -/
theorem pin_evc5 (q : BPin5) {s : T5} (hs : Proper s) (hq : q.peels.all BPeel5.okb = true)
    (hb : q.blk.okb = true) :
    (q.toPin B₁ B₂ B₃ B₄ B₅ m).ev s = q.evc (kcodes B₁ B₂ B₃ B₄ B₅ s) (canon s) := by
  unfold Pin5.ev BPin5.evc BPin5.toPin allEv5
  simp only
  congr 1
  · rw [List.all_map]
    refine all_congr_mem fun p hp => ?_
    have hpk : p.okb = true := List.all_eq_true.mp hq p hp
    cases p with
    | ev r k =>
      simp only [BPeel5.okb, decide_eq_true_eq] at hpk
      simp only [Function.comp, BPeel5.fac, Fac5.ev, BPeel5.evc, evk_codes _ _ _ _ _ _ hpk.1]
    | eq r j =>
      simp only [BPeel5.okb, decide_eq_true_eq] at hpk
      simp only [Function.comp, BPeel5.fac, Fac5.ev, BPeel5.evc]
      rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq]
      exact (eqv_canon hs hpk.1 hpk.2.1)
  · cases hbb : q.blk with
    | none => rfl
    | one r k =>
      rw [hbb] at hb; simp only [BBlk5.okb, decide_eq_true_eq] at hb
      simp only [BBlk5.blk, Blk5.ev, BBlk5.evc, evk_codes _ _ _ _ _ _ hb.1]
    | two r k k' =>
      rw [hbb] at hb; simp only [BBlk5.okb, decide_eq_true_eq] at hb
      simp only [BBlk5.blk, Blk5.ev, BBlk5.evc, evk_codes _ _ _ _ _ _ (show r < 5 by omega),
        evk_codes _ _ _ _ _ _ (show r + 1 < 5 by omega)]
    | three r k k' k'' =>
      rw [hbb] at hb; simp only [BBlk5.okb, decide_eq_true_eq] at hb
      simp only [BBlk5.blk, Blk5.ev, BBlk5.evc, evk_codes _ _ _ _ _ _ (show r < 5 by omega),
        evk_codes _ _ _ _ _ _ (show r + 1 < 5 by omega),
        evk_codes _ _ _ _ _ _ (show r + 2 < 5 by omega)]

/-- **The pins average out.** -/
theorem sum_fired5 (hw : InCone5 w) (h₁ : 4 ≤ X₁.card) (h₂ : 4 ≤ X₂.card) (h₃ : 4 ≤ X₃.card)
    (h₄ : 4 ≤ X₄.card) (h₅ : 4 ≤ X₅.card) (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5)
    (hB₃ : B₃.card = 5) (hB₄ : B₄.card = 5) (hB₅ : B₅.card = 5) (hm : MOK B₁ B₂ B₃ B₄ B₅ m)
    {rm : List ℕ} :
    ∀ P : List BPin5, P.all (BPin5.okb rm) = true →
      ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 5 w s * (fired P (kcodes B₁ B₂ B₃ B₄ B₅ s) (canon s) : ℝ)
        ≤ ((lamBnd P m : ℚ) : ℝ) * ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 5 w s
  | [], _ => by simp [fired, lamBnd]
  | q :: P, hP => by
    simp only [List.all_cons, Bool.and_eq_true] at hP
    have ih := sum_fired5 hw h₁ h₂ h₃ h₄ h₅ hB₁ hB₂ hB₃ hB₄ hB₅ hm P hP.2
    have hq := pin_sum5 hw h₁ h₂ h₃ h₄ h₅ (q.toPin B₁ B₂ B₃ B₄ B₅ m)
      (toPin_OK hB₁ hB₂ hB₃ hB₄ hB₅ hm hP.1)
    rw [toPin_bnd] at hq
    have hok := hP.1
    simp only [BPin5.okb, Bool.and_eq_true] at hok
    obtain ⟨⟨⟨hb, hp⟩, -⟩, -⟩ := hok
    have e1 : ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 5 w s * (fired (q :: P) (kcodes B₁ B₂ B₃ B₄ B₅ s)
          (canon s) : ℝ)
        = (q.lam : ℝ) * ∑ s ∈ (sts X₁ X₂ X₃ X₄ X₅).filter
            (fun t => (q.toPin B₁ B₂ B₃ B₄ B₅ m).ev t = true), GU 5 w s
          + ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 5 w s * (fired P (kcodes B₁ B₂ B₃ B₄ B₅ s)
            (canon s) : ℝ) := by
      rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun s hs => ?_)
      rw [pin_evc5 q (proper_of_mem_sts hs) (bpeelOK_all hp) hb]
      simp only [fired, List.map_cons, List.sum_cons]
      split_ifs <;> push_cast <;> ring
    rw [e1]
    have hl : (0 : ℝ) ≤ q.lam := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hq hl
    simp only [lamBnd, List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast]
    simp only [lamBnd] at ih
    linarith

end sound

/-! ### The seam from a certificate -/

section seam

variable {w : Wt5} {X₁ X₂ X₃ X₄ X₅ B₁ B₂ B₃ B₄ B₅ : Finset ℕ} {m2 m3 m4 m5 : ℕ}

theorem NUo_pos : ∀ o : Fin 11, 0 < NUo o := by decide

theorem canons_getD_def {i : ℕ} (hi : i < 15) (d₁ d₂ : T5) : canons.getD i d₁ = canons.getD i d₂ := by
  have h : i < canons.length := by simpa [canons] using hi
  rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ h]

theorem canon_index0 {s : T5} (hs : Proper s) :
    ∃ i < 15, canons.getD i (0, 0, 0, 0, 0) = canon s := by
  obtain ⟨i, hi, e⟩ := canon_index hs
  exact ⟨i, hi, by rw [canons_getD_def hi]; exact e⟩

theorem sdiff_pos5 {B C : Finset ℕ} (hB : B.card = 5) {m : ℕ} (hm : (C ∩ B).card + m = 5) {x : ℕ}
    (hx : x ∈ B \ C) : 0 < m := by
  have h1 := Finset.card_sdiff_add_card_inter B C
  rw [Finset.inter_comm] at h1
  have h2 : 0 < (B \ C).card := Finset.card_pos.mpr ⟨x, hx⟩
  omega

/-- The codes of an actual state are admissible. -/
theorem bvalid_kcodes (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5) (hB₃ : B₃.card = 5)
    (hB₄ : B₄.card = 5) (hB₅ : B₅.card = 5) (c2 : (B₁ ∩ B₂).card + m2 = 5)
    (c3 : (B₂ ∩ B₃).card + m3 = 5) (c4 : (B₃ ∩ B₄).card + m4 = 5) (c5 : (B₄ ∩ B₅).card + m5 = 5)
    {s : T5} (hs : Proper s) :
    bvalid5 m2 m3 m4 m5 (rcode B₁ B₁ B₂ (r1 s)) (rcode B₁ B₂ B₃ (r2 s)) (rcode B₂ B₃ B₄ (r3 s))
      (rcode B₃ B₄ B₅ (r4 s)) (rcode B₄ B₅ B₅ (r5 s)) = true := by
  obtain ⟨p12, p23, p34, p45⟩ := hs
  have i2 := card_inter_rcode hB₁ hB₂ c2 B₁ B₃ p12
  have i3 := card_inter_rcode hB₂ hB₃ c3 B₁ B₄ p23
  have i4 := card_inter_rcode hB₃ hB₄ c4 B₂ B₅ p34
  have i5 := card_inter_rcode hB₄ hB₅ c5 B₃ B₅ p45
  have pm : ∀ {Bp Bi Bn : Finset ℕ} {x m : ℕ}, Bi.card = 5 → (Bp ∩ Bi).card + m = 5 →
      (kM (rcode Bp Bi Bn x) == 0 || 0 < m) = true := by
    intro Bp Bi Bn x m hBi hm
    rw [kM_code]
    split_ifs with h
    · simp only [beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq]
      right; exact sdiff_pos5 hBi hm h
    · simp
  have px : ∀ {Bp Bi Bn : Finset ℕ} {x m : ℕ}, Bi.card = 5 → (Bi ∩ Bn).card + m = 5 →
      (kX (rcode Bp Bi Bn x) == 0 || 0 < m) = true := by
    intro Bp Bi Bn x m hBi hm
    rw [kX_code]
    split_ifs with h
    · simp only [beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq]
      right; rw [Finset.inter_comm] at hm; exact sdiff_pos5 hBi hm h
    · simp
  have z1 : kM (rcode B₁ B₁ B₂ (r1 s)) = 0 := by rw [kM_code]; simp
  have z5 : kX (rcode B₄ B₅ B₅ (r5 s)) = 0 := by rw [kX_code]; simp
  simp only [bvalid5, Bool.and_eq_true, z1, z5, beq_self_eq_true, true_and, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨pm hB₂ c2, pm hB₃ c3⟩, pm hB₄ c4⟩, pm hB₅ c5⟩, px hB₁ c2⟩, px hB₂ c3⟩,
    px hB₃ c4⟩, px hB₄ c5⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩

/-- **The bound for one state from a certificate.** -/
theorem state_bit55 (hw : InCone5 w) (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5)
    (hB₃ : B₃.card = 5) (hB₄ : B₄.card = 5) (hB₅ : B₅.card = 5) (c2 : (B₁ ∩ B₂).card + m2 = 5)
    (c3 : (B₂ ∩ B₃).card + m3 = 5) (c4 : (B₃ ∩ B₄).card + m4 = 5) (c5 : (B₄ ∩ B₅).card + m5 = 5)
    {rm : List ℕ} (hrm : RMok rm) {C : BitCert5} (hP : C.pins.all (BPin5.okb rm) = true)
    (hall : all5k (fun c1 => all5k (fun c2 => all5k (fun c3 => all5k (fun c4 => all5k (fun c5 =>
      bitAt5 m2 m3 m4 m5 C c1 c2 c3 c4 c5))))) = true)
    {s : T5} (hs : Proper s) :
    GU 5 w s * ((C.D : ℝ) + C.K - fired C.pins (kcodes B₁ B₂ B₃ B₄ B₅ s) (canon s))
      ≤ C.D * GB w B₁ B₂ B₃ B₄ B₅ s := by
  have hst5 := state55 hw hB₁ hB₂ hB₃ hB₄ hB₅ hs (w := w)
  rw [card_erase_rcode hB₁ B₁ B₂, card_erase_rcode hB₂ B₁ B₃, card_erase_rcode hB₃ B₂ B₄,
    card_erase_rcode hB₄ B₃ B₅, card_erase_rcode hB₅ B₄ B₅] at hst5
  have e2 := card_inter_rcode hB₁ hB₂ c2 B₁ B₃ hs.1
  have e3 := card_inter_rcode hB₂ hB₃ c3 B₁ B₄ hs.2.1
  have e4 := card_inter_rcode hB₃ hB₄ c4 B₂ B₅ hs.2.2.1
  have e5 := card_inter_rcode hB₄ hB₅ c5 B₃ B₅ hs.2.2.2
  have hv := bvalid_kcodes hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5 hs
  obtain ⟨i, hi, hci⟩ := canon_index0 hs
  have hk : kcodes B₁ B₂ B₃ B₄ B₅ s = (rcode B₁ B₁ B₂ (r1 s), rcode B₁ B₂ B₃ (r2 s),
    rcode B₂ B₃ B₄ (r3 s), rcode B₃ B₄ B₅ (r4 s), rcode B₄ B₅ B₅ (r5 s)) := rfl
  rw [hk]
  set a1 := rcode B₁ B₁ B₂ (r1 s)
  set a2 := rcode B₁ B₂ B₃ (r2 s)
  set a3 := rcode B₂ B₃ B₄ (r3 s)
  set a4 := rcode B₃ B₄ B₅ (r4 s)
  set a5 := rcode B₄ B₅ B₅ (r5 s)
  have l1 : a1 < 5 := by have := rcode_le B₁ B₁ B₂ (r1 s); omega
  have l2 : a2 < 5 := by have := rcode_le B₁ B₂ B₃ (r2 s); omega
  have l3 : a3 < 5 := by have := rcode_le B₂ B₃ B₄ (r3 s); omega
  have l4 : a4 < 5 := by have := rcode_le B₃ B₄ B₅ (r4 s); omega
  have l5 : a5 < 5 := by have := rcode_le B₄ B₅ B₅ (r5 s); omega
  have hat : bitAt5 m2 m3 m4 m5 C a1 a2 a3 a4 a5 = true :=
    all5k_spec (all5k_spec (all5k_spec (all5k_spec (all5k_spec hall (by omega)) (by omega))
      (by omega)) (by omega)) (by omega)
  simp only [bitAt5, hv, Bool.not_true, Bool.false_or] at hat
  have hst := List.all_eq_true.mp hat i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hst
  obtain ⟨hR0, hineq⟩ := hst
  rw [firedL_eq hrm l1 l2 l3 l4 l5 hi C.pins hP, ORBL_eq i hi, hci] at hineq
  rw [ORBL_eq i hi, hci] at hR0
  rw [← orb_congr (samePat_canon hs)] at hineq hR0
  have f2 : ((B₁.erase (r1 s)) ∩ (B₂.erase (r2 s))).card = nE5 m2 a1 a2 := by unfold nE5; omega
  have f3 : ((B₂.erase (r2 s)) ∩ (B₃.erase (r3 s))).card = nE5 m3 a2 a3 := by unfold nE5; omega
  have f4 : ((B₃.erase (r3 s)) ∩ (B₄.erase (r4 s))).card = nE5 m4 a3 a4 := by unfold nE5; omega
  have f5 : ((B₄.erase (r4 s)) ∩ (B₅.erase (r5 s))).card = nE5 m5 a4 a5 := by unfold nE5; omega
  rw [f2, f3, f4, f5, ← kapP_kapM] at hst5
  -- generalize
  have hNU : NUL.getD (orb s) 0 = NUo (orb s) := NUL_eq (orb s)
  rw [hNU] at hineq
  generalize kapP (4 + kH a1) (4 + kH a2) (4 + kH a3) (4 + kH a4) (4 + kH a5)
    (nE5 m2 a1 a2) (nE5 m3 a2 a3) (nE5 m4 a3 a4) (nE5 m5 a4 a5) = P at hineq hst5
  generalize kapM (4 + kH a1) (4 + kH a2) (4 + kH a3) (4 + kH a4) (4 + kH a5)
    (nE5 m2 a1 a2) (nE5 m3 a2 a3) (nE5 m4 a3 a4) (nE5 m5 a4 a5) = M at hineq hst5
  have hRof : Rof (4 + kH a1) (4 + kH a2) (4 + kH a3) (4 + kH a4) (4 + kH a5) (orb s)
      = (patCerts.getD (nidx (4 + kH a1) (4 + kH a2) (4 + kH a3) (4 + kH a4) (4 + kH a5))
          default).R.getD (orb s) 0 := rfl
  rw [hRof] at hst5
  generalize (patCerts.getD (nidx (4 + kH a1) (4 + kH a2) (4 + kH a3) (4 + kH a4) (4 + kH a5))
    default).R.getD (orb s) 0 = R at hineq hst5 hR0
  generalize fired C.pins (a1, a2, a3, a4, a5) (canon s) = F at hineq ⊢
  generalize hNU0' : NUo (orb s) = NU at hineq hst5
  generalize hE : (1000000000 : ℕ) = E at hineq
  have hE' : (1000000000 : ℝ) = (E : ℝ) := by rw [← hE]; norm_num
  rw [hE'] at hst5
  have hNU0 : 0 < NU := by rw [← hNU0']; exact NUo_pos (orb s)
  have hU : 0 ≤ GU 5 w s := GU_nonneg55 hw s
  have hX : (0 : ℝ) < (NU : ℝ) * R := by
    have : (0 : ℝ) < NU := by exact_mod_cast hNU0
    have : (0 : ℝ) < R := by exact_mod_cast hR0
    positivity
  have hineqR : ((C.D : ℝ) + C.K) * NU * R + C.D * E * M ≤ C.D * E * P + F * NU * R := by
    exact_mod_cast hineq
  push_cast at hst5
  have k1 : ((C.D : ℝ) + C.K - F) * (NU * R) ≤ C.D * E * ((P : ℝ) - M) := by linarith
  have k2 := mul_le_mul_of_nonneg_right k1 hU
  have k3 := mul_le_mul_of_nonneg_left hst5 (Nat.cast_nonneg C.D : (0 : ℝ) ≤ C.D)
  have key : GU 5 w s * ((C.D : ℝ) + C.K - F) * (NU * R) ≤ C.D * GB w B₁ B₂ B₃ B₄ B₅ s * (NU * R) := by
    linarith
  exact le_of_mul_le_mul_right key hX

/-- **The seam inequality from a dual certificate over the state bits.** -/
theorem seam_of_bit55 (hw : InCone5 w) (h₁ : 4 ≤ X₁.card) (h₂ : 4 ≤ X₂.card) (h₃ : 4 ≤ X₃.card)
    (h₄ : 4 ≤ X₄.card) (h₅ : 4 ≤ X₅.card) (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5)
    (hB₃ : B₃.card = 5) (hB₄ : B₄.card = 5) (hB₅ : B₅.card = 5) (c2 : (B₁ ∩ B₂).card + m2 = 5)
    (c3 : (B₂ ∩ B₃).card + m3 = 5) (c4 : (B₃ ∩ B₄).card + m4 = 5) (c5 : (B₄ ∩ B₅).card + m5 = 5)
    (C : BitCert5) (hC : bitOK5 RM m2 m3 m4 m5 C = true) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 5 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GB w B₁ B₂ B₃ B₄ B₅ s := by
  simp only [bitOK5, pinsOK5, Bool.and_eq_true, decide_eq_true_eq] at hC
  obtain ⟨⟨⟨hD, hP⟩, hL⟩, hall⟩ := hC
  have hm : MOK B₁ B₂ B₃ B₄ B₅ [m2, m3, m4, m5] := ⟨c2, c3, c4, c5⟩
  set Ω := sts X₁ X₂ X₃ X₄ X₅ with hΩ
  have hDR : (0 : ℝ) < C.D := by exact_mod_cast hD
  have hstate : ∀ s ∈ Ω, GU 5 w s * ((C.D : ℝ) + C.K
      - fired C.pins (kcodes B₁ B₂ B₃ B₄ B₅ s) (canon s)) ≤ C.D * GB w B₁ B₂ B₃ B₄ B₅ s :=
    fun s hs => state_bit55 hw hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5 RM_ok hP hall (proper_of_mem_sts hs)
  have hsum := Finset.sum_le_sum hstate
  have hf := sum_fired5 hw h₁ h₂ h₃ h₄ h₅ hB₁ hB₂ hB₃ hB₄ hB₅ hm C.pins hP
  set W := ∑ s ∈ Ω, GU 5 w s with hW
  have hLR : ((lamBnd C.pins [m2, m3, m4, m5] : ℚ) : ℝ) ≤ C.K := by exact_mod_cast hL
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun s _ => GU_nonneg55 hw s
  have e : ∑ s ∈ Ω, GU 5 w s * ((C.D : ℝ) + C.K
      - fired C.pins (kcodes B₁ B₂ B₃ B₄ B₅ s) (canon s))
      = ((C.D : ℝ) + C.K) * W
        - ∑ s ∈ Ω, GU 5 w s * (fired C.pins (kcodes B₁ B₂ B₃ B₄ B₅ s) (canon s) : ℝ) := by
    rw [hW, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [e, ← Finset.mul_sum] at hsum
  have h1 : ((lamBnd C.pins [m2, m3, m4, m5] : ℚ) : ℝ) * W ≤ C.K * W :=
    mul_le_mul_of_nonneg_right hLR hW0
  have h2 : (C.D : ℝ) * W ≤ C.D * ∑ s ∈ Ω, GB w B₁ B₂ B₃ B₄ B₅ s := by linarith
  exact le_of_mul_le_mul_left h2 hDR

/-- The ratio bounds are positive. -/
theorem Rof_pos : ∀ a ∈ [4, 5], ∀ b ∈ [4, 5], ∀ c ∈ [4, 5], ∀ d ∈ [4, 5], ∀ e ∈ [4, 5],
    ∀ o : Fin 11, 0 < Rof a b c d e o := by decide +kernel

theorem NUR_le_NM (nv : ℕ) (hnv : nv < 32) (o : Fin 11) :
    NUL.getD o 0 * (patCerts.getD nv default).R.getD o 0 ≤ NM.getD nv 0 := by
  rw [NM_ok nv hnv, NURmax]
  have hmem : NUL.getD o 0 * (patCerts.getD nv default).R.getD o 0
      ∈ (List.range 11).map fun o => NUL.getD o 0 * (patCerts.getD nv default).R.getD o 0 :=
    List.mem_map.mpr ⟨o, List.mem_range.mpr o.isLt, rfl⟩
  generalize (List.range 11).map (fun o => NUL.getD o 0 * (patCerts.getD nv default).R.getD o 0) = L
    at hmem
  induction L with
  | nil => exact absurd hmem List.not_mem_nil
  | cons x L ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hmem with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem nidx_lt {a b c d e : ℕ} (ha : a = 4 ∨ a = 5) (hb : b = 4 ∨ b = 5) (hc : c = 4 ∨ c = 5)
    (hd : d = 4 ∨ d = 5) (he : e = 4 ∨ e = 5) : nidx a b c d e < 32 := by
  unfold nidx; omega

theorem kH45 (c : ℕ) : 4 + kH c = 4 ∨ 4 + kH c = 5 := by unfold kH; split_ifs <;> simp

/-- **The seam inequality for a pointwise class.** -/
theorem seam_of_pt55 (hw : InCone5 w) (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5)
    (hB₃ : B₃.card = 5) (hB₄ : B₄.card = 5) (hB₅ : B₅.card = 5) (c2 : (B₁ ∩ B₂).card + m2 = 5)
    (c3 : (B₂ ∩ B₃).card + m3 = 5) (c4 : (B₃ ∩ B₄).card + m4 = 5) (c5 : (B₄ ∩ B₅).card + m5 = 5)
    (hC : ptOK5 NM m2 m3 m4 m5 = true) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 5 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GB w B₁ B₂ B₃ B₄ B₅ s := by
  refine Finset.sum_le_sum fun s hs' => ?_
  have hs := proper_of_mem_sts hs'
  have hst5 := state55 hw hB₁ hB₂ hB₃ hB₄ hB₅ hs (w := w)
  rw [card_erase_rcode hB₁ B₁ B₂, card_erase_rcode hB₂ B₁ B₃, card_erase_rcode hB₃ B₂ B₄,
    card_erase_rcode hB₄ B₃ B₅, card_erase_rcode hB₅ B₄ B₅] at hst5
  have e2 := card_inter_rcode hB₁ hB₂ c2 B₁ B₃ hs.1
  have e3 := card_inter_rcode hB₂ hB₃ c3 B₁ B₄ hs.2.1
  have e4 := card_inter_rcode hB₃ hB₄ c4 B₂ B₅ hs.2.2.1
  have e5 := card_inter_rcode hB₄ hB₅ c5 B₃ B₅ hs.2.2.2
  have hv := bvalid_kcodes hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5 hs
  set a1 := rcode B₁ B₁ B₂ (r1 s)
  set a2 := rcode B₁ B₂ B₃ (r2 s)
  set a3 := rcode B₂ B₃ B₄ (r3 s)
  set a4 := rcode B₃ B₄ B₅ (r4 s)
  set a5 := rcode B₄ B₅ B₅ (r5 s)
  have hat : ptAt5 m2 m3 m4 m5 NM a1 a2 a3 a4 a5 = true :=
    all5k_spec (all5k_spec (all5k_spec (all5k_spec (all5k_spec hC
      (by have := rcode_le B₁ B₁ B₂ (r1 s); omega))
      (by have := rcode_le B₁ B₂ B₃ (r2 s); omega)) (by have := rcode_le B₂ B₃ B₄ (r3 s); omega))
      (by have := rcode_le B₃ B₄ B₅ (r4 s); omega)) (by have := rcode_le B₄ B₅ B₅ (r5 s); omega)
  simp only [ptAt5, hv, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hat
  have f2 : ((B₁.erase (r1 s)) ∩ (B₂.erase (r2 s))).card = nE5 m2 a1 a2 := by unfold nE5; omega
  have f3 : ((B₂.erase (r2 s)) ∩ (B₃.erase (r3 s))).card = nE5 m3 a2 a3 := by unfold nE5; omega
  have f4 : ((B₃.erase (r3 s)) ∩ (B₄.erase (r4 s))).card = nE5 m4 a3 a4 := by unfold nE5; omega
  have f5 : ((B₄.erase (r4 s)) ∩ (B₅.erase (r5 s))).card = nE5 m5 a4 a5 := by unfold nE5; omega
  rw [f2, f3, f4, f5, ← kapP_kapM] at hst5
  have hle := NUR_le_NM _ (nidx_lt (kH45 a1) (kH45 a2) (kH45 a3) (kH45 a4) (kH45 a5)) (orb s)
  have hRp := Rof_pos _ (mem45 (kH45 a1)) _ (mem45 (kH45 a2)) _ (mem45 (kH45 a3))
    _ (mem45 (kH45 a4)) _ (mem45 (kH45 a5)) (orb s)
  have hRof : Rof (4 + kH a1) (4 + kH a2) (4 + kH a3) (4 + kH a4) (4 + kH a5) (orb s)
      = (patCerts.getD (nidx (4 + kH a1) (4 + kH a2) (4 + kH a3) (4 + kH a4) (4 + kH a5))
          default).R.getD (orb s) 0 := rfl
  rw [hRof] at hst5 hRp
  rw [NUL_eq] at hle
  generalize kapP (4 + kH a1) (4 + kH a2) (4 + kH a3) (4 + kH a4) (4 + kH a5)
    (nE5 m2 a1 a2) (nE5 m3 a2 a3) (nE5 m4 a3 a4) (nE5 m5 a4 a5) = P at hat hst5
  generalize kapM (4 + kH a1) (4 + kH a2) (4 + kH a3) (4 + kH a4) (4 + kH a5)
    (nE5 m2 a1 a2) (nE5 m3 a2 a3) (nE5 m4 a3 a4) (nE5 m5 a4 a5) = M at hat hst5
  generalize NM.getD (nidx (4 + kH a1) (4 + kH a2) (4 + kH a3) (4 + kH a4) (4 + kH a5)) 0 = Nm
    at hat hle
  generalize (patCerts.getD (nidx (4 + kH a1) (4 + kH a2) (4 + kH a3) (4 + kH a4) (4 + kH a5))
    default).R.getD (orb s) 0 = R at hst5 hRp hle
  generalize hNU0' : NUo (orb s) = NU at hst5 hle
  have hNU0 : 0 < NU := by rw [← hNU0']; exact NUo_pos (orb s)
  generalize hE : (1000000000 : ℕ) = E at hat
  have hE' : (1000000000 : ℝ) = (E : ℝ) := by rw [← hE]; norm_num
  rw [hE'] at hst5
  push_cast at hst5
  have hU : 0 ≤ GU 5 w s := GU_nonneg55 hw s
  have hX : (0 : ℝ) < (NU : ℝ) * R := by
    have : (0 : ℝ) < NU := by exact_mod_cast hNU0
    have : (0 : ℝ) < R := by exact_mod_cast hRp
    positivity
  have hatR : (Nm : ℝ) + E * M ≤ E * P := by exact_mod_cast hat
  have hleR : (NU : ℝ) * R ≤ Nm := by exact_mod_cast hle
  have k1 : (NU : ℝ) * R ≤ E * ((P : ℝ) - M) := by linarith
  have k2 := mul_le_mul_of_nonneg_right k1 hU
  have key : GU 5 w s * (NU * R) ≤ GB w B₁ B₂ B₃ B₄ B₅ s * (NU * R) := by linarith
  exact le_of_mul_le_mul_right key hX

end seam

theorem bitOK5_of {m2 m3 m4 m5 : ℕ} {C : BitCert5} (hp : pinsOK5 RM m2 m3 m4 m5 C = true)
    (h0 : bitPart5 m2 m3 m4 m5 C 0 = true) (h1 : bitPart5 m2 m3 m4 m5 C 1 = true)
    (h2 : bitPart5 m2 m3 m4 m5 C 2 = true) (h3 : bitPart5 m2 m3 m4 m5 C 3 = true)
    (h4 : bitPart5 m2 m3 m4 m5 C 4 = true) : bitOK5 RM m2 m3 m4 m5 C = true := by
  simp [bitOK5, all5k, hp, h0, h1, h2, h3, h4]

end GridGen.Five.K5
