/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.ExDefs

/-!
# Height six at `k = 6`: soundness of the exact certificates

For a shape `j` (rows `r < j` with the `6`-list `U`, rows `r ≥ j` with `V`, `|U ∩ V| = 5`) and a
certificate passing `certOK`, `patS` and `patK` for every canonical pattern, the seam
inequality holds (`seam_shape`). The steps:

* every proper column `s` has a type: its pattern `p = canon s` and kinds `κ` (`kap`); the type is
  admissible (`admK_kap`, `popc_wm_le`) and its kinds are among `kopts` (`kap_mem`);
* relabelling `U ∪ V` onto `{0, …, 6}` (`exists_sigma`) turns the successor lists of `s` into the
  masks of the type (`GB_eq_masks`), whose weighted count is a combination of the orbit counts
  (`card_orb_setOf`), so the cone test of the leaf gives `e · GU ≤ D · GB` (`leaf_sound`);
* the pins of the certificate become pins of `GridGen/Six/Pins.lean` on atom sets (`XP.toPin`),
  whose events on `s` are the compiled conditions on the type (`penC_eq`); `Σ λ · bnd ≤ K`
  averages them out (`seam_of_pins`).
-/

namespace GridGen.Six

open Finset

/-! ### The seam from pins -/

/-- The fired multipliers of a list of pins. -/
def firedP (P : List (Pin6 × ℕ)) (s : T6) : ℕ := (P.map fun q => if q.1.ev s then q.2 else 0).sum

section pins

variable {w : Wt6} {X₁ X₂ X₃ X₄ X₅ X₆ : Finset ℕ}

theorem sum_firedP (hw : InCone6 w) (h₁ : 5 ≤ X₁.card) (h₂ : 5 ≤ X₂.card) (h₃ : 5 ≤ X₃.card)
    (h₄ : 5 ≤ X₄.card) (h₅ : 5 ≤ X₅.card) (h₆ : 5 ≤ X₆.card) :
    ∀ P : List (Pin6 × ℕ), (∀ q ∈ P, q.1.OK) →
      ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w s * (firedP P s : ℝ)
        ≤ (((P.map fun q => (q.2 : ℚ) * q.1.bnd).sum : ℚ) : ℝ) * ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w s
  | [], _ => by simp [firedP]
  | q :: P, hP => by
    have ih := sum_firedP hw h₁ h₂ h₃ h₄ h₅ h₆ P (fun x hx => hP x (by simp [hx]))
    have hq := pin_sum6 hw h₁ h₂ h₃ h₄ h₅ h₆ q.1 (hP q (by simp))
    have e1 : ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w s * (firedP (q :: P) s : ℝ)
        = (q.2 : ℝ) * ∑ s ∈ (sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => q.1.ev t = true), GU 6 w s
          + ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w s * (firedP P s : ℝ) := by
      rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      simp only [firedP, List.map_cons, List.sum_cons]
      split_ifs <;> push_cast <;> ring
    rw [e1]
    have hl : (0 : ℝ) ≤ q.2 := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hq hl
    simp only [List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast]
    linarith

/-- **The seam inequality from state inequalities and pins.** -/
theorem seam_of_pins (hw : InCone6 w) (h₁ : 5 ≤ X₁.card) (h₂ : 5 ≤ X₂.card) (h₃ : 5 ≤ X₃.card)
    (h₄ : 5 ≤ X₄.card) (h₅ : 5 ≤ X₅.card) (h₆ : 5 ≤ X₆.card) {g : T6 → ℝ}
    (P : List (Pin6 × ℕ)) (hP : ∀ q ∈ P, q.1.OK) {K D : ℕ} (hD : 0 < D)
    (hL : (P.map fun q => (q.2 : ℚ) * q.1.bnd).sum ≤ K)
    (hstate : ∀ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w s * ((D : ℝ) + K - firedP P s) ≤ D * g s) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, g s := by
  set Ω := sts X₁ X₂ X₃ X₄ X₅ X₆ with hΩ
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hsum := Finset.sum_le_sum hstate
  have hf := sum_firedP hw h₁ h₂ h₃ h₄ h₅ h₆ P hP
  set W := ∑ s ∈ Ω, GU 6 w s with hW
  have hLR : (((P.map fun q => (q.2 : ℚ) * q.1.bnd).sum : ℚ) : ℝ) ≤ K := by exact_mod_cast hL
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun s _ => GU_nonneg hw s
  have e : ∑ s ∈ Ω, GU 6 w s * ((D : ℝ) + K - firedP P s)
      = ((D : ℝ) + K) * W - ∑ s ∈ Ω, GU 6 w s * (firedP P s : ℝ) := by
    rw [hW, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [e, ← Finset.mul_sum] at hsum
  have h1 : (((P.map fun q => (q.2 : ℚ) * q.1.bnd).sum : ℚ) : ℝ) * W ≤ K * W :=
    mul_le_mul_of_nonneg_right hLR hW0
  have h2 : (D : ℝ) * W ≤ D * ∑ s ∈ Ω, g s := by linarith
  exact le_of_mul_le_mul_left h2 hDR

end pins

/-! ### Shapes, atoms and pins on atoms -/

/-- The list of row `r` in shape `j`. -/
def bj (j : ℕ) (U V : Finset ℕ) (r : ℕ) : Finset ℕ := if r < j then U else V

/-- The colours of an atom set: bit `0` the common colours, bit `5` the colour of `U` only, bit `6`
the colour of `V` only. -/
def aset (U V : Finset ℕ) (S : ℕ) : Finset ℕ :=
  ((if S.testBit 0 = true then U ∩ V else ∅) ∪ (if S.testBit 5 = true then U \ V else ∅)) ∪
    (if S.testBit 6 = true then V \ U else ∅)

section shape

variable {U V : Finset ℕ}

theorem card_sdiff_one (hU : U.card = 6) (hW : (U ∩ V).card = 5) : (U \ V).card = 1 := by
  have := Finset.card_sdiff_add_card_inter U V; omega

theorem card_aset (hU : U.card = 6) (hV : V.card = 6) (hW : (U ∩ V).card = 5) (S : ℕ) :
    (aset U V S).card ≤ asz S := by
  have h1 := card_sdiff_one hU hW
  have h2 := card_sdiff_one hV (by rw [Finset.inter_comm]; exact hW)
  unfold aset asz
  refine (Finset.card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right (Finset.card_union_le _ _) _).trans ?_
  cases S.testBit 0 <;> cases S.testBit 5 <;> cases S.testBit 6 <;> simp [h1, h2, hW]

/-- The block of a pin, on atom sets. -/
def xblk (j : ℕ) (U V : Finset ℕ) : ℕ → List ℕ → Blk6
  | r, [S] => Blk6.one r (aset U V S ∩ bj j U V r) (asz S)
  | r, [S, S'] => Blk6.two r (aset U V S ∩ bj j U V r) (aset U V S' ∩ bj j U V (r + 1)) (asz S)
      (asz S')
  | r, [S, S', S''] => Blk6.three r (aset U V S ∩ bj j U V r) (aset U V S' ∩ bj j U V (r + 1))
      (aset U V S'' ∩ bj j U V (r + 2)) (asz S) (asz S') (asz S'')
  | _, _ => Blk6.none

/-- A peel on atom sets. -/
def XF.toFac (j : ℕ) (U V : Finset ℕ) : XF → Fac6
  | XF.mem r S => Fac6.mem r (aset U V S ∩ bj j U V r) (asz S)
  | XF.eq r i => Fac6.eqr r i

/-- A pin on atom sets. -/
def XP.toPin (j : ℕ) (U V : Finset ℕ) (q : XP) : Pin6 :=
  ⟨xblk j U V q.r0 q.bs, q.peels.map (XF.toFac j U V)⟩

theorem toFac_bnd (j : ℕ) (U V : Finset ℕ) (f : XF) : (f.toFac j U V).bnd qX = f.bnd := by
  cases f <;> rfl

theorem xblk_bnd (j : ℕ) (U V : Finset ℕ) (r : ℕ) (bs : List ℕ) :
    (xblk j U V r bs).bnd = blkBnd r bs := by
  match bs with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | _ :: _ :: _ :: _ :: _ => rfl

theorem xtoPin_bnd (j : ℕ) (U V : Finset ℕ) (q : XP) : (q.toPin j U V).bnd = xbnd q := by
  unfold XP.toPin Pin6.bnd xbnd
  rw [xblk_bnd, List.map_map]
  congr 2
  exact List.map_congr_left fun f _ => toFac_bnd j U V f

theorem xblk_reads (j : ℕ) (U V : Finset ℕ) (r : ℕ) (bs : List ℕ) (h : bs.length ≤ 3) (i : ℕ) :
    (xblk j U V r bs).reads i = blkReads r bs i := by
  match bs, h with
  | [], _ => simp [xblk, Blk6.reads, blkReads]
  | [_], _ => simp only [xblk, Blk6.reads, blkReads, List.length_singleton]; by_cases h : r = i <;>
      simp [h] <;> omega
  | [_, _], _ => simp only [xblk, Blk6.reads, blkReads, List.length_cons, List.length_nil]
                 by_cases h1 : r = i <;> by_cases h2 : r + 1 = i <;> simp [h1, h2] <;> omega
  | [_, _, _], _ => simp only [xblk, Blk6.reads, blkReads, List.length_cons, List.length_nil]
                    by_cases h1 : r = i <;> by_cases h2 : r + 1 = i <;> by_cases h3 : r + 2 = i <;>
                      simp [h1, h2, h3] <;> omega

theorem toFac_reads (j : ℕ) (U V : Finset ℕ) (f : XF) (i : ℕ) :
    (f.toFac j U V).reads i = f.reads i := by cases f <;> rfl

theorem toFac_row (j : ℕ) (U V : Finset ℕ) (f : XF) : (f.toFac j U V).row = f.row := by
  cases f <;> rfl

theorem toFac_ok (hU : U.card = 6) (hV : V.card = 6) (hW : (U ∩ V).card = 5) (j : ℕ) {f : XF}
    (hf : f.okb = true) : (f.toFac j U V).ok := by
  cases f with
  | mem r S =>
    simp only [XF.okb, decide_eq_true_eq] at hf
    exact ⟨hf, (Finset.card_le_card Finset.inter_subset_left).trans (card_aset hU hV hW S)⟩
  | eq r i =>
    simp only [XF.okb, decide_eq_true_eq] at hf
    exact hf

theorem peelOK_of (hU : U.card = 6) (hV : V.card = 6) (hW : (U ∩ V).card = 5) (j : ℕ)
    {r0 : ℕ} {bs : List ℕ} (hb : bs.length ≤ 3) :
    ∀ {ps : List XF}, xpeelOK r0 bs ps = true →
      PeelOK6 (xblk j U V r0 bs).reads (ps.map (XF.toFac j U V))
  | [], _ => trivial
  | f :: fs, h => by
    simp only [xpeelOK, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨?_, ?_, toFac_ok hU hV hW j h3, peelOK_of hU hV hW j hb h4⟩
    · rw [toFac_row, xblk_reads j U V r0 bs hb]; exact h1
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      rw [toFac_reads, toFac_row]
      have := List.all_eq_true.mp h2 g' hg'
      simpa using this

theorem xtoPin_OK (hU : U.card = 6) (hV : V.card = 6) (hW : (U ∩ V).card = 5) (j : ℕ) {q : XP}
    (hq : q.okb = true) : (q.toPin j U V).OK := by
  simp only [XP.okb, Bool.and_eq_true, decide_eq_true_eq] at hq
  obtain ⟨⟨hl, hr⟩, hp⟩ := hq
  refine ⟨?_, peelOK_of hU hV hW j hl hp⟩
  have hc : ∀ (S : ℕ) (r : ℕ), (aset U V S ∩ bj j U V r).card ≤ asz S := fun S r =>
    (Finset.card_le_card Finset.inter_subset_left).trans (card_aset hU hV hW S)
  unfold XP.toPin
  match h : q.bs, hl, hr with
  | [], _, _ => trivial
  | [S], _, hr => exact ⟨by simp at hr; omega, hc S _⟩
  | [S, S'], _, hr => exact ⟨by simp at hr; omega, hc S _, hc S' _⟩
  | [S, S', S''], _, hr => exact ⟨by simp at hr; omega, hc S _, hc S' _, hc S'' _⟩
  | _ :: _ :: _ :: _ :: _, hl, _ => exact absurd hl (by simp)

end shape

end GridGen.Six
