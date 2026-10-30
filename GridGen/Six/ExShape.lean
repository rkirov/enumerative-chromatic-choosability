/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.ExSeam

/-!
# Height six at `k = 6`: the seam on a single-mismatch shape, assembled

`seam_shape`: a certificate for shape `j` gives `Σ GU ≤ Σ GB` for every system of lists of shape
`j` (rows `r < j` with a `6`-list `U`, rows `r ≥ j` with a `6`-list `V`, `|U ∩ V| = 5`).
-/

namespace GridGen.Six

open Finset

section shape

variable {j : ℕ} {U V : Finset ℕ}

/-! ### The successor count of a column -/

/-- **The successor count is that of the masks of the type.** -/
theorem GB_eq_masks (w : Wt6) (hU : U.card = 6) (hV : V.card = 6) (hW : (U ∩ V).card = 5)
    {s : T6} (hs : Proper s) :
    GB w (bj j U V 0) (bj j U V 1) (bj j U V 2) (bj j U V 3) (bj j U V 4) (bj j U V 5) s
      = ∑ o : Fin 32, (cntO o (mskL j (labL (canon s) (kap j U V s))) : ℝ) * w o := by
  obtain ⟨σ, hinj, -, hims⟩ := exists_sigma (j := j) hU hV hW hs
  have hsub : ∀ r, (bj j U V r).erase (rowAt r s) ⊆ U ∪ V := by
    intro r
    refine (Finset.erase_subset _ _).trans ?_
    unfold bj; split_ifs
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  have hU' : Set.InjOn σ ↑((bj j U V 0).erase (rowAt 0 s) ∪ (bj j U V 1).erase (rowAt 1 s) ∪
      (bj j U V 2).erase (rowAt 2 s) ∪ (bj j U V 3).erase (rowAt 3 s) ∪
      (bj j U V 4).erase (rowAt 4 s) ∪ (bj j U V 5).erase (rowAt 5 s)) := by
    apply hinj.mono
    intro x hx
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hx
    have : x ∈ U ∪ V := by
      rcases hx with ((((h | h) | h) | h) | h) | h <;> exact hsub _ h
    exact_mod_cast this
  unfold GB
  have e := G_image w hU'
  rw [hims 0 (by norm_num), hims 1 (by norm_num), hims 2 (by norm_num), hims 3 (by norm_num),
    hims 4 (by norm_num), hims 5 (by norm_num)] at e
  show G w ((bj j U V 0).erase (rowAt 0 s)) ((bj j U V 1).erase (rowAt 1 s))
    ((bj j U V 2).erase (rowAt 2 s)) ((bj j U V 3).erase (rowAt 3 s))
    ((bj j U V 4).erase (rowAt 4 s)) ((bj j U V 5).erase (rowAt 5 s)) = _
  rw [← e, G_eq_sum_orb]
  refine Finset.sum_congr rfl fun o _ => ?_
  congr 1
  have := card_orb_setOf (mskL j (labL (canon s) (kap j U V s))) o
  simp only [mskL, List.getD_cons_zero, List.getD_cons_succ] at this ⊢
  exact_mod_cast this

/-! ### The pins on a column -/

theorem labIn_eq (S x : ℕ) : labIn S x = (decide (x < 7) && (if x < 5 then S.testBit 0 else S.testBit x)) := by
  unfold labIn; rw [nblt, nblt]; split_ifs with h <;> simp [h]

/-- **A colour lies in an atom set of its row iff its label does.** -/
theorem mem_aset_iff (hU : U.card = 6) (hV : V.card = 6) (hW : (U ∩ V).card = 5) {s : T6}
    (hs : Proper s) {r : ℕ} (hr : r < 6) (S : ℕ) :
    rowAt r s ∈ aset U V S ∩ bj j U V r ↔
      labIn S ((labL (canon s) (kap j U V s)).getD r 7) = true := by
  set x := rowAt r s with hx
  have hk : kap j U V s r = kapC j U V r x := rfl
  rw [labIn_eq]
  unfold aset bj
  by_cases h0 : x ∈ U ∩ V
  · have hl := lab_common (j := j) hW hs hr ((kap_zero_iff s r).mpr h0)
    have hxU := (Finset.mem_inter.mp h0).1
    have hxV := (Finset.mem_inter.mp h0).2
    simp only [hl.2, ite_true, show (labL (canon s) (kap j U V s)).getD r 7 < 7 by omega,
      decide_true, Bool.true_and]
    split_ifs <;> simp_all [Finset.mem_union, Finset.mem_sdiff]
  · have hl := lab_other (j := j) (U := U) (V := V) hr (fun h => h0 ((kap_zero_iff s r).mp h))
    rw [hl, hk]
    unfold kapC
    rw [ite_eq_right h0]
    by_cases h5 : r < j ∧ x ∈ U
    · have hxV : x ∉ V := fun h => h0 (Finset.mem_inter.mpr ⟨h5.2, h⟩)
      rw [ite_eq_left h5, ite_eq_left h5.1]
      simp only [show (5 : ℕ) < 7 by norm_num, show ¬ (5 : ℕ) < 5 by norm_num, decide_true,
        Bool.true_and, ite_false]
      split_ifs <;> simp_all [Finset.mem_union, Finset.mem_sdiff]
    · rw [ite_eq_right h5]
      by_cases h6 : j ≤ r ∧ x ∈ V
      · have hxU : x ∉ U := fun h => h0 (Finset.mem_inter.mpr ⟨h, h6.2⟩)
        rw [ite_eq_left h6, ite_eq_right (show ¬ r < j by omega)]
        simp only [show (6 : ℕ) < 7 by norm_num, show ¬ (6 : ℕ) < 5 by norm_num, decide_true,
          Bool.true_and, ite_false]
        split_ifs <;> simp_all [Finset.mem_union, Finset.mem_sdiff]
      · rw [ite_eq_right h6]
        simp only [show ¬ (7 : ℕ) < 7 by norm_num, decide_false, Bool.false_and, Bool.false_eq_true,
          iff_false]
        intro hm
        have hb : x ∈ (if r < j then U else V) := (Finset.mem_inter.mp hm).2
        by_cases hrj : r < j
        · rw [ite_eq_left hrj] at hb; exact h5 ⟨hrj, hb⟩
        · rw [ite_eq_right hrj] at hb; exact h6 ⟨by omega, hb⟩

theorem allEv_peels (hU : U.card = 6) (hV : V.card = 6) (hW : (U ∩ V).card = 5) {s : T6}
    (hs : Proper s) : ∀ ps : List XF, (∀ f ∈ ps, f.okb = true) →
      allEv6 (ps.map (XF.toFac j U V)) s = (eqsOK (canon s) ps &&
        (memConds ps).all fun rs => labIn rs.2 ((labL (canon s) (kap j U V s)).getD rs.1 7))
  | [], _ => rfl
  | f :: ps, h => by
    have ih := allEv_peels hU hV hW hs ps (fun g hg => h g (by simp [hg]))
    have hf := h f (by simp)
    unfold allEv6 at ih ⊢
    rw [List.map_cons, List.all_cons, ih]
    cases f with
    | mem r S =>
      simp only [XF.okb, decide_eq_true_eq] at hf
      simp only [XF.toFac, Fac6.ev, eqsOK, memConds, List.all_cons]
      have := mem_aset_iff (j := j) hU hV hW hs hf S
      by_cases hm : rowAt r s ∈ aset U V S ∩ bj j U V r
      · rw [decide_eq_true hm, this.mp hm]; simp
      · rw [decide_eq_false hm, show labIn S ((labL (canon s) (kap j U V s)).getD r 7) = false from
          by simpa using (fun h' => hm (this.mpr h'))]
        simp
    | eq r i =>
      simp only [XF.okb, decide_eq_true_eq] at hf
      simp only [XF.toFac, Fac6.ev, eqsOK, memConds]
      rw [nbeq]
      have := canon_rows hs hf.1 hf.2.1
      by_cases he : rowAt r s = rowAt i s
      · rw [decide_eq_true he, decide_eq_true (this.mpr he)]; simp
      · rw [decide_eq_false he, decide_eq_false (fun h' => he (this.mp h'))]; simp

theorem blk_ev (hU : U.card = 6) (hV : V.card = 6) (hW : (U ∩ V).card = 5) {s : T6}
    (hs : Proper s) {r0 : ℕ} {bs : List ℕ} (hl : bs.length ≤ 3) (hr : r0 + bs.length ≤ 6) :
    (xblk j U V r0 bs).ev s = (blkConds r0 bs).all fun rs =>
      labIn rs.2 ((labL (canon s) (kap j U V s)).getD rs.1 7) := by
  have m : ∀ r < 6, ∀ S, decide (rowAt r s ∈ aset U V S ∩ bj j U V r)
      = labIn S ((labL (canon s) (kap j U V s)).getD r 7) := by
    intro r hr S
    have := mem_aset_iff (j := j) hU hV hW hs hr S
    by_cases hm : rowAt r s ∈ aset U V S ∩ bj j U V r
    · rw [decide_eq_true hm, this.mp hm]
    · rw [decide_eq_false hm]
      exact (by simpa using (fun h' => hm (this.mpr h')) : _ = false).symm
  match bs, hl, hr with
  | [], _, _ => rfl
  | [S], _, hr =>
    simp only [List.length_singleton] at hr
    simp only [xblk, Blk6.ev, blkConds, List.all_cons, List.all_nil, Bool.and_true]
    exact m r0 (by omega) S
  | [S, S'], _, hr =>
    simp only [List.length_cons, List.length_nil] at hr
    simp only [xblk, Blk6.ev, blkConds, List.all_cons, List.all_nil, Bool.and_true]
    rw [m r0 (by omega) S, m (r0 + 1) (by omega) S']
  | [S, S', S''], _, hr =>
    simp only [List.length_cons, List.length_nil] at hr
    simp only [xblk, Blk6.ev, blkConds, List.all_cons, List.all_nil, Bool.and_true]
    rw [m r0 (by omega) S, m (r0 + 1) (by omega) S', m (r0 + 2) (by omega) S'', Bool.and_assoc]
  | _ :: _ :: _ :: _ :: _, hl, _ => exact absurd hl (by simp)

theorem xpeelOK_okb {r0 : ℕ} {bs : List ℕ} : ∀ {ps : List XF}, xpeelOK r0 bs ps = true →
    ∀ f ∈ ps, f.okb = true
  | [], _ => by simp
  | f :: fs, h => by
    simp only [xpeelOK, Bool.and_eq_true] at h
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact h.1.2
    · exact xpeelOK_okb h.2 g hg

/-- **The fired pins of a column are the compiled penalty of its type.** -/
theorem firedP_eq (hU : U.card = 6) (hV : V.card = 6) (hW : (U ∩ V).card = 5) {s : T6}
    (hs : Proper s) : ∀ P : List XP, P.all XP.okb = true →
      firedP (P.map fun q => (q.toPin j U V, q.lam)) s
        = penC (compileX (canon s) P) (labL (canon s) (kap j U V s))
  | [], _ => rfl
  | q :: P, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := firedP_eq hU hV hW hs P h.2
    have hq := h.1
    simp only [XP.okb, Bool.and_eq_true, decide_eq_true_eq] at hq
    have hev : (q.toPin j U V).ev s = (eqsOK (canon s) q.peels &&
        ((blkConds q.r0 q.bs ++ memConds q.peels).all fun rs =>
          labIn rs.2 ((labL (canon s) (kap j U V s)).getD rs.1 7))) := by
      unfold XP.toPin Pin6.ev
      simp only
      rw [allEv_peels hU hV hW hs q.peels (xpeelOK_okb hq.2), blk_ev hU hV hW hs hq.1.1 hq.1.2,
        List.all_append]
      cases eqsOK (canon s) q.peels <;> cases (memConds q.peels).all _ <;>
        cases (blkConds q.r0 q.bs).all _ <;> rfl
    unfold firedP at ih ⊢
    unfold compileX at ih ⊢
    rw [List.map_cons, List.map_cons, List.sum_cons, ih, List.filterMap_cons]
    simp only [hev]
    unfold compileOne
    cases he : eqsOK (canon s) q.peels
    · simp [Bool.cond_false]
    · simp only [Bool.cond_true, Bool.true_and]
      unfold penC
      rw [List.foldr_cons]
      simp only [Nat.add_eq]
      split_ifs with hc
      · rw [hc]; rfl
      · rw [Bool.not_eq_true] at hc; rw [hc]; rfl

/-! ### The seam -/

theorem canons_length : canons.length = 52 := by decide +kernel

/-- **The seam inequality on shape `j` from a certificate.** -/
theorem seam_shape {D K : ℕ} {P : List XP} {CPS : List (List (List (ℕ × ℕ) × ℕ))}
    {PSI : List (List ℕ)} (hc : certOK D K P = true)
    (hpat : ∀ i < 52, patS P (CPS.getD i []) (PSI.getD i []) (canons.getD i (0, 0, 0, 0, 0, 0)) = true ∧
      ∀ k0 ∈ kopts j 0, patK D K j (CPS.getD i []) (PSI.getD i [])
        (canons.getD i (0, 0, 0, 0, 0, 0)) k0 = true)
    {w : Wt6} (hw : InCone6 w) {X₁ X₂ X₃ X₄ X₅ X₆ : Finset ℕ} (h₁ : 5 ≤ X₁.card)
    (h₂ : 5 ≤ X₂.card) (h₃ : 5 ≤ X₃.card) (h₄ : 5 ≤ X₄.card) (h₅ : 5 ≤ X₅.card)
    (h₆ : 5 ≤ X₆.card) (hU : U.card = 6) (hV : V.card = 6) (hW : (U ∩ V).card = 5) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w s
      ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆,
          GB w (bj j U V 0) (bj j U V 1) (bj j U V 2) (bj j U V 3) (bj j U V 4) (bj j U V 5) s := by
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hD, hP⟩, hL⟩ := hc
  have hD' : 0 < D := by simpa [nblt] using hD
  refine seam_of_pins hw h₁ h₂ h₃ h₄ h₅ h₆ (P.map fun q => (q.toPin j U V, q.lam))
    (fun q hq => by
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
      exact xtoPin_OK hU hV hW j (List.all_eq_true.mp hP q' hq'))
    hD' (by
      rw [List.map_map]
      convert hL using 2
      exact List.map_congr_left fun q _ => by simp [xtoPin_bnd]) ?_
  intro s hs
  have hs' := proper_of_mem_sts hs
  -- the pattern and its data
  obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem (canon_mem hs')
  rw [canons_length] at hi
  have hget : canons.getD i (0, 0, 0, 0, 0, 0) = canon s := by
    rw [List.getD_eq_getElem _ _ (by rw [canons_length]; exact hi), hpi]
  obtain ⟨hS, hK⟩ := hpat i hi
  rw [hget] at hS hK
  simp only [patS, Bool.and_eq_true, decide_eq_true_eq] at hS
  obtain ⟨hpsi, hcps⟩ := hS
  -- the type passes
  set k := kap j U V s with hk
  have hleaf : leafX D K j (CPS.getD i []) (PSI.getD i []) (canon s) (k 0) (k 1) (k 2) (k 3) (k 4)
      (k 5) = true := by
    have h0 := hK (k 0) (kap_mem s (by norm_num))
    unfold patK at h0
    have h1 := List.all_eq_true.mp h0 (k 1) (kap_mem s (by norm_num))
    have h2 := List.all_eq_true.mp h1 (k 2) (kap_mem s (by norm_num))
    have h3 := List.all_eq_true.mp h2 (k 3) (kap_mem s (by norm_num))
    have h4 := List.all_eq_true.mp h3 (k 4) (kap_mem s (by norm_num))
    have h5 := List.all_eq_true.mp h4 (k 5) (kap_mem s (by norm_num))
    have ha : (admK (canon s) (k 0) (k 1) (k 2) (k 3) (k 4) (k 5) &&
        Nat.ble (popc (wmask (canon s) (k 0) (k 1) (k 2) (k 3) (k 4) (k 5))) 5) = true := by
      rw [Bool.and_eq_true, kap_adm hU hV hW hs', Nat.ble_eq]
      exact ⟨rfl, popc_wm_le hW hs'⟩
    rw [ha] at h5
    simpa using h5
  rw [leafX_eq] at hleaf
  have hcone := okc6_sound hleaf hpsi hw
  -- the state inequality
  rw [GB_eq_masks w hU hV hW hs', GU_six w hs', orb_congr (samePat_canon hs'),
    firedP_eq hU hV hW hs' P hP, hcps]
  set pe := penC (CPS.getD i []) (labL (canon s) k)
  have hGU : 0 ≤ rowV6 (orb (canon s)) w := (rowV6_pos hw _).le
  have hsub : ((D : ℝ) + K - pe) ≤ ((D + K - pe : ℕ) : ℝ) := by
    rcases le_total pe (D + K) with h | h
    · rw [Nat.cast_sub h]; push_cast; rfl
    · rw [Nat.sub_eq_zero_of_le h]; push_cast
      have : ((D + K : ℕ) : ℝ) ≤ pe := by exact_mod_cast h
      push_cast at this; linarith
  calc rowV6 (orb (canon s)) w * ((D : ℝ) + K - pe)
      ≤ rowV6 (orb (canon s)) w * ((D + K - pe : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hsub hGU
    _ = ((D + K - pe : ℕ) : ℝ) * rowV6 (orb (canon s)) w := by ring
    _ ≤ _ := hcone

end shape

/-! ### The table of accumulations is sound -/

theorem xtAll_bin (f : ℕ → ℕ → Bool) (l : XT) (key val : ℕ) (r : XT) :
    xtAll f (XT.bin l key val r) = (xtAll f l && f key val && xtAll f r) := rfl

theorem xtGet_bin (k : ℕ) (l : XT) (key val : ℕ) (r : XT) :
    xtGet k (XT.bin l key val r)
      = cond (Nat.blt k key) (xtGet k l) (cond (Nat.beq k key) (Nat.succ val) (xtGet k r)) := rfl

/-- A value found in a checked tree satisfies the check. -/
theorem xtGet_spec {f : ℕ → ℕ → Bool} {k v : ℕ} :
    ∀ {t : XT}, xtAll f t = true → xtGet k t = v + 1 → f k v = true
  | XT.tip, _, h => absurd h (by simp [xtGet])
  | XT.bin l key val r, ha, h => by
    rw [xtAll_bin, Bool.and_eq_true, Bool.and_eq_true] at ha
    rw [xtGet_bin] at h
    cases hb : Nat.blt k key
    · cases he : Nat.beq k key
      · rw [hb, he] at h
        exact xtGet_spec ha.2 h
      · rw [hb, he] at h
        have e1 : k = key := Nat.eq_of_beq_eq_true he
        have e2 : val = v := Nat.succ.inj h
        rw [e1, ← e2]; exact ha.1.2
    · rw [hb] at h
      exact xtGet_spec ha.1.1 h

theorem lane4_lkey {l0 l1 l2 l3 l4 l5 : ℕ} (h0 : l0 < 16) (h1 : l1 < 16) (h2 : l2 < 16)
    (h3 : l3 < 16) (h4 : l4 < 16) (h5 : l5 < 16) :
    [lane4 (lkey l0 l1 l2 l3 l4 l5) 0, lane4 (lkey l0 l1 l2 l3 l4 l5) 1,
      lane4 (lkey l0 l1 l2 l3 l4 l5) 2, lane4 (lkey l0 l1 l2 l3 l4 l5) 3,
      lane4 (lkey l0 l1 l2 l3 l4 l5) 4, lane4 (lkey l0 l1 l2 l3 l4 l5) 5]
      = [l0, l1, l2, l3, l4, l5] := by
  have e : lkey l0 l1 l2 l3 l4 l5 = pkF 4 (fun i => [l0, l1, l2, l3, l4, l5].getD i 0) 6 := by
    simp only [lkey, pkF, Nat.add_eq, Nat.mul_eq, List.getD_cons_zero, List.getD_cons_succ]
    norm_num
  have hl : ∀ i < 6, [l0, l1, l2, l3, l4, l5].getD i 0 < 2 ^ 4 := by
    intro i hi
    interval_cases i <;> simp <;> omega
  simp only [lane4_eq, e, lane_pkF hl (show 0 < 6 by norm_num), lane_pkF hl (show 1 < 6 by norm_num),
    lane_pkF hl (show 2 < 6 by norm_num), lane_pkF hl (show 3 < 6 by norm_num),
    lane_pkF hl (show 4 < 6 by norm_num), lane_pkF hl (show 5 < 6 by norm_num),
    List.getD_cons_zero, List.getD_cons_succ]

/-- A checked table entry is the accumulation of the masks of its labels. -/
theorem tabE_sound {j key val : ℕ} (h : tabE j key val = true) :
    val = accS (itab (mskL j [lane4 key 0, lane4 key 1, lane4 key 2, lane4 key 3, lane4 key 4,
      lane4 key 5])) MQ6 := by
  unfold tabE at h
  have := tab_eq (mskL j [lane4 key 0, lane4 key 1, lane4 key 2, lane4 key 3, lane4 key 4,
    lane4 key 5]) (mskL_lt j _)
  simp only [mskL, List.getD_cons_zero, List.getD_cons_succ] at this
  rw [this] at h
  have h2 := hor_eq (mskL j [lane4 key 0, lane4 key 1, lane4 key 2, lane4 key 3, lane4 key 4,
    lane4 key 5])
  simp only [mskL, List.getD_cons_zero, List.getD_cons_succ] at h2
  rw [h2, accG_eq] at h
  exact (Nat.eq_of_beq_eq_true h).symm

/-- **The leaf with the table gives the leaf.** -/
theorem leafX_of_T {D K j : ℕ} {cps : List (List (ℕ × ℕ) × ℕ)} {psi : List ℕ} {p : T6} {t : XT}
    (ht : xtAll (tabE j) t = true) (k : ℕ → ℕ)
    (h : leafT D K j cps psi p t (k 0) (k 1) (k 2) (k 3) (k 4) (k 5) = true) :
    leafX D K j cps psi p (k 0) (k 1) (k 2) (k 3) (k 4) (k 5) = true := by
  rw [leafX_eq]
  unfold leafT leafT1 leafT2 leafT3 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨b0, b1⟩, b2⟩, b3⟩, b4⟩, b5⟩, hv, hok⟩ := h
  simp only [Nat.blt_eq] at b0 b1 b2 b3 b4 b5
  generalize hV : xtGet (lkey (lab (wmask p (k 0) (k 1) (k 2) (k 3) (k 4) (k 5)) (r1 p) (k 0))
    (lab (wmask p (k 0) (k 1) (k 2) (k 3) (k 4) (k 5)) (r2 p) (k 1))
    (lab (wmask p (k 0) (k 1) (k 2) (k 3) (k 4) (k 5)) (r3 p) (k 2))
    (lab (wmask p (k 0) (k 1) (k 2) (k 3) (k 4) (k 5)) (r4 p) (k 3))
    (lab (wmask p (k 0) (k 1) (k 2) (k 3) (k 4) (k 5)) (r5 p) (k 4))
    (lab (wmask p (k 0) (k 1) (k 2) (k 3) (k 4) (k 5)) (r6 p) (k 5))) t = v at hv hok
  have hv0 : v ≠ 0 := by
    intro e; rw [e] at hv; simp at hv
  obtain ⟨u, rfl⟩ : ∃ u, v = u + 1 := ⟨v - 1, by omega⟩
  have hE := tabE_sound (xtGet_spec ht hV)
  rw [lane4_lkey b0 b1 b2 b3 b4 b5] at hE
  have e1 : Nat.sub (u + 1) 1 = u := Nat.add_sub_cancel u 1
  rw [e1] at hok
  rw [hE] at hok
  simpa only [labL, wmK, Nat.sub_eq, Nat.add_eq] using hok

/-- **The check of a pattern with the table gives its check.** -/
theorem patK_of_T {D K j : ℕ} {cps : List (List (ℕ × ℕ) × ℕ)} {psi : List ℕ} {p : T6} {t : XT}
    (ht : xtAll (tabE j) t = true) {k0 : ℕ} (h : patKT D K j cps psi p t k0 = true) :
    patK D K j cps psi p k0 = true := by
  unfold patK
  unfold patKT at h
  simp only [List.all_eq_true] at h ⊢
  intro k1 h1 k2 h2 k3 h3 k4 h4 k5 h5
  have hh := h k1 h1 k2 h2 k3 h3 k4 h4 k5 h5
  rw [Bool.or_eq_true] at hh ⊢
  rcases hh with g | g
  · exact Or.inl g
  · exact Or.inr (leafX_of_T ht (fun r => [k0, k1, k2, k3, k4, k5].getD r 0) g)

/-- The checks of a range of patterns: the data `patS` and the kinds with the table. -/
theorem pats_of_T {D K j : ℕ} {P : List XP} {CPS : List (List (List (ℕ × ℕ) × ℕ))}
    {PSI : List (List ℕ)} {t : XT} (ht : xtAll (tabE j) t = true)
    (h0 : patChunk D K j P CPS PSI t 0 13 = true) (h1 : patChunk D K j P CPS PSI t 13 13 = true)
    (h2 : patChunk D K j P CPS PSI t 26 13 = true) (h3 : patChunk D K j P CPS PSI t 39 13 = true) :
    ∀ i < 52, patS P (CPS.getD i []) (PSI.getD i []) (canons.getD i (0, 0, 0, 0, 0, 0)) = true ∧
      ∀ k0 ∈ kopts j 0, patK D K j (CPS.getD i []) (PSI.getD i [])
        (canons.getD i (0, 0, 0, 0, 0, 0)) k0 = true := by
  intro i hi
  have pick : ∀ a b, patChunk D K j P CPS PSI t a b = true → a ≤ i → i < a + b →
      (patS P (CPS.getD i []) (PSI.getD i []) (canons.getD i (0, 0, 0, 0, 0, 0)) &&
        (kopts j 0).all (patKT D K j (CPS.getD i []) (PSI.getD i [])
          (canons.getD i (0, 0, 0, 0, 0, 0)) t)) = true := by
    intro a b h ha hb
    exact List.all_eq_true.mp h i (List.mem_range'_1.mpr ⟨ha, hb⟩)
  have hc : (patS P (CPS.getD i []) (PSI.getD i []) (canons.getD i (0, 0, 0, 0, 0, 0)) &&
      (kopts j 0).all (patKT D K j (CPS.getD i []) (PSI.getD i [])
        (canons.getD i (0, 0, 0, 0, 0, 0)) t)) = true := by
    rcases Nat.lt_or_ge i 13 with g | g
    · exact pick 0 13 h0 (by omega) (by omega)
    rcases Nat.lt_or_ge i 26 with g' | g'
    · exact pick 13 13 h1 g (by omega)
    rcases Nat.lt_or_ge i 39 with g'' | g''
    · exact pick 26 13 h2 g' (by omega)
    · exact pick 39 13 h3 g'' (by omega)
  rw [Bool.and_eq_true] at hc
  exact ⟨hc.1, fun k0 hk => patK_of_T ht (List.all_eq_true.mp hc.2 k0 hk)⟩

end GridGen.Six
