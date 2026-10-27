/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.K4.GTree

/-!
# Height four at `k = 4`: branching on actual lists (layer B3)

Codex's (OpenAI) explicit-list branching (`ai_research_notes/cx/h4k4b/NOTE.md`): a free row is
replaced by every possible **list type**, a sublist of the colour table together with fresh
colours of available atoms (`ltypes`). Every actual list of three or four colours has one of these
types (`ltypes_cover`), so the classification statement `GOK` of a node follows from the
statements of all its list children (`evalGAT_sound`). A child is closed by a numeric tree with a
nonnegative value, by further branching, or, when every row is an explicit list, by being a bad
pattern (`badFCheck`, `badMCheck`).
-/

namespace GridGen.Four.K4

open Finset

/-! ### List types -/

/-- The sublists of `[0, n)` of length at most four. -/
def idSubs (n : ℕ) : List (List ℕ) := (List.range n).sublists.filter fun l => Nat.ble l.length 4

/-- All lists of fresh masks: for each `(mask, cap)` in order, `k ≤ cap` copies, at most `b` in all. -/
def freshMS : List (ℕ × ℕ) → ℕ → List (List ℕ)
  | [], _ => [[]]
  | (m, c) :: L, b =>
    (List.range (Nat.succ (Nat.min c b))).flatMap fun k =>
      (freshMS L (Nat.sub b k)).map fun F => List.replicate k m ++ F

/-- The caps of the fresh masks: atoms not used up (at most four), then the outside colour. -/
def capsOf (sh : Sh) (nd : GNode) : List (ℕ × ℕ) :=
  (List.range' 1 15).map (fun m => (m, Nat.min 4 (Nat.sub (sh.na m) (gcnt nd.cols m)))) ++ [(0, 4)]

/-- **The list types of a free row**: old ids and fresh masks, three or four colours in all. -/
def ltypes (sh : Sh) (nd : GNode) : List (List ℕ × List ℕ) :=
  (idSubs nd.cols.length).flatMap fun S =>
    ((freshMS (capsOf sh nd) (Nat.sub 4 S.length)).filter fun F =>
      Nat.ble 3 (Nat.add S.length F.length)).map fun F => (S, F)

/-- The node with row `i` the explicit list of a type. -/
def lchild (nd : GNode) (i : ℕ) (ty : List ℕ × List ℕ) : GNode :=
  (nd.addCols ty.2).set i (some (ty.1 ++ List.range' nd.cols.length ty.2.length))

/-- **The classification at a general node**: every realization and filling that is not a bad
pattern has nonnegative seam vector at the twelve rays. -/
def GOK (B : Col) (nd : GNode) : Prop :=
  ∀ ρ, nd.Real B ρ → ∀ Y : Col, CardsIn 3 4 Y → ¬ Bad (gfill nd ρ Y) B →
    RaysOK (dvec (gfill nd ρ Y) B)

theorem gok_of_good {B : Col} {nd : GNode} {v : V5} (h : GGood B nd v) (hv : v.nonneg = true) :
    GOK B nd := by
  intro ρ hρ Y hY _
  apply raysOK_of_fam
  intro k w hw
  rw [dot_dvec]
  exact le_trans (V5.nonneg_get hv k) (h ρ hρ Y hY k w hw)


/-! ### Every actual list has a type -/

theorem mem_freshMS : ∀ (L : List (ℕ × ℕ)) (b : ℕ) (cnt : ℕ → ℕ), (∀ p ∈ L, cnt p.1 ≤ p.2) →
    (L.map fun p => cnt p.1).sum ≤ b →
    L.flatMap (fun p => List.replicate (cnt p.1) p.1) ∈ freshMS L b
  | [], b, cnt, _, _ => by simp [freshMS]
  | (m, c) :: L, b, cnt, hc, hs => by
    simp only [List.map_cons, List.sum_cons] at hs
    simp only [freshMS, List.flatMap_cons, List.mem_flatMap, List.mem_range, List.mem_map]
    refine ⟨cnt m, ?_, L.flatMap (fun p => List.replicate (cnt p.1) p.1), ?_, rfl⟩
    · have := hc (m, c) List.mem_cons_self
      simp only at this
      simp only [Nat.min_def]; split_ifs <;> omega
    · exact mem_freshMS L _ cnt (fun p hp => hc p (List.mem_cons_of_mem _ hp))
        (by simp only [Nat.sub_eq]; omega)

theorem capsOf_masks (sh : Sh) (nd : GNode) : (capsOf sh nd).map Prod.fst =
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0] := by
  simp [capsOf, List.range']

/-- **Coverage**: every actual list of three or four colours in a free row has a type. -/
theorem ltypes_cover {B : Col} {sh : Sh} (hB : ShapeOf B sh) {nd : GNode} {ρ : ℕ → ℕ}
    (hρ : nd.Real B ρ) {i : ℕ} (hi : i < 4) (hfree : nd.get i = none) (Y : Col)
    (hYi : 3 ≤ (rowC Y i).card ∧ (rowC Y i).card ≤ 4) :
    ∃ ty ∈ ltypes sh nd, ∃ ρ', (lchild nd i ty).Real B ρ' ∧
      gfill (lchild nd i ty) ρ' Y = gfill nd ρ Y := by
  set n := nd.cols.length
  set Yi := rowC Y i
  obtain ⟨hmk, hinj, hrows⟩ := hρ
  -- the old ids of the list
  set S := (List.range n).filter fun t => decide (ρ t ∈ Yi)
  have hSsub : S.Sublist (List.range n) := List.filter_sublist
  have hSnd : S.Nodup := hSsub.nodup (List.nodup_range)
  have hSlt : ∀ t ∈ S, t < n := fun t ht => List.mem_range.mp (hSsub.subset ht)
  have hSimg : (S.map ρ).toFinset = Yi.filter (fun x => x ∈ gcolSet nd ρ) := by
    ext x
    simp only [List.mem_toFinset, List.mem_map, S, List.mem_filter, List.mem_range,
      decide_eq_true_eq, Finset.mem_filter, gcolSet, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨t, ⟨ht, hx⟩, rfl⟩; exact ⟨hx, t, ht, rfl⟩
    · rintro ⟨hx, t, ht, rfl⟩; exact ⟨t, ⟨ht, hx⟩, rfl⟩
  have hSlen : S.length = (Yi.filter (fun x => x ∈ gcolSet nd ρ)).card := by
    rw [← hSimg, List.toFinset_card_of_nodup]
    · simp
    · exact List.Nodup.map_on (fun a ha b hb e => hinj a (hSlt a ha) b (hSlt b hb) e) hSnd
  -- the fresh colours, by mask
  set Fset := Yi.filter fun x => x ∉ gcolSet nd ρ
  let blk : ℕ → List ℕ := fun m => (Fset.filter fun x => mv B x = m).toList
  set Fl := (capsOf sh nd).flatMap fun p => blk p.1
  set F := Fl.map (mv B)
  have hcapsm : ∀ m < 16, ∃ p ∈ capsOf sh nd, p.1 = m := by
    intro m hm
    have : m ∈ (capsOf sh nd).map Prod.fst := by rw [capsOf_masks]; interval_cases m <;> simp
    obtain ⟨p, hp, e⟩ := List.mem_map.mp this
    exact ⟨p, hp, e⟩
  have hcapsnd : ((capsOf sh nd).map Prod.fst).Nodup := by rw [capsOf_masks]; decide
  have hFl_mem : ∀ x, x ∈ Fl ↔ x ∈ Fset := by
    intro x
    simp only [Fl, List.mem_flatMap, blk, Finset.mem_toList, Finset.mem_filter]
    constructor
    · rintro ⟨p, -, hx, -⟩; exact hx
    · intro hx
      obtain ⟨p, hp, e⟩ := hcapsm (mv B x) (mv_lt B x)
      exact ⟨p, hp, hx, e.symm⟩
  have hFl_nd : Fl.Nodup := by
    refine List.nodup_flatMap.mpr ⟨fun p _ => Finset.nodup_toList _, ?_⟩
    have : ((capsOf sh nd).map Prod.fst).Pairwise (fun m m' => (blk m).Disjoint (blk m')) := by
      refine List.Pairwise.imp_of_mem ?_ hcapsnd
      intro m m' _ _ hne x hx hx'
      simp only [blk, Finset.mem_toList, Finset.mem_filter] at hx hx'
      exact hne (hx.2.symm.trans hx'.2)
    rw [List.pairwise_map] at this
    exact this.imp fun h => h
  have hFl_toFinset : Fl.toFinset = Fset := by ext x; rw [List.mem_toFinset]; exact hFl_mem x
  have hFlen : Fl.length = Fset.card := by
    rw [← hFl_toFinset, List.toFinset_card_of_nodup hFl_nd]
  have hF : F = (capsOf sh nd).flatMap fun p => List.replicate (blk p.1).length p.1 := by
    simp only [F, Fl, List.map_flatMap]
    congr 1; funext p
    apply List.eq_replicate_iff.mpr
    refine ⟨by simp, fun m hm => ?_⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
    simp only [blk, Finset.mem_toList, Finset.mem_filter] at hx
    exact hx.2
  -- the type
  have hcard : (Yi.filter (fun x => x ∈ gcolSet nd ρ)).card + Fset.card = Yi.card :=
    Finset.card_filter_add_card_filter_not (s := Yi) (fun x => x ∈ gcolSet nd ρ)
  set ty : List ℕ × List ℕ := (S, F)
  have hty : ty ∈ ltypes sh nd := by
    simp only [ltypes, List.mem_flatMap, List.mem_map, List.mem_filter]
    refine ⟨S, ?_, F, ⟨?_, ?_⟩, rfl⟩
    · simp only [idSubs, List.mem_filter, List.mem_sublists, Nat.ble_eq]
      exact ⟨hSsub, by omega⟩
    · rw [hF]
      apply mem_freshMS (capsOf sh nd) _ (fun m => (blk m).length)
      · intro p hp
        simp only [blk, Finset.length_toList]
        simp only [capsOf, List.mem_append, List.mem_map, List.mem_range'_1,
          List.mem_singleton] at hp
        rcases hp with ⟨m, hm, rfl⟩ | rfl
        · simp only
          have h1 := gfresh_count hB ⟨hmk, hinj, hrows⟩ Yi (m := m) (by omega) (by omega)
          have h2 : (Fset.filter fun x => mv B x = m).card
              ≤ (Yi.filter fun x => mv B x = m ∧ x ∉ gcolSet nd ρ).card := by
            apply Finset.card_le_card; intro x hx
            simp only [Fset, Finset.mem_filter] at hx ⊢; exact ⟨hx.1.1, hx.2, hx.1.2⟩
          have h3 : (Fset.filter fun x => mv B x = m).card ≤ 4 :=
            (Finset.card_le_card (fun x hx => (Finset.mem_filter.mp
              (Finset.mem_filter.mp hx).1).1)).trans hYi.2
          simp only [Nat.min_def, Nat.sub_eq]; split_ifs <;> omega
        · simp only
          exact (Finset.card_le_card (fun x hx => (Finset.mem_filter.mp
            (Finset.mem_filter.mp hx).1).1)).trans hYi.2
      · have : ((capsOf sh nd).map fun p => (blk p.1).length).sum = Fl.length := by
          simp [Fl, List.length_flatMap]
        rw [this, hFlen, Nat.sub_eq]; omega
    · rw [Nat.ble_eq, Nat.add_eq, List.length_map, hSlen, hFlen]; omega
  -- the realization
  set ρ' : ℕ → ℕ := fun t => if t < n then ρ t else Fl.getD (t - n) 0
  have hFlF : F.length = Fl.length := List.length_map _
  have hlo : ∀ t < n, ρ' t = ρ t := fun t ht => if_pos ht
  have hhi : ∀ k (hk : k < Fl.length), ρ' (n + k) = Fl[k] := by
    intro k hk
    simp only [ρ', show ¬ (n + k < n) by omega, if_false, show n + k - n = k by omega]
    rw [List.getD_eq_getElem _ _ hk]
  have hFlout : ∀ x ∈ Fl, x ∉ gcolSet nd ρ := fun x hx =>
    (Finset.mem_filter.mp ((hFl_mem x).mp hx)).2
  have hrange : (List.range' n F.length).map ρ' = Fl := by
    apply List.ext_getElem
    · simp [hFlF]
    · intro k h1 h2
      simp only [List.getElem_map, List.getElem_range', one_mul]
      exact hhi k h2
  have hcols : (lchild nd i ty).cols = nd.cols ++ F := by
    simp only [lchild, GNode.cols_set, GNode.addCols]; rfl
  have hget : ∀ j < 4, (lchild nd i ty).get j =
      if j = i then some (S ++ List.range' n F.length) else nd.get j := by
    intro j hj
    split_ifs with hji
    · subst hji; exact GNode.get_set_same _ hj _
    · simp only [lchild]; rw [GNode.get_set_ne _ hi hj hji, GNode.get_addCols]
  refine ⟨ty, hty, ρ', ⟨?_, ?_, ?_⟩, ?_⟩
  · -- masks
    intro t ht
    rw [hcols, List.length_append] at ht
    rw [hcols]
    by_cases htn : t < n
    · rw [hlo t htn, List.getD_append _ _ _ _ htn]; exact hmk t htn
    · obtain ⟨k, rfl⟩ : ∃ k, t = n + k := ⟨t - n, by omega⟩
      have hk : k < Fl.length := by omega
      rw [hhi k hk, List.getD_append_right _ _ _ _ (by omega), show n + k - n = k by omega,
        List.getD_eq_getElem _ _ (by omega)]
      simp [F]
  · -- distinct colours
    intro t ht t' ht' e
    rw [hcols, List.length_append] at ht ht'
    by_cases htn : t < n <;> by_cases htn' : t' < n
    · rw [hlo t htn, hlo t' htn'] at e; exact hinj t htn t' htn' e
    · obtain ⟨k, rfl⟩ : ∃ k, t' = n + k := ⟨t' - n, by omega⟩
      rw [hlo t htn, hhi k (by omega)] at e
      exact absurd (Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr htn, e⟩)
        (hFlout _ (List.getElem_mem _))
    · obtain ⟨k, rfl⟩ : ∃ k, t = n + k := ⟨t - n, by omega⟩
      rw [hhi k (by omega), hlo t' htn'] at e
      exact absurd (Finset.mem_image.mpr ⟨t', Finset.mem_range.mpr htn', e.symm⟩)
        (hFlout _ (List.getElem_mem _))
    · obtain ⟨k, rfl⟩ : ∃ k, t = n + k := ⟨t - n, by omega⟩
      obtain ⟨k', rfl⟩ : ∃ k', t' = n + k' := ⟨t' - n, by omega⟩
      rw [hhi k (by omega), hhi k' (by omega)] at e
      have := (List.Nodup.getElem_inj_iff hFl_nd).mp e
      omega
  · -- rows
    intro j hj L e
    rw [hcols, List.length_append]
    rw [hget j hj] at e
    split_ifs at e with hji
    · simp only [Option.some.injEq] at e; subst e
      refine ⟨fun t ht => ?_, ?_⟩
      · rcases List.mem_append.mp ht with ht | ht
        · have := hSlt t ht; omega
        · have := List.mem_range'_1.mp ht; omega
      · refine List.nodup_append.mpr ⟨hSnd, List.nodup_range', ?_⟩
        intro a ha b hb hab; subst hab
        have := hSlt a ha; have := (List.mem_range'_1.mp hb).1; omega
    · obtain ⟨h1, h2⟩ := hrows j hj L e
      exact ⟨fun t ht => by have := h1 t ht; omega, h2⟩
  · -- the column is unchanged
    have hrow : ∀ j < 4, rowC (gfill (lchild nd i ty) ρ' Y) j = rowC (gfill nd ρ Y) j := by
      intro j hj
      rw [rowC_gfill _ _ _ hj, rowC_gfill _ _ _ hj, hget j hj]
      split_ifs with hji
      · subst hji
        rw [hfree]
        simp only [gfr, List.map_append, List.toFinset_append]
        rw [hrange, hFl_toFinset]
        have hS' : S.map ρ' = S.map ρ := List.map_congr_left fun t ht => hlo t (hSlt t ht)
        rw [hS', hSimg]
        ext x; simp only [Finset.mem_union, Finset.mem_filter, Fset]; tauto
      · cases hg : nd.get j with
        | none => rfl
        | some L =>
          have hL := (hrows j hj L hg).1
          simp only [gfr]
          congr 1
          exact List.map_congr_left fun t ht => hlo t (hL t ht)
    have e0 := hrow 0 (by norm_num)
    have e1 := hrow 1 (by norm_num)
    have e2 := hrow 2 (by norm_num)
    have e3 := hrow 3 (by norm_num)
    simp only [rowC] at e0 e1 e2 e3
    exact Prod.ext e0 (Prod.ext e1 (Prod.ext e2 e3))


/-! ### Bad patterns -/

/-- Two id lists with the same elements. -/
def sameIds (L M : List ℕ) : Bool := Nat.beq L.length M.length && L.all fun a => M.contains a

theorem toFinset_of_sameIds {L M : List ℕ} (hL : L.Nodup) (hM : M.Nodup)
    (h : sameIds L M = true) (ρ : ℕ → ℕ) : (L.map ρ).toFinset = (M.map ρ).toFinset := by
  simp only [sameIds, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, List.contains_iff_mem] at h
  have hsub : L.toFinset ⊆ M.toFinset := fun a ha =>
    List.mem_toFinset.mpr (h.2 a (List.mem_toFinset.mp ha))
  have heq : L.toFinset = M.toFinset := Finset.eq_of_subset_of_card_le hsub (by
    rw [List.toFinset_card_of_nodup hL, List.toFinset_card_of_nodup hM, h.1])
  ext x
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, List.mem_toFinset.mp (heq ▸ List.mem_toFinset.mpr ha), rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, List.mem_toFinset.mp (heq.symm ▸ List.mem_toFinset.mpr ha), rfl⟩

theorem testBit_mIdx : ∀ a b c d : Bool,
    Nat.testBit (mIdx (a, b, c, d)) 0 = a ∧ Nat.testBit (mIdx (a, b, c, d)) 1 = b ∧
      Nat.testBit (mIdx (a, b, c, d)) 2 = c ∧ Nat.testBit (mIdx (a, b, c, d)) 3 = d := by decide

theorem mem_rowB (B : Col) (c : ℕ) : ∀ j < 4, (c ∈ rowC B j ↔ Nat.testBit (mv B c) j = true) := by
  intro j hj
  obtain ⟨h0, h1, h2, h3⟩ := testBit_mIdx (decide (c ∈ B.1)) (decide (c ∈ B.2.1))
    (decide (c ∈ B.2.2.1)) (decide (c ∈ B.2.2.2))
  simp only [mv, memv]
  interval_cases j
  · rw [h0]; simp [rowC]
  · rw [h1]; simp [rowC]
  · rw [h2]; simp [rowC]
  · rw [h3]; simp [rowC]

theorem atom_full {B : Col} {sh : Sh} (hB : ShapeOf B sh) {m : ℕ} (h0 : 0 < m) (h16 : m < 16)
    (S : Finset ℕ) (hS : ∀ c ∈ S, mv B c = m) (hc : sh.na m ≤ S.card) : atomN B m = S := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro c hcS; exact mem_atomN (by omega) (hS c hcS)
  · rw [hB.2.2 m h0 h16]; exact hc

theorem mv_support {B : Col} {sh : Sh} (hB : ShapeOf B sh) (c : ℕ) :
    mv B c = 0 ∨ 0 < sh.na (mv B c) := by
  by_cases h : mv B c = 0
  · exact Or.inl h
  · right
    have h16 := mv_lt B c
    rw [← hB.2.2 _ (Nat.pos_of_ne_zero h) h16]
    exact Finset.card_pos.mpr ⟨c, mem_atomN h rfl⟩

/-- The edge shape: atoms `15 : 3`, `7 : 1`, `8 : 1`. -/
def edgeShape (sh : Sh) : Bool :=
  Nat.beq (sh.na 15) 3 && Nat.beq (sh.na 7) 1 && Nat.beq (sh.na 8) 1 &&
    [1, 2, 3, 4, 5, 6, 9, 10, 11, 12, 13, 14].all fun m => Nat.beq (sh.na m) 0

/-- The central shape: atoms `15 : 3`, `3 : 1`, `12 : 1`. -/
def centShape (sh : Sh) : Bool :=
  Nat.beq (sh.na 15) 3 && Nat.beq (sh.na 3) 1 && Nat.beq (sh.na 12) 1 &&
    [1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14].all fun m => Nat.beq (sh.na m) 0

/-- Ids of the table with given masks, three of them distinct. -/
def idsOK (nd : GNode) (x y z a b mA mB : ℕ) : Bool :=
  Nat.blt x nd.cols.length && Nat.blt y nd.cols.length && Nat.blt z nd.cols.length &&
    Nat.blt a nd.cols.length && Nat.blt b nd.cols.length &&
    Nat.beq (nd.cols.getD x 0) 15 && Nat.beq (nd.cols.getD y 0) 15 &&
    Nat.beq (nd.cols.getD z 0) 15 && Nat.beq (nd.cols.getD a 0) mA &&
    Nat.beq (nd.cols.getD b 0) mB && !(Nat.beq x y) && !(Nat.beq x z) && !(Nat.beq y z)

/-- **A forward edge pattern** (E1–E3) with ids `x y z a b`. -/
def badFCheck (sh : Sh) (nd : GNode) (x y z a b : ℕ) : Bool :=
  edgeShape sh && idsOK nd x y z a b 7 8 &&
    match nd.r0, nd.r1, nd.r2, nd.r3 with
    | some L0, some L1, some L2, some L3 =>
      sameIds L1 [x, y, z] && sameIds L2 [x, y, a] && sameIds L3 [x, y, b] &&
        (sameIds L0 [x, y, a] || sameIds L0 [y, z, a] || sameIds L0 [x, z, a] ||
          sameIds L0 [x, y, z, a])
    | _, _, _, _ => false

/-- **A central pattern** (M) with ids `x y z a b`. -/
def badMCheck (sh : Sh) (nd : GNode) (x y z a b : ℕ) : Bool :=
  centShape sh && idsOK nd x y z a b 3 12 &&
    match nd.r0, nd.r1, nd.r2, nd.r3 with
    | some L0, some L1, some L2, some L3 =>
      sameIds L0 [x, y, z] && sameIds L1 [x, y, a] && sameIds L2 [x, y, b] && sameIds L3 [x, y, z]
    | _, _, _, _ => false


theorem rowB_of_support {B : Col} {U : Finset ℕ} (hU : ∀ c, mv B c ≠ 0 → c ∈ U) {j : ℕ}
    (hj : j < 4) : rowC B j = U.filter fun c => Nat.testBit (mv B c) j = true := by
  ext c
  rw [mem_rowB B c j hj, Finset.mem_filter]
  constructor
  · intro h
    refine ⟨hU c fun h0 => ?_, h⟩
    rw [h0, Nat.zero_testBit] at h; exact absurd h (by decide)
  · exact fun h => h.2

/-- The colours of the five named ids, with their masks. -/
theorem five_facts {B : Col} {sh : Sh} (hB : ShapeOf B sh) {nd : GNode} {ρ : ℕ → ℕ}
    (hρ : nd.Real B ρ) {x y z a b mA mB : ℕ} (h : idsOK nd x y z a b mA mB = true) :
    mv B (ρ x) = 15 ∧ mv B (ρ y) = 15 ∧ mv B (ρ z) = 15 ∧ mv B (ρ a) = mA ∧ mv B (ρ b) = mB ∧
      ρ x ≠ ρ y ∧ ρ x ≠ ρ z ∧ ρ y ≠ ρ z ∧ x < nd.cols.length ∧ y < nd.cols.length ∧
      z < nd.cols.length ∧ a < nd.cols.length ∧ b < nd.cols.length ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  unfold idsOK at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hx, hy⟩, hz⟩, ha⟩, hb⟩, mx⟩, my⟩, mz⟩, ma⟩, mb⟩, nxy⟩, nxz⟩, nyz⟩ := h
  rw [Nat.blt_eq] at hx hy hz ha hb
  rw [Nat.beq_eq] at mx my mz ma mb
  have dxy := ne_of_beq_false nxy
  have dxz := ne_of_beq_false nxz
  have dyz := ne_of_beq_false nyz
  have e := fun t ht => hρ.1 t ht
  exact ⟨(e x hx).trans mx, (e y hy).trans my, (e z hz).trans mz, (e a ha).trans ma,
    (e b hb).trans mb, fun h => dxy (hρ.2.1 x hx y hy h), fun h => dxz (hρ.2.1 x hx z hz h),
    fun h => dyz (hρ.2.1 y hy z hz h), hx, hy, hz, ha, hb, dxy, dxz, dyz⟩


theorem nodup3 {x y z : ℕ} (h1 : x ≠ y) (h2 : x ≠ z) (h3 : y ≠ z) : [x, y, z].Nodup := by
  simp [h1, h2, h3]

theorem nodup4 {x y z a : ℕ} (h1 : x ≠ y) (h2 : x ≠ z) (h3 : y ≠ z) (h4 : x ≠ a) (h5 : y ≠ a)
    (h6 : z ≠ a) : [x, y, z, a].Nodup := by
  simp [h1, h2, h3, h4, h5, h6]

theorem rowList {B : Col} {nd : GNode} {ρ : ℕ → ℕ} (hρ : nd.Real B ρ) {j : ℕ} (hj : j < 4)
    {L M : List ℕ} (e : nd.get j = some L) (hM : M.Nodup) (h : sameIds L M = true) :
    (L.map ρ).toFinset = (M.map ρ).toFinset :=
  toFinset_of_sameIds (hρ.2.2 j hj L e).2 hM h ρ

/-- **A checked forward edge pattern is bad.** -/
theorem badF_of_check {B : Col} {sh : Sh} (hB : ShapeOf B sh) {nd : GNode} {x y z a b : ℕ}
    (h : badFCheck sh nd x y z a b = true) {ρ : ℕ → ℕ} (hρ : nd.Real B ρ) (Y : Col) :
    Bad (gfill nd ρ Y) B := by
  unfold badFCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hsh, hids⟩, hrows⟩ := h
  obtain ⟨mx, my, mz, ma, mb, dxy, dxz, dyz, -, -, -, -, -, ixy, ixz, iyz⟩ := five_facts hB hρ hids
  unfold edgeShape at hsh
  simp only [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, List.mem_cons, List.mem_nil_iff,
    or_false, forall_eq_or_imp, forall_eq] at hsh
  obtain ⟨⟨⟨n15, n7⟩, n8⟩, z1, z2, z3, z4, z5, z6, z9, z10, z11, z12, z13, z14⟩ := hsh
  -- the masks of all colours
  have hmask : ∀ c, mv B c = 0 ∨ mv B c = 7 ∨ mv B c = 8 ∨ mv B c = 15 := by
    intro c
    rcases mv_support hB c with h0 | hpos
    · exact Or.inl h0
    · have h16 := mv_lt B c
      interval_cases hm : mv B c <;> simp_all
  have dxa : ρ x ≠ ρ a := fun e => by rw [← e] at ma; omega
  have dya : ρ y ≠ ρ a := fun e => by rw [← e] at ma; omega
  have dza : ρ z ≠ ρ a := fun e => by rw [← e] at ma; omega
  have dxb : ρ x ≠ ρ b := fun e => by rw [← e] at mb; omega
  have dyb : ρ y ≠ ρ b := fun e => by rw [← e] at mb; omega
  have dzb : ρ z ≠ ρ b := fun e => by rw [← e] at mb; omega
  have dab : ρ a ≠ ρ b := fun e => by rw [← e] at mb; omega
  -- the atoms
  have a15 : atomN B 15 = {ρ x, ρ y, ρ z} := atom_full hB (by norm_num) (by norm_num) _
    (by intro c hc; simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with rfl | rfl | rfl <;> assumption)
    (by rw [n15, card3 dxy dxz dyz])
  have a7 : atomN B 7 = {ρ a} := atom_full hB (by norm_num) (by norm_num) _
    (by intro c hc; rw [Finset.mem_singleton] at hc; rw [hc]; exact ma) (by simp [n7])
  have a8 : atomN B 8 = {ρ b} := atom_full hB (by norm_num) (by norm_num) _
    (by intro c hc; rw [Finset.mem_singleton] at hc; rw [hc]; exact mb) (by simp [n8])
  have hsupp : ∀ c, mv B c ≠ 0 → c ∈ ({ρ x, ρ y, ρ z, ρ a, ρ b} : Finset ℕ) := by
    intro c hc
    have hmem : c ∈ atomN B (mv B c) := mem_atomN hc rfl
    rcases hmask c with h | h | h | h
    · exact absurd h hc
    · rw [h, a7] at hmem; simp [Finset.mem_singleton.mp hmem]
    · rw [h, a8] at hmem; simp [Finset.mem_singleton.mp hmem]
    · rw [h, a15] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
      rcases hmem with h' | h' | h' <;> simp [h']
  have hB' : B = edgeB (ρ x) (ρ y) (ρ z) (ρ a) (ρ b) := by
    obtain ⟨B1, B2, B3, B4⟩ := B
    have r0 := rowB_of_support hsupp (j := 0) (by norm_num)
    have r1 := rowB_of_support hsupp (j := 1) (by norm_num)
    have r2 := rowB_of_support hsupp (j := 2) (by norm_num)
    have r3 := rowB_of_support hsupp (j := 3) (by norm_num)
    simp only [rowC] at r0 r1 r2 r3
    have bits : Nat.testBit 15 0 = true ∧ Nat.testBit 15 1 = true ∧ Nat.testBit 15 2 = true ∧
        Nat.testBit 15 3 = true ∧ Nat.testBit 7 0 = true ∧ Nat.testBit 7 1 = true ∧
        Nat.testBit 7 2 = true ∧ Nat.testBit 7 3 = false ∧ Nat.testBit 8 0 = false ∧
        Nat.testBit 8 1 = false ∧ Nat.testBit 8 2 = false ∧ Nat.testBit 8 3 = true := by decide
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := bits
    simp only [Finset.filter_insert, Finset.filter_singleton, mx, my, mz, ma, mb, b1, b2, b3, b4,
      b5, b6, b7, b8, b9, b10, b11, b12, if_true, if_false, Bool.false_eq_true] at r0 r1 r2 r3
    simp only [edgeB, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [r0]; try simp
    · rw [r1]; try simp
    · rw [r2]; try simp
    · rw [r3]; try simp
  have ixa : x ≠ a := fun e => dxa (by rw [e])
  have iya : y ≠ a := fun e => dya (by rw [e])
  have iza : z ≠ a := fun e => dza (by rw [e])
  have ixb : x ≠ b := fun e => dxb (by rw [e])
  have iyb : y ≠ b := fun e => dyb (by rw [e])
  obtain ⟨cols, q0, q1, q2, q3⟩ := nd
  simp only at hrows
  split at hrows
  · next L0 L1 L2 L3 =>
    simp only [Bool.and_eq_true, Bool.or_eq_true] at hrows
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h0⟩ := hrows
    have f1 := rowList hρ (j := 1) (by norm_num) rfl (nodup3 ixy ixz iyz) h1
    have f2 := rowList hρ (j := 2) (by norm_num) rfl (nodup3 ixy ixa iya) h2
    have f3 := rowList hρ (j := 3) (by norm_num) rfl (nodup3 ixy ixb iyb) h3
    refine Or.inl ⟨ρ x, ρ y, ρ z, ρ a, ρ b,
      ⟨dxy, dxz, dyz, Ne.symm dxa, Ne.symm dya, Ne.symm dza, Ne.symm dxb, Ne.symm dyb, Ne.symm dzb,
        dab⟩, hB', ?_, ?_, ?_, ?_⟩
    · simp only [gfill, gfr]; rw [f1]; simp
    · simp only [gfill, gfr]; rw [f2]; simp
    · simp only [gfill, gfr]; rw [f3]; simp
    · simp only [gfill, gfr]
      rcases h0 with ((h0 | h0) | h0) | h0
      · left; rw [rowList hρ (j := 0) (by norm_num) rfl (nodup3 ixy ixa iya) h0]; simp
      · right; left; rw [rowList hρ (j := 0) (by norm_num) rfl (nodup3 iyz iya iza) h0]; simp
      · right; right; left; rw [rowList hρ (j := 0) (by norm_num) rfl (nodup3 ixz ixa iza) h0]; simp
      · right; right; right
        rw [rowList hρ (j := 0) (by norm_num) rfl (nodup4 ixy ixz iyz ixa iya iza) h0]; simp
  · exact absurd hrows (by simp)


/-- **A checked central pattern is bad.** -/
theorem badM_of_check {B : Col} {sh : Sh} (hB : ShapeOf B sh) {nd : GNode} {x y z a b : ℕ}
    (h : badMCheck sh nd x y z a b = true) {ρ : ℕ → ℕ} (hρ : nd.Real B ρ) (Y : Col) :
    Bad (gfill nd ρ Y) B := by
  unfold badMCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hsh, hids⟩, hrows⟩ := h
  obtain ⟨mx, my, mz, ma, mb, dxy, dxz, dyz, -, -, -, -, -, ixy, ixz, iyz⟩ := five_facts hB hρ hids
  unfold centShape at hsh
  simp only [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, List.mem_cons, List.mem_nil_iff,
    or_false, forall_eq_or_imp, forall_eq] at hsh
  obtain ⟨⟨⟨n15, n3⟩, n12⟩, z1, z2, z4, z5, z6, z7, z8, z9, z10, z11, z13, z14⟩ := hsh
  have hmask : ∀ c, mv B c = 0 ∨ mv B c = 3 ∨ mv B c = 12 ∨ mv B c = 15 := by
    intro c
    rcases mv_support hB c with h0 | hpos
    · exact Or.inl h0
    · have h16 := mv_lt B c
      interval_cases hm : mv B c <;> simp_all
  have dxa : ρ x ≠ ρ a := fun e => by rw [← e] at ma; omega
  have dya : ρ y ≠ ρ a := fun e => by rw [← e] at ma; omega
  have dza : ρ z ≠ ρ a := fun e => by rw [← e] at ma; omega
  have dxb : ρ x ≠ ρ b := fun e => by rw [← e] at mb; omega
  have dyb : ρ y ≠ ρ b := fun e => by rw [← e] at mb; omega
  have dzb : ρ z ≠ ρ b := fun e => by rw [← e] at mb; omega
  have dab : ρ a ≠ ρ b := fun e => by rw [← e] at mb; omega
  have a15 : atomN B 15 = {ρ x, ρ y, ρ z} := atom_full hB (by norm_num) (by norm_num) _
    (by intro c hc; simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with rfl | rfl | rfl <;> assumption)
    (by rw [n15, card3 dxy dxz dyz])
  have a3 : atomN B 3 = {ρ a} := atom_full hB (by norm_num) (by norm_num) _
    (by intro c hc; rw [Finset.mem_singleton] at hc; rw [hc]; exact ma) (by simp [n3])
  have a12 : atomN B 12 = {ρ b} := atom_full hB (by norm_num) (by norm_num) _
    (by intro c hc; rw [Finset.mem_singleton] at hc; rw [hc]; exact mb) (by simp [n12])
  have hsupp : ∀ c, mv B c ≠ 0 → c ∈ ({ρ x, ρ y, ρ z, ρ a, ρ b} : Finset ℕ) := by
    intro c hc
    have hmem : c ∈ atomN B (mv B c) := mem_atomN hc rfl
    rcases hmask c with h | h | h | h
    · exact absurd h hc
    · rw [h, a3] at hmem; simp [Finset.mem_singleton.mp hmem]
    · rw [h, a12] at hmem; simp [Finset.mem_singleton.mp hmem]
    · rw [h, a15] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
      rcases hmem with h' | h' | h' <;> simp [h']
  have hB' : B = centB (ρ x) (ρ y) (ρ z) (ρ a) (ρ b) := by
    obtain ⟨B1, B2, B3, B4⟩ := B
    have r0 := rowB_of_support hsupp (j := 0) (by norm_num)
    have r1 := rowB_of_support hsupp (j := 1) (by norm_num)
    have r2 := rowB_of_support hsupp (j := 2) (by norm_num)
    have r3 := rowB_of_support hsupp (j := 3) (by norm_num)
    simp only [rowC] at r0 r1 r2 r3
    have bits : Nat.testBit 15 0 = true ∧ Nat.testBit 15 1 = true ∧ Nat.testBit 15 2 = true ∧
        Nat.testBit 15 3 = true ∧ Nat.testBit 3 0 = true ∧ Nat.testBit 3 1 = true ∧
        Nat.testBit 3 2 = false ∧ Nat.testBit 3 3 = false ∧ Nat.testBit 12 0 = false ∧
        Nat.testBit 12 1 = false ∧ Nat.testBit 12 2 = true ∧ Nat.testBit 12 3 = true := by decide
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := bits
    simp only [Finset.filter_insert, Finset.filter_singleton, mx, my, mz, ma, mb, b1, b2, b3, b4,
      b5, b6, b7, b8, b9, b10, b11, b12, if_true, if_false, Bool.false_eq_true] at r0 r1 r2 r3
    simp only [centB, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [r0]; try simp
    · rw [r1]; try simp
    · rw [r2]; try simp
    · rw [r3]; try simp
  have ixa : x ≠ a := fun e => dxa (by rw [e])
  have iya : y ≠ a := fun e => dya (by rw [e])
  have ixb : x ≠ b := fun e => dxb (by rw [e])
  have iyb : y ≠ b := fun e => dyb (by rw [e])
  obtain ⟨cols, q0, q1, q2, q3⟩ := nd
  simp only at hrows
  split at hrows
  · next L0 L1 L2 L3 =>
    simp only [Bool.and_eq_true] at hrows
    obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := hrows
    have f0 := rowList hρ (j := 0) (by norm_num) rfl (nodup3 ixy ixz iyz) h0
    have f1 := rowList hρ (j := 1) (by norm_num) rfl (nodup3 ixy ixa iya) h1
    have f2 := rowList hρ (j := 2) (by norm_num) rfl (nodup3 ixy ixb iyb) h2
    have f3 := rowList hρ (j := 3) (by norm_num) rfl (nodup3 ixy ixz iyz) h3
    refine Or.inr (Or.inr ⟨ρ x, ρ y, ρ z, ρ a, ρ b,
      ⟨dxy, dxz, dyz, Ne.symm dxa, Ne.symm dya, Ne.symm dza, Ne.symm dxb, Ne.symm dyb, Ne.symm dzb,
        dab⟩, hB', ?_⟩)
    simp only [gfill, gfr]
    rw [f0, f1, f2, f3]
    simp
  · exact absurd hrows (by simp)

/-! ### The branching trees -/

mutual
/-- A certificate tree of explicit-list branching. -/
inductive GAT where
  | num : GCT → GAT
  | split : ℕ → GATL → GAT
  | badF : ℕ → ℕ → ℕ → ℕ → ℕ → GAT
  | badM : ℕ → ℕ → ℕ → ℕ → ℕ → GAT
  | given : ℕ → GAT
/-- A list of branching trees. -/
inductive GATL where
  | nil : GATL
  | cons : GAT → GATL → GATL
end

/-- Equality of optional id lists, as a check. -/
def olBEq : Option (List ℕ) → Option (List ℕ) → Bool
  | none, none => true
  | some L, some M => L == M
  | _, _ => false

theorem eq_of_olBEq {a b : Option (List ℕ)} (h : olBEq a b = true) : a = b := by
  rcases a with _ | L <;> rcases b with _ | M <;> simp_all [olBEq]

/-- Equality of general nodes, as a check. -/
def gnodeBEq (a b : GNode) : Bool :=
  (a.cols == b.cols) && olBEq a.r0 b.r0 && olBEq a.r1 b.r1 && olBEq a.r2 b.r2 && olBEq a.r3 b.r3

theorem eq_of_gnodeBEq {a b : GNode} (h : gnodeBEq a b = true) : a = b := by
  obtain ⟨c, a0, a1, a2, a3⟩ := a
  obtain ⟨c', b0, b1, b2, b3⟩ := b
  simp only [gnodeBEq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hc, h0⟩, h1⟩, h2⟩, h3⟩ := h
  rw [hc, eq_of_olBEq h0, eq_of_olBEq h1, eq_of_olBEq h2, eq_of_olBEq h3]

/-- The classification at a node, for every column of the shape. -/
def GOKSh (sh : Sh) (nd : GNode) : Prop := ∀ B : Col, ShapeOf B sh → GOK B nd

mutual
/-- **The check of a branching tree**; `given idx` refers to a node of `gs` proved separately. -/
def evalGAT (sh : Sh) (tab : BTab) (gs : List GNode) (nd : GNode) : GAT → Bool
  | .num t =>
    match evalGCT sh tab nd t with
    | some v => v.nonneg
    | none => false
  | .split i ks => Nat.blt i 4 && (nd.get i).isNone && evalGATL sh tab gs nd i (ltypes sh nd) ks
  | .badF x y z a b => badFCheck sh nd x y z a b
  | .badM x y z a b => badMCheck sh nd x y z a b
  | .given idx =>
    match gs[idx]? with
    | some nd' => gnodeBEq nd' nd
    | none => false
/-- The check of the list children. -/
def evalGATL (sh : Sh) (tab : BTab) (gs : List GNode) (nd : GNode) (i : ℕ)
    (tys : List (List ℕ × List ℕ)) : GATL → Bool
  | .nil => tys.isEmpty
  | .cons k ks =>
    match tys with
    | [] => false
    | ty :: tys' => evalGAT sh tab gs (lchild nd i ty) k && evalGATL sh tab gs nd i tys' ks
end

mutual
/-- **Soundness of a branching tree.** -/
theorem evalGAT_sound {B : Col} {sh : Sh} (hB : ShapeOf B sh) {tab : BTab}
    (htab : BTabOK sh tab) {gs : List GNode} (hgs : ∀ nd ∈ gs, GOK B nd) :
    ∀ (T : GAT) (nd : GNode), evalGAT sh tab gs nd T = true → GOK B nd
  | .num t, nd, h => by
    simp only [evalGAT] at h
    split at h
    · next v hv => exact gok_of_good (evalGCT_sound hB htab t nd v hv) h
    · exact absurd h (by simp)
  | .split i ks, nd, h => by
    simp only [evalGAT, Bool.and_eq_true, Nat.blt_eq, Option.isNone_iff_eq_none] at h
    obtain ⟨⟨hi, hfree⟩, hk⟩ := h
    intro ρ hρ Y hY hbad
    have hYi : 3 ≤ (rowC Y i).card ∧ (rowC Y i).card ≤ 4 := by
      obtain ⟨c1, c2, c3, c4⟩ := hY
      interval_cases i
      · exact c1
      · exact c2
      · exact c3
      · exact c4
    obtain ⟨ty, hty, ρ', hreal, hfill⟩ := ltypes_cover hB hρ hi hfree Y hYi
    have hchild := evalGATL_sound hB htab hgs ks nd i _ hk ty hty
    have := hchild ρ' hreal Y hY (by rw [hfill]; exact hbad)
    rwa [hfill] at this
  | .badF x y z a b, nd, h => by
    intro ρ hρ Y _ hbad
    exact absurd (badF_of_check hB h hρ Y) hbad
  | .badM x y z a b, nd, h => by
    intro ρ hρ Y _ hbad
    exact absurd (badM_of_check hB h hρ Y) hbad
  | .given idx, nd, h => by
    simp only [evalGAT] at h
    split at h
    · next nd' hn =>
      rw [← eq_of_gnodeBEq h]
      exact hgs nd' (List.mem_of_getElem? hn)
    · exact absurd h (by simp)
/-- Soundness of the list children. -/
theorem evalGATL_sound {B : Col} {sh : Sh} (hB : ShapeOf B sh) {tab : BTab}
    (htab : BTabOK sh tab) {gs : List GNode} (hgs : ∀ nd ∈ gs, GOK B nd) :
    ∀ (ks : GATL) (nd : GNode) (i : ℕ) (tys : List (List ℕ × List ℕ)),
      evalGATL sh tab gs nd i tys ks = true → ∀ ty ∈ tys, GOK B (lchild nd i ty)
  | .nil, nd, i, tys, h, ty, hty => by
    simp only [evalGATL, List.isEmpty_iff] at h; subst h; simp at hty
  | .cons k ks, nd, i, tys, h, ty, hty => by
    cases tys with
    | nil => simp at hty
    | cons a tys' =>
      simp only [evalGATL, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hty with rfl | hty'
      · exact evalGAT_sound hB htab hgs k _ h.1
      · exact evalGATL_sound hB htab hgs ks nd i tys' h.2 ty hty'
end

/-- **A separately checked branching node.** -/
theorem gokSh_of_eval {sh : Sh} {tab : BTab} (htab : BTabOK sh tab) {gs : List GNode}
    (hgs : ∀ nd ∈ gs, GOKSh sh nd) {nd : GNode} {T : GAT} (h : evalGAT sh tab gs nd T = true) :
    GOKSh sh nd := fun B hB =>
  evalGAT_sound hB htab (fun nd' h' => hgs nd' h' B hB) T nd h

/-- **A shape certified by explicit-list branching.** -/
theorem certAt_of_b3 {xs : List ℕ} {tab : BTab} (htab : BTabOK (shOf xs) tab)
    {gs : List GNode} (hgs : ∀ nd ∈ gs, GOKSh (shOf xs) nd)
    {T : GAT} (h : evalGAT (shOf xs) tab gs GNode.root T = true) : CertAt xs := by
  intro B hB hx Y hY hbad
  subst hx
  have hok := gokSh_of_eval htab hgs h B (shapeOf_atoms hB) id (GNode.real_root B id) Y hY
  have hf : gfill GNode.root id Y = Y := by
    obtain ⟨Y1, Y2, Y3, Y4⟩ := Y; rfl
  rw [hf] at hok
  exact hok hbad

/-! ### Short names for generated trees -/

abbrev GLf : GCT := GCT.leaf
abbrev GPr : GCT := GCT.prune
abbrev GNd (i : ℕ) (ts : List ℕ) (k : GCTL) (o : GCT) : GCT := GCT.node i ts k o
abbrev GKs (a : GCT) (b : GCTL) : GCTL := GCTL.cons a b
abbrev GEn : GCTL := GCTL.nil
abbrev An (t : GCT) : GAT := GAT.num t
abbrev As (i : ℕ) (k : GATL) : GAT := GAT.split i k
abbrev Ak (a : GAT) (b : GATL) : GATL := GATL.cons a b
abbrev Ae : GATL := GATL.nil
abbrev Bf (x y z a b : ℕ) : GAT := GAT.badF x y z a b
abbrev Bm (x y z a b : ℕ) : GAT := GAT.badM x y z a b
abbrev Ag (i : ℕ) : GAT := GAT.given i
abbrev Kl : KT := KT.leaf
abbrev Kn (l : KT) (k : ℕ) (r : KT) : KT := KT.node l k r
abbrev Vl : KV := KV.leaf
abbrev Vn (l : KV) (k : ℕ) (v : V5) (r : KV) : KV := KV.node l k v r

end GridGen.Four.K4
