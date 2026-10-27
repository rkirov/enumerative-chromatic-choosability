/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.K4.Fmt

/-!
# Height four at `k = 4`: pointwise certificates

For most next columns `B` every single proper state already contributes nonnegatively (Codex's
(OpenAI) "pointwise" shapes, `ai_research_notes/cx/h4k4b/NOTE.md`; layers A and B1 of the review's
design). This is checked per pattern `e` and own bits `o` of the state, by a **pointwise tree**
(`PT`): a box over the region of all such states (`box`), or a split on the mask of the next class
of colours not yet fixed (`split`, one subtree per available mask, ascending), down to single column
types (`exact`). `evalPT_sound`: a tree that checks proves the pointwise statement `PGood`.

**Clusters** (the review's I-interval regrouping, `H4_K4_CERT_LEVERS_2026-10-26.md`): the root box of
a pattern and own bits depends on the shape only through its Venn sizes once atom availability is
ignored (all masks available, `65535`). A cluster `[vl, vh]` whose box is nonnegative covers every
shape with Venn sizes in it (`cluster_rootOK`).
-/

namespace GridGen.Four.K4

open Finset

mutual
/-- A pointwise certificate tree. -/
inductive PT where
  | box : PT
  | exact : PT
  | split : PTL → PT
/-- A list of pointwise trees. -/
inductive PTL where
  | nil : PTL
  | cons : PT → PTL → PTL
end

/-- The first row whose class has no placed row. -/
def nextFree (nd : Node) (e13 e24 e14 : Bool) : Option ℕ :=
  cond (firstMask nd (cls e13 e24 e14 0)).isNone (some 0)
    (cond (firstMask nd (cls e13 e24 e14 1)).isNone (some 1)
      (cond (firstMask nd (cls e13 e24 e14 2)).isNone (some 2)
        (cond (firstMask nd (cls e13 e24 e14 3)).isNone (some 3) none)))

/-- Place the rows of a list with mask `m` and tag `r`. -/
def placeAll (nd : Node) (m r : ℕ) : List ℕ → Node
  | [] => nd
  | j :: L => (placeAll nd m r L).set j (some (m, r))

/-- The masks of a 16-bit set, ascending. -/
def masksOf (ps : ℕ) : List ℕ := (List.range 16).filter fun m => Nat.testBit ps m

mutual
/-- **The check of a pointwise tree** at a node, for the pattern `e` and own bits `o`. -/
def evalPT (sh : Sh) (nd : Node) (e13 e24 e14 : Bool) (o : ℕ) : PT → Bool
  | .box => regionNN (regionAt sh.I sh.I (avail sh nd) nd e13 e24 e14 o)
  | .exact =>
    match leafNode sh nd with
    | some v => v.nonneg
    | none => false
  | .split ks =>
    match nextFree nd e13 e24 e14 with
    | some r => evalPTL sh nd e13 e24 e14 o r
        (masksOf (Nat.land (avail sh nd) (clsT o (cls e13 e24 e14 r)))) ks
    | none => false
/-- The check of the subtrees of a split. -/
def evalPTL (sh : Sh) (nd : Node) (e13 e24 e14 : Bool) (o r : ℕ) (ms : List ℕ) : PTL → Bool
  | .nil => ms.isEmpty
  | .cons k ks =>
    match ms with
    | [] => false
    | m :: ms' => evalPT sh (placeAll nd m r (cls e13 e24 e14 r)) e13 e24 e14 o k &&
        evalPTL sh nd e13 e24 e14 o r ms' ks
end

/-- **The pointwise statement** at a node, for a pattern and own bits: every proper completion
of every realization with that pattern and those own bits contributes nonnegatively. -/
def PGood (B : Col) (nd : Node) (e13 e24 e14 : Bool) (o : ℕ) : Prop :=
  ∀ ρ, nd.Real B ρ → ∀ s : T4, Proper s → Completes nd ρ s → epat s = (e13, e24, e14) →
    ownOf B s = o → ∀ k : Fin 5, ∀ w ∈ famW k, 0 ≤ gw B w s


/-! ### Soundness -/

theorem placeAll_get (nd : Node) (m r : ℕ) :
    ∀ (L : List ℕ), (∀ j ∈ L, j < 4) → ∀ j < 4,
      (placeAll nd m r L).get j = if j ∈ L then some (m, r) else nd.get j
  | [], _, j, _ => by simp [placeAll]
  | a :: L, hL, j, hj => by
    simp only [placeAll]
    have ha := hL a List.mem_cons_self
    by_cases hja : j = a
    · subst hja; rw [Node.get_set_same _ hj]; simp
    · rw [Node.get_set_ne _ ha hj hja, placeAll_get nd m r L (fun j' h => hL j' (List.mem_cons_of_mem _ h)) j hj]
      simp [hja]

theorem nextFree_spec {nd : Node} {e13 e24 e14 : Bool} {r : ℕ}
    (h : nextFree nd e13 e24 e14 = some r) :
    r < 4 ∧ firstMask nd (cls e13 e24 e14 r) = none := by
  unfold nextFree at h
  cases h0 : (firstMask nd (cls e13 e24 e14 0)).isNone
  · rw [h0, cond_false] at h
    cases h1 : (firstMask nd (cls e13 e24 e14 1)).isNone
    · rw [h1, cond_false] at h
      cases h2 : (firstMask nd (cls e13 e24 e14 2)).isNone
      · rw [h2, cond_false] at h
        cases h3 : (firstMask nd (cls e13 e24 e14 3)).isNone
        · rw [h3, cond_false] at h; exact absurd h (by simp)
        · rw [h3, cond_true, Option.some.injEq] at h; subst h
          exact ⟨by norm_num, Option.isNone_iff_eq_none.mp h3⟩
      · rw [h2, cond_true, Option.some.injEq] at h; subst h
        exact ⟨by norm_num, Option.isNone_iff_eq_none.mp h2⟩
    · rw [h1, cond_true, Option.some.injEq] at h; subst h
      exact ⟨by norm_num, Option.isNone_iff_eq_none.mp h1⟩
  · rw [h0, cond_true, Option.some.injEq] at h; subst h
    exact ⟨by norm_num, Option.isNone_iff_eq_none.mp h0⟩

theorem mem_masksOf {ps m : ℕ} (hm : m < 16) (h : Nat.testBit ps m = true) : m ∈ masksOf ps := by
  unfold masksOf
  exact List.mem_filter.mpr ⟨List.mem_range.mpr hm, h⟩

/-- A split covers every available mask. -/
theorem evalPTL_mem {sh : Sh} {nd : Node} {e13 e24 e14 : Bool} {o r : ℕ} :
    ∀ (ms : List ℕ) (ks : PTL), evalPTL sh nd e13 e24 e14 o r ms ks = true → ∀ m ∈ ms,
      ∃ k, evalPT sh (placeAll nd m r (cls e13 e24 e14 r)) e13 e24 e14 o k = true
  | [], _, _, m, hm => by simp at hm
  | _ :: _, .nil, h, _, _ => by simp [evalPTL] at h
  | a :: ms, .cons k ks, h, m, hm => by
    simp only [evalPTL, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨k, h.1⟩
    · exact evalPTL_mem ms ks h.2 m hm

/-- Realizing a placed class of fresh colour `x` at its rows. -/
theorem real_placeAll {B : Col} {nd : Node} {ρ : ℕ → ℕ} (hρ : nd.Real B ρ) {L : List ℕ}
    (hL : ∀ j ∈ L, j < 4) (hfree : ∀ j ∈ L, nd.get j = none) {r m x : ℕ} (hr : r ∈ L)
    (hx : x ∉ placedSet nd ρ) (hm : mv B x = m) :
    (placeAll nd m r L).Real B (Function.update ρ r x) := by
  have hr4 := hL r hr
  have hg := placeAll_get nd m r L hL
  have tag_ne : ∀ j < 4, ∀ m' t', nd.get j = some (m', t') → t' ≠ r := by
    intro j hj m' t' e
    obtain ⟨-, h2, -, -⟩ := hρ j hj m' t' e
    rintro rfl; rw [hfree _ hr] at h2; exact absurd h2 (by simp)
  intro j hj m' t' e
  rw [hg j hj] at e
  split_ifs at e with hjL
  · simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine ⟨hr4, by rw [hg r hr4, if_pos hr], by rw [Function.update_self]; exact hm, ?_⟩
    intro j' hj' m'' t'' e' he
    rw [hg j' hj'] at e'
    split_ifs at e' with hj'L
    · simp only [Option.some.injEq, Prod.mk.injEq] at e'; exact e'.2
    · have hne := tag_ne j' hj' m'' t'' e'
      rw [Function.update_self, Function.update_of_ne hne] at he
      exact absurd (mem_placedSet.mpr ⟨j', hj', m'', t'', e', he⟩) hx
  · obtain ⟨h1, h2, h3, h4⟩ := hρ j hj m' t' e
    have hne := tag_ne j hj m' t' e
    have ht'L : t' ∉ L := fun h => by rw [hfree t' h] at h2; exact absurd h2 (by simp)
    refine ⟨h1, by rw [hg t' h1, if_neg ht'L]; exact h2, by rw [Function.update_of_ne hne]; exact h3, ?_⟩
    intro j' hj' m'' t'' e' he
    rw [Function.update_of_ne hne] at he
    rw [hg j' hj'] at e'
    split_ifs at e' with hj'L
    · simp only [Option.some.injEq, Prod.mk.injEq] at e'
      obtain ⟨rfl, rfl⟩ := e'
      rw [Function.update_self] at he
      exact absurd (mem_placedSet.mpr ⟨j, hj, m', t', e, he.symm⟩) hx
    · have hne' := tag_ne j' hj' m'' t'' e'
      rw [Function.update_of_ne hne'] at he
      exact h4 j' hj' m'' t'' e' he

mutual
/-- **Soundness of a pointwise tree.** -/
theorem evalPT_sound {B : Col} {sh : Sh} (hB : ShapeOf B sh) {e13 e24 e14 : Bool} {o : ℕ} :
    ∀ (T : PT) (nd : Node), evalPT sh nd e13 e24 e14 o T = true → PGood B nd e13 e24 e14 o
  | .box, nd, h => by
    intro ρ hρ s hs hc he ho k w hw
    obtain ⟨x, hx, hle⟩ := regionAt_sound hB hρ hs hc
    simp only [evalPT] at h
    rw [he, ho] at hx
    rw [hx] at h
    exact le_trans (V5.nonneg_get h k) (hle k w hw)
  | .exact, nd, h => by
    intro ρ hρ s hs hc _ _ k w hw
    simp only [evalPT] at h
    split at h
    · next v hv =>
      have hg := leaf_good hB hv ρ hρ (range 3, range 3, range 3, range 3)
        ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩, ⟨by simp, by simp⟩, ⟨by simp, by simp⟩⟩ k w hw
      obtain ⟨q0, q1, q2, q3⟩ := nd
      unfold leafNode at hv
      split at hv
      · next m0 t0 m1 t1 m2 t2 m3 t3 e0 e1 e2 e3 =>
        simp only at e0 e1 e2 e3
        subst e0 e1 e2 e3
        have c0 := hc 0 (by norm_num) m0 t0 rfl
        have c1 := hc 1 (by norm_num) m1 t1 rfl
        have c2 := hc 2 (by norm_num) m2 t2 rfl
        have c3 := hc 3 (by norm_num) m3 t3 rfl
        simp only [fill, fillR, sumP_single] at hg
        obtain ⟨a, b, c, d⟩ := s
        simp only [rowT, r1, r2, r3, r4] at c0 c1 c2 c3
        subst c0 c1 c2 c3
        exact le_trans (V5.nonneg_get h k) hg
      · exact absurd hv (by simp)
    · exact absurd h (by simp)
  | .split ks, nd, h => by
    intro ρ hρ s hs hc he ho k w hw
    simp only [evalPT] at h
    split at h
    · next r hr =>
      obtain ⟨hr4, hfm⟩ := nextFree_spec hr
      have hfree := firstMask_none hfm
      -- the mask of the class of row `r`
      have hrs := (rsAt_mem hB hρ (fun _ hm h => testBit_avail hm h) hs hc hr4).1
      unfold rsAt at hrs
      rw [he, ho] at hrs
      simp only at hrs
      rw [hfm] at hrs
      have hkt := evalPTL_sound hB ks nd r _ h (mv B (rowT s r)) (mem_masksOf (mv_lt _ _) hrs)
      have hL4 : ∀ j ∈ cls e13 e24 e14 r, j < 4 := fun j h => cls_lt h
      obtain ⟨L, hL⟩ := head_mem_cls e13 e24 e14 hr4
      have hrL : r ∈ cls e13 e24 e14 r := by rw [hL]; exact List.mem_cons_self
      -- the colour of the class is not placed
      have hxp : rowT s r ∉ placedSet nd ρ := by
        intro hp
        obtain ⟨j', hj', m', t', e', hx⟩ := mem_placedSet.mp hp
        obtain ⟨ht4, het, -, -⟩ := hρ j' hj' m' t' e'
        have hct := hc t' ht4 m' t' het
        have hmem : t' ∈ cls (epat s).1 (epat s).2.1 (epat s).2.2 r :=
          (mem_cls_iff hs hr4 ht4).mpr (hct.trans hx.symm)
        rw [he] at hmem
        rw [hfree t' hmem] at het; exact absurd het (by simp)
      have hreal := real_placeAll hρ hL4 hfree hrL hxp rfl
      have hcomp : Completes (placeAll nd (mv B (rowT s r)) r (cls e13 e24 e14 r))
          (Function.update ρ r (rowT s r)) s := by
        intro j hj m t e
        rw [placeAll_get nd _ r _ hL4 j hj] at e
        split_ifs at e with hjL
        · simp only [Option.some.injEq, Prod.mk.injEq] at e
          obtain ⟨-, rfl⟩ := e
          rw [Function.update_self]
          have hjL' : j ∈ cls (epat s).1 (epat s).2.1 (epat s).2.2 r := by rw [he]; exact hjL
          exact (mem_cls_iff hs hr4 hj).mp hjL'
        · obtain ⟨-, h2, -, -⟩ := hρ j hj m t e
          have hne : t ≠ r := by rintro rfl; rw [hfree _ hrL] at h2; exact absurd h2 (by simp)
          rw [Function.update_of_ne hne]; exact hc j hj m t e
      exact hkt _ hreal s hs hcomp he ho k w hw
    · exact absurd h (by simp)
/-- Soundness of the subtrees of a split. -/
theorem evalPTL_sound {B : Col} {sh : Sh} (hB : ShapeOf B sh) {e13 e24 e14 : Bool} {o : ℕ} :
    ∀ (ks : PTL) (nd : Node) (r : ℕ) (ms : List ℕ),
      evalPTL sh nd e13 e24 e14 o r ms ks = true → ∀ m ∈ ms,
        PGood B (placeAll nd m r (cls e13 e24 e14 r)) e13 e24 e14 o
  | .nil, nd, r, ms, h, m, hm => by
    simp only [evalPTL, List.isEmpty_iff] at h; subst h; simp at hm
  | .cons k ks, nd, r, ms, h, m, hm => by
    cases ms with
    | nil => simp at hm
    | cons a ms' =>
      simp only [evalPTL, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact evalPT_sound hB k _ h.1
      · exact evalPTL_sound hB ks nd r ms' h.2 m hm'
end

/-- The pointwise statement at the root for every pattern and own bits gives nonnegative seam
sums. -/
theorem raysOK_of_pointwise {B : Col} (h : ∀ e ∈ pats, ∀ o < 16, PGood B Node.root e.1 e.2.1 e.2.2 o)
    {Y : Col} : RaysOK (dvec Y B) := by
  apply raysOK_of_fam
  intro k w hw
  rw [dot_dvec]
  apply Finset.sum_nonneg; intro a _
  apply Finset.sum_nonneg; intro b _
  apply Finset.sum_nonneg; intro c _
  apply Finset.sum_nonneg; intro d _
  by_cases hs : Proper (a, b, c, d)
  · have ho : ownOf B (a, b, c, d) < 16 := by
      unfold ownOf; simp only [bn, Nat.add_eq, Nat.mul_eq]
      cases Nat.testBit (mv B (r1 (a, b, c, d))) 0 <;> cases Nat.testBit (mv B (r2 (a, b, c, d))) 1 <;>
        cases Nat.testBit (mv B (r3 (a, b, c, d))) 2 <;>
        cases Nat.testBit (mv B (r4 (a, b, c, d))) 3 <;> simp
    exact h _ (epat_mem hs) _ ho id (Node.real_root B id) _ hs
      (fun j hj m t e => by interval_cases j <;> simp [Node.root, Node.get] at e) rfl rfl k w hw
  · exact le_of_eq (gw_improper B w hs).symm


/-! ### Clusters and the pointwise certificate of a shape -/

/-- **A cluster**: the root box of a pattern and own bits, all masks available, Venn sizes in
`[vl, vh]`, is nonnegative. -/
def clusterOK (vl vh : VN) (e13 e24 e14 : Bool) (o : ℕ) : Bool :=
  regionNN (regionAt vl vh 65535 Node.root e13 e24 e14 o)

theorem testBit_65535 : ∀ m < 16, Nat.testBit 65535 m = true := by decide

theorem cluster_pgood {B : Col} {sh : Sh} (hB : ShapeOf B sh) {vl vh : VN} {e13 e24 e14 : Bool}
    {o : ℕ} (h : clusterOK vl vh e13 e24 e14 o = true) (hl : VLe vl sh.I) (hh : VLe sh.I vh) :
    PGood B Node.root e13 e24 e14 o := by
  intro ρ hρ s hs hc he ho k w hw
  obtain ⟨x, hx, hle⟩ := regionAt_sound_gen hB hρ hl hh (fun m hm _ => testBit_65535 m hm) hs hc
  unfold clusterOK at h
  rw [he, ho] at hx
  rw [hx] at h
  exact le_trans (V5.nonneg_get h k) (hle k w hw)

/-- `VLe` as a check. -/
def vleB (a b : VN) : Bool :=
  Nat.ble a.x12 b.x12 && Nat.ble a.x23 b.x23 && Nat.ble a.x34 b.x34 && Nat.ble a.x13 b.x13 &&
    Nat.ble a.x24 b.x24 && Nat.ble a.x14 b.x14 && Nat.ble a.x123 b.x123 && Nat.ble a.x234 b.x234 &&
    Nat.ble a.x124 b.x124 && Nat.ble a.x134 b.x134 && Nat.ble a.x1234 b.x1234

theorem VLe_of_vleB {a b : VN} (h : vleB a b = true) : VLe a b := by
  simp only [vleB, Bool.and_eq_true, Nat.ble_eq] at h
  unfold VLe; omega

/-- The certificate of one pattern and own bits: a tree, or a cluster of the table. -/
inductive PC where
  | tree : PT → PC
  | cl : ℕ → PC

/-- The pattern of index `p`. -/
def patOf (p : ℕ) : Bool × Bool × Bool := pats.getD p (false, false, false)

/-- The check of one certificate, for region `q = 16 p + o`. -/
def pcOK (sh : Sh) (ctab : ℕ → List (VN × VN)) (q : ℕ) : PC → Bool
  | .tree t => evalPT sh Node.root (patOf (q / 16)).1 (patOf (q / 16)).2.1 (patOf (q / 16)).2.2
      (q % 16) t
  | .cl idx =>
    match (ctab q)[idx]? with
    | some c => vleB c.1 sh.I && vleB sh.I c.2
    | none => false

/-- A verified cluster table. -/
def CtabOK (ctab : ℕ → List (VN × VN)) : Prop :=
  ∀ q < 80, ∀ c ∈ ctab q,
    clusterOK c.1 c.2 (patOf (q / 16)).1 (patOf (q / 16)).2.1 (patOf (q / 16)).2.2 (q % 16) = true

/-- **The pointwise check of a shape**: eighty certificates, one per pattern and own bits. -/
def pwOK (sh : Sh) (ctab : ℕ → List (VN × VN)) (certs : List PC) : Bool :=
  allBelow 80 fun q => pcOK sh ctab q (certs.getD q (PC.cl 1000000))

theorem pcOK_pgood {B : Col} {sh : Sh} (hB : ShapeOf B sh) {ctab : ℕ → List (VN × VN)}
    (hct : CtabOK ctab) {q : ℕ} (hq : q < 80) {c : PC} (h : pcOK sh ctab q c = true) :
    PGood B Node.root (patOf (q / 16)).1 (patOf (q / 16)).2.1 (patOf (q / 16)).2.2 (q % 16) := by
  cases c with
  | tree t => exact evalPT_sound hB t Node.root h
  | cl idx =>
    simp only [pcOK] at h
    split at h
    · next c hc =>
      simp only [Bool.and_eq_true] at h
      exact cluster_pgood hB (hct q hq c (List.mem_of_getElem? hc)) (VLe_of_vleB h.1)
        (VLe_of_vleB h.2)
    · exact absurd h (by simp)

theorem pats_patOf {e : Bool × Bool × Bool} (he : e ∈ pats) : ∃ p < 5, patOf p = e := by
  simp only [pats, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by norm_num, rfl⟩
  · exact ⟨1, by norm_num, rfl⟩
  · exact ⟨2, by norm_num, rfl⟩
  · exact ⟨3, by norm_num, rfl⟩
  · exact ⟨4, by norm_num, rfl⟩

/-- **A pointwise-certified shape** has nonnegative seam vectors for every `Y`. -/
theorem raysOK_of_pwOK {B : Col} {sh : Sh} (hB : ShapeOf B sh) {ctab : ℕ → List (VN × VN)}
    (hct : CtabOK ctab) {certs : List PC} (h : pwOK sh ctab certs = true) (Y : Col) :
    RaysOK (dvec Y B) := by
  apply raysOK_of_pointwise
  intro e he o ho
  obtain ⟨p, hp, rfl⟩ := pats_patOf he
  have hq : 16 * p + o < 80 := by omega
  have h1 := allBelow_spec h hq
  have := pcOK_pgood hB hct hq h1
  have e1 : (16 * p + o) / 16 = p := by omega
  have e2 : (16 * p + o) % 16 = o := by omega
  rw [e1, e2] at this
  exact this

end GridGen.Four.K4
