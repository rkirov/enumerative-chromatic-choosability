/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.K4.Chain

/-!
# Height four at `k = 4`: nodes of the certificate trees

A **node** places some of the four rows: a placed row carries the mask of its colour and a **tag**,
the row where that colour was placed first (so two placed rows have the same colour iff they have
the same tag, and the row named by a tag is placed with that tag). A **realization** `ρ` sends tags
to actual colours with the given masks, injectively (`Node.Real`). Filling the unplaced rows with
lists `Y` gives a column `fill nd ρ Y`; a node value `v` is **good** if it bounds the seam sum over
every such column at every valuation (`Good`).

The **options** for an unplaced row `i` are the colours already placed (improper when a neighbour
of `i` has that colour), and a fresh colour of each mask `m ≠ 0` whose atom is not used up, with
multiplicity `n_m - used_m` (`opts`); a fresh colour outside every list is the last option.

The **shape** of `B` is its Venn sizes and atom sizes (`ShapeOf`). A fresh colour of mask `m ≠ 0`
shows that its atom is not used up (`used_lt`).
-/

namespace GridGen.Four.K4

open Finset

/-! ### Shapes -/

/-- The colours of the lists of `B` with mask `m`. -/
def atomN (B : Col) (m : ℕ) : Finset ℕ := (uni B).filter (fun c => mv B c = m)

/-- A shape: atom sizes by mask (`n.getD m 0`) and Venn sizes. -/
structure Sh where
  n : List ℕ
  I : VN

/-- The atom size of a mask. -/
def Sh.na (sh : Sh) (m : ℕ) : ℕ := sh.n.getD m 0

/-- `B` has four lists of four colours and the shape `sh`. -/
def ShapeOf (B : Col) (sh : Sh) : Prop :=
  CardsIn 4 4 B ∧ sh.I.toVenn = vennOf B.1 B.2.1 B.2.2.1 B.2.2.2 ∧
    ∀ m, 0 < m → m < 16 → (atomN B m).card = sh.na m

theorem mem_uni_of_mv {B : Col} {c : ℕ} (h : mv B c ≠ 0) : c ∈ uni B := by
  unfold mv mIdx memv at h
  unfold uni
  simp only [Finset.mem_union]
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  apply h
  simp [h1, h2, h3, h4, bn]

theorem mem_atomN {B : Col} {c m : ℕ} (hm : m ≠ 0) (h : mv B c = m) : c ∈ atomN B m := by
  unfold atomN
  rw [Finset.mem_filter]
  exact ⟨mem_uni_of_mv (h ▸ hm), h⟩

/-! ### Nodes -/

/-- A row: unplaced, or placed with a mask and a tag. -/
abbrev Pl := Option (ℕ × ℕ)

/-- A node. -/
structure Node where
  r0 : Pl
  r1 : Pl
  r2 : Pl
  r3 : Pl

/-- A row of a node. -/
def Node.get (nd : Node) : ℕ → Pl
  | 0 => nd.r0
  | 1 => nd.r1
  | 2 => nd.r2
  | _ => nd.r3

/-- Set a row of a node. -/
def Node.set (nd : Node) (i : ℕ) (p : Pl) : Node :=
  match i with
  | 0 => ⟨p, nd.r1, nd.r2, nd.r3⟩
  | 1 => ⟨nd.r0, p, nd.r2, nd.r3⟩
  | 2 => ⟨nd.r0, nd.r1, p, nd.r3⟩
  | _ => ⟨nd.r0, nd.r1, nd.r2, p⟩

theorem Node.get_set_same (nd : Node) {i : ℕ} (hi : i < 4) (p : Pl) : (nd.set i p).get i = p := by
  interval_cases i <;> rfl

theorem Node.get_set_ne (nd : Node) {i j : ℕ} (hi : i < 4) (hj : j < 4) (h : j ≠ i) (p : Pl) :
    (nd.set i p).get j = nd.get j := by
  interval_cases i <;> interval_cases j <;> first | rfl | exact absurd rfl h

/-- The empty node. -/
def Node.root : Node := ⟨none, none, none, none⟩

/-- **A realization**: tags to colours, with the right masks, injectively; the row named by a tag
is placed with that tag. -/
def Node.Real (B : Col) (nd : Node) (ρ : ℕ → ℕ) : Prop :=
  ∀ j < 4, ∀ m t, nd.get j = some (m, t) →
    t < 4 ∧ nd.get t = some (m, t) ∧ mv B (ρ t) = m ∧
      ∀ j' < 4, ∀ m' t', nd.get j' = some (m', t') → ρ t = ρ t' → t = t'

theorem Node.real_root (B : Col) (ρ : ℕ → ℕ) : Node.root.Real B ρ := by
  intro j hj m t h
  interval_cases j <;> simp [Node.root, Node.get] at h

/-- Fill an unplaced row with a list. -/
def fillR (p : Pl) (ρ : ℕ → ℕ) (Y : Finset ℕ) : Finset ℕ :=
  match p with
  | some (_, t) => {ρ t}
  | none => Y

/-- **The column of a node**, its unplaced rows filled from `Y`. -/
def fill (nd : Node) (ρ : ℕ → ℕ) (Y : Col) : Col :=
  (fillR nd.r0 ρ Y.1, fillR nd.r1 ρ Y.2.1, fillR nd.r2 ρ Y.2.2.1, fillR nd.r3 ρ Y.2.2.2)

theorem rowC_fill (nd : Node) (ρ : ℕ → ℕ) (Y : Col) {i : ℕ} (hi : i < 4) :
    rowC (fill nd ρ Y) i = fillR (nd.get i) ρ (rowC Y i) := by
  interval_cases i <;> rfl

/-- The seam value of one tuple at a weight. -/
def gw (B : Col) (w : Q) (s : T4) : ℤ := dot (gvec B s) w

/-- **A good node value**: a lower bound of the seam sums of all realizations and fillings, at
every weight of every valuation family. -/
def Good (B : Col) (nd : Node) (v : V5) : Prop :=
  ∀ ρ, nd.Real B ρ → ∀ Y : Col, CardsIn 3 4 Y →
    ∀ k : Fin 5, ∀ w ∈ famW k, (v.get k).val ≤ sumP (gw B w) (fill nd ρ Y)

/-! ### Options -/

/-- `p` is placed with tag `t`. -/
def tagIs (p : Pl) (t : ℕ) : Bool :=
  match p with
  | some (_, t') => Nat.beq t' t
  | none => false

/-- The colour of row `j` is placed first there and has mask `m`. -/
def firstM (p : Pl) (m j : ℕ) : Bool :=
  match p with
  | some (m', t) => Nat.beq m' m && Nat.beq t j
  | none => false

/-- The number of placed colours of mask `m`. -/
def usedM (nd : Node) (m : ℕ) : ℕ :=
  Nat.add (Nat.add (bn (firstM nd.r0 m 0)) (bn (firstM nd.r1 m 1)))
    (Nat.add (bn (firstM nd.r2 m 2)) (bn (firstM nd.r3 m 3)))

/-- An option for a row. -/
inductive Opt where
  /-- An already placed colour (its mask, its tag, improper for this row). -/
  | old (m t : ℕ) (imp : Bool)
  /-- A fresh colour of mask `m`, with multiplicity `μ`. -/
  | fresh (m μ : ℕ)

/-- Row `i` is adjacent to a row with tag `t`. -/
def adjTag (nd : Node) (i t : ℕ) : Bool :=
  match i with
  | 0 => tagIs nd.r1 t
  | 1 => tagIs nd.r0 t || tagIs nd.r2 t
  | 2 => tagIs nd.r1 t || tagIs nd.r3 t
  | _ => tagIs nd.r2 t

/-- The option of the colour placed first at row `j`, if any. -/
def oldOpt (nd : Node) (i j : ℕ) : List Opt :=
  match nd.get j with
  | some (m, t) => cond (Nat.beq t j) [Opt.old m j (adjTag nd i j)] []
  | none => []

/-- The nonempty atoms of a shape, with their sizes, by ascending mask. The same for every node of
a tree, so the kernel evaluates it once per declaration. -/
def shAtoms (sh : Sh) : List (ℕ × ℕ) :=
  (List.range' 1 15).filterMap fun m => cond (Nat.blt 0 (sh.na m)) (some (m, sh.na m)) none

/-- The fresh options. -/
def freshOpts (sh : Sh) (nd : Node) : List Opt :=
  (shAtoms sh).filterMap fun p =>
    let μ := Nat.sub p.2 (usedM nd p.1)
    cond (Nat.blt 0 μ) (some (Opt.fresh p.1 μ)) none

/-- **The options for row `i`** (the outside colour excluded). -/
def opts (sh : Sh) (nd : Node) (i : ℕ) : List Opt :=
  oldOpt nd i 0 ++ oldOpt nd i 1 ++ oldOpt nd i 2 ++ oldOpt nd i 3 ++ freshOpts sh nd

/-- The node after choosing an option for row `i`. -/
def Opt.child (nd : Node) (i : ℕ) : Opt → Node
  | .old m t _ => nd.set i (some (m, t))
  | .fresh m _ => nd.set i (some (m, i))

/-- The node after choosing the outside colour for row `i`. -/
def outChild (nd : Node) (i : ℕ) : Node := nd.set i (some (0, i))

/-- The multiplicity of an option. -/
def Opt.mult : Opt → ℕ
  | .old _ _ _ => 1
  | .fresh _ μ => μ

/-- An option is improper. -/
def Opt.imp : Opt → Bool
  | .old _ _ b => b
  | .fresh _ _ => false


/-! ### Placed colours and capacities -/

/-- The colour of a placed row. -/
def plSet (p : Pl) (ρ : ℕ → ℕ) : Finset ℕ :=
  match p with
  | some (_, t) => {ρ t}
  | none => ∅

/-- The placed colours. -/
def placedSet (nd : Node) (ρ : ℕ → ℕ) : Finset ℕ :=
  plSet nd.r0 ρ ∪ plSet nd.r1 ρ ∪ plSet nd.r2 ρ ∪ plSet nd.r3 ρ

theorem mem_placedSet {nd : Node} {ρ : ℕ → ℕ} {x : ℕ} :
    x ∈ placedSet nd ρ ↔ ∃ j < 4, ∃ m t, nd.get j = some (m, t) ∧ x = ρ t := by
  constructor
  · intro h
    simp only [placedSet, Finset.mem_union] at h
    rcases h with ((h | h) | h) | h
    · refine ⟨0, by norm_num, ?_⟩
      unfold plSet at h; split at h
      · next m t e => exact ⟨m, t, e, Finset.mem_singleton.mp h⟩
      · simp at h
    · refine ⟨1, by norm_num, ?_⟩
      unfold plSet at h; split at h
      · next m t e => exact ⟨m, t, e, Finset.mem_singleton.mp h⟩
      · simp at h
    · refine ⟨2, by norm_num, ?_⟩
      unfold plSet at h; split at h
      · next m t e => exact ⟨m, t, e, Finset.mem_singleton.mp h⟩
      · simp at h
    · refine ⟨3, by norm_num, ?_⟩
      unfold plSet at h; split at h
      · next m t e => exact ⟨m, t, e, Finset.mem_singleton.mp h⟩
      · simp at h
  · rintro ⟨j, hj, m, t, e, rfl⟩
    simp only [placedSet, Finset.mem_union]
    interval_cases j <;> simp only [Node.get] at e <;> simp [plSet, e]

theorem firstM_iff (p : Pl) (m j : ℕ) : firstM p m j = true ↔ p = some (m, j) := by
  unfold firstM
  split
  · next m' t => simp [Nat.beq_eq, Bool.and_eq_true]
  · simp

theorem usedM_eq (nd : Node) (m : ℕ) :
    usedM nd m = ((Finset.range 4).filter fun j => firstM (nd.get j) m j = true).card := by
  rw [Finset.card_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, usedM, bn, Nat.add_eq, Node.get]
  cases firstM nd.r0 m 0 <;> cases firstM nd.r1 m 1 <;> cases firstM nd.r2 m 2 <;>
    cases firstM nd.r3 m 3 <;> rfl

/-- **Capacity**: a colour of mask `m ≠ 0` that is not placed shows `used_m < n_m`. -/
theorem used_lt {B : Col} {sh : Sh} (hB : ShapeOf B sh) {nd : Node} {ρ : ℕ → ℕ}
    (hρ : nd.Real B ρ) {x m : ℕ} (hx : x ∉ placedSet nd ρ) (hm : mv B x = m) (h0 : m ≠ 0) :
    usedM nd m < sh.na m := by
  have hm16 : m < 16 := hm ▸ mv_lt B x
  rw [← hB.2.2 m (Nat.pos_of_ne_zero h0) hm16, usedM_eq]
  set F := (Finset.range 4).filter fun j => firstM (nd.get j) m j = true
  have hinj : Set.InjOn ρ ↑F := by
    intro j hj j' hj' e
    simp only [F, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq, firstM_iff] at hj hj'
    exact ((hρ j hj.1 m j hj.2).2.2.2 j' hj'.1 m j' hj'.2 e)
  rw [← Finset.card_image_of_injOn hinj]
  have hsub : insert x (F.image ρ) ⊆ atomN B m := by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact mem_atomN h0 hm
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
      simp only [F, Finset.mem_filter, Finset.mem_range, firstM_iff] at hj
      exact mem_atomN h0 (hρ j hj.1 m j hj.2).2.2.1
  have hxn : x ∉ F.image ρ := by
    intro hc
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    simp only [F, Finset.mem_filter, Finset.mem_range, firstM_iff] at hj
    exact hx (mem_placedSet.mpr ⟨j, hj.1, m, j, hj.2, rfl⟩)
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxn] at this
  omega

/-! ### Choosing a colour for a row -/

theorem setC_fill (nd : Node) (ρ ρ' : ℕ → ℕ) (Y : Col) {i : ℕ} (hi : i < 4)
    (hfree : nd.get i = none)
    (hagree : ∀ j < 4, ∀ m t, nd.get j = some (m, t) → ρ' t = ρ t) (m0 t0 x : ℕ)
    (hx : ρ' t0 = x) :
    setC (fill nd ρ Y) i {x} = fill (nd.set i (some (m0, t0))) ρ' Y := by
  obtain ⟨a, b, c, d⟩ := nd
  have fr : ∀ (p : Pl), (∀ m t, p = some (m, t) → ρ' t = ρ t) → ∀ Z : Finset ℕ,
      fillR p ρ Z = fillR p ρ' Z := by
    intro p hp Z
    cases p with
    | none => rfl
    | some q => obtain ⟨m, t⟩ := q; simp only [fillR, hp m t rfl]
  have ha := fr a (fun m t h => hagree 0 (by norm_num) m t h)
  have hb := fr b (fun m t h => hagree 1 (by norm_num) m t h)
  have hc := fr c (fun m t h => hagree 2 (by norm_num) m t h)
  have hd := fr d (fun m t h => hagree 3 (by norm_num) m t h)
  have fs : ∀ Z : Finset ℕ, fillR (some (m0, t0)) ρ' Z = {x} := fun Z => by simp [fillR, hx]
  interval_cases i <;> simp only [Node.get] at hfree <;> subst hfree <;>
    simp only [fill, setC, Node.set, fs, ha, hb, hc, hd]

theorem real_old {B : Col} {nd : Node} {ρ : ℕ → ℕ} (hρ : nd.Real B ρ) {i m t : ℕ} (hi : i < 4)
    (hfree : nd.get i = none) (ht : t < 4) (hmt : nd.get t = some (m, t)) :
    (nd.set i (some (m, t))).Real B ρ := by
  have hti : t ≠ i := by rintro rfl; rw [hfree] at hmt; exact absurd hmt (by simp)
  have hT := hρ t ht m t hmt
  intro j hj m' t' e
  by_cases hji : j = i
  · subst hji
    rw [Node.get_set_same nd hj] at e
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine ⟨ht, by rw [Node.get_set_ne nd hj ht hti]; exact hmt, hT.2.2.1, ?_⟩
    intro j' hj' m'' t'' e' he
    by_cases hj'i : j' = j
    · subst hj'i; rw [Node.get_set_same nd hj'] at e'
      simp only [Option.some.injEq, Prod.mk.injEq] at e'; exact e'.2
    · rw [Node.get_set_ne nd hj hj' hj'i] at e'
      exact hT.2.2.2 j' hj' m'' t'' e' he
  · rw [Node.get_set_ne nd hi hj hji] at e
    obtain ⟨h1, h2, h3, h4⟩ := hρ j hj m' t' e
    have hti' : t' ≠ i := by rintro rfl; rw [hfree] at h2; exact absurd h2 (by simp)
    refine ⟨h1, by rw [Node.get_set_ne nd hi h1 hti']; exact h2, h3, ?_⟩
    intro j' hj' m'' t'' e' he
    by_cases hj'i : j' = i
    · subst hj'i; rw [Node.get_set_same nd hj'] at e'
      simp only [Option.some.injEq, Prod.mk.injEq] at e'
      obtain ⟨rfl, rfl⟩ := e'
      exact h4 t ht _ _ hmt he
    · rw [Node.get_set_ne nd hi hj' hj'i] at e'
      exact h4 j' hj' m'' t'' e' he

theorem real_fresh {B : Col} {nd : Node} {ρ : ℕ → ℕ} (hρ : nd.Real B ρ) {i m x : ℕ} (hi : i < 4)
    (hfree : nd.get i = none) (hx : x ∉ placedSet nd ρ) (hm : mv B x = m) :
    (nd.set i (some (m, i))).Real B (Function.update ρ i x) := by
  have tag_ne : ∀ j < 4, ∀ m' t', nd.get j = some (m', t') → t' ≠ i := by
    intro j hj m' t' e
    obtain ⟨-, h2, -, -⟩ := hρ j hj m' t' e
    rintro rfl; rw [hfree] at h2; exact absurd h2 (by simp)
  intro j hj m' t' e
  by_cases hji : j = i
  · subst hji
    rw [Node.get_set_same nd hj] at e
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine ⟨hj, Node.get_set_same nd hj _, by rw [Function.update_self]; exact hm, ?_⟩
    intro j' hj' m'' t'' e' he
    by_cases hj'i : j' = j
    · subst hj'i; rw [Node.get_set_same nd hj'] at e'
      simp only [Option.some.injEq, Prod.mk.injEq] at e'; exact e'.2
    · rw [Node.get_set_ne nd hj hj' hj'i] at e'
      have hne := tag_ne j' hj' m'' t'' e'
      rw [Function.update_self, Function.update_of_ne hne] at he
      exact absurd (mem_placedSet.mpr ⟨j', hj', m'', t'', e', he⟩) hx
  · rw [Node.get_set_ne nd hi hj hji] at e
    obtain ⟨h1, h2, h3, h4⟩ := hρ j hj m' t' e
    have hne := tag_ne j hj m' t' e
    refine ⟨h1, by rw [Node.get_set_ne nd hi h1 hne]; exact h2,
      by rw [Function.update_of_ne hne]; exact h3, ?_⟩
    intro j' hj' m'' t'' e' he
    rw [Function.update_of_ne hne] at he
    by_cases hj'i : j' = i
    · subst hj'i; rw [Node.get_set_same nd hj'] at e'
      simp only [Option.some.injEq, Prod.mk.injEq] at e'
      obtain ⟨rfl, rfl⟩ := e'
      rw [Function.update_self] at he
      exact absurd (mem_placedSet.mpr ⟨j, hj, m', t', e, he.symm⟩) hx
    · rw [Node.get_set_ne nd hi hj' hj'i] at e'
      have hne' := tag_ne j' hj' m'' t'' e'
      rw [Function.update_of_ne hne'] at he
      exact h4 j' hj' m'' t'' e' he

/-! ### Improper choices -/

theorem gw_improper (B : Col) (w : Q) {s : T4} (hs : ¬ Proper s) : gw B w s = 0 := by
  unfold gw gvec; rw [if_neg hs, dot_zero]

theorem sumP_eq_zero (g : T4 → ℤ) (Z : Col)
    (h : ∀ a ∈ Z.1, ∀ b ∈ Z.2.1, ∀ c ∈ Z.2.2.1, ∀ d ∈ Z.2.2.2, g (a, b, c, d) = 0) :
    sumP g Z = 0 :=
  Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => Finset.sum_eq_zero fun c hc =>
    Finset.sum_eq_zero fun d hd => h a ha b hb c hc d hd

/-- Two adjacent singleton rows of the same colour: every tuple is improper. -/
theorem sumP_adj_zero (B : Col) (w : Q) (Z : Col) {x : ℕ} {i : ℕ} (hi : i < 3)
    (h1 : rowC Z i = {x}) (h2 : rowC Z (i + 1) = {x}) : sumP (gw B w) Z = 0 := by
  apply sumP_eq_zero
  intro a ha b hb c hc d hd
  apply gw_improper
  interval_cases i <;> simp only [rowC] at h1 h2
  · rw [h1, Finset.mem_singleton] at ha; rw [h2, Finset.mem_singleton] at hb
    exact fun h => h.1 (ha.trans hb.symm)
  · rw [h1, Finset.mem_singleton] at hb; rw [h2, Finset.mem_singleton] at hc
    exact fun h => h.2.1 (hb.trans hc.symm)
  · rw [h1, Finset.mem_singleton] at hc; rw [h2, Finset.mem_singleton] at hd
    exact fun h => h.2.2 (hc.trans hd.symm)

end GridGen.Four.K4
