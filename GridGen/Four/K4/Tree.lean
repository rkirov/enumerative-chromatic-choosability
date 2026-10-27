/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.K4.Prune

/-!
# Height four at `k = 4`: certificate trees for the recurrence

A **certificate tree** (`CT`) for a node is a leaf (all rows placed: the value of the column
type), a pruned node (every completion is nonnegative: value `0`), or a branching on an unplaced row
`i`: one subtree per option of the row (`opts`, the trees of improper options are ignored) and one
for the outside colour, with five option indices choosing the thresholds `t` of the `t`-bound
(`GridGen/Four/K4/Chain.lean`). `evalCT` computes the node value in `Nat`-pair arithmetic.

**Soundness** (`evalCT_sound`): the computed value is good, i.e. a lower bound of the seam sums of
every realization and every filling of the unplaced rows by lists of three or four colours, at every
weight of every valuation family. For the branching this is Codex's (OpenAI) minimum-over-lists
recurrence (`ai_research_notes/cx/h4k4b/NOTE.md`) at the level of column types with atom
capacities, as designed in `ai_research_notes/H4_K4_CERT_LEVERS_2026-10-26.md` (lever 2); every
choice of the thresholds is sound, so they are certificate data.
-/

namespace GridGen.Four.K4

open Finset

mutual
/-- A certificate tree. -/
inductive CT where
  | leaf : CT
  | prune : CT
  | node : ℕ → List ℕ → CTL → CT → CT
  | given : ℕ → CT
/-- A list of certificate trees. -/
inductive CTL where
  | nil : CTL
  | cons : CT → CTL → CTL
end

/-- The value of a node with all rows placed. -/
def leafNode (sh : Sh) (nd : Node) : Option V5 :=
  match nd.r0, nd.r1, nd.r2, nd.r3 with
  | some (m0, t0), some (m1, t1), some (m2, t2), some (m3, t3) =>
    cond (Nat.beq t0 t1 || Nat.beq t1 t2 || Nat.beq t2 t3) none
      (some (leafV sh.I m0 m1 m2 m3 (Nat.beq t0 t2) (Nat.beq t1 t3) (Nat.beq t0 t3)))
  | _, _, _, _ => none

/-- The value of entry `idx` of a list of option values at the valuation `f`, or `d`. -/
def nthV (f : V5 → Zp) (d : Zp) : List (V5 × ℕ) → ℕ → Zp
  | [], _ => d
  | p :: _, 0 => f p.1
  | _ :: L, n + 1 => nthV f d L n

/-- `∑ μ · max(0, t - f v)` over a list of values with multiplicities, in `Nat` operations. -/
def tbN (f : V5 → Zp) (t : Zp) : List (V5 × ℕ) → ℕ
  | [] => 0
  | p :: L => Nat.add (Nat.mul p.2 (Nat.sub (Nat.add (f p.1).n t.p) (Nat.add (f p.1).p t.n)))
      (tbN f t L)

/-- `∑ μ · min(0, f v - t)` over a list of values with multiplicities. -/
def tbF (f : V5 → Zp) (t : Zp) (L : List (V5 × ℕ)) : Zp := ⟨0, tbN f t L⟩

/-- The `t`-bound at the valuation `f`; the threshold is the value of the option `idx` (or of the
outside colour), capped by the outside value. -/
def tcF (f : V5 → Zp) (L : List (V5 × ℕ)) (vo : V5) (idx : ℕ) : Zp :=
  let t := Zp.min (nthV f (f vo) L idx) (f vo)
  Zp.add (Zp.add (Zp.smul 3 t) (Zp.negPart t)) (tbF f t L)

/-- The `t`-bound at one valuation. -/
def tcomb1 (L : List (V5 × ℕ)) (vo : V5) (k : Fin 5) (idx : ℕ) : Zp :=
  tcF (fun v => v.get k) L vo idx

/-- The `t`-bound at the five valuations (each read off by its projection, which the kernel
evaluates in one step). -/
def tcombV (L : List (V5 × ℕ)) (vo : V5) (ts : List ℕ) : V5 :=
  ⟨tcF V5.a L vo (ts.getD 0 0), tcF V5.b L vo (ts.getD 1 0), tcF V5.c L vo (ts.getD 2 0),
    tcF V5.d L vo (ts.getD 3 0), tcF V5.e L vo (ts.getD 4 0)⟩

/-- Equality of placed rows, as a check. -/
def plBEq : Pl → Pl → Bool
  | none, none => true
  | some (a, b), some (c, d) => Nat.beq a c && Nat.beq b d
  | _, _ => false

/-- Equality of nodes, as a check. -/
def nodeBEq (a b : Node) : Bool :=
  plBEq a.r0 b.r0 && plBEq a.r1 b.r1 && plBEq a.r2 b.r2 && plBEq a.r3 b.r3

theorem eq_of_plBEq {a b : Pl} (h : plBEq a b = true) : a = b := by
  rcases a with _ | ⟨a1, a2⟩ <;> rcases b with _ | ⟨b1, b2⟩ <;> simp_all [plBEq, Nat.beq_eq]

theorem eq_of_nodeBEq {a b : Node} (h : nodeBEq a b = true) : a = b := by
  obtain ⟨a0, a1, a2, a3⟩ := a
  obtain ⟨b0, b1, b2, b3⟩ := b
  simp only [nodeBEq, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  rw [eq_of_plBEq h0, eq_of_plBEq h1, eq_of_plBEq h2, eq_of_plBEq h3]

mutual
/-- **The value of a certificate tree** at a node. `given idx` takes the value of the entry `idx`
of `gs` if it is stated for this node (it is proved separately). -/
def evalCT (sh : Sh) (gs : List (Node × V5)) (nd : Node) : CT → Option V5
  | .leaf => leafNode sh nd
  | .prune => cond (pruneOK sh nd) (some V5.zero) none
  | .node i ts kids ok =>
    cond (Nat.blt i 4 && (nd.get i).isNone)
      (match evalKids sh gs nd i (opts sh nd i) kids, evalCT sh gs (outChild nd i) ok with
        | some L, some vo => some (tcombV L vo ts)
        | _, _ => none)
      none
  | .given idx =>
    match gs[idx]? with
    | some p => cond (nodeBEq p.1 nd) (some p.2) none
    | none => none
/-- The values of the options of a row. -/
def evalKids (sh : Sh) (gs : List (Node × V5)) (nd : Node) (i : ℕ) (os : List Opt) :
    CTL → Option (List (V5 × ℕ))
  | .nil =>
    match os with
    | [] => some []
    | _ :: _ => none
  | .cons k ks =>
    match os with
    | [] => none
    | o :: os' =>
      match cond o.imp (some V5.zero) (evalCT sh gs (o.child nd i) k), evalKids sh gs nd i os' ks with
      | some v, some L => some ((v, o.mult) :: L)
      | _, _ => none
end


/-! ### Soundness of a leaf -/

theorem ne_of_beq_false {a b : ℕ} (h : Nat.beq a b = false) : a ≠ b := by
  rintro rfl; rw [Nat.beq_refl] at h; exact absurd h (by decide)

theorem sumP_single (g : T4 → ℤ) (a b c d : ℕ) : sumP g ({a}, {b}, {c}, {d}) = g (a, b, c, d) := by
  simp [sumP]

theorem leaf_good {B : Col} {sh : Sh} (hB : ShapeOf B sh) {nd : Node} {v : V5}
    (h : leafNode sh nd = some v) : Good B nd v := by
  obtain ⟨q0, q1, q2, q3⟩ := nd
  unfold leafNode at h
  split at h
  · next m0 t0 m1 t1 m2 t2 m3 t3 e0 e1 e2 e3 =>
    simp only at e0 e1 e2 e3
    subst e0 e1 e2 e3
    cases hadj : (Nat.beq t0 t1 || Nat.beq t1 t2 || Nat.beq t2 t3)
    · rw [hadj, cond_false, Option.some.injEq] at h
      subst h
      intro ρ hρ Y _ k w hw
      simp only [fill, fillR]
      rw [sumP_single]
      have R0 := hρ 0 (by norm_num) m0 t0 rfl
      have R1 := hρ 1 (by norm_num) m1 t1 rfl
      have R2 := hρ 2 (by norm_num) m2 t2 rfl
      have R3 := hρ 3 (by norm_num) m3 t3 rfl
      simp only [Node.get] at R0 R1 R2 R3
      -- equal colours iff equal tags
      have eqv : ∀ (a b : ℕ) (ma mb : ℕ), (∃ j < 4, (⟨some (m0, t0), some (m1, t1), some (m2, t2),
          some (m3, t3)⟩ : Node).get j = some (ma, a)) → (∃ j < 4, (⟨some (m0, t0),
          some (m1, t1), some (m2, t2), some (m3, t3)⟩ : Node).get j = some (mb, b)) →
          (ρ a = ρ b ↔ a = b) := by
        rintro a b ma mb ⟨j, hj, ej⟩ ⟨j', hj', ej'⟩
        exact ⟨(hρ j hj ma a ej).2.2.2 j' hj' mb b ej', fun h => h ▸ rfl⟩
      have e01 := eqv t0 t1 m0 m1 ⟨0, by norm_num, rfl⟩ ⟨1, by norm_num, rfl⟩
      have e12 := eqv t1 t2 m1 m2 ⟨1, by norm_num, rfl⟩ ⟨2, by norm_num, rfl⟩
      have e23 := eqv t2 t3 m2 m3 ⟨2, by norm_num, rfl⟩ ⟨3, by norm_num, rfl⟩
      have e02 := eqv t0 t2 m0 m2 ⟨0, by norm_num, rfl⟩ ⟨2, by norm_num, rfl⟩
      have e13 := eqv t1 t3 m1 m3 ⟨1, by norm_num, rfl⟩ ⟨3, by norm_num, rfl⟩
      have e03 := eqv t0 t3 m0 m3 ⟨0, by norm_num, rfl⟩ ⟨3, by norm_num, rfl⟩
      simp only [Bool.or_eq_false_iff] at hadj
      obtain ⟨⟨n01, n12⟩, n23⟩ := hadj
      replace n01 := ne_of_beq_false n01
      replace n12 := ne_of_beq_false n12
      replace n23 := ne_of_beq_false n23
      have hs : Proper (ρ t0, ρ t1, ρ t2, ρ t3) :=
        ⟨fun h => n01 (e01.mp h), fun h => n12 (e12.mp h), fun h => n23 (e23.mp h)⟩
      have := leafV_sound B sh.I hB.2.1 hs k w hw
      simp only [r1, r2, r3, r4] at this
      rw [R0.2.2.1, R1.2.2.1, R2.2.2.1, R3.2.2.1] at this
      have d02 : decide (ρ t0 = ρ t2) = Nat.beq t0 t2 := by
        rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.beq_eq]; exact e02
      have d13 : decide (ρ t1 = ρ t3) = Nat.beq t1 t3 := by
        rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.beq_eq]; exact e13
      have d03 : decide (ρ t0 = ρ t3) = Nat.beq t0 t3 := by
        rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.beq_eq]; exact e03
      rw [d02, d13, d03] at this
      exact this
    · rw [hadj, cond_true] at h; exact absurd h (by simp)
  · simp at h


/-! ### Options -/

theorem mem_oldOpt {nd : Node} {i j : ℕ} {o : Opt} (h : o ∈ oldOpt nd i j) :
    ∃ m, nd.get j = some (m, j) ∧ o = Opt.old m j (adjTag nd i j) := by
  unfold oldOpt at h
  split at h
  · next m t e =>
    cases ht : Nat.beq t j
    · rw [ht, cond_false] at h; simp at h
    · rw [ht, cond_true, List.mem_singleton] at h
      rw [Nat.beq_eq] at ht; subst ht
      exact ⟨m, e, h⟩
  · simp at h

theorem mem_shAtoms {sh : Sh} {p : ℕ × ℕ} (h : p ∈ shAtoms sh) :
    0 < p.1 ∧ p.1 < 16 ∧ p.2 = sh.na p.1 := by
  unfold shAtoms at h
  obtain ⟨m, hm, e⟩ := List.mem_filterMap.mp h
  obtain ⟨h1, h2⟩ := List.mem_range'_1.mp hm
  cases hb : Nat.blt 0 (sh.na m)
  · simp only [hb, Bool.cond_false] at e; exact absurd e (by simp)
  · simp only [hb, Bool.cond_true, Option.some.injEq] at e
    subst e; exact ⟨by omega, by omega, rfl⟩

theorem atom_mem_shAtoms (sh : Sh) {m : ℕ} (h0 : 0 < m) (h16 : m < 16) (hpos : 0 < sh.na m) :
    (m, sh.na m) ∈ shAtoms sh := by
  unfold shAtoms
  refine List.mem_filterMap.mpr ⟨m, List.mem_range'_1.mpr ⟨by omega, by omega⟩, ?_⟩
  have : Nat.blt 0 (sh.na m) = true := by rw [Nat.blt_eq]; exact hpos
  simp only [this, Bool.cond_true]

theorem mem_freshOpts {sh : Sh} {nd : Node} {o : Opt} (h : o ∈ freshOpts sh nd) :
    ∃ m μ, 0 < m ∧ m < 16 ∧ μ = Nat.sub (sh.na m) (usedM nd m) ∧ o = Opt.fresh m μ := by
  unfold freshOpts at h
  obtain ⟨p, hp, e⟩ := List.mem_filterMap.mp h
  obtain ⟨h1, h2, h3⟩ := mem_shAtoms hp
  cases hb : Nat.blt 0 (Nat.sub p.2 (usedM nd p.1))
  · simp only [hb, Bool.cond_false] at e; exact absurd e (by simp)
  · simp only [hb, Bool.cond_true, Option.some.injEq] at e
    exact ⟨p.1, _, h1, h2, by rw [h3], e.symm⟩

theorem mem_opts {sh : Sh} {nd : Node} {i : ℕ} {o : Opt} (h : o ∈ opts sh nd i) :
    (∃ j < 4, ∃ m, nd.get j = some (m, j) ∧ o = Opt.old m j (adjTag nd i j)) ∨
      ∃ m μ, 0 < m ∧ m < 16 ∧ μ = Nat.sub (sh.na m) (usedM nd m) ∧ o = Opt.fresh m μ := by
  simp only [opts, List.mem_append] at h
  rcases h with (((h | h) | h) | h) | h
  · exact Or.inl ⟨0, by norm_num, mem_oldOpt h⟩
  · exact Or.inl ⟨1, by norm_num, mem_oldOpt h⟩
  · exact Or.inl ⟨2, by norm_num, mem_oldOpt h⟩
  · exact Or.inl ⟨3, by norm_num, mem_oldOpt h⟩
  · exact Or.inr (mem_freshOpts h)

theorem old_mem_opts (sh : Sh) {nd : Node} (i : ℕ) {m t : ℕ} (ht : t < 4)
    (e : nd.get t = some (m, t)) : Opt.old m t (adjTag nd i t) ∈ opts sh nd i := by
  have hm : Opt.old m t (adjTag nd i t) ∈ oldOpt nd i t := by
    simp only [oldOpt, e, Nat.beq_refl, cond_true, List.mem_singleton]
  simp only [opts, List.mem_append]
  interval_cases t
  · exact Or.inl (Or.inl (Or.inl (Or.inl hm)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr hm)))
  · exact Or.inl (Or.inl (Or.inr hm))
  · exact Or.inl (Or.inr hm)

theorem fresh_mem_opts (sh : Sh) (nd : Node) (i : ℕ) {m : ℕ} (h0 : 0 < m) (h16 : m < 16)
    (hpos : 0 < Nat.sub (sh.na m) (usedM nd m)) :
    Opt.fresh m (Nat.sub (sh.na m) (usedM nd m)) ∈ opts sh nd i := by
  simp only [opts, List.mem_append]
  right
  unfold freshOpts
  refine List.mem_filterMap.mpr ⟨(m, sh.na m), atom_mem_shAtoms sh h0 h16
    (by simp only [Nat.sub_eq] at hpos; omega), ?_⟩
  have : Nat.blt 0 (Nat.sub (sh.na m) (usedM nd m)) = true := by rw [Nat.blt_eq]; exact hpos
  simp only [this, Bool.cond_true]

/-- The colours an option stands for. -/
def predOf (B : Col) (nd : Node) (ρ : ℕ → ℕ) : Opt → ℕ → Bool
  | .old _ t _, x => decide (x = ρ t)
  | .fresh m _, x => decide (mv B x = m) && decide (x ∉ placedSet nd ρ)

/-- **Fresh colours of a mask** in a list: at most the atom size minus the used ones. -/
theorem fresh_count {B : Col} {sh : Sh} (hB : ShapeOf B sh) {nd : Node} {ρ : ℕ → ℕ}
    (hρ : nd.Real B ρ) (Y : Finset ℕ) {m : ℕ} (h0 : 0 < m) (h16 : m < 16) (μ : ℕ) :
    (Y.filter fun x => predOf B nd ρ (Opt.fresh m μ) x = true).card + usedM nd m ≤ sh.na m := by
  rw [← hB.2.2 m h0 h16, usedM_eq]
  set F := (Finset.range 4).filter fun j => firstM (nd.get j) m j = true
  have hinj : Set.InjOn ρ ↑F := by
    intro j hj j' hj' e
    simp only [F, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq, firstM_iff] at hj hj'
    exact ((hρ j hj.1 m j hj.2).2.2.2 j' hj'.1 m j' hj'.2 e)
  rw [← Finset.card_image_of_injOn hinj, ← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · simp only [Finset.mem_filter, predOf, Bool.and_eq_true, decide_eq_true_eq] at hc
      exact mem_atomN (by omega) hc.2.1
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
      simp only [F, Finset.mem_filter, Finset.mem_range, firstM_iff] at hj
      exact mem_atomN (by omega) (hρ j hj.1 m j hj.2).2.2.1
  · rw [Finset.disjoint_left]
    intro c hc hc'
    simp only [Finset.mem_filter, predOf, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc'
    simp only [F, Finset.mem_filter, Finset.mem_range, firstM_iff] at hj
    exact hc.2.2 (mem_placedSet.mpr ⟨j, hj.1, m, j, hj.2, rfl⟩)

theorem tagIs_iff (p : Pl) (t : ℕ) : tagIs p t = true ↔ ∃ m, p = some (m, t) := by
  unfold tagIs
  split
  · next m t' => simp [Nat.beq_eq]
  · simp

/-- An improper option: a neighbour of row `i` has the colour. -/
theorem adjTag_spec {nd : Node} {i t : ℕ} (hi : i < 4) (h : adjTag nd i t = true) :
    ∃ i' < 4, (i' + 1 = i ∨ i' = i + 1) ∧ ∃ m, nd.get i' = some (m, t) := by
  interval_cases i <;> simp only [adjTag, Bool.or_eq_true, tagIs_iff] at h
  · obtain ⟨m, e⟩ := h; exact ⟨1, by norm_num, Or.inr rfl, m, e⟩
  · rcases h with ⟨m, e⟩ | ⟨m, e⟩
    · exact ⟨0, by norm_num, Or.inl rfl, m, e⟩
    · exact ⟨2, by norm_num, Or.inr rfl, m, e⟩
  · rcases h with ⟨m, e⟩ | ⟨m, e⟩
    · exact ⟨1, by norm_num, Or.inl rfl, m, e⟩
    · exact ⟨3, by norm_num, Or.inr rfl, m, e⟩
  · obtain ⟨m, e⟩ := h; exact ⟨2, by norm_num, Or.inl rfl, m, e⟩

theorem rowC_setC_same (Z : Col) {i : ℕ} (hi : i < 4) (X : Finset ℕ) : rowC (setC Z i X) i = X := by
  interval_cases i <;> rfl

theorem rowC_setC_ne (Z : Col) {i j : ℕ} (hi : i < 4) (hj : j < 4) (h : j ≠ i) (X : Finset ℕ) :
    rowC (setC Z i X) j = rowC Z j := by
  interval_cases i <;> interval_cases j <;> first | rfl | exact absurd rfl h

theorem adj_zero {B : Col} (w : Q) {nd : Node} {ρ : ℕ → ℕ} (Y : Col) {i t : ℕ} (hi : i < 4)
    (h : adjTag nd i t = true) : sumP (gw B w) (setC (fill nd ρ Y) i {ρ t}) = 0 := by
  obtain ⟨i', hi', hadj, m, e⟩ := adjTag_spec hi h
  have hne : i' ≠ i := by omega
  have r1 := rowC_setC_same (fill nd ρ Y) hi {ρ t}
  have r2 : rowC (setC (fill nd ρ Y) i {ρ t}) i' = {ρ t} := by
    rw [rowC_setC_ne _ hi hi' hne, rowC_fill _ _ _ hi', e]; rfl
  rcases hadj with h1 | h1
  · subst h1; exact sumP_adj_zero B w _ (by omega) r2 r1
  · subst h1; exact sumP_adj_zero B w _ (by omega) r1 r2

/-! ### Soundness of a branching -/

/-- What the value of an option certifies. -/
def OptVal (B : Col) (nd : Node) (i : ℕ) (o : Opt) (p : V5 × ℕ) : Prop :=
  p.2 = o.mult ∧ (o.imp = true → p.1 = V5.zero) ∧ (o.imp = false → Good B (o.child nd i) p.1)

theorem tbF_val (f : V5 → Zp) (t : Zp) : ∀ L : List (V5 × ℕ),
    (tbF f t L).val = ((L.map fun p => (f p.1, p.2)).map
      fun p => (p.2 : ℤ) * min 0 (p.1.val - t.val)).sum
  | [] => by simp [tbF, tbN]
  | p :: L => by
    have ih := tbF_val f t L
    simp only [tbF, Zp.val_mk, Nat.cast_zero, zero_sub] at ih ⊢
    simp only [tbN, Nat.add_eq, Nat.mul_eq, Nat.sub_eq, List.map_cons, List.sum_cons]
    push_cast
    rw [neg_add, ih]
    congr 1
    simp only [Zp.val]
    rcases le_total ((f p.1).n + t.p) ((f p.1).p + t.n) with h | h
    · rw [Nat.sub_eq_zero_of_le h]; push_cast
      rw [min_eq_left (by push_cast at h ⊢; linarith)]; ring
    · rw [Nat.cast_sub h]; push_cast
      rw [min_eq_right (by push_cast at h ⊢; linarith)]; ring

theorem forall₂_map_snd {α β γ : Type*} {R : α → β → Prop} (F : β → γ) :
    ∀ {os : List α} {L : List β}, List.Forall₂ R os L → (List.zip os L).map (fun q => F q.2) = L.map F
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [forall₂_map_snd F h]

theorem forall₂_mem_left {α β : Type*} {R : α → β → Prop} :
    ∀ {os : List α} {L : List β}, List.Forall₂ R os L → ∀ o ∈ os, ∃ p, (o, p) ∈ List.zip os L
  | _, _, .nil, _, h => by simp at h
  | _, _, @List.Forall₂.cons _ _ _ a b _ _ _ h, o, ho => by
    rcases List.mem_cons.mp ho with rfl | ho
    · exact ⟨b, by simp⟩
    · obtain ⟨p, hp⟩ := forall₂_mem_left h o ho
      exact ⟨p, List.mem_cons_of_mem _ hp⟩

theorem fill_agree {nd : Node} {ρ : ℕ → ℕ} {B : Col} (hρ : nd.Real B ρ) {i : ℕ}
    (hfree : nd.get i = none) (x : ℕ) :
    ∀ j < 4, ∀ m t, nd.get j = some (m, t) → Function.update ρ i x t = ρ t := by
  intro j hj m t e
  obtain ⟨-, h2, -, -⟩ := hρ j hj m t e
  have : t ≠ i := by rintro rfl; rw [hfree] at h2; exact absurd h2 (by simp)
  exact Function.update_of_ne this _ _

theorem tcombV_get (L : List (V5 × ℕ)) (vo : V5) (ts : List ℕ) (k : Fin 5) :
    (tcombV L vo ts).get k = tcomb1 L vo k (ts.getD k 0) := by
  fin_cases k <;> rfl

/-- **Soundness of a branching on row `i`.** -/
theorem tnode_good {B : Col} {sh : Sh} (hB : ShapeOf B sh) {nd : Node} {i : ℕ} (hi : i < 4)
    (hfree : nd.get i = none) {L : List (V5 × ℕ)}
    (hL : List.Forall₂ (OptVal B nd i) (opts sh nd i) L) {vo : V5}
    (hvo : Good B (outChild nd i) vo) (ts : List ℕ) : Good B nd (tcombV L vo ts) := by
  intro ρ hρ Y hY k w hw
  set Z := fill nd ρ Y
  set Yi := rowC Y i
  have hYi : 3 ≤ Yi.card ∧ Yi.card ≤ 4 := by
    obtain ⟨c1, c2, c3, c4⟩ := hY
    simp only [Yi]
    interval_cases i
    · exact c1
    · exact c2
    · exact c3
    · exact c4
  set h : ℕ → ℤ := fun x => sumP (gw B w) (setC Z i {x})
  have hsplit : sumP (gw B w) Z = ∑ x ∈ Yi, h x := by
    rw [sumP_split _ _ i hi, rowC_fill _ _ _ hi, hfree]; rfl
  -- the threshold
  set Lk := L.map fun p => (p.1.get k, p.2)
  set tZ := Zp.min (nthV (fun v => v.get k) (vo.get k) L (ts.getD k 0)) (vo.get k)
  set t := tZ.val
  have ht : t ≤ (vo.get k).val := by simp only [t, tZ, Zp.val_min]; exact min_le_right _ _
  have hval : ((tcombV L vo ts).get k).val = 3 * t + min 0 t
      + (Lk.map fun p => (p.2 : ℤ) * min 0 (p.1.val - t)).sum := by
    rw [tcombV_get]
    simp only [tcomb1, tcF, Zp.val_add, Zp.val_smul, Zp.val_negPart, tbF_val]
    push_cast; ring
  rw [hval, hsplit]
  -- the outside colours
  have hout : ∀ x, x ∉ placedSet nd ρ → mv B x = 0 → (vo.get k).val ≤ h x := by
    intro x hx hm
    have hr := real_fresh hρ hi hfree hx hm
    have hf := setC_fill nd ρ (Function.update ρ i x) Y hi hfree (fill_agree hρ hfree x) 0 i x
      (Function.update_self _ _ _)
    have := hvo _ hr Y hY k w hw
    simp only [h]; rw [hf]; exact this
  -- the option values
  have hopt : ∀ o ∈ opts sh nd i, ∀ p, OptVal B nd i o p → ∀ x, predOf B nd ρ o x = true →
      (p.1.get k).val ≤ h x := by
    intro o ho p hp x hx
    obtain ⟨-, himp, hgood⟩ := hp
    rcases mem_opts ho with ⟨j, hj, m, e, rfl⟩ | ⟨m, μ, h0, h16, -, rfl⟩
    · simp only [predOf, decide_eq_true_eq] at hx; subst hx
      cases hadj : adjTag nd i j
      · have hg := hgood hadj
        have hr := real_old hρ hi hfree hj e
        have hf := setC_fill nd ρ ρ Y hi hfree (fun _ _ _ _ _ => rfl) m j (ρ j) rfl
        have := hg ρ hr Y hY k w hw
        simp only [h]; rw [hf]; exact this
      · rw [himp hadj, V5.get_zero]
        simp only [h]; rw [adj_zero w Y hi hadj]
    · simp only [predOf, Bool.and_eq_true, decide_eq_true_eq] at hx
      have hg := hgood rfl
      have hr := real_fresh hρ hi hfree hx.2 hx.1
      have hf := setC_fill nd ρ (Function.update ρ i x) Y hi hfree (fill_agree hρ hfree x) m i x
        (Function.update_self _ _ _)
      have := hg _ hr Y hY k w hw
      simp only [h]; rw [hf]; exact this
  -- the classes
  set C : List Cls := (List.zip (opts sh nd i) L).map fun q =>
    (predOf B nd ρ q.1, (q.2.1.get k).val, q.2.2)
  have hCsum : (C.map fun c => (c.2.2 : ℤ) * min 0 (c.2.1 - t)).sum
      = (Lk.map fun p => (p.2 : ℤ) * min 0 (p.1.val - t)).sum := by
    simp only [C, Lk, List.map_map]
    congr 1
    exact forall₂_map_snd (fun p : V5 × ℕ => (p.2 : ℤ) * min 0 ((p.1.get k).val - t)) hL
  have hall := List.forall₂_iff_zip.mp hL
  have hcls := sum_classes t (fun x => min 0 (h x - t)) (fun x => min_le_left _ _) C Yi
    (by
      intro x hx
      by_cases hp : x ∈ placedSet nd ρ
      · left
        obtain ⟨j, hj, m, t', e, rfl⟩ := mem_placedSet.mp hp
        obtain ⟨ht4, e', -, -⟩ := hρ j hj m t' e
        have hmem := old_mem_opts sh i ht4 e'
        obtain ⟨p, hzp⟩ := forall₂_mem_left hL _ hmem
        refine ⟨_, List.mem_map.mpr ⟨_, hzp, rfl⟩, ?_⟩
        simp [predOf]
      · by_cases h0 : mv B x = 0
        · right
          have := hout x hp h0
          omega
        · left
          have hlt := used_lt hB hρ hp rfl h0
          have hmem := fresh_mem_opts sh nd i (m := mv B x) (Nat.pos_of_ne_zero h0) (mv_lt B x)
            (by simp only [Nat.sub_eq]; omega)
          obtain ⟨p, hzp⟩ := forall₂_mem_left hL _ hmem
          refine ⟨_, List.mem_map.mpr ⟨_, hzp, rfl⟩, ?_⟩
          simp [predOf, hp])
    (by
      intro c hc x hx
      obtain ⟨⟨o, p⟩, hz, rfl⟩ := List.mem_map.mp hc
      have hle := hopt o (List.of_mem_zip hz).1 p (hall.2 hz) x hx
      exact min_le_min_left 0 (by linarith))
    (by
      intro c hc
      obtain ⟨⟨o, p⟩, hz, rfl⟩ := List.mem_map.mp hc
      obtain ⟨hmult, -, -⟩ := hall.2 hz
      simp only
      rw [hmult]
      rcases mem_opts (List.of_mem_zip hz).1 with ⟨j, hj, m, e, rfl⟩ | ⟨m, μ, h0, h16, hμ, rfl⟩
      · simp only [predOf, Opt.mult]
        refine (Finset.card_le_card (t := {ρ j}) ?_).trans (by simp)
        intro x hx; simp only [Finset.mem_filter, decide_eq_true_eq] at hx
        exact Finset.mem_singleton.mpr hx.2
      · have := fresh_count hB hρ Yi h0 h16 μ
        show _ ≤ μ
        rw [Nat.sub_eq] at hμ; omega)
  have htb := tbound hYi h t
  rw [hCsum] at hcls
  linarith


/-! ### Soundness of the trees -/

mutual
/-- **Soundness of a certificate tree**, given the separately proved values `gs`. -/
theorem evalCT_sound {B : Col} {sh : Sh} (hB : ShapeOf B sh) {gs : List (Node × V5)}
    (hgs : ∀ p ∈ gs, Good B p.1 p.2) :
    ∀ (T : CT) (nd : Node) (v : V5), evalCT sh gs nd T = some v → Good B nd v
  | .leaf, nd, v, h => leaf_good hB h
  | .prune, nd, v, h => by
    simp only [evalCT] at h
    cases hp : pruneOK sh nd
    · rw [hp, cond_false] at h; exact absurd h (by simp)
    · rw [hp, cond_true, Option.some.injEq] at h; subst h; exact prune_good hB hp
  | .node i ts kids ok, nd, v, h => by
    simp only [evalCT] at h
    cases hc : (Nat.blt i 4 && (nd.get i).isNone)
    · rw [hc, cond_false] at h; exact absurd h (by simp)
    · rw [hc, cond_true] at h
      simp only [Bool.and_eq_true, Nat.blt_eq, Option.isNone_iff_eq_none] at hc
      split at h
      · next L vo hk ho =>
        rw [Option.some.injEq] at h; subst h
        exact tnode_good hB hc.1 hc.2 (evalKids_sound hB hgs kids nd i _ L hk)
          (evalCT_sound hB hgs ok _ vo ho) ts
      · exact absurd h (by simp)
  | .given idx, nd, v, h => by
    simp only [evalCT] at h
    split at h
    · next p hp =>
      cases he : nodeBEq p.1 nd
      · rw [he, cond_false] at h; exact absurd h (by simp)
      · rw [he, cond_true, Option.some.injEq] at h
        subst h
        rw [← eq_of_nodeBEq he]
        exact hgs p (List.mem_of_getElem? hp)
    · exact absurd h (by simp)
/-- Soundness of the option values. -/
theorem evalKids_sound {B : Col} {sh : Sh} (hB : ShapeOf B sh) {gs : List (Node × V5)}
    (hgs : ∀ p ∈ gs, Good B p.1 p.2) :
    ∀ (ks : CTL) (nd : Node) (i : ℕ) (os : List Opt) (L : List (V5 × ℕ)),
      evalKids sh gs nd i os ks = some L → List.Forall₂ (OptVal B nd i) os L
  | .nil, nd, i, os, L, h => by
    cases os with
    | nil => simp only [evalKids, Option.some.injEq] at h; subst h; exact .nil
    | cons o os => simp [evalKids] at h
  | .cons k ks, nd, i, os, L, h => by
    cases os with
    | nil => simp [evalKids] at h
    | cons o os' =>
      simp only [evalKids] at h
      split at h
      · next v L' hv hL' =>
        rw [Option.some.injEq] at h; subst h
        refine .cons ⟨rfl, ?_, ?_⟩ (evalKids_sound hB hgs ks nd i os' L' hL')
        · intro himp; rw [himp, cond_true, Option.some.injEq] at hv; exact hv.symm
        · intro himp; rw [himp, cond_false] at hv; exact evalCT_sound hB hgs k _ v hv
      · exact absurd h (by simp)
end

/-- Nonnegativity at the valuation families gives nonnegativity at the twelve rays. -/
theorem raysOK_of_fam {d : Q} (h : ∀ k : Fin 5, ∀ w ∈ famW k, 0 ≤ dot d w) : RaysOK d := by
  obtain ⟨d0, d1, d2, d3⟩ := d
  have t := fun (w : Q) (hw : w ∈ famW 4) => h 4 w hw
  intro r hr
  simp only [rays, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h 0 _ (by simp [famW])
  · exact h 1 _ (by simp [famW])
  · exact h 2 _ (by simp [famW])
  · exact h 3 _ (by simp [famW])
  all_goals first
    | (have := t (20000, 18906, 17184, 17814) (by simp [famW]); simp only [dot] at this ⊢; omega)
    | (have := t (20000, 18906, 17184, 17818) (by simp [famW]); simp only [dot] at this ⊢; omega)
    | (have := t (20000, 18906, 17188, 17814) (by simp [famW]); simp only [dot] at this ⊢; omega)
    | (have := t (20000, 18906, 17188, 17818) (by simp [famW]); simp only [dot] at this ⊢; omega)
    | (have := t (20000, 18908, 17184, 17814) (by simp [famW]); simp only [dot] at this ⊢; omega)
    | (have := t (20000, 18908, 17184, 17818) (by simp [famW]); simp only [dot] at this ⊢; omega)
    | (have := t (20000, 18908, 17188, 17814) (by simp [famW]); simp only [dot] at this ⊢; omega)
    | (have := t (20000, 18908, 17188, 17818) (by simp [famW]); simp only [dot] at this ⊢; omega)

/-- **A certified shape**: the tree evaluates at the root to a nonnegative value. Then every
`Y` with lists of three or four colours has `dvec Y B` nonnegative at the twelve rays. -/
theorem raysOK_of_tree {B : Col} {sh : Sh} (hB : ShapeOf B sh) {gs : List (Node × V5)}
    (hgs : ∀ p ∈ gs, Good B p.1 p.2) {T : CT} {v : V5}
    (h : evalCT sh gs Node.root T = some v) (hv : v.nonneg = true) {Y : Col} (hY : CardsIn 3 4 Y) :
    RaysOK (dvec Y B) := by
  have hg := evalCT_sound hB hgs T Node.root v h id (Node.real_root B id) Y hY
  have hall : ∀ k : Fin 5, ∀ w ∈ famW k, 0 ≤ dot (dvec Y B) w := by
    intro k w hw
    rw [dot_dvec]
    have := hg k w hw
    have h0 := V5.nonneg_get hv k
    simp only [fill, Node.root, fillR] at this
    exact le_trans h0 this
  exact raysOK_of_fam hall

/-- `u ≤ v` at every valuation, as a check. -/
def V5.leB (u v : V5) : Bool :=
  Zp.le u.a v.a && Zp.le u.b v.b && Zp.le u.c v.c && Zp.le u.d v.d && Zp.le u.e v.e

theorem V5.le_of_leB {u v : V5} (h : V5.leB u v = true) (k : Fin 5) :
    (u.get k).val ≤ (v.get k).val := by
  simp only [V5.leB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he⟩ := h
  fin_cases k
  · exact (Zp.le_iff _ _).mp ha
  · exact (Zp.le_iff _ _).mp hb
  · exact (Zp.le_iff _ _).mp hc
  · exact (Zp.le_iff _ _).mp hd
  · exact (Zp.le_iff _ _).mp he

theorem good_mono {B : Col} {nd : Node} {u v : V5} (h : Good B nd v) (hle : V5.leB u v = true) :
    Good B nd u := fun ρ hρ Y hY k w hw =>
  le_trans (V5.le_of_leB hle k) (h ρ hρ Y hY k w hw)

end GridGen.Four.K4
