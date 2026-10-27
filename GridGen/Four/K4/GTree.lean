/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.K4.GNode

/-!
# Height four at `k = 4`: the recurrence on general nodes (layer B3)

Numeric certificate trees for general nodes (`GNode`), the analogue of `CT`:

* a **leaf** (every row placed) is the exact sum over the tuples of the explicit lists
  (`gleafV`): each proper tuple contributes the value of its column type (`leafV`), each improper
  one zero;
* a **pruned** node is nonnegative: for every choice of one colour from each placed row, the
  ordinary node of that choice is prunable (`gpruneOK`, via `pruneOK`);
* a **branching** on a free row `i` is the `t`-bound over the options of the row: a colour of the
  table, a fresh colour of an atom not used up, or a fresh colour outside every list (`gtnode_good`,
  the summed-function recurrence of Codex's (OpenAI) explicit-list branching).
-/

namespace GridGen.Four.K4

open Finset

/-! ### Values -/

/-- Componentwise sum. -/
def V5.add (u v : V5) : V5 :=
  ⟨Zp.add u.a v.a, Zp.add u.b v.b, Zp.add u.c v.c, Zp.add u.d v.d, Zp.add u.e v.e⟩

theorem V5.get_add (u v : V5) (k : Fin 5) :
    ((V5.add u v).get k).val = (u.get k).val + (v.get k).val := by
  fin_cases k <;> simp [V5.add, V5.get]

/-- `∑_{a ∈ L} f a`. -/
def vsumL (L : List ℕ) (f : ℕ → V5) : V5 := L.foldr (fun a acc => V5.add (f a) acc) V5.zero

theorem vsumL_get (L : List ℕ) (f : ℕ → V5) (k : Fin 5) :
    ((vsumL L f).get k).val = (L.map fun a => ((f a).get k).val).sum := by
  induction L with
  | nil => simp [vsumL, V5.get_zero]
  | cons a L ih => simp only [vsumL, List.foldr_cons] at ih ⊢; rw [V5.get_add, ih]; simp

theorem nat_mod_eq' (a b : ℕ) : Nat.mod a b = a % b := rfl

theorem nat_div_eq' (a b : ℕ) : Nat.div a b = a / b := rfl

/-! ### A table of leaf values

The column types summed at the leaves of a shape's trees repeat across all of its theorems. Their
values are proved once, in the shape's table (`GridGen/Four/K4/Data/B3Tab.lean`), and a tuple looks
its type up by key. -/

/-- A search tree of values by key. -/
inductive KV where
  | leaf : KV
  | node : KV → ℕ → V5 → KV → KV

/-- The value of a key, if any. -/
def KV.get : KV → ℕ → Option V5
  | .leaf, _ => none
  | .node l k v r, x => cond (Nat.beq x k) (some v) (cond (Nat.blt x k) (l.get x) (r.get x))

/-- Every entry satisfies `f`. -/
def KV.all (f : ℕ → V5 → Bool) : KV → Bool
  | .leaf => true
  | .node l k v r => l.all f && f k v && r.all f

theorem KV.of_get {f : ℕ → V5 → Bool} : ∀ {t : KV}, t.all f = true → ∀ {x : ℕ} {v : V5},
    t.get x = some v → f x v = true
  | .leaf, _, _, _, hx => by simp [KV.get] at hx
  | .node l k w r, h, x, v, hx => by
    simp only [KV.all, Bool.and_eq_true] at h
    simp only [KV.get] at hx
    cases e : Nat.beq x k
    · rw [e, Bool.cond_false] at hx
      cases e' : Nat.blt x k
      · rw [e', Bool.cond_false] at hx; exact KV.of_get h.2 hx
      · rw [e', Bool.cond_true] at hx; exact KV.of_get h.1.1 hx
    · rw [e, Bool.cond_true, Option.some.injEq] at hx
      rw [Nat.beq_eq] at e; subst e; subst hx; exact h.1.2

/-- A value table: search trees with the largest key of each, in increasing order. -/
def lvGet : List (ℕ × KV) → ℕ → Option V5
  | [], _ => none
  | p :: L, x => cond (Nat.ble x p.1) (p.2.get x) (lvGet L x)

theorem lvGet_spec : ∀ {L : List (ℕ × KV)} {x : ℕ} {v : V5}, lvGet L x = some v →
    ∃ p ∈ L, p.2.get x = some v
  | [], _, _, h => by simp [lvGet] at h
  | p :: L, x, v, h => by
    simp only [lvGet] at h
    cases e : Nat.ble x p.1
    · rw [e, Bool.cond_false] at h
      obtain ⟨q, hq, hm⟩ := lvGet_spec h
      exact ⟨q, List.mem_cons_of_mem _ hq, hm⟩
    · rw [e, Bool.cond_true] at h; exact ⟨p, List.mem_cons_self, h⟩

/-- The key of a column type. -/
def leafKey (m0 m1 m2 m3 : ℕ) (e13 e24 e14 : Bool) : ℕ :=
  Nat.add (Nat.add (Nat.add m0 (Nat.mul 16 m1)) (Nat.add (Nat.mul 256 m2) (Nat.mul 4096 m3)))
    (Nat.mul 65536 (Nat.add (bn e13) (Nat.add (Nat.mul 2 (bn e24)) (Nat.mul 4 (bn e14)))))

/-- The values of the column type of a key. -/
def leafOfKey (I : VN) (k : ℕ) : V5 :=
  leafV I (Nat.mod k 16) (Nat.mod (Nat.div k 16) 16) (Nat.mod (Nat.div k 256) 16)
    (Nat.mod (Nat.div k 4096) 16) (Nat.beq (Nat.mod (Nat.div k 65536) 2) 1)
    (Nat.beq (Nat.mod (Nat.div k 131072) 2) 1) (Nat.beq (Nat.div k 262144) 1)

theorem leafOfKey_leafKey (I : VN) {m0 m1 m2 m3 : ℕ} (e13 e24 e14 : Bool) (h0 : m0 < 16)
    (h1 : m1 < 16) (h2 : m2 < 16) (h3 : m3 < 16) :
    leafOfKey I (leafKey m0 m1 m2 m3 e13 e24 e14) = leafV I m0 m1 m2 m3 e13 e24 e14 := by
  unfold leafOfKey leafKey
  simp only [Nat.add_eq, Nat.mul_eq, nat_mod_eq', nat_div_eq']
  cases e13 <;> cases e24 <;> cases e14 <;> simp only [bn, cond_true, cond_false] <;>
    congr 1 <;> first | omega | (rw [Nat.beq_eq]; omega) | (rw [Bool.eq_false_iff]; intro h; rw [Nat.beq_eq] at h; omega)

/-- A verified value table: each entry is at most the values of its column type. -/
def LvOK (I : VN) (lv : List (ℕ × KV)) : Prop :=
  ∀ p ∈ lv, p.2.all (fun k v => V5.leB v (leafOfKey I k)) = true

theorem lvOK_nil (I : VN) : LvOK I [] := fun _ h => absurd h List.not_mem_nil

theorem lvOK_cons {I : VN} {mx : ℕ} {t : KV} {lv : List (ℕ × KV)}
    (h : t.all (fun k v => V5.leB v (leafOfKey I k)) = true) (ht : LvOK I lv) :
    LvOK I ((mx, t) :: lv) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact h
  · exact ht p hp

/-- The values of a column type, from the table when it is there. -/
def leafT (I : VN) (lv : List (ℕ × KV)) (m0 m1 m2 m3 : ℕ) (e13 e24 e14 : Bool) : V5 :=
  match lvGet lv (leafKey m0 m1 m2 m3 e13 e24 e14) with
  | some v => v
  | none => leafV I m0 m1 m2 m3 e13 e24 e14

theorem leafT_le {I : VN} {lv : List (ℕ × KV)} (hlv : LvOK I lv) {m0 m1 m2 m3 : ℕ}
    (e13 e24 e14 : Bool) (h0 : m0 < 16) (h1 : m1 < 16) (h2 : m2 < 16) (h3 : m3 < 16) (k : Fin 5) :
    ((leafT I lv m0 m1 m2 m3 e13 e24 e14).get k).val
      ≤ ((leafV I m0 m1 m2 m3 e13 e24 e14).get k).val := by
  unfold leafT
  split
  · next v hv =>
    obtain ⟨p, hp, hg⟩ := lvGet_spec hv
    have := KV.of_get (hlv p hp) hg
    rw [leafOfKey_leafKey I e13 e24 e14 h0 h1 h2 h3] at this
    exact V5.le_of_leB this k
  · exact le_refl _

/-- The value of one tuple of colour ids. -/
def tupV (sh : Sh) (lv : List (ℕ × KV)) (cols : List ℕ) (a b c d : ℕ) : V5 :=
  cond (Nat.beq a b || Nat.beq b c || Nat.beq c d) V5.zero
    (leafT sh.I lv (cols.getD a 0) (cols.getD b 0) (cols.getD c 0) (cols.getD d 0) (Nat.beq a c)
      (Nat.beq b d) (Nat.beq a d))

/-- **The value of a fully placed general node.** -/
def gleafV (sh : Sh) (lv : List (ℕ × KV)) (nd : GNode) : Option V5 :=
  match nd.r0, nd.r1, nd.r2, nd.r3 with
  | some L0, some L1, some L2, some L3 =>
    some (vsumL L0 fun a => vsumL L1 fun b => vsumL L2 fun c => vsumL L3 fun d =>
      tupV sh lv nd.cols a b c d)
  | _, _, _, _ => none

/-! ### The sum over a column with explicit rows -/

theorem sum_toFinset_map {ρ : ℕ → ℕ} {L : List ℕ} (hL : L.Nodup)
    (hinj : ∀ a ∈ L, ∀ b ∈ L, ρ a = ρ b → a = b) (f : ℕ → ℤ) :
    ∑ x ∈ (L.map ρ).toFinset, f x = (L.map fun a => f (ρ a)).sum := by
  rw [List.sum_toFinset _ (List.Nodup.map_on hinj hL), List.map_map]
  rfl

/-- **Soundness of a leaf** of a general node. -/
theorem gleaf_good {B : Col} {sh : Sh} (hB : ShapeOf B sh) {lv : List (ℕ × KV)}
    (hlv : LvOK sh.I lv) {nd : GNode} {v : V5} (h : gleafV sh lv nd = some v) : GGood B nd v := by
  obtain ⟨cols, q0, q1, q2, q3⟩ := nd
  unfold gleafV at h
  split at h
  · next L0 L1 L2 L3 e0 e1 e2 e3 =>
    simp only at e0 e1 e2 e3
    subst e0 e1 e2 e3
    rw [Option.some.injEq] at h; subst h
    intro ρ hρ Y _ k w hw
    obtain ⟨hm, hinj, hrows⟩ := hρ
    have R := fun j hj L e => hrows j hj L e
    obtain ⟨b0, n0⟩ := R 0 (by norm_num) L0 rfl
    obtain ⟨b1, n1⟩ := R 1 (by norm_num) L1 rfl
    obtain ⟨b2, n2⟩ := R 2 (by norm_num) L2 rfl
    obtain ⟨b3, n3⟩ := R 3 (by norm_num) L3 rfl
    simp only [GNode.get] at b0 b1 b2 b3 n0 n1 n2 n3
    have inj : ∀ (L : List ℕ), (∀ t ∈ L, t < cols.length) → ∀ a ∈ L, ∀ b ∈ L, ρ a = ρ b → a = b :=
      fun L hL a ha b hb e => hinj a (hL a ha) b (hL b hb) e
    simp only [gfill, gfr, sumP]
    rw [sum_toFinset_map n0 (inj L0 b0)]
    rw [vsumL_get]
    apply List.sum_le_sum; intro a ha
    rw [sum_toFinset_map n1 (inj L1 b1), vsumL_get]
    apply List.sum_le_sum; intro b hb
    rw [sum_toFinset_map n2 (inj L2 b2), vsumL_get]
    apply List.sum_le_sum; intro c hc
    rw [sum_toFinset_map n3 (inj L3 b3), vsumL_get]
    apply List.sum_le_sum; intro d hd
    -- one tuple
    have ha' := b0 a ha; have hb' := b1 b hb; have hc' := b2 c hc; have hd' := b3 d hd
    have eqv : ∀ x y, x < cols.length → y < cols.length → (ρ x = ρ y ↔ x = y) :=
      fun x y hx hy => ⟨hinj x hx y hy, fun e => e ▸ rfl⟩
    unfold tupV
    cases hadj : (Nat.beq a b || Nat.beq b c || Nat.beq c d)
    · rw [cond_false]
      simp only [Bool.or_eq_false_iff] at hadj
      obtain ⟨⟨nab, nbc⟩, ncd⟩ := hadj
      have hs : Proper (ρ a, ρ b, ρ c, ρ d) :=
        ⟨fun e => ne_of_beq_false nab ((eqv a b ha' hb').mp e),
          fun e => ne_of_beq_false nbc ((eqv b c hb' hc').mp e),
          fun e => ne_of_beq_false ncd ((eqv c d hc' hd').mp e)⟩
      have := leafV_sound B sh.I hB.2.1 hs k w hw
      simp only [r1, r2, r3, r4] at this
      rw [hm a ha', hm b hb', hm c hc', hm d hd'] at this
      have d02 : decide (ρ a = ρ c) = Nat.beq a c := by
        rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.beq_eq]; exact eqv a c ha' hc'
      have d13 : decide (ρ b = ρ d) = Nat.beq b d := by
        rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.beq_eq]; exact eqv b d hb' hd'
      have d03 : decide (ρ a = ρ d) = Nat.beq a d := by
        rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.beq_eq]; exact eqv a d ha' hd'
      rw [d02, d13, d03] at this
      have mlt : ∀ x, x < cols.length → cols.getD x 0 < 16 := fun x hx => by
        rw [← hm x hx]; exact mv_lt B _
      exact le_trans (leafT_le hlv _ _ _ (mlt a ha') (mlt b hb') (mlt c hc') (mlt d hd') k) this
    · rw [cond_true, V5.get_zero]
      apply le_of_eq; symm
      apply gw_improper
      simp only [Bool.or_eq_true, Nat.beq_eq] at hadj
      rintro ⟨p1, p2, p3⟩
      rcases hadj with (e | e) | e
      · exact p1 (by rw [e])
      · exact p2 (by rw [e])
      · exact p3 (by rw [e])
  · exact absurd h (by simp)


/-! ### Pruning through ordinary nodes -/

/-- **Pointwise pruning** (the inside of `prune_good`): every proper completion of a prunable
ordinary node contributes nonnegatively. -/
theorem prune_pt {B : Col} {sh : Sh} (hB : ShapeOf B sh) {nd : Node} (h : pruneOK sh nd = true)
    {ρ : ℕ → ℕ} (hρ : nd.Real B ρ) {s : T4} (hs : Proper s) (hcomp : Completes nd ρ s)
    (k : Fin 5) (w : Q) (hw : w ∈ famW k) : 0 ≤ gw B w s := by
  obtain ⟨x, hx, hle⟩ := regionAt_sound hB hρ hs hcomp
  have he := epat_mem hs
  unfold pruneOK at h
  have h1 := List.all_eq_true.mp h _ he
  rw [consistent_epat hρ hs hcomp, Bool.not_true, Bool.false_or] at h1
  have h2 := allBelow_spec h1 (x := ownOf B s) (by
    unfold ownOf; simp only [bn, Nat.add_eq, Nat.mul_eq]
    cases Nat.testBit (mv B (r1 s)) 0 <;> cases Nat.testBit (mv B (r2 s)) 1 <;>
      cases Nat.testBit (mv B (r3 s)) 2 <;> cases Nat.testBit (mv B (r4 s)) 3 <;> simp)
  have hoc := ownCompat_own hρ hs hcomp
  rw [hoc, Bool.not_true, Bool.false_or, hx] at h2
  unfold regionNN at h2
  exact le_trans (V5.nonneg_get h2 k) (hle k w hw)

/-- Equality of optional ids, as a check. -/
def optBEq : Option ℕ → Option ℕ → Bool
  | some a, some b => Nat.beq a b
  | none, none => true
  | _, _ => false

theorem optBEq_iff (a b : Option ℕ) : optBEq a b = true ↔ a = b := by
  rcases a with _ | a <;> rcases b with _ | b <;> simp [optBEq, Nat.beq_eq]

/-- The four chosen ids. -/
def cget (c0 c1 c2 c3 : Option ℕ) : ℕ → Option ℕ
  | 0 => c0
  | 1 => c1
  | 2 => c2
  | _ => c3

/-- The first row with the same chosen id. -/
def otag (c0 c1 c2 c3 : Option ℕ) (j : ℕ) : ℕ :=
  cond (optBEq c0 (cget c0 c1 c2 c3 j)) 0 (cond (optBEq c1 (cget c0 c1 c2 c3 j)) 1
    (cond (optBEq c2 (cget c0 c1 c2 c3 j)) 2 3))

/-- The ordinary node of a choice of one id per placed row. -/
def ordNode (cols : List ℕ) (c0 c1 c2 c3 : Option ℕ) : Node :=
  let pl := fun (c : Option ℕ) (j : ℕ) => match c with
    | some a => some (cols.getD a 0, otag c0 c1 c2 c3 j)
    | none => none
  ⟨pl c0 0, pl c1 1, pl c2 2, pl c3 3⟩

theorem ordNode_get (cols : List ℕ) (c0 c1 c2 c3 : Option ℕ) {j : ℕ} (hj : j < 4) :
    (ordNode cols c0 c1 c2 c3).get j = match cget c0 c1 c2 c3 j with
      | some a => some (cols.getD a 0, otag c0 c1 c2 c3 j)
      | none => none := by
  interval_cases j <;> rfl

theorem otag_spec (c0 c1 c2 c3 : Option ℕ) {j : ℕ} (hj : j < 4) :
    otag c0 c1 c2 c3 j < 4 ∧ cget c0 c1 c2 c3 (otag c0 c1 c2 c3 j) = cget c0 c1 c2 c3 j ∧
      ∀ r < 4, cget c0 c1 c2 c3 r = cget c0 c1 c2 c3 j →
        otag c0 c1 c2 c3 r = otag c0 c1 c2 c3 j := by
  refine ⟨?_, ?_, ?_⟩
  · unfold otag
    cases optBEq c0 (cget c0 c1 c2 c3 j) <;> cases optBEq c1 (cget c0 c1 c2 c3 j) <;>
      cases optBEq c2 (cget c0 c1 c2 c3 j) <;> simp
  · unfold otag
    cases h0 : optBEq c0 (cget c0 c1 c2 c3 j)
    · cases h1 : optBEq c1 (cget c0 c1 c2 c3 j)
      · cases h2 : optBEq c2 (cget c0 c1 c2 c3 j)
        · simp only [cond_false]
          have n0 := mt (optBEq_iff _ _).mpr (by rw [h0]; decide)
          have n1 := mt (optBEq_iff _ _).mpr (by rw [h1]; decide)
          have n2 := mt (optBEq_iff _ _).mpr (by rw [h2]; decide)
          interval_cases j <;> simp_all [cget]
        · simp only [cond_false, cond_true]; exact (optBEq_iff _ _).mp h2
      · simp only [cond_false, cond_true]; exact (optBEq_iff _ _).mp h1
    · simp only [cond_true]; exact (optBEq_iff _ _).mp h0
  · intro r _ e
    unfold otag
    rw [e]

/-- All choices of one id per placed row. -/
def optAll (p : Option (List ℕ)) (f : Option ℕ → Bool) : Bool :=
  match p with
  | some L => L.all fun a => f (some a)
  | none => f none

/-! ### A table of prunable ordinary nodes

The same ordinary node is pruned many times in the trees of one shape (from different general
nodes and different choices of ids). A shape's prunable nodes are therefore proved once, in a table
(`GridGen/Four/K4/Data/B3Tab.lean`), and a choice is looked up there by the key of its node. -/

/-- A search tree of naturals. -/
inductive KT where
  | leaf : KT
  | node : KT → ℕ → KT → KT

/-- Membership (the search order is only for speed: a `true` answer is always a key of the tree). -/
def KT.mem : KT → ℕ → Bool
  | .leaf, _ => false
  | .node l k r, x => cond (Nat.beq x k) true (cond (Nat.blt x k) (l.mem x) (r.mem x))

/-- Every key satisfies `f`. -/
def KT.all (f : ℕ → Bool) : KT → Bool
  | .leaf => true
  | .node l k r => l.all f && f k && r.all f

theorem KT.of_mem {f : ℕ → Bool} : ∀ {t : KT}, t.all f = true → ∀ {x : ℕ}, t.mem x = true → f x = true
  | .leaf, _, _, hx => by simp [KT.mem] at hx
  | .node l k r, h, x, hx => by
    simp only [KT.all, Bool.and_eq_true] at h
    simp only [KT.mem] at hx
    cases e : Nat.beq x k
    · rw [e, Bool.cond_false] at hx
      cases e' : Nat.blt x k
      · rw [e', Bool.cond_false] at hx; exact KT.of_mem h.2 hx
      · rw [e', Bool.cond_true] at hx; exact KT.of_mem h.1.1 hx
    · rw [Nat.beq_eq] at e; subst e; exact h.1.2

/-- A table: search trees with the largest key of each, in increasing order. -/
def tabMem : List (ℕ × KT) → ℕ → Bool
  | [], _ => false
  | p :: L, x => cond (Nat.ble x p.1) (p.2.mem x) (tabMem L x)

theorem tabMem_spec : ∀ {L : List (ℕ × KT)} {x : ℕ}, tabMem L x = true → ∃ p ∈ L, p.2.mem x = true
  | [], _, h => by simp [tabMem] at h
  | p :: L, x, h => by
    simp only [tabMem] at h
    cases e : Nat.ble x p.1
    · rw [e, Bool.cond_false] at h
      obtain ⟨q, hq, hm⟩ := tabMem_spec h
      exact ⟨q, List.mem_cons_of_mem _ hq, hm⟩
    · rw [e, Bool.cond_true] at h; exact ⟨p, List.mem_cons_self, h⟩

/-- The key of a placed row. -/
def plKey (p : Pl) : ℕ :=
  match p with
  | some (m, t) => Nat.add 1 (Nat.add m (Nat.mul 16 t))
  | none => 0

/-- The key of an ordinary node. -/
def nodeKey (nd : Node) : ℕ :=
  Nat.add (Nat.add (plKey nd.r0) (Nat.mul 128 (plKey nd.r1)))
    (Nat.add (Nat.mul 16384 (plKey nd.r2)) (Nat.mul 2097152 (plKey nd.r3)))

/-- The placed row of a key. -/
def plOfKey (c : ℕ) : Pl :=
  cond (Nat.beq c 0) none (some (Nat.mod (Nat.sub c 1) 16, Nat.div (Nat.sub c 1) 16))

/-- The ordinary node of a key. -/
def nodeOfKey (k : ℕ) : Node :=
  ⟨plOfKey (Nat.mod k 128), plOfKey (Nat.mod (Nat.div k 128) 128),
    plOfKey (Nat.mod (Nat.div k 16384) 128), plOfKey (Nat.div k 2097152)⟩

/-- A placed row with a mask and a tag in range. -/
def plValid (p : Pl) : Bool :=
  match p with
  | some (m, t) => Nat.blt m 16 && Nat.blt t 4
  | none => true

/-- An ordinary node with masks and tags in range: its key determines it. -/
def nodeValid (nd : Node) : Bool :=
  plValid nd.r0 && plValid nd.r1 && plValid nd.r2 && plValid nd.r3

theorem plKey_lt {p : Pl} (h : plValid p = true) : plKey p < 128 := by
  rcases p with _ | ⟨m, t⟩
  · simp [plKey]
  · simp only [plValid, Bool.and_eq_true, Nat.blt_eq] at h
    simp only [plKey, Nat.add_eq, Nat.mul_eq]; omega

theorem plOfKey_plKey {p : Pl} (h : plValid p = true) : plOfKey (plKey p) = p := by
  rcases p with _ | ⟨m, t⟩
  · rfl
  · simp only [plValid, Bool.and_eq_true, Nat.blt_eq] at h
    have h1 : Nat.beq (plKey (some (m, t))) 0 = false := by
      cases e : Nat.beq (plKey (some (m, t))) 0
      · rfl
      · rw [Nat.beq_eq] at e; simp only [plKey, Nat.add_eq, Nat.mul_eq] at e; omega
    simp only [plOfKey, h1, Bool.cond_false, Option.some.injEq, Prod.mk.injEq]
    simp only [plKey, Nat.add_eq, Nat.mul_eq, Nat.sub_eq, nat_mod_eq', nat_div_eq']
    omega

theorem nodeOfKey_nodeKey {nd : Node} (h : nodeValid nd = true) : nodeOfKey (nodeKey nd) = nd := by
  obtain ⟨p0, p1, p2, p3⟩ := nd
  simp only [nodeValid, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  have l0 := plKey_lt h0
  have l1 := plKey_lt h1
  have l2 := plKey_lt h2
  have l3 := plKey_lt h3
  simp only [nodeOfKey, nodeKey, Nat.add_eq, Nat.mul_eq, nat_mod_eq', nat_div_eq']
  have e0 : (plKey p0 + 128 * plKey p1 + (16384 * plKey p2 + 2097152 * plKey p3)) % 128
      = plKey p0 := by omega
  have e1 : (plKey p0 + 128 * plKey p1 + (16384 * plKey p2 + 2097152 * plKey p3)) / 128 % 128
      = plKey p1 := by omega
  have e2 : (plKey p0 + 128 * plKey p1 + (16384 * plKey p2 + 2097152 * plKey p3)) / 16384 % 128
      = plKey p2 := by omega
  have e3 : (plKey p0 + 128 * plKey p1 + (16384 * plKey p2 + 2097152 * plKey p3)) / 2097152
      = plKey p3 := by omega
  rw [e0, e1, e2, e3, plOfKey_plKey h0, plOfKey_plKey h1, plOfKey_plKey h2, plOfKey_plKey h3]

/-- **A table of prunable nodes** of a shape. -/
def TabOK (sh : Sh) (tab : List (ℕ × KT)) : Prop :=
  ∀ p ∈ tab, p.2.all (fun k => pruneOK sh (nodeOfKey k)) = true

theorem tabOK_nil (sh : Sh) : TabOK sh [] := fun _ h => absurd h List.not_mem_nil

theorem tabOK_cons {sh : Sh} {mx : ℕ} {t : KT} {tab : List (ℕ × KT)}
    (h : t.all (fun k => pruneOK sh (nodeOfKey k)) = true) (ht : TabOK sh tab) :
    TabOK sh ((mx, t) :: tab) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact h
  · exact ht p hp

/-- A node found in the table is prunable; otherwise it is checked directly. -/
def pruneTab (sh : Sh) (tab : List (ℕ × KT)) (nd : Node) : Bool :=
  (nodeValid nd && tabMem tab (nodeKey nd)) || pruneOK sh nd

theorem pruneOK_of_tab {sh : Sh} {tab : List (ℕ × KT)} (htab : TabOK sh tab) {nd : Node}
    (h : pruneTab sh tab nd = true) : pruneOK sh nd = true := by
  unfold pruneTab at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rw [Bool.and_eq_true] at h
    obtain ⟨p, hp, hm⟩ := tabMem_spec h.2
    have := KT.of_mem (htab p hp) hm
    rwa [nodeOfKey_nodeKey h.1] at this
  · exact h

/-- **A prunable general node**: every choice gives a prunable ordinary node. -/
def gpruneOK (sh : Sh) (tab : List (ℕ × KT)) (nd : GNode) : Bool :=
  optAll nd.r0 fun c0 => optAll nd.r1 fun c1 => optAll nd.r2 fun c2 => optAll nd.r3 fun c3 =>
    pruneTab sh tab (ordNode nd.cols c0 c1 c2 c3)

/-- **The tables of a shape**: its prunable nodes and its leaf values. -/
structure BTab where
  pr : List (ℕ × KT)
  lv : List (ℕ × KV)

/-- Verified tables. -/
def BTabOK (sh : Sh) (t : BTab) : Prop := TabOK sh t.pr ∧ LvOK sh.I t.lv

theorem optAll_spec {p : Option (List ℕ)} {f : Option ℕ → Bool} (h : optAll p f = true)
    {ρ : ℕ → ℕ} {Y : Finset ℕ} {x : ℕ} (hx : x ∈ gfr p ρ Y) :
    ∃ c, f c = true ∧ (∀ a, c = some a → ρ a = x ∧ ∃ L, p = some L ∧ a ∈ L) ∧
      (c = none → p = none) := by
  cases p with
  | none => exact ⟨none, h, fun a e => absurd e (by simp), fun _ => rfl⟩
  | some L =>
    simp only [gfr, List.mem_toFinset, List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨some a, List.all_eq_true.mp h a ha, fun a' e => by
      simp only [Option.some.injEq] at e; subst e; exact ⟨rfl, L, rfl, ha⟩, fun e => absurd e (by simp)⟩

/-- **Soundness of pruning** a general node. -/
theorem gprune_good {B : Col} {sh : Sh} (hB : ShapeOf B sh) {tab : List (ℕ × KT)}
    (htab : TabOK sh tab) {nd : GNode} (h : gpruneOK sh tab nd = true) : GGood B nd V5.zero := by
  intro ρ hρ Y _ k w hw
  rw [V5.get_zero]
  apply Finset.sum_nonneg; intro a ha
  apply Finset.sum_nonneg; intro b hb
  apply Finset.sum_nonneg; intro c hc
  apply Finset.sum_nonneg; intro d hd
  by_cases hs : Proper (a, b, c, d)
  · unfold gpruneOK at h
    obtain ⟨c0, h0, s0, z0⟩ := optAll_spec h ha
    obtain ⟨c1, h1, s1, z1⟩ := optAll_spec h0 hb
    obtain ⟨c2, h2, s2, z2⟩ := optAll_spec h1 hc
    obtain ⟨c3, h3, s3, z3⟩ := optAll_spec h2 hd
    set s : T4 := (a, b, c, d)
    -- the chosen id of a placed row realizes the tuple's colour there
    have hS : ∀ j < 4, ∀ a', cget c0 c1 c2 c3 j = some a' →
        ρ a' = rowT s j ∧ ∃ L, nd.get j = some L ∧ a' ∈ L := by
      intro j hj a' e
      interval_cases j
      · obtain ⟨e1, L, e2, e3⟩ := s0 a' e; exact ⟨e1, L, e2, e3⟩
      · obtain ⟨e1, L, e2, e3⟩ := s1 a' e; exact ⟨e1, L, e2, e3⟩
      · obtain ⟨e1, L, e2, e3⟩ := s2 a' e; exact ⟨e1, L, e2, e3⟩
      · obtain ⟨e1, L, e2, e3⟩ := s3 a' e; exact ⟨e1, L, e2, e3⟩
    have hlt : ∀ j < 4, ∀ a', cget c0 c1 c2 c3 j = some a' → a' < nd.cols.length := by
      intro j hj a' e
      obtain ⟨-, L, eL, ha'⟩ := hS j hj a' e
      exact (hρ.2.2 j hj L eL).1 a' ha'
    -- the ordinary node and its realization by the tuple itself
    set O := ordNode nd.cols c0 c1 c2 c3
    have hO : O.Real B (rowT s) := by
      intro j hj m t e
      rw [ordNode_get _ _ _ _ _ hj] at e
      obtain ⟨ot4, oc, oeq⟩ := otag_spec c0 c1 c2 c3 hj
      cases hcj : cget c0 c1 c2 c3 j with
      | none => rw [hcj] at e; exact absurd e (by simp)
      | some a' =>
        rw [hcj] at e
        simp only [Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        have hct : cget c0 c1 c2 c3 (otag c0 c1 c2 c3 j) = some a' := oc.trans hcj
        refine ⟨ot4, ?_, ?_, ?_⟩
        · rw [ordNode_get _ _ _ _ _ ot4, hct, oeq _ ot4 oc]
        · rw [← (hS _ ot4 a' hct).1]; exact hρ.1 a' (hlt j hj a' hcj)
        · intro j' hj' m' t' e' he
          rw [ordNode_get _ _ _ _ _ hj'] at e'
          cases hcj' : cget c0 c1 c2 c3 j' with
          | none => rw [hcj'] at e'; exact absurd e' (by simp)
          | some b' =>
            rw [hcj'] at e'
            simp only [Option.some.injEq, Prod.mk.injEq] at e'
            obtain ⟨-, rfl⟩ := e'
            obtain ⟨ot4', oc', oeq'⟩ := otag_spec c0 c1 c2 c3 hj'
            have hct' : cget c0 c1 c2 c3 (otag c0 c1 c2 c3 j') = some b' := oc'.trans hcj'
            have r1' := (hS _ ot4 a' hct).1
            have r2' := (hS _ ot4' b' hct').1
            have hab : a' = b' := hρ.2.1 a' (hlt _ ot4 a' hct) b' (hlt _ ot4' b' hct')
              (r1'.trans (he.trans r2'.symm))
            subst hab
            exact oeq' _ hj (hcj.trans hcj'.symm)
    have hC : Completes O (rowT s) s := by
      intro j hj m t e
      rw [ordNode_get _ _ _ _ _ hj] at e
      obtain ⟨ot4, oc, -⟩ := otag_spec c0 c1 c2 c3 hj
      cases hcj : cget c0 c1 c2 c3 j with
      | none => rw [hcj] at e; exact absurd e (by simp)
      | some a' =>
        rw [hcj] at e
        simp only [Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨-, rfl⟩ := e
        rw [← (hS j hj a' hcj).1, ← (hS _ ot4 a' (oc.trans hcj)).1]
    exact prune_pt hB (pruneOK_of_tab htab h3) hO hs hC k w hw
  · exact le_of_eq (gw_improper B w hs).symm


/-! ### Branching on a free row -/

/-- An option for a free row of a general node. -/
inductive GOpt where
  | old (t : ℕ) (imp : Bool)
  | fresh (m μ : ℕ)

/-- The row is the single colour `t`. -/
def gsingle (p : Option (List ℕ)) (t : ℕ) : Bool :=
  match p with
  | some [a] => Nat.beq a t
  | _ => false

/-- A neighbour of row `i` is the single colour `t`. -/
def gadj (nd : GNode) (i t : ℕ) : Bool :=
  match i with
  | 0 => gsingle nd.r1 t
  | 1 => gsingle nd.r0 t || gsingle nd.r2 t
  | 2 => gsingle nd.r1 t || gsingle nd.r3 t
  | _ => gsingle nd.r2 t

/-- **The options of a free row**: each colour of the table, and a fresh colour of every atom not
used up (the outside colour excluded). -/
def gopts (sh : Sh) (nd : GNode) (i : ℕ) : List GOpt :=
  (List.range nd.cols.length).map (fun t => GOpt.old t (gadj nd i t)) ++
    (shAtoms sh).filterMap fun p =>
      let μ := Nat.sub p.2 (gcnt nd.cols p.1)
      cond (Nat.blt 0 μ) (some (GOpt.fresh p.1 μ)) none

/-- The node after choosing an option. -/
def GOpt.child (nd : GNode) (i : ℕ) : GOpt → GNode
  | .old t _ => nd.set i (some [t])
  | .fresh m _ => (nd.addCols [m]).set i (some [nd.cols.length])

/-- The node after choosing the outside colour. -/
def goutChild (nd : GNode) (i : ℕ) : GNode := (nd.addCols [0]).set i (some [nd.cols.length])

def GOpt.mult : GOpt → ℕ
  | .old _ _ => 1
  | .fresh _ μ => μ

def GOpt.imp : GOpt → Bool
  | .old _ b => b
  | .fresh _ _ => false

mutual
/-- A numeric certificate tree for a general node. -/
inductive GCT where
  | leaf : GCT
  | prune : GCT
  | node : ℕ → List ℕ → GCTL → GCT → GCT
/-- A list of numeric certificate trees. -/
inductive GCTL where
  | nil : GCTL
  | cons : GCT → GCTL → GCTL
end

mutual
/-- **The value of a numeric certificate tree** at a general node. -/
def evalGCT (sh : Sh) (tab : BTab) (nd : GNode) : GCT → Option V5
  | .leaf => gleafV sh tab.lv nd
  | .prune => cond (gpruneOK sh tab.pr nd) (some V5.zero) none
  | .node i ts kids ok =>
    cond (Nat.blt i 4 && (nd.get i).isNone)
      (match evalGKids sh tab nd i (gopts sh nd i) kids, evalGCT sh tab (goutChild nd i) ok with
        | some L, some vo => some (tcombV L vo ts)
        | _, _ => none)
      none
/-- The values of the options of a free row. -/
def evalGKids (sh : Sh) (tab : BTab) (nd : GNode) (i : ℕ) (os : List GOpt) :
    GCTL → Option (List (V5 × ℕ))
  | .nil =>
    match os with
    | [] => some []
    | _ :: _ => none
  | .cons k ks =>
    match os with
    | [] => none
    | o :: os' =>
      match cond o.imp (some V5.zero) (evalGCT sh tab (o.child nd i) k), evalGKids sh tab nd i os' ks with
      | some v, some L => some ((v, o.mult) :: L)
      | _, _ => none
end

/-! ### Soundness of a branching -/

theorem gsetC_fill {nd : GNode} {ρ ρ' : ℕ → ℕ} {B : Col} (hρ : nd.Real B ρ) (Y : Col) {i : ℕ}
    (hi : i < 4) (hfree : nd.get i = none) (hagree : ∀ t < nd.cols.length, ρ' t = ρ t)
    (ms : List ℕ) (t x : ℕ) (hx : ρ' t = x) :
    setC (gfill nd ρ Y) i {x} = gfill ((nd.addCols ms).set i (some [t])) ρ' Y := by
  obtain ⟨cols, q0, q1, q2, q3⟩ := nd
  have fr : ∀ j < 4, ∀ (p : Option (List ℕ)), (⟨cols, q0, q1, q2, q3⟩ : GNode).get j = p →
      ∀ Z, gfr p ρ Z = gfr p ρ' Z := by
    intro j hj p e Z
    cases p with
    | none => rfl
    | some L =>
      have hL := (hρ.2.2 j hj L e).1
      simp only [gfr]
      congr 1
      exact List.map_congr_left (fun a ha => (hagree a (hL a ha)).symm)
  have fs : ∀ Z : Finset ℕ, gfr (some [t]) ρ' Z = {x} := fun Z => by simp [gfr, hx]
  have h0 := fr 0 (by norm_num) q0 rfl
  have h1 := fr 1 (by norm_num) q1 rfl
  have h2 := fr 2 (by norm_num) q2 rfl
  have h3 := fr 3 (by norm_num) q3 rfl
  interval_cases i <;> simp only [GNode.get] at hfree <;> subst hfree <;>
    simp only [gfill, setC, GNode.set, GNode.addCols, fs, h0, h1, h2, h3]

theorem greal_old {B : Col} {nd : GNode} {ρ : ℕ → ℕ} (hρ : nd.Real B ρ) {i t : ℕ} (hi : i < 4)
    (ht : t < nd.cols.length) : (nd.set i (some [t])).Real B ρ := by
  obtain ⟨hm, hinj, hrows⟩ := hρ
  refine ⟨by rw [GNode.cols_set]; exact hm, by rw [GNode.cols_set]; exact hinj, ?_⟩
  intro j hj L e
  rw [GNode.cols_set]
  by_cases hji : j = i
  · subst hji; rw [GNode.get_set_same _ hj] at e
    simp only [Option.some.injEq] at e; subst e
    exact ⟨by simpa using ht, List.nodup_singleton t⟩
  · rw [GNode.get_set_ne _ hi hj hji] at e; exact hrows j hj L e

theorem greal_fresh {B : Col} {nd : GNode} {ρ : ℕ → ℕ} (hρ : nd.Real B ρ) {i m x : ℕ} (hi : i < 4)
    (hx : x ∉ gcolSet nd ρ) (hm : mv B x = m) :
    ((nd.addCols [m]).set i (some [nd.cols.length])).Real B
      (Function.update ρ nd.cols.length x) := by
  obtain ⟨hmk, hinj, hrows⟩ := hρ
  have hlen : ((nd.addCols [m]).set i (some [nd.cols.length])).cols = nd.cols ++ [m] := by
    rw [GNode.cols_set]; rfl
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rw [hlen] at ht ⊢
    rw [List.length_append, List.length_singleton] at ht
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
    · rw [Function.update_of_ne (by omega), List.getD_append _ _ _ _ ht]; exact hmk t ht
    · rw [Function.update_self, List.getD_append_right _ _ _ _ le_rfl]; simpa using hm
  · intro t ht t' ht' e
    rw [hlen, List.length_append, List.length_singleton] at ht ht'
    have hne : ∀ s < nd.cols.length, ρ s ≠ x := fun s hs e' =>
      hx (Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr hs, e'⟩)
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl <;>
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht' with ht' | rfl
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)] at e
      exact hinj t ht t' ht' e
    · rw [Function.update_of_ne (by omega), Function.update_self] at e; exact absurd e (hne t ht)
    · rw [Function.update_self, Function.update_of_ne (by omega)] at e
      exact absurd e.symm (hne t' ht')
    · rfl
  · intro j hj L e
    rw [hlen, List.length_append, List.length_singleton]
    by_cases hji : j = i
    · subst hji; rw [GNode.get_set_same _ hj] at e
      simp only [Option.some.injEq] at e; subst e
      exact ⟨by simp, List.nodup_singleton _⟩
    · rw [GNode.get_set_ne _ hi hj hji, GNode.get_addCols] at e
      obtain ⟨h1, h2⟩ := hrows j hj L e
      exact ⟨fun t ht => by have := h1 t ht; omega, h2⟩

theorem gsingle_iff (p : Option (List ℕ)) (t : ℕ) : gsingle p t = true ↔ p = some [t] := by
  unfold gsingle
  split
  · next a => simp [Nat.beq_eq]
  · next h => simp only [Bool.false_eq_true, false_iff]; intro e; subst e; exact h t rfl

theorem gadj_spec {nd : GNode} {i t : ℕ} (hi : i < 4) (h : gadj nd i t = true) :
    ∃ i' < 4, (i' + 1 = i ∨ i' = i + 1) ∧ nd.get i' = some [t] := by
  interval_cases i <;> simp only [gadj, Bool.or_eq_true, gsingle_iff] at h
  · exact ⟨1, by norm_num, Or.inr rfl, h⟩
  · rcases h with h | h
    · exact ⟨0, by norm_num, Or.inl rfl, h⟩
    · exact ⟨2, by norm_num, Or.inr rfl, h⟩
  · rcases h with h | h
    · exact ⟨1, by norm_num, Or.inl rfl, h⟩
    · exact ⟨3, by norm_num, Or.inr rfl, h⟩
  · exact ⟨2, by norm_num, Or.inl rfl, h⟩

theorem gadj_zero {B : Col} (w : Q) {nd : GNode} {ρ : ℕ → ℕ} (Y : Col) {i t : ℕ} (hi : i < 4)
    (h : gadj nd i t = true) : sumP (gw B w) (setC (gfill nd ρ Y) i {ρ t}) = 0 := by
  obtain ⟨i', hi', hadj, e⟩ := gadj_spec hi h
  have hne : i' ≠ i := by omega
  have r1 := rowC_setC_same (gfill nd ρ Y) hi {ρ t}
  have r2 : rowC (setC (gfill nd ρ Y) i {ρ t}) i' = {ρ t} := by
    rw [rowC_setC_ne _ hi hi' hne, rowC_gfill _ _ _ hi', e]; simp [gfr]
  rcases hadj with h1 | h1
  · subst h1; exact sumP_adj_zero B w _ (by omega) r2 r1
  · subst h1; exact sumP_adj_zero B w _ (by omega) r1 r2

/-- What the value of an option certifies. -/
def GOptVal (B : Col) (nd : GNode) (i : ℕ) (o : GOpt) (p : V5 × ℕ) : Prop :=
  p.2 = o.mult ∧ (o.imp = true → p.1 = V5.zero) ∧ (o.imp = false → GGood B (o.child nd i) p.1)

/-- The colours an option stands for. -/
def gpredOf (B : Col) (nd : GNode) (ρ : ℕ → ℕ) : GOpt → ℕ → Bool
  | .old t _, x => decide (x = ρ t)
  | .fresh m _, x => decide (mv B x = m ∧ x ∉ gcolSet nd ρ)

theorem mem_gopts {sh : Sh} {nd : GNode} {i : ℕ} {o : GOpt} (h : o ∈ gopts sh nd i) :
    (∃ t < nd.cols.length, o = GOpt.old t (gadj nd i t)) ∨
      ∃ m μ, 0 < m ∧ m < 16 ∧ μ = Nat.sub (sh.na m) (gcnt nd.cols m) ∧ o = GOpt.fresh m μ := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h
    exact Or.inl ⟨t, List.mem_range.mp ht, rfl⟩
  · right
    obtain ⟨p, hp, e⟩ := List.mem_filterMap.mp h
    obtain ⟨h1, h2, h3⟩ := mem_shAtoms hp
    cases hb : Nat.blt 0 (Nat.sub p.2 (gcnt nd.cols p.1))
    · simp only [hb, Bool.cond_false] at e; exact absurd e (by simp)
    · simp only [hb, Bool.cond_true, Option.some.injEq] at e
      exact ⟨p.1, _, h1, h2, by rw [h3], e.symm⟩

theorem old_mem_gopts (sh : Sh) (nd : GNode) (i : ℕ) {t : ℕ} (ht : t < nd.cols.length) :
    GOpt.old t (gadj nd i t) ∈ gopts sh nd i :=
  List.mem_append_left _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)

theorem fresh_mem_gopts (sh : Sh) (nd : GNode) (i : ℕ) {m : ℕ} (h0 : 0 < m) (h16 : m < 16)
    (hpos : 0 < Nat.sub (sh.na m) (gcnt nd.cols m)) :
    GOpt.fresh m (Nat.sub (sh.na m) (gcnt nd.cols m)) ∈ gopts sh nd i := by
  refine List.mem_append_right _ (List.mem_filterMap.mpr ⟨(m, sh.na m),
    atom_mem_shAtoms sh h0 h16 (by simp only [Nat.sub_eq] at hpos; omega), ?_⟩)
  have : Nat.blt 0 (Nat.sub (sh.na m) (gcnt nd.cols m)) = true := by rw [Nat.blt_eq]; exact hpos
  simp only [this, Bool.cond_true]

/-- **Soundness of a branching** of a general node. -/
theorem gtnode_good {B : Col} {sh : Sh} (hB : ShapeOf B sh) {nd : GNode} {i : ℕ} (hi : i < 4)
    (hfree : nd.get i = none) {L : List (V5 × ℕ)}
    (hL : List.Forall₂ (GOptVal B nd i) (gopts sh nd i) L) {vo : V5}
    (hvo : GGood B (goutChild nd i) vo) (ts : List ℕ) : GGood B nd (tcombV L vo ts) := by
  intro ρ hρ Y hY k w hw
  set Z := gfill nd ρ Y
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
    rw [sumP_split _ _ i hi, rowC_gfill _ _ _ hi, hfree]; rfl
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
  have hagree : ∀ x, ∀ t' < nd.cols.length, Function.update ρ nd.cols.length x t' = ρ t' :=
    fun x t' ht' => Function.update_of_ne (by omega) _ _
  have hout : ∀ x, x ∉ gcolSet nd ρ → mv B x = 0 → (vo.get k).val ≤ h x := by
    intro x hx hm
    have hr := greal_fresh hρ hi hx hm
    have hf := gsetC_fill hρ Y hi hfree (hagree x) [0] nd.cols.length x (Function.update_self _ _ _)
    have := hvo _ hr Y hY k w hw
    simp only [h]; rw [hf]; exact this
  have hopt : ∀ o ∈ gopts sh nd i, ∀ p, GOptVal B nd i o p → ∀ x, gpredOf B nd ρ o x = true →
      (p.1.get k).val ≤ h x := by
    intro o ho p hp x hx
    obtain ⟨-, himp, hgood⟩ := hp
    rcases mem_gopts ho with ⟨t', ht', rfl⟩ | ⟨m, μ, h0, h16, -, rfl⟩
    · simp only [gpredOf, decide_eq_true_eq] at hx; subst hx
      cases hadj : gadj nd i t'
      · have hg := hgood hadj
        have hr := greal_old hρ hi ht'
        have hf := gsetC_fill hρ Y hi hfree (fun _ _ => rfl) [] t' (ρ t') rfl
        have hset : (nd.addCols []).set i (some [t']) = nd.set i (some [t']) := by
          simp [GNode.addCols]
        rw [hset] at hf
        have := hg ρ hr Y hY k w hw
        simp only [h]; rw [hf]; exact this
      · rw [himp hadj, V5.get_zero]
        simp only [h]; rw [gadj_zero w Y hi hadj]
    · simp only [gpredOf, decide_eq_true_eq] at hx
      have hg := hgood rfl
      have hr := greal_fresh hρ hi hx.2 hx.1
      have hf := gsetC_fill hρ Y hi hfree (hagree x) [m] nd.cols.length x (Function.update_self _ _ _)
      have := hg _ hr Y hY k w hw
      simp only [h]; rw [hf]; exact this
  set C : List Cls := (List.zip (gopts sh nd i) L).map fun q =>
    (gpredOf B nd ρ q.1, (q.2.1.get k).val, q.2.2)
  have hCsum : (C.map fun c => (c.2.2 : ℤ) * min 0 (c.2.1 - t)).sum
      = (Lk.map fun p => (p.2 : ℤ) * min 0 (p.1.val - t)).sum := by
    simp only [C, Lk, List.map_map]
    congr 1
    exact forall₂_map_snd (fun p : V5 × ℕ => (p.2 : ℤ) * min 0 ((p.1.get k).val - t)) hL
  have hall := List.forall₂_iff_zip.mp hL
  have hcls := sum_classes t (fun x => min 0 (h x - t)) (fun x => min_le_left _ _) C Yi
    (by
      intro x hx
      by_cases hp : x ∈ gcolSet nd ρ
      · left
        obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp hp
        have hmem := old_mem_gopts sh nd i (Finset.mem_range.mp ht')
        obtain ⟨p, hzp⟩ := forall₂_mem_left hL _ hmem
        refine ⟨_, List.mem_map.mpr ⟨_, hzp, rfl⟩, ?_⟩
        simp [gpredOf]
      · by_cases h0 : mv B x = 0
        · right
          have := hout x hp h0
          omega
        · left
          have hlt := gused_lt hB hρ hp rfl h0
          have hmem := fresh_mem_gopts sh nd i (m := mv B x) (Nat.pos_of_ne_zero h0) (mv_lt B x)
            (by simp only [Nat.sub_eq]; omega)
          obtain ⟨p, hzp⟩ := forall₂_mem_left hL _ hmem
          refine ⟨_, List.mem_map.mpr ⟨_, hzp, rfl⟩, ?_⟩
          simp [gpredOf, hp])
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
      rcases mem_gopts (List.of_mem_zip hz).1 with ⟨t', ht', rfl⟩ | ⟨m, μ, h0, h16, hμ, rfl⟩
      · simp only [gpredOf, GOpt.mult]
        refine (Finset.card_le_card (t := {ρ t'}) ?_).trans (by simp)
        intro x hx; simp only [Finset.mem_filter, decide_eq_true_eq] at hx
        exact Finset.mem_singleton.mpr hx.2
      · have := gfresh_count hB hρ Yi h0 h16
        show (Yi.filter fun x => gpredOf B nd ρ (GOpt.fresh m μ) x = true).card ≤ μ
        simp only [gpredOf, decide_eq_true_eq]
        rw [Nat.sub_eq] at hμ; omega)
  have htb := tbound hYi h t
  rw [hCsum] at hcls
  linarith

mutual
/-- **Soundness of a numeric certificate tree** of a general node. -/
theorem evalGCT_sound {B : Col} {sh : Sh} (hB : ShapeOf B sh) {tab : BTab}
    (htab : BTabOK sh tab) :
    ∀ (T : GCT) (nd : GNode) (v : V5), evalGCT sh tab nd T = some v → GGood B nd v
  | .leaf, nd, v, h => gleaf_good hB htab.2 h
  | .prune, nd, v, h => by
    simp only [evalGCT] at h
    cases hp : gpruneOK sh tab.pr nd
    · rw [hp, cond_false] at h; exact absurd h (by simp)
    · rw [hp, cond_true, Option.some.injEq] at h; subst h; exact gprune_good hB htab.1 hp
  | .node i ts kids ok, nd, v, h => by
    simp only [evalGCT] at h
    cases hc : (Nat.blt i 4 && (nd.get i).isNone)
    · rw [hc, cond_false] at h; exact absurd h (by simp)
    · rw [hc, cond_true] at h
      simp only [Bool.and_eq_true, Nat.blt_eq, Option.isNone_iff_eq_none] at hc
      split at h
      · next L vo hk ho =>
        rw [Option.some.injEq] at h; subst h
        exact gtnode_good hB hc.1 hc.2 (evalGKids_sound hB htab kids nd i _ L hk)
          (evalGCT_sound hB htab ok _ vo ho) ts
      · exact absurd h (by simp)
/-- Soundness of the option values of a general node. -/
theorem evalGKids_sound {B : Col} {sh : Sh} (hB : ShapeOf B sh) {tab : BTab}
    (htab : BTabOK sh tab) :
    ∀ (ks : GCTL) (nd : GNode) (i : ℕ) (os : List GOpt) (L : List (V5 × ℕ)),
      evalGKids sh tab nd i os ks = some L → List.Forall₂ (GOptVal B nd i) os L
  | .nil, nd, i, os, L, h => by
    cases os with
    | nil => simp only [evalGKids, Option.some.injEq] at h; subst h; exact .nil
    | cons o os => simp [evalGKids] at h
  | .cons k ks, nd, i, os, L, h => by
    cases os with
    | nil => simp [evalGKids] at h
    | cons o os' =>
      simp only [evalGKids] at h
      split at h
      · next v L' hv hL' =>
        rw [Option.some.injEq] at h; subst h
        refine .cons ⟨rfl, ?_, ?_⟩ (evalGKids_sound hB htab ks nd i os' L' hL')
        · intro himp; rw [himp, cond_true, Option.some.injEq] at hv; exact hv.symm
        · intro himp; rw [himp, cond_false] at hv; exact evalGCT_sound hB htab k _ v hv
      · exact absurd h (by simp)
end

end GridGen.Four.K4
