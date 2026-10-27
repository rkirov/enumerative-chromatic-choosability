/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.K4.Node

/-!
# Height four at `k = 4`: regions at a node

A proper completion `s` of a node (placed rows fixed, the others free) has an **equality pattern**
`e = (e₁₃, e₂₄, e₁₄)` (one of five) and **own bits** `o` (`oⱼ = [sⱼ ∈ Bⱼ]`). For each pattern and
own bits, `regionAt` builds a region (`GridGen/Four/K4/Region.lean`): a row whose class (the rows
of the same colour, `cls`) contains a placed row gets that row's mask; a free class gets the masks
with the class's own bits that are still available (mask `0`, or an atom not used up by the placed
colours, `avail`). `regionAt_sound`: every proper completion of every realization lies in the
region of its own pattern and own bits, so the region's box valuations bound it.

`pruneOK`: every region of every consistent pattern has nonnegative valuations. Then every proper
completion contributes nonnegatively at every weight, and the node value `0` is good
(`prune_good`).
-/

namespace GridGen.Four.K4

open Finset

/-! ### Patterns -/

/-- The rows of the class of row `j` under the pattern `(e₁₃, e₂₄, e₁₄)`. -/
def cls (e13 e24 e14 : Bool) : ℕ → List ℕ
  | 0 => 0 :: (cond e13 [2] [] ++ cond e14 [3] [])
  | 1 => 1 :: cond e24 [3] []
  | 2 => 2 :: cond e13 [0] []
  | _ => 3 :: (cond e24 [1] [] ++ cond e14 [0] [])

/-- The row `j` of a tuple. -/
def rowT (s : T4) : ℕ → ℕ
  | 0 => r1 s
  | 1 => r2 s
  | 2 => r3 s
  | _ => r4 s

/-- The pattern of a tuple. -/
def epat (s : T4) : Bool × Bool × Bool :=
  (decide (r1 s = r3 s), decide (r2 s = r4 s), decide (r1 s = r4 s))

/-- For a proper tuple, the class of a row under its pattern is the rows of the same colour. -/
theorem mem_cls_iff {s : T4} (hs : Proper s) {j r : ℕ} (hj : j < 4) (hr : r < 4) :
    r ∈ cls (epat s).1 (epat s).2.1 (epat s).2.2 j ↔ rowT s r = rowT s j := by
  obtain ⟨p12, p23, p34⟩ := hs
  obtain ⟨a, b, c, d⟩ := s
  simp only [r1, r2, r3, r4] at p12 p23 p34
  interval_cases j <;> interval_cases r <;>
    by_cases h13 : a = c <;> by_cases h24 : b = d <;> by_cases h14 : a = d <;>
    simp_all [cls, epat, rowT, r1, r2, r3, r4, eq_comm]

/-- The five patterns of proper tuples. -/
def pats : List (Bool × Bool × Bool) :=
  [(true, true, false), (true, false, false), (false, true, false), (false, false, true),
    (false, false, false)]

theorem epat_mem {s : T4} (hs : Proper s) : epat s ∈ pats := by
  obtain ⟨p12, p23, p34⟩ := hs
  obtain ⟨a, b, c, d⟩ := s
  simp only [r1, r2, r3, r4] at p12 p23 p34
  by_cases h13 : a = c <;> by_cases h24 : b = d <;> by_cases h14 : a = d <;>
    simp_all [epat, pats, r1, r2, r3, r4]

/-! ### The region of a pattern and own bits at a node -/

/-- The mask of the first placed row of a list of rows. -/
def firstMask (nd : Node) : List ℕ → Option ℕ
  | [] => none
  | r :: L =>
    match nd.get r with
    | some (m, _) => some m
    | none => firstMask nd L

/-- The masks with bit `j` equal to `b`. -/
def tset (j : ℕ) (b : Bool) : ℕ := cond b (upJ (Nat.pow 2 j)) (Nat.sub 65535 (upJ (Nat.pow 2 j)))

/-- The masks with the own bits `o` on the rows `L`. -/
def clsT (o : ℕ) : List ℕ → ℕ
  | [] => 65535
  | r :: L => Nat.land (tset r (Nat.testBit o r)) (clsT o L)

/-- The masks of the shape's atoms, and `0`. -/
def availRoot (sh : Sh) : ℕ :=
  (List.range' 1 15).foldl (fun acc m => cond (Nat.blt 0 (sh.na m)) (Nat.lor acc (Nat.pow 2 m)) acc) 1

/-- Clear the mask of row `j` if the placed colours use its atom up (only the row that places a
colour first, tag `j`, can). -/
def availClr (sh : Sh) (nd : Node) (j : ℕ) (p : Pl) (acc : ℕ) : ℕ :=
  match p with
  | some (m, t) =>
    cond (Nat.beq t j && !(Nat.beq m 0) && !(Nat.blt (usedM nd m) (sh.na m)))
      (Nat.xor acc (Nat.land acc (Nat.pow 2 m))) acc
  | none => acc

/-- The available masks: `0`, and every atom not used up by the placed colours. Only the masks of
the (at most four) placed rows can be used up, so the shape's mask set `availRoot sh`, the same
for every node of a tree, is corrected at those masks. -/
def avail (sh : Sh) (nd : Node) : ℕ :=
  availClr sh nd 3 nd.r3 (availClr sh nd 2 nd.r2 (availClr sh nd 1 nd.r1
    (availClr sh nd 0 nd.r0 (availRoot sh))))

/-- The mask set of row `j`. -/
def rsAt (av : ℕ) (nd : Node) (e13 e24 e14 : Bool) (o j : ℕ) : ℕ :=
  match firstMask nd (cls e13 e24 e14 j) with
  | some m => Nat.pow 2 m
  | none => Nat.land av (clsT o (cls e13 e24 e14 j))

/-- `k n`, with `n` evaluated first: the kernel passes the same small term (`0` or `Nat.succ` of a
literal) for equal values, and so shares the computations on it (its cache is keyed by terms). -/
def natCase {α : Type} (n : ℕ) (k : ℕ → α) : α :=
  match n with
  | 0 => k 0
  | p + 1 => k (Nat.succ p)

theorem natCase_eq {α : Type} (n : ℕ) (k : ℕ → α) : natCase n k = k n := by
  cases n <;> rfl

/-- **The region of a pattern and own bits at a node**, for Venn sizes in `[vl, vh]` and
available masks `av`. The four mask sets are evaluated first, so that the bit computations of
equal mask sets are shared by all the regions of a tree. -/
def regionAt (vl vh : VN) (av : ℕ) (nd : Node) (e13 e24 e14 : Bool) (o : ℕ) : Option V5 :=
  natCase (rsAt av nd e13 e24 e14 o 0) fun r0 => natCase (rsAt av nd e13 e24 e14 o 1) fun r1 =>
    natCase (rsAt av nd e13 e24 e14 o 2) fun r2 => natCase (rsAt av nd e13 e24 e14 o 3) fun r3 =>
      regionV vl vh r0 r1 r2 r3 e13 e24 e14

theorem regionAt_eq (vl vh : VN) (av : ℕ) (nd : Node) (e13 e24 e14 : Bool) (o : ℕ) :
    regionAt vl vh av nd e13 e24 e14 o = regionV vl vh (rsAt av nd e13 e24 e14 o 0)
      (rsAt av nd e13 e24 e14 o 1) (rsAt av nd e13 e24 e14 o 2) (rsAt av nd e13 e24 e14 o 3)
      e13 e24 e14 := by
  simp only [regionAt, natCase_eq]

/-- A region whose valuations are nonnegative (or which is empty). -/
def regionNN (r : Option V5) : Bool :=
  match r with
  | some v => v.nonneg
  | none => true

/-- Two placed rows have the same tag exactly when `b`. -/
def pairOK (nd : Node) (i j : ℕ) (b : Bool) : Bool :=
  match nd.get i, nd.get j with
  | some (_, t), some (_, t') => Nat.beq t t' == b
  | _, _ => true

/-- The placed rows agree with the pattern: same tag iff same class. -/
def consistent (nd : Node) (e13 e24 e14 : Bool) : Bool :=
  pairOK nd 0 1 false && pairOK nd 1 2 false && pairOK nd 2 3 false && pairOK nd 0 2 e13 &&
    pairOK nd 1 3 e24 && pairOK nd 0 3 e14

/-- Four bits as a number. -/
def four (b0 b1 b2 b3 : Bool) : ℕ :=
  Nat.add (Nat.add (bn b0) (Nat.mul 2 (bn b1))) (Nat.add (Nat.mul 4 (bn b2)) (Nat.mul 8 (bn b3)))

/-- Bit `j` of a fixed mask, if any. -/
def fmBit (p : Option ℕ) (j : ℕ) : Bool :=
  match p with
  | some m => Nat.testBit m j
  | none => false

/-- The own bits fixed by the placed rows: those of the rows whose class has a placed row. -/
def ownM (nd : Node) (e13 e24 e14 : Bool) : ℕ :=
  four (firstMask nd (cls e13 e24 e14 0)).isSome (firstMask nd (cls e13 e24 e14 1)).isSome
    (firstMask nd (cls e13 e24 e14 2)).isSome (firstMask nd (cls e13 e24 e14 3)).isSome

/-- Their values: bit `j` of the placed mask of row `j`'s class. -/
def ownV (nd : Node) (e13 e24 e14 : Bool) : ℕ :=
  four (fmBit (firstMask nd (cls e13 e24 e14 0)) 0) (fmBit (firstMask nd (cls e13 e24 e14 1)) 1)
    (fmBit (firstMask nd (cls e13 e24 e14 2)) 2) (fmBit (firstMask nd (cls e13 e24 e14 3)) 3)

/-- The own bits agree with the fixed masks (other own bits only repeat a region). The masks
`ownM`, `ownV` are the same for the sixteen own-bit vectors of a pattern, so each costs the kernel
one `land` and one `beq`. -/
def ownCompat (nd : Node) (e13 e24 e14 : Bool) (o : ℕ) : Bool :=
  Nat.beq (Nat.land o (ownM nd e13 e24 e14)) (ownV nd e13 e24 e14)

/-- `f 0 && ⋯ && f (n - 1)`. -/
def allBelow : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n + 1, f => allBelow n f && f n

theorem allBelow_spec {n : ℕ} {f : ℕ → Bool} (h : allBelow n f = true) {x : ℕ} (hx : x < n) :
    f x = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [allBelow, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
    · exact ih h.1 hx
    · exact h.2

/-- **A prunable node**: every region of every consistent pattern is nonnegative. -/
def pruneOK (sh : Sh) (nd : Node) : Bool :=
  let av := avail sh nd
  pats.all fun e => !consistent nd e.1 e.2.1 e.2.2 ||
    allBelow 16 fun o => !ownCompat nd e.1 e.2.1 e.2.2 o ||
      regionNN (regionAt sh.I sh.I av nd e.1 e.2.1 e.2.2 o)


/-! ### Soundness -/

/-- A tuple completes a node under a realization. -/
def Completes (nd : Node) (ρ : ℕ → ℕ) (s : T4) : Prop :=
  ∀ j < 4, ∀ m t, nd.get j = some (m, t) → rowT s j = ρ t

/-- The own bits of a tuple. -/
def ownOf (B : Col) (s : T4) : ℕ :=
  Nat.add (Nat.add (bn (Nat.testBit (mv B (r1 s)) 0)) (Nat.mul 2 (bn (Nat.testBit (mv B (r2 s)) 1))))
    (Nat.add (Nat.mul 4 (bn (Nat.testBit (mv B (r3 s)) 2)))
      (Nat.mul 8 (bn (Nat.testBit (mv B (r4 s)) 3))))

theorem testBit_own4 : ∀ b0 b1 b2 b3 : Bool,
    Nat.testBit (Nat.add (Nat.add (bn b0) (Nat.mul 2 (bn b1)))
      (Nat.add (Nat.mul 4 (bn b2)) (Nat.mul 8 (bn b3)))) 0 = b0 ∧
    Nat.testBit (Nat.add (Nat.add (bn b0) (Nat.mul 2 (bn b1)))
      (Nat.add (Nat.mul 4 (bn b2)) (Nat.mul 8 (bn b3)))) 1 = b1 ∧
    Nat.testBit (Nat.add (Nat.add (bn b0) (Nat.mul 2 (bn b1)))
      (Nat.add (Nat.mul 4 (bn b2)) (Nat.mul 8 (bn b3)))) 2 = b2 ∧
    Nat.testBit (Nat.add (Nat.add (bn b0) (Nat.mul 2 (bn b1)))
      (Nat.add (Nat.mul 4 (bn b2)) (Nat.mul 8 (bn b3)))) 3 = b3 := by
  decide

theorem testBit_ownOf (B : Col) (s : T4) {r : ℕ} (hr : r < 4) :
    Nat.testBit (ownOf B s) r = Nat.testBit (mv B (rowT s r)) r := by
  obtain ⟨h0, h1, h2, h3⟩ := testBit_own4 (Nat.testBit (mv B (r1 s)) 0)
    (Nat.testBit (mv B (r2 s)) 1) (Nat.testBit (mv B (r3 s)) 2) (Nat.testBit (mv B (r4 s)) 3)
  unfold ownOf
  interval_cases r
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem firstMask_some {nd : Node} {L : List ℕ} {m : ℕ} (h : firstMask nd L = some m) :
    ∃ r ∈ L, ∃ t, nd.get r = some (m, t) := by
  induction L with
  | nil => simp [firstMask] at h
  | cons a L ih =>
    unfold firstMask at h
    split at h
    · next m' t e =>
      simp only [Option.some.injEq] at h; subst h
      exact ⟨a, List.mem_cons_self, t, e⟩
    · obtain ⟨r, hr, t, e⟩ := ih h
      exact ⟨r, List.mem_cons_of_mem _ hr, t, e⟩

theorem firstMask_none {nd : Node} {L : List ℕ} (h : firstMask nd L = none) :
    ∀ r ∈ L, nd.get r = none := by
  induction L with
  | nil => simp
  | cons a L ih =>
    unfold firstMask at h
    split at h
    · simp at h
    · next e =>
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact e
      · exact ih h r hr

theorem cls_lt {e13 e24 e14 : Bool} {j r : ℕ} (hr : r ∈ cls e13 e24 e14 j) : r < 4 := by
  unfold cls at hr
  split at hr <;> cases e13 <;> cases e24 <;> cases e14 <;> simp_all <;> omega

theorem head_mem_cls (e13 e24 e14 : Bool) {j : ℕ} (hj : j < 4) : ∃ L, cls e13 e24 e14 j = j :: L := by
  interval_cases j <;> exact ⟨_, rfl⟩

theorem sing_bits : ∀ m < 16, ∀ J < 16,
    allJ (Nat.pow 2 m) J = sup m J ∧ anyJ (Nat.pow 2 m) J = sup m J := by decide

theorem testBit_pow_self (m : ℕ) : Nat.testBit (Nat.pow 2 m) m = true := by
  rw [show Nat.pow 2 m = 2 ^ m from rfl, Nat.testBit_two_pow_self]

theorem testBit_tset : ∀ r < 4, ∀ b : Bool, ∀ m < 16,
    Nat.testBit (tset r b) m = (Nat.testBit m r == b) := by decide

theorem compl_upJ : ∀ J < 16, Nat.land (Nat.sub 65535 (upJ J)) (upJ J) = 0 := by decide

theorem testBit_clsT {o m : ℕ} (hm : m < 16) :
    ∀ L : List ℕ, (∀ r ∈ L, r < 4 ∧ Nat.testBit m r = Nat.testBit o r) →
      Nat.testBit (clsT o L) m = true
  | [], _ => by unfold clsT; interval_cases m <;> decide
  | r :: L, h => by
    unfold clsT
    rw [show Nat.land (tset r (Nat.testBit o r)) (clsT o L)
      = tset r (Nat.testBit o r) &&& clsT o L from rfl, Nat.testBit_and]
    obtain ⟨hr, hb⟩ := h r List.mem_cons_self
    rw [testBit_tset r hr _ m hm, hb, beq_self_eq_true, Bool.true_and]
    exact testBit_clsT hm L fun r' hr' => h r' (List.mem_cons_of_mem _ hr')

theorem testBit_fold_avail (P : ℕ → Bool) (x : ℕ) :
    ∀ (L : List ℕ) (init : ℕ), (Nat.testBit init x = true ∨ (x ∈ L ∧ P x = true)) →
      Nat.testBit (L.foldl (fun acc m => cond (P m) (Nat.lor acc (Nat.pow 2 m)) acc) init) x = true
  | [], init, h => by
    rcases h with h | ⟨h, -⟩
    · exact h
    · simp at h
  | a :: L, init, h => by
    simp only [List.foldl_cons]
    apply testBit_fold_avail P x L
    rcases h with h | ⟨h, hp⟩
    · left
      cases P a
      · exact h
      · simp only [cond_true]
        rw [show Nat.lor init (Nat.pow 2 a) = init ||| 2 ^ a from rfl, Nat.testBit_or, h,
          Bool.true_or]
    · rcases List.mem_cons.mp h with rfl | h
      · left
        simp only [hp, cond_true]
        rw [show Nat.lor init (Nat.pow 2 x) = init ||| 2 ^ x from rfl, Nat.testBit_or,
          Nat.testBit_two_pow_self, Bool.or_true]
      · right; exact ⟨h, hp⟩

theorem testBit_availClr {sh : Sh} {nd : Node} {j : ℕ} {p : Pl} {acc m : ℕ}
    (h : m = 0 ∨ usedM nd m < sh.na m) (hacc : Nat.testBit acc m = true) :
    Nat.testBit (availClr sh nd j p acc) m = true := by
  unfold availClr
  rcases p with _ | ⟨m', t⟩
  · exact hacc
  · simp only
    cases hc : (Nat.beq t j && !(Nat.beq m' 0) && !(Nat.blt (usedM nd m') (sh.na m')))
    · exact hacc
    · simp only [Bool.cond_true]
      have hne : m' ≠ m := by
        rintro rfl
        rcases h with rfl | h
        · rw [Nat.beq_refl] at hc; simp at hc
        · rw [Nat.blt_eq.mpr h] at hc; simp at hc
      rw [show Nat.xor acc (Nat.land acc (Nat.pow 2 m')) = acc ^^^ (acc &&& 2 ^ m') from rfl,
        Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow, hacc]
      simp [hne]

theorem testBit_avail {sh : Sh} {nd : Node} {m : ℕ} (hm : m < 16)
    (h : m = 0 ∨ usedM nd m < sh.na m) : Nat.testBit (avail sh nd) m = true := by
  have hroot : Nat.testBit (availRoot sh) m = true := by
    unfold availRoot
    apply testBit_fold_avail
    by_cases h0 : m = 0
    · subst h0; left; decide
    · right
      refine ⟨List.mem_range'_1.mpr ⟨by omega, by omega⟩, ?_⟩
      rcases h with h | h
      · exact absurd h h0
      · simp only [Nat.blt_eq]; omega
  unfold avail
  exact testBit_availClr h (testBit_availClr h (testBit_availClr h (testBit_availClr h hroot)))

theorem testBit_land' (a b i : ℕ) :
    Nat.testBit (Nat.land a b) i = (Nat.testBit a i && Nat.testBit b i) := Nat.testBit_and a b i

/-- A free row's mask set agrees on the row's own bit. -/
theorem unif_rs (av R : ℕ) {j : ℕ} (hj : j < 4) (b : Bool) :
    Unif (Nat.land av (Nat.land (tset j b) R)) (Nat.pow 2 j) := by
  have hJ : Nat.pow 2 j < 16 := by interval_cases j <;> decide
  cases b
  · right
    have hc : Nat.land (tset j false) (upJ (Nat.pow 2 j)) = 0 := compl_upJ _ hJ
    have h0 : Nat.land (Nat.land av (Nat.land (tset j false) R)) (upJ (Nat.pow 2 j)) = 0 := by
      apply Nat.eq_of_testBit_eq; intro i
      have hci := congrArg (fun z => Nat.testBit z i) hc
      simp only [testBit_land', Nat.zero_testBit] at hci ⊢
      revert hci
      cases Nat.testBit av i <;> cases Nat.testBit (tset j false) i <;>
        cases Nat.testBit R i <;> cases Nat.testBit (upJ (Nat.pow 2 j)) i <;> decide
    unfold anyJ; rw [h0]; rfl
  · left
    have h1 : Nat.land (Nat.land av (Nat.land (tset j true) R)) (upJ (Nat.pow 2 j))
        = Nat.land av (Nat.land (tset j true) R) := by
      apply Nat.eq_of_testBit_eq; intro i
      simp only [testBit_land', tset, cond_true]
      cases Nat.testBit av i <;> cases Nat.testBit (upJ (Nat.pow 2 j)) i <;>
        cases Nat.testBit R i <;> rfl
    unfold allJ; rw [h1]; exact Nat.beq_refl _

/-- **The masks of a proper completion lie in the region of its pattern and own bits.** -/
theorem rsAt_mem {B : Col} {sh : Sh} (hB : ShapeOf B sh) {nd : Node} {ρ : ℕ → ℕ}
    (hρ : nd.Real B ρ) {av : ℕ}
    (hav : ∀ m < 16, (m = 0 ∨ usedM nd m < sh.na m) → Nat.testBit av m = true)
    {s : T4} (hs : Proper s) (hc : Completes nd ρ s) {j : ℕ} (hj : j < 4) :
    Nat.testBit (rsAt av nd (epat s).1 (epat s).2.1 (epat s).2.2 (ownOf B s) j)
        (mv B (rowT s j)) = true ∧
      Unif (rsAt av nd (epat s).1 (epat s).2.1 (epat s).2.2 (ownOf B s) j)
        (Nat.pow 2 j) := by
  have hmv : mv B (rowT s j) < 16 := mv_lt _ _
  unfold rsAt
  split
  · next m hm =>
    obtain ⟨r, hr, t, e⟩ := firstMask_some hm
    have hr4 := cls_lt hr
    have h1 := hc r hr4 m t e
    have h2 := (mem_cls_iff hs hj hr4).mp hr
    have hmask : mv B (rowT s j) = m := by
      rw [← h2, h1]; exact (hρ r hr4 m t e).2.2.1
    have hm16 : m < 16 := hmask ▸ hmv
    rw [hmask]
    refine ⟨testBit_pow_self m, ?_⟩
    have := sing_bits m hm16 (Nat.pow 2 j) (by interval_cases j <;> decide)
    unfold Unif; rw [this.1, this.2]
    cases sup m (Nat.pow 2 j) <;> simp
  · next hn =>
    have hfree := firstMask_none hn
    obtain ⟨L, hL⟩ := head_mem_cls (epat s).1 (epat s).2.1 (epat s).2.2 hj
    refine ⟨?_, ?_⟩
    · rw [testBit_land']
      refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
      · apply hav _ hmv
        by_cases h0 : mv B (rowT s j) = 0
        · exact Or.inl h0
        · right
          refine used_lt hB hρ ?_ rfl h0
          intro hp
          obtain ⟨j', hj', m', t', e', hx⟩ := mem_placedSet.mp hp
          obtain ⟨ht4, het, -, -⟩ := hρ j' hj' m' t' e'
          have hct := hc t' ht4 m' t' het
          have : t' ∈ cls (epat s).1 (epat s).2.1 (epat s).2.2 j :=
            (mem_cls_iff hs hj ht4).mpr (hct.trans hx.symm)
          rw [hfree t' this] at het; exact absurd het (by simp)
      · apply testBit_clsT hmv
        intro r hr
        have hr4 := cls_lt hr
        refine ⟨hr4, ?_⟩
        rw [testBit_ownOf B s hr4, (mem_cls_iff hs hj hr4).mp hr]
    · rw [hL]
      exact unif_rs _ _ hj _

/-- A proper completion lies in its region (Venn sizes in `[vl, vh]`, available masks `av`),
which then bounds it. -/
theorem regionAt_sound_gen {B : Col} {sh : Sh} (hB : ShapeOf B sh) {nd : Node} {ρ : ℕ → ℕ}
    (hρ : nd.Real B ρ) {vl vh : VN} (hl : VLe vl sh.I) (hh : VLe sh.I vh) {av : ℕ}
    (hav : ∀ m < 16, (m = 0 ∨ usedM nd m < sh.na m) → Nat.testBit av m = true)
    {s : T4} (hs : Proper s) (hc : Completes nd ρ s) :
    ∃ x, regionAt vl vh av nd (epat s).1 (epat s).2.1 (epat s).2.2 (ownOf B s)
        = some x ∧ ∀ k w, w ∈ famW k → (x.get k).val ≤ dot (gvec B s) w := by
  obtain ⟨m0, u0⟩ := rsAt_mem hB hρ hav hs hc (j := 0) (by norm_num)
  obtain ⟨m1, u1⟩ := rsAt_mem hB hρ hav hs hc (j := 1) (by norm_num)
  obtain ⟨m2, u2⟩ := rsAt_mem hB hρ hav hs hc (j := 2) (by norm_num)
  obtain ⟨m3, u3⟩ := rsAt_mem hB hρ hav hs hc (j := 3) (by norm_num)
  rw [regionAt_eq]
  exact regionV_sound B hB.1 sh.I hB.2.1 hl hh hs m0 m1 m2 m3 u0 u1 u2 u3

/-- A proper completion lies in its region, which then bounds it. -/
theorem regionAt_sound {B : Col} {sh : Sh} (hB : ShapeOf B sh) {nd : Node} {ρ : ℕ → ℕ}
    (hρ : nd.Real B ρ) {s : T4} (hs : Proper s) (hc : Completes nd ρ s) :
    ∃ x, regionAt sh.I sh.I (avail sh nd) nd (epat s).1 (epat s).2.1 (epat s).2.2 (ownOf B s)
        = some x ∧ ∀ k w, w ∈ famW k → (x.get k).val ≤ dot (gvec B s) w :=
  regionAt_sound_gen hB hρ (VLe_refl _) (VLe_refl _) (fun _ hm h => testBit_avail hm h) hs hc

theorem pairOK_of {B : Col} {nd : Node} {ρ : ℕ → ℕ} (hρ : nd.Real B ρ) {s : T4}
    (hc : Completes nd ρ s) {i j : ℕ} (hi : i < 4) (hj : j < 4) {b : Bool}
    (hb : rowT s i = rowT s j ↔ b = true) : pairOK nd i j b = true := by
  unfold pairOK
  rcases ei : nd.get i with _ | ⟨m, t⟩
  · rfl
  rcases ej : nd.get j with _ | ⟨m', t'⟩
  · rfl
  have key : Nat.beq t t' = true ↔ rowT s i = rowT s j := by
    rw [hc i hi m t ei, hc j hj m' t' ej, Nat.beq_eq]
    exact ⟨fun h => h ▸ rfl, fun h => (hρ i hi m t ei).2.2.2 j hj m' t' ej h⟩
  have hk := key.trans hb
  simp only
  cases b <;> cases h : Nat.beq t t'
  · rfl
  · exact absurd (hk.mp h) (by decide)
  · exact absurd (h ▸ hk.mpr rfl) (by decide)
  · rfl

/-- The placed rows are consistent with the pattern of a proper completion. -/
theorem consistent_epat {B : Col} {nd : Node} {ρ : ℕ → ℕ} (hρ : nd.Real B ρ) {s : T4}
    (hs : Proper s) (hc : Completes nd ρ s) :
    consistent nd (epat s).1 (epat s).2.1 (epat s).2.2 = true := by
  obtain ⟨p12, p23, p34⟩ := hs
  unfold consistent
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨pairOK_of hρ hc (by norm_num) (by norm_num) ?_,
    pairOK_of hρ hc (by norm_num) (by norm_num) ?_⟩, pairOK_of hρ hc (by norm_num) (by norm_num) ?_⟩,
    pairOK_of hρ hc (by norm_num) (by norm_num) ?_⟩, pairOK_of hρ hc (by norm_num) (by norm_num) ?_⟩,
    pairOK_of hρ hc (by norm_num) (by norm_num) ?_⟩ <;>
    simp only [rowT, epat, decide_eq_true_eq] <;> simp_all

theorem land_four : ∀ a0 a1 a2 a3 b0 b1 b2 b3 : Bool,
    Nat.land (four a0 a1 a2 a3) (four b0 b1 b2 b3) = four (a0 && b0) (a1 && b1) (a2 && b2) (a3 && b3) := by
  decide

theorem ownCompat_own {B : Col} {nd : Node} {ρ : ℕ → ℕ} (hρ : nd.Real B ρ) {s : T4}
    (hs : Proper s) (hc : Completes nd ρ s) :
    ownCompat nd (epat s).1 (epat s).2.1 (epat s).2.2 (ownOf B s) = true := by
  have key : ∀ j < 4, (Nat.testBit (mv B (rowT s j)) j
      && (firstMask nd (cls (epat s).1 (epat s).2.1 (epat s).2.2 j)).isSome)
      = fmBit (firstMask nd (cls (epat s).1 (epat s).2.1 (epat s).2.2 j)) j := by
    intro j hj
    unfold fmBit
    split
    · next m hm =>
      obtain ⟨r, hr, t, e⟩ := firstMask_some hm
      have hr4 := cls_lt hr
      have hmask : mv B (rowT s j) = m := by
        rw [← (mem_cls_iff hs hj hr4).mp hr, hc r hr4 m t e]; exact (hρ r hr4 m t e).2.2.1
      rw [hmask, hm, Option.isSome_some, Bool.and_true]
    · next hn => rw [hn, Option.isSome_none, Bool.and_false]
  have ho : ownOf B s = four (Nat.testBit (mv B (rowT s 0)) 0) (Nat.testBit (mv B (rowT s 1)) 1)
      (Nat.testBit (mv B (rowT s 2)) 2) (Nat.testBit (mv B (rowT s 3)) 3) := rfl
  unfold ownCompat ownM ownV
  rw [ho, land_four, key 0 (by norm_num), key 1 (by norm_num), key 2 (by norm_num),
    key 3 (by norm_num)]
  exact Nat.beq_refl _

/-- **A prunable node has the good value `0`.** -/
theorem prune_good {B : Col} {sh : Sh} (hB : ShapeOf B sh) {nd : Node} (h : pruneOK sh nd = true) :
    Good B nd V5.zero := by
  intro ρ hρ Y _ k w hw
  rw [V5.get_zero]
  apply Finset.sum_nonneg; intro a ha
  apply Finset.sum_nonneg; intro b hb
  apply Finset.sum_nonneg; intro c hc
  apply Finset.sum_nonneg; intro d hd
  by_cases hs : Proper (a, b, c, d)
  · have hcomp : Completes nd ρ (a, b, c, d) := by
      intro j hj m t e
      obtain ⟨q0, q1, q2, q3⟩ := nd
      interval_cases j <;> simp only [Node.get] at e <;> subst e <;>
        simp only [fill, fillR, Finset.mem_singleton] at ha hb hc hd <;>
        simp only [rowT, r1, r2, r3, r4] <;> assumption
    obtain ⟨x, hx, hle⟩ := regionAt_sound hB hρ hs hcomp
    have he := epat_mem hs
    unfold pruneOK at h
    have h1 := List.all_eq_true.mp h _ he
    rw [consistent_epat hρ hs hcomp, Bool.not_true, Bool.false_or] at h1
    have h2 := allBelow_spec h1 (x := ownOf B (a, b, c, d)) (by
      unfold ownOf; simp only [bn, Nat.add_eq, Nat.mul_eq]
      cases Nat.testBit (mv B (r1 (a, b, c, d))) 0 <;> cases Nat.testBit (mv B (r2 (a, b, c, d))) 1 <;>
        cases Nat.testBit (mv B (r3 (a, b, c, d))) 2 <;>
        cases Nat.testBit (mv B (r4 (a, b, c, d))) 3 <;> simp)
    have hoc := ownCompat_own hρ hs hcomp
    rw [hoc, Bool.not_true, Bool.false_or, hx] at h2
    unfold regionNN at h2
    exact le_trans (V5.nonneg_get h2 k) (hle k w hw)
  · exact le_of_eq (gw_improper B w hs).symm

end GridGen.Four.K4
