/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.State
import GridGen.Six.Anti

/-!
# Height six at `k = 6`: dual certificates over the state bits

`GridGen/Five/K5/BitLP.lean` and `BitSound.lean` with six rows; the bit-LP certificates of
`ai_research_notes/cx/h6k6/NOTE.md` (Codex, OpenAI), independently re-checked in
`H6_K6_REVIEW_2026-10-29.md` §3. A previous column `s` has row codes (`kcodes`, `rcode` of
`GridGen/Six/Count.lean`) and an equality pattern; by `state66`,
`GB ≥ GU · (1 + V)` with `V = 10¹² · N6g(codes) / (R · NU) - 1`.

**Pins.** A pin (`BPin6`) is a block of one to three consecutive rows, each in one of the sets
`Bᵣ ∖ Bᵣ₋₁` (kind `0`), `Bᵣ ∖ Bᵣ₊₁` (kind `1`) or their union (kind `2`), and a list of peels (a
row in such a set, or an equality of two rows) in a valid order; its event carries at most `bnd`
of the uniform weight (`pin_sum6`), the set sizes being bounded by the mismatches.

**Averaging** (`sum_fired6`): the pins that fire at a state, weighted by their multipliers and
summed against the uniform weights, cost at most `Σ λ · bnd` of the total uniform weight. A
certificate whose state inequalities `GU · (D + K - fired) ≤ D · GB` hold at every state, with
`Σ λ · bnd ≤ K`, gives the seam inequality (`seam_of_states`).
-/

namespace GridGen.Six

open Finset

/-! ### Lists and sets by row -/

/-- The list before a row (an end row is its own neighbour). -/
def Bpv (B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ) (r : ℕ) : Finset ℕ :=
  if r = 0 then B₁ else bl B₁ B₂ B₃ B₄ B₅ B₆ (r - 1)

/-- The list after a row. -/
def Bnx (B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ) (r : ℕ) : Finset ℕ :=
  if 5 ≤ r then B₆ else bl B₁ B₂ B₃ B₄ B₅ B₆ (r + 1)

/-- The colour set of a row event: kind `0` new against the previous list, `1` against the next
one, `2` either. -/
def Dset (B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ) (r k : ℕ) : Finset ℕ :=
  if k = 0 then bl B₁ B₂ B₃ B₄ B₅ B₆ r \ Bpv B₁ B₂ B₃ B₄ B₅ B₆ r
  else if k = 1 then bl B₁ B₂ B₃ B₄ B₅ B₆ r \ Bnx B₁ B₂ B₃ B₄ B₅ B₆ r
  else (bl B₁ B₂ B₃ B₄ B₅ B₆ r \ Bpv B₁ B₂ B₃ B₄ B₅ B₆ r) ∪
    (bl B₁ B₂ B₃ B₄ B₅ B₆ r \ Bnx B₁ B₂ B₃ B₄ B₅ B₆ r)

/-- The codes of a state. -/
def kcodes (B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ) (s : T6) : T6 :=
  (rcode B₁ B₁ B₂ (r1 s), rcode B₁ B₂ B₃ (r2 s), rcode B₂ B₃ B₄ (r3 s),
    rcode B₃ B₄ B₅ (r4 s), rcode B₄ B₅ B₆ (r5 s), rcode B₅ B₆ B₆ (r6 s))

theorem crow_codes (B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ) (s : T6) {r : ℕ} (hr : r < 6) :
    rowAt r (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)
      = rcode (Bpv B₁ B₂ B₃ B₄ B₅ B₆ r) (bl B₁ B₂ B₃ B₄ B₅ B₆ r) (Bnx B₁ B₂ B₃ B₄ B₅ B₆ r)
          (rowAt r s) := by
  interval_cases r <;> rfl

/-- A row event on a code. -/
def evk (k c : ℕ) : Bool :=
  if k = 0 then kM c == 1 else if k = 1 then kX c == 1 else kU c == 1

theorem evk_code (Bp Bi Bn : Finset ℕ) (x k : ℕ) :
    evk k (rcode Bp Bi Bn x)
      = decide (x ∈ (if k = 0 then Bi \ Bp else if k = 1 then Bi \ Bn
          else (Bi \ Bp) ∪ (Bi \ Bn))) := by
  unfold evk
  rw [kM_code, kX_code, kU_code]
  split_ifs <;> simp_all

theorem evk_codes (B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ) (s : T6) {r : ℕ} (hr : r < 6) (k : ℕ) :
    evk k (rowAt r (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s))
      = decide (rowAt r s ∈ Dset B₁ B₂ B₃ B₄ B₅ B₆ r k) := by
  rw [crow_codes _ _ _ _ _ _ _ hr, evk_code]; rfl

/-- The mismatch before and after a row (`m = [m₁, …, m₅]`, `mⱼ` between rows `j-1` and `j`
numbered from `0`). -/
def mprev (m : List ℕ) (r : ℕ) : ℕ := if r = 0 then 0 else m.getD (r - 1) 0
def mnext (m : List ℕ) (r : ℕ) : ℕ := if 5 ≤ r then 0 else m.getD r 0

/-- The declared size of a row event. -/
def dsz (m : List ℕ) (r k : ℕ) : ℕ :=
  if k = 0 then mprev m r else if k = 1 then mnext m r else mprev m r + mnext m r

theorem card_sdiff6 {B C : Finset ℕ} (hB : B.card = 6) {m : ℕ} (h : (B ∩ C).card + m = 6) :
    (B \ C).card = m := by
  have := Finset.card_sdiff_add_card_inter B C; omega

/-- The mismatches of the lists. -/
def MOK (B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ) (m : List ℕ) : Prop :=
  (B₁ ∩ B₂).card + m.getD 0 0 = 6 ∧ (B₂ ∩ B₃).card + m.getD 1 0 = 6 ∧
    (B₃ ∩ B₄).card + m.getD 2 0 = 6 ∧ (B₄ ∩ B₅).card + m.getD 3 0 = 6 ∧
    (B₅ ∩ B₆).card + m.getD 4 0 = 6

theorem dset_card {B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ} (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6)
    (hB₃ : B₃.card = 6) (hB₄ : B₄.card = 6) (hB₅ : B₅.card = 6) (hB₆ : B₆.card = 6)
    {m : List ℕ} (hm : MOK B₁ B₂ B₃ B₄ B₅ B₆ m) {r : ℕ} (hr : r < 6) (k : ℕ) :
    (Dset B₁ B₂ B₃ B₄ B₅ B₆ r k).card ≤ dsz m r k := by
  obtain ⟨c2, c3, c4, c5, c6⟩ := hm
  have c2' : (B₂ ∩ B₁).card + m.getD 0 0 = 6 := by rw [inter_comm]; exact c2
  have c3' : (B₃ ∩ B₂).card + m.getD 1 0 = 6 := by rw [inter_comm]; exact c3
  have c4' : (B₄ ∩ B₃).card + m.getD 2 0 = 6 := by rw [inter_comm]; exact c4
  have c5' : (B₅ ∩ B₄).card + m.getD 3 0 = 6 := by rw [inter_comm]; exact c5
  have c6' : (B₆ ∩ B₅).card + m.getD 4 0 = 6 := by rw [inter_comm]; exact c6
  have hp : (bl B₁ B₂ B₃ B₄ B₅ B₆ r \ Bpv B₁ B₂ B₃ B₄ B₅ B₆ r).card = mprev m r := by
    interval_cases r
    · simp [bl, Bpv, mprev]
    · exact card_sdiff6 hB₂ c2'
    · exact card_sdiff6 hB₃ c3'
    · exact card_sdiff6 hB₄ c4'
    · exact card_sdiff6 hB₅ c5'
    · exact card_sdiff6 hB₆ c6'
  have hn : (bl B₁ B₂ B₃ B₄ B₅ B₆ r \ Bnx B₁ B₂ B₃ B₄ B₅ B₆ r).card = mnext m r := by
    interval_cases r
    · exact card_sdiff6 hB₁ c2
    · exact card_sdiff6 hB₂ c3
    · exact card_sdiff6 hB₃ c4
    · exact card_sdiff6 hB₄ c5
    · exact card_sdiff6 hB₅ c6
    · simp [bl, Bnx, mnext]
  unfold Dset dsz
  split_ifs
  · exact hp.le
  · exact hn.le
  · exact (card_union_le _ _).trans (by rw [hp, hn])

/-! ### Pins over the state bits -/

/-- A peel: a row in a set, or two rows equal. -/
inductive BPeel6
  | ev (r k : ℕ)
  | eq (r j : ℕ)

/-- A block: none, or one to three consecutive rows. -/
inductive BBlk6
  | none
  | one (r k : ℕ)
  | two (r k k' : ℕ)
  | three (r k k' k'' : ℕ)

/-- A pin with its integer multiplier. -/
structure BPin6 where
  blk : BBlk6
  peels : List BPeel6
  lam : ℕ

namespace BPeel6

def row : BPeel6 → ℕ | ev r _ => r | eq r _ => r
def reads : BPeel6 → ℕ → Bool
  | ev r _, i => decide (r = i)
  | eq r j, i => decide (r = i) || decide (j = i)
def okb : BPeel6 → Bool
  | ev r k => decide (r < 6 ∧ k < 3)
  | eq r j => decide (r < 6 ∧ j < 6 ∧ j ≠ r)

/-- The event on codes and a pattern. -/
def evc (c p : T6) : BPeel6 → Bool
  | ev r k => evk k (rowAt r c)
  | eq r j => rowAt r p == rowAt j p

def bnd (m : List ℕ) : BPeel6 → ℚ
  | ev r k => min (qX r * dsz m r k) 1
  | eq r _ => qX r

/-- The factor for actual lists. -/
def fac (B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ) (m : List ℕ) : BPeel6 → Fac6
  | ev r k => Fac6.mem r (Dset B₁ B₂ B₃ B₄ B₅ B₆ r k) (dsz m r k)
  | eq r j => Fac6.eqr r j

end BPeel6

namespace BBlk6

def reads : BBlk6 → ℕ → Bool
  | none, _ => false
  | one r _, i => decide (r = i)
  | two r _ _, i => decide (r = i) || decide (r + 1 = i)
  | three r _ _ _, i => decide (r = i) || decide (r + 1 = i) || decide (r + 2 = i)

def okb : BBlk6 → Bool
  | none => true
  | one r k => decide (r < 6 ∧ k < 3)
  | two r k k' => decide (r < 5 ∧ k < 3 ∧ k' < 3)
  | three r k k' k'' => decide (r < 4 ∧ k < 3 ∧ k' < 3 ∧ k'' < 3)

/-- The row conditions of a block. -/
def conds : BBlk6 → List (ℕ × ℕ)
  | none => []
  | one r k => [(r, k)]
  | two r k k' => [(r, k), (r + 1, k')]
  | three r k k' k'' => [(r, k), (r + 1, k'), (r + 2, k'')]

def evc (c : T6) : BBlk6 → Bool
  | none => true
  | one r k => evk k (rowAt r c)
  | two r k k' => evk k (rowAt r c) && evk k' (rowAt (r + 1) c)
  | three r k k' k'' => evk k (rowAt r c) && evk k' (rowAt (r + 1) c) && evk k'' (rowAt (r + 2) c)

def bnd (m : List ℕ) : BBlk6 → ℚ
  | none => 1
  | one r k => βQ6 (dsz m r k) 5 (fsd r * fsd (5 - r))
  | two r k k' => βQ6 (dsz m r k * dsz m (r + 1) k') 20 (fsd r * fsd (4 - r))
  | three r k k' k'' =>
      βQ6 (dsz m r k * dsz m (r + 1) k' * dsz m (r + 2) k'') 80 (fsd r * fsd (3 - r))

def blk (B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ) (m : List ℕ) : BBlk6 → Blk6
  | none => Blk6.none
  | one r k => Blk6.one r (Dset B₁ B₂ B₃ B₄ B₅ B₆ r k) (dsz m r k)
  | two r k k' => Blk6.two r (Dset B₁ B₂ B₃ B₄ B₅ B₆ r k) (Dset B₁ B₂ B₃ B₄ B₅ B₆ (r + 1) k')
      (dsz m r k) (dsz m (r + 1) k')
  | three r k k' k'' => Blk6.three r (Dset B₁ B₂ B₃ B₄ B₅ B₆ r k)
      (Dset B₁ B₂ B₃ B₄ B₅ B₆ (r + 1) k') (Dset B₁ B₂ B₃ B₄ B₅ B₆ (r + 2) k'')
      (dsz m r k) (dsz m (r + 1) k') (dsz m (r + 2) k'')

end BBlk6

/-- The peel order, as a boolean. -/
def bpeelOK (b : BBlk6) : List BPeel6 → Bool
  | [] => true
  | p :: ps => !(b.reads p.row) && ps.all (fun g => !(g.reads p.row)) && p.okb && bpeelOK b ps

namespace BPin6

def evc (q : BPin6) (c p : T6) : Bool := q.peels.all (fun f => f.evc c p) && q.blk.evc c

def bnd (q : BPin6) (m : List ℕ) : ℚ := (q.peels.map (BPeel6.bnd m)).prod * q.blk.bnd m

def okb (q : BPin6) : Bool := q.blk.okb && bpeelOK q.blk q.peels

/-- The pin of actual lists. -/
def toPin (B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ) (m : List ℕ) (q : BPin6) : Pin6 :=
  ⟨q.blk.blk B₁ B₂ B₃ B₄ B₅ B₆ m, q.peels.map (BPeel6.fac B₁ B₂ B₃ B₄ B₅ B₆ m)⟩

end BPin6

/-- The multipliers of the pins that fire. -/
def fired (P : List BPin6) (c p : T6) : ℕ :=
  (P.map fun q => if q.evc c p then q.lam else 0).sum

/-- `Σ λ · bnd`. -/
def lamBnd (P : List BPin6) (m : List ℕ) : ℚ := (P.map fun q => (q.lam : ℚ) * q.bnd m).sum

/-! ### Pins on actual states -/

section sound

variable {w : Wt6} {X₁ X₂ X₃ X₄ X₅ X₆ B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ} {m : List ℕ}

theorem all_congr_mem {α : Type*} {f g : α → Bool} :
    ∀ {L : List α}, (∀ x ∈ L, f x = g x) → L.all f = L.all g
  | [], _ => rfl
  | x :: L, h => by
    simp only [List.all_cons]
    rw [h x List.mem_cons_self, all_congr_mem (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem bpeelOK_all {b : BBlk6} : ∀ {ps : List BPeel6}, bpeelOK b ps = true →
    ps.all BPeel6.okb = true
  | [], _ => rfl
  | p :: ps, h => by
    simp only [bpeelOK, Bool.and_eq_true] at h
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨h.1.2, bpeelOK_all h.2⟩

theorem peel_reads6 (p : BPeel6) :
    (p.fac B₁ B₂ B₃ B₄ B₅ B₆ m).reads = p.reads ∧ (p.fac B₁ B₂ B₃ B₄ B₅ B₆ m).row = p.row := by
  cases p <;> exact ⟨rfl, rfl⟩

theorem blk_reads6 (b : BBlk6) : (b.blk B₁ B₂ B₃ B₄ B₅ B₆ m).reads = b.reads := by
  cases b <;> rfl

theorem peelOK_of6 (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6)
    (hB₄ : B₄.card = 6) (hB₅ : B₅.card = 6) (hB₆ : B₆.card = 6) (hm : MOK B₁ B₂ B₃ B₄ B₅ B₆ m)
    (b : BBlk6) :
    ∀ ps : List BPeel6, bpeelOK b ps = true →
      PeelOK6 (b.blk B₁ B₂ B₃ B₄ B₅ B₆ m).reads (ps.map (BPeel6.fac B₁ B₂ B₃ B₄ B₅ B₆ m))
  | [], _ => trivial
  | p :: ps, h => by
    simp only [bpeelOK, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.all_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨?_, ?_, ?_, peelOK_of6 hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm b ps h4⟩
    · rw [blk_reads6, (peel_reads6 p).2]; exact h1
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      rw [(peel_reads6 g').1, (peel_reads6 p).2]
      have := h2 g' hg'
      simpa using this
    · cases p with
      | ev r k =>
        simp only [BPeel6.okb, decide_eq_true_eq] at h3
        exact ⟨h3.1, dset_card hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm h3.1 k⟩
      | eq r j =>
        simp only [BPeel6.okb, decide_eq_true_eq] at h3
        exact h3

theorem blk_ok6 (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6)
    (hB₄ : B₄.card = 6) (hB₅ : B₅.card = 6) (hB₆ : B₆.card = 6) (hm : MOK B₁ B₂ B₃ B₄ B₅ B₆ m)
    (b : BBlk6) (hb : b.okb = true) : (b.blk B₁ B₂ B₃ B₄ B₅ B₆ m).ok := by
  cases b with
  | none => trivial
  | one r k =>
    simp only [BBlk6.okb, decide_eq_true_eq] at hb
    exact ⟨hb.1, dset_card hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm hb.1 k⟩
  | two r k k' =>
    simp only [BBlk6.okb, decide_eq_true_eq] at hb
    exact ⟨hb.1, dset_card hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm (by omega) k,
      dset_card hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm (by omega) k'⟩
  | three r k k' k'' =>
    simp only [BBlk6.okb, decide_eq_true_eq] at hb
    exact ⟨hb.1, dset_card hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm (by omega) k,
      dset_card hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm (by omega) k',
      dset_card hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm (by omega) k''⟩

theorem toPin_OK (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6)
    (hB₄ : B₄.card = 6) (hB₅ : B₅.card = 6) (hB₆ : B₆.card = 6) (hm : MOK B₁ B₂ B₃ B₄ B₅ B₆ m)
    {q : BPin6} (hq : q.okb = true) : (q.toPin B₁ B₂ B₃ B₄ B₅ B₆ m).OK := by
  simp only [BPin6.okb, Bool.and_eq_true] at hq
  exact ⟨blk_ok6 hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm q.blk hq.1,
    peelOK_of6 hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm q.blk q.peels hq.2⟩

theorem toPin_bnd (q : BPin6) : (q.toPin B₁ B₂ B₃ B₄ B₅ B₆ m).bnd = q.bnd m := by
  unfold Pin6.bnd BPin6.bnd BPin6.toPin
  congr 1
  · rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    cases p <;> rfl
  · cases q.blk <;> rfl

/-- The event of a pin on a state is its event on the codes and the canonical pattern. -/
theorem pin_evc6 (q : BPin6) {s : T6} (hs : Proper s) (hq : q.okb = true) :
    (q.toPin B₁ B₂ B₃ B₄ B₅ B₆ m).ev s = q.evc (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s) (canon s) := by
  simp only [BPin6.okb, Bool.and_eq_true] at hq
  obtain ⟨hb, hp⟩ := hq
  have hpk := bpeelOK_all hp
  unfold Pin6.ev BPin6.evc BPin6.toPin allEv6
  simp only
  congr 1
  · rw [List.all_map]
    refine all_congr_mem fun p hp' => ?_
    have hpk' : p.okb = true := List.all_eq_true.mp hpk p hp'
    cases p with
    | ev r k =>
      simp only [BPeel6.okb, decide_eq_true_eq] at hpk'
      simp only [Function.comp, BPeel6.fac, Fac6.ev, BPeel6.evc, evk_codes _ _ _ _ _ _ _ hpk'.1]
    | eq r j =>
      simp only [BPeel6.okb, decide_eq_true_eq] at hpk'
      simp only [Function.comp, BPeel6.fac, Fac6.ev, BPeel6.evc]
      rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq, canon_eq_foT hs,
        foT_rows s hpk'.1 hpk'.2.1]
  · cases hbb : q.blk with
    | none => rfl
    | one r k =>
      rw [hbb] at hb; simp only [BBlk6.okb, decide_eq_true_eq] at hb
      simp only [BBlk6.blk, Blk6.ev, BBlk6.evc, evk_codes _ _ _ _ _ _ _ hb.1]
    | two r k k' =>
      rw [hbb] at hb; simp only [BBlk6.okb, decide_eq_true_eq] at hb
      simp only [BBlk6.blk, Blk6.ev, BBlk6.evc, evk_codes _ _ _ _ _ _ _ (show r < 6 by omega),
        evk_codes _ _ _ _ _ _ _ (show r + 1 < 6 by omega)]
    | three r k k' k'' =>
      rw [hbb] at hb; simp only [BBlk6.okb, decide_eq_true_eq] at hb
      simp only [BBlk6.blk, Blk6.ev, BBlk6.evc, evk_codes _ _ _ _ _ _ _ (show r < 6 by omega),
        evk_codes _ _ _ _ _ _ _ (show r + 1 < 6 by omega),
        evk_codes _ _ _ _ _ _ _ (show r + 2 < 6 by omega)]

/-- **The pins average out.** -/
theorem sum_fired6 (hw : InCone6 w) (h₁ : 5 ≤ X₁.card) (h₂ : 5 ≤ X₂.card) (h₃ : 5 ≤ X₃.card)
    (h₄ : 5 ≤ X₄.card) (h₅ : 5 ≤ X₅.card) (h₆ : 5 ≤ X₆.card) (hB₁ : B₁.card = 6)
    (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6) (hB₄ : B₄.card = 6) (hB₅ : B₅.card = 6)
    (hB₆ : B₆.card = 6) (hm : MOK B₁ B₂ B₃ B₄ B₅ B₆ m) :
    ∀ P : List BPin6, P.all BPin6.okb = true →
      ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆,
          GU 6 w s * (fired P (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s) (canon s) : ℝ)
        ≤ ((lamBnd P m : ℚ) : ℝ) * ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w s
  | [], _ => by simp [fired, lamBnd]
  | q :: P, hP => by
    simp only [List.all_cons, Bool.and_eq_true] at hP
    have ih := sum_fired6 hw h₁ h₂ h₃ h₄ h₅ h₆ hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm P hP.2
    have hq := pin_sum6 hw h₁ h₂ h₃ h₄ h₅ h₆ (q.toPin B₁ B₂ B₃ B₄ B₅ B₆ m)
      (toPin_OK hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm hP.1)
    rw [toPin_bnd] at hq
    have e1 : ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w s * (fired (q :: P)
          (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s) (canon s) : ℝ)
        = (q.lam : ℝ) * ∑ s ∈ (sts X₁ X₂ X₃ X₄ X₅ X₆).filter
            (fun t => (q.toPin B₁ B₂ B₃ B₄ B₅ B₆ m).ev t = true), GU 6 w s
          + ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w s * (fired P (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)
            (canon s) : ℝ) := by
      rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun s hs => ?_)
      rw [pin_evc6 q (proper_of_mem_sts hs) hP.1]
      simp only [fired, List.map_cons, List.sum_cons]
      split_ifs <;> push_cast <;> ring
    rw [e1]
    have hl : (0 : ℝ) ≤ q.lam := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hq hl
    simp only [lamBnd, List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast]
    simp only [lamBnd] at ih
    linarith

end sound

/-! ### The seam from state inequalities -/

/-- **The seam inequality from a certificate**: state inequalities with the fired multipliers
and `Σ λ · bnd ≤ K` average to the seam. -/
theorem seam_of_states {w : Wt6} {X₁ X₂ X₃ X₄ X₅ X₆ B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ} {m : List ℕ}
    (hw : InCone6 w) (h₁ : 5 ≤ X₁.card) (h₂ : 5 ≤ X₂.card) (h₃ : 5 ≤ X₃.card)
    (h₄ : 5 ≤ X₄.card) (h₅ : 5 ≤ X₅.card) (h₆ : 5 ≤ X₆.card) (hB₁ : B₁.card = 6)
    (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6) (hB₄ : B₄.card = 6) (hB₅ : B₅.card = 6)
    (hB₆ : B₆.card = 6) (hm : MOK B₁ B₂ B₃ B₄ B₅ B₆ m) {P : List BPin6} {K D : ℕ} (hD : 0 < D)
    (hP : P.all BPin6.okb = true) (hL : lamBnd P m ≤ K)
    (hstate : ∀ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w s * ((D : ℝ) + K
      - fired P (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s) (canon s)) ≤ D * GB w B₁ B₂ B₃ B₄ B₅ B₆ s) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w s
      ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GB w B₁ B₂ B₃ B₄ B₅ B₆ s := by
  set Ω := sts X₁ X₂ X₃ X₄ X₅ X₆ with hΩ
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hsum := Finset.sum_le_sum hstate
  have hf := sum_fired6 hw h₁ h₂ h₃ h₄ h₅ h₆ hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm P hP
  set W := ∑ s ∈ Ω, GU 6 w s with hW
  have hLR : ((lamBnd P m : ℚ) : ℝ) ≤ K := by exact_mod_cast hL
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun s _ => GU_nonneg hw s
  have e : ∑ s ∈ Ω, GU 6 w s * ((D : ℝ) + K
      - fired P (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s) (canon s))
      = ((D : ℝ) + K) * W
        - ∑ s ∈ Ω, GU 6 w s * (fired P (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s) (canon s) : ℝ) := by
    rw [hW, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [e, ← Finset.mul_sum] at hsum
  have h1 : ((lamBnd P m : ℚ) : ℝ) * W ≤ K * W := mul_le_mul_of_nonneg_right hLR hW0
  have h2 : (D : ℝ) * W ≤ D * ∑ s ∈ Ω, GB w B₁ B₂ B₃ B₄ B₅ B₆ s := by linarith
  exact le_of_mul_le_mul_left h2 hDR

end GridGen.Six
