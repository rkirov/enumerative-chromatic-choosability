/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.K5.State

/-!
# Height five at `k = 5`: dual certificates over the state bits

`ai_research_notes/cx/h5k5/NOTE.md` §2 and `H5_K5_REVIEW_2026-10-28.md` (c), in the form of
`GridGen/Four/BitLP5k.lean`. A previous column `s` has row codes (`kcodes`) and a canonical
pattern; by `state55`, `GB ≥ GU · (1 + V)` with `V = 10⁹ · N5g(codes) / (R · NU) - 1`, a function
of the codes and the pattern.

**Pins.** A pin (`BPin5`) is a block of one to three consecutive rows, each in one of the sets
`Bᵣ ∖ Bᵣ₋₁` (kind `0`), `Bᵣ ∖ Bᵣ₊₁` (kind `1`) or their union (kind `2`), and a list of peels (a
row in such a set, or an equality of two rows) in a valid order; its event carries at most `bnd`
of the uniform weight (`pin_sum5`), the set sizes being bounded by the mismatches.

**The certificate** (`BitCert5`): integer multipliers `λ`, a constant `K` and a denominator `D`.
The kernel check `bitOK5` verifies `Σ λ · bnd ≤ K` and, at every admissible code vector and
pattern, `V ≥ (K - Σ_{pins that fire} λ)/D` (in integers); averaging gives the seam inequality
(`seam_of_bit55`). A pointwise class has no pins and `K = 0`.
-/

namespace GridGen.Five.K5

open Finset GridGen.Five GridGen.Five.Ex5

/-! ### Lists and sets by row -/

/-- The list before a row (an end row is its own neighbour). -/
def Bpv (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (r : ℕ) : Finset ℕ :=
  if r = 0 then B₁ else bl B₁ B₂ B₃ B₄ B₅ (r - 1)

/-- The list after a row. -/
def Bnx (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (r : ℕ) : Finset ℕ :=
  if 4 ≤ r then B₅ else bl B₁ B₂ B₃ B₄ B₅ (r + 1)

/-- The colour set of a row event: kind `0` new against the previous list, `1` against the next
one, `2` either. -/
def Dset (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (r k : ℕ) : Finset ℕ :=
  if k = 0 then bl B₁ B₂ B₃ B₄ B₅ r \ Bpv B₁ B₂ B₃ B₄ B₅ r
  else if k = 1 then bl B₁ B₂ B₃ B₄ B₅ r \ Bnx B₁ B₂ B₃ B₄ B₅ r
  else (bl B₁ B₂ B₃ B₄ B₅ r \ Bpv B₁ B₂ B₃ B₄ B₅ r) ∪ (bl B₁ B₂ B₃ B₄ B₅ r \ Bnx B₁ B₂ B₃ B₄ B₅ r)

/-- The code of a row. -/
def crow (c : ℕ × ℕ × ℕ × ℕ × ℕ) (r : ℕ) : ℕ :=
  match r with
  | 0 => c.1
  | 1 => c.2.1
  | 2 => c.2.2.1
  | 3 => c.2.2.2.1
  | _ => c.2.2.2.2

theorem crow_codes (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (s : T5) {r : ℕ} (hr : r < 5) :
    crow (kcodes B₁ B₂ B₃ B₄ B₅ s) r
      = rcode (Bpv B₁ B₂ B₃ B₄ B₅ r) (bl B₁ B₂ B₃ B₄ B₅ r) (Bnx B₁ B₂ B₃ B₄ B₅ r) (rowAt r s) := by
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

theorem evk_codes (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (s : T5) {r : ℕ} (hr : r < 5) (k : ℕ) :
    evk k (crow (kcodes B₁ B₂ B₃ B₄ B₅ s) r)
      = decide (rowAt r s ∈ Dset B₁ B₂ B₃ B₄ B₅ r k) := by
  rw [crow_codes _ _ _ _ _ _ hr, evk_code]; rfl

/-- The mismatch before and after a row (`m = [m₂, m₃, m₄, m₅]`). -/
def mprev (m : List ℕ) (r : ℕ) : ℕ := if r = 0 then 0 else m.getD (r - 1) 0
def mnext (m : List ℕ) (r : ℕ) : ℕ := if 4 ≤ r then 0 else m.getD r 0

/-- The declared size of a row event. -/
def dsz (m : List ℕ) (r k : ℕ) : ℕ :=
  if k = 0 then mprev m r else if k = 1 then mnext m r else mprev m r + mnext m r

theorem card_sdiff5 {B C : Finset ℕ} (hB : B.card = 5) {m : ℕ} (h : (B ∩ C).card + m = 5) :
    (B \ C).card = m := by
  have := Finset.card_sdiff_add_card_inter B C; omega

/-- The mismatches of the lists. -/
def MOK (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (m : List ℕ) : Prop :=
  (B₁ ∩ B₂).card + m.getD 0 0 = 5 ∧ (B₂ ∩ B₃).card + m.getD 1 0 = 5 ∧
    (B₃ ∩ B₄).card + m.getD 2 0 = 5 ∧ (B₄ ∩ B₅).card + m.getD 3 0 = 5

theorem dset_card {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5)
    (hB₃ : B₃.card = 5) (hB₄ : B₄.card = 5) (hB₅ : B₅.card = 5) {m : List ℕ}
    (hm : MOK B₁ B₂ B₃ B₄ B₅ m) {r : ℕ} (hr : r < 5) (k : ℕ) :
    (Dset B₁ B₂ B₃ B₄ B₅ r k).card ≤ dsz m r k := by
  obtain ⟨c2, c3, c4, c5⟩ := hm
  have c2' : (B₂ ∩ B₁).card + m.getD 0 0 = 5 := by rw [inter_comm]; exact c2
  have c3' : (B₃ ∩ B₂).card + m.getD 1 0 = 5 := by rw [inter_comm]; exact c3
  have c4' : (B₄ ∩ B₃).card + m.getD 2 0 = 5 := by rw [inter_comm]; exact c4
  have c5' : (B₅ ∩ B₄).card + m.getD 3 0 = 5 := by rw [inter_comm]; exact c5
  have hp : (bl B₁ B₂ B₃ B₄ B₅ r \ Bpv B₁ B₂ B₃ B₄ B₅ r).card = mprev m r := by
    interval_cases r
    · simp [bl, Bpv, mprev]
    · exact card_sdiff5 hB₂ c2'
    · exact card_sdiff5 hB₃ c3'
    · exact card_sdiff5 hB₄ c4'
    · exact card_sdiff5 hB₅ c5'
  have hn : (bl B₁ B₂ B₃ B₄ B₅ r \ Bnx B₁ B₂ B₃ B₄ B₅ r).card = mnext m r := by
    interval_cases r
    · exact card_sdiff5 hB₁ c2
    · exact card_sdiff5 hB₂ c3
    · exact card_sdiff5 hB₃ c4
    · exact card_sdiff5 hB₄ c5
    · simp [bl, Bnx, mnext]
  unfold Dset dsz
  split_ifs
  · exact hp.le
  · exact hn.le
  · exact (card_union_le _ _).trans (by rw [hp, hn])

/-! ### Pins over the state bits -/

/-- A peel: a row in a set, or two rows equal. -/
inductive BPeel5
  | ev (r k : ℕ)
  | eq (r j : ℕ)

/-- A block: none, or one to three consecutive rows. -/
inductive BBlk5
  | none
  | one (r k : ℕ)
  | two (r k k' : ℕ)
  | three (r k k' k'' : ℕ)

/-- A pin with its integer multiplier. -/
structure BPin5 where
  blk : BBlk5
  peels : List BPeel5
  lam : ℕ
  bm : ℕ
  em : ℕ

namespace BPeel5

def row : BPeel5 → ℕ | ev r _ => r | eq r _ => r
def reads : BPeel5 → ℕ → Bool
  | ev r _, i => decide (r = i)
  | eq r j, i => decide (r = i) || decide (j = i)
def okb : BPeel5 → Bool
  | ev r k => decide (r < 5 ∧ k < 3)
  | eq r j => decide (r < 5 ∧ j < 5 ∧ j ≠ r)

/-- The event on codes and a canonical pattern. -/
def evc (c : ℕ × ℕ × ℕ × ℕ × ℕ) (p : T5) : BPeel5 → Bool
  | ev r k => evk k (crow c r)
  | eq r j => rowAt r p == rowAt j p

def bnd (m : List ℕ) : BPeel5 → ℚ
  | ev r k => min (qX r * dsz m r k) 1
  | eq r _ => qX r

/-- The factor for actual lists. -/
def fac (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (m : List ℕ) : BPeel5 → Fac5
  | ev r k => Fac5.mem r (Dset B₁ B₂ B₃ B₄ B₅ r k) (dsz m r k)
  | eq r j => Fac5.eqr r j

end BPeel5

namespace BBlk5

def reads : BBlk5 → ℕ → Bool
  | none, _ => false
  | one r _, i => decide (r = i)
  | two r _ _, i => decide (r = i) || decide (r + 1 = i)
  | three r _ _ _, i => decide (r = i) || decide (r + 1 = i) || decide (r + 2 = i)

def okb : BBlk5 → Bool
  | none => true
  | one r k => decide (r < 5 ∧ k < 3)
  | two r k k' => decide (r < 4 ∧ k < 3 ∧ k' < 3)
  | three r k k' k'' => decide (r < 3 ∧ k < 3 ∧ k' < 3 ∧ k'' < 3)

/-- The row conditions of a block. -/
def conds : BBlk5 → List (ℕ × ℕ)
  | none => []
  | one r k => [(r, k)]
  | two r k k' => [(r, k), (r + 1, k')]
  | three r k k' k'' => [(r, k), (r + 1, k'), (r + 2, k'')]

def evc (c : ℕ × ℕ × ℕ × ℕ × ℕ) : BBlk5 → Bool
  | none => true
  | one r k => evk k (crow c r)
  | two r k k' => evk k (crow c r) && evk k' (crow c (r + 1))
  | three r k k' k'' => evk k (crow c r) && evk k' (crow c (r + 1)) && evk k'' (crow c (r + 2))

def bnd (m : List ℕ) : BBlk5 → ℚ
  | none => 1
  | one r k => βQ5 (dsz m r k) 4 (fsd r * fsd (4 - r))
  | two r k k' => βQ5 (dsz m r k * dsz m (r + 1) k') 12 (fsd r * fsd (3 - r))
  | three r k k' k'' =>
      βQ5 (dsz m r k * dsz m (r + 1) k' * dsz m (r + 2) k'') 36 (fsd r * fsd (2 - r))

def blk (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (m : List ℕ) : BBlk5 → Blk5
  | none => Blk5.none
  | one r k => Blk5.one r (Dset B₁ B₂ B₃ B₄ B₅ r k) (dsz m r k)
  | two r k k' => Blk5.two r (Dset B₁ B₂ B₃ B₄ B₅ r k) (Dset B₁ B₂ B₃ B₄ B₅ (r + 1) k')
      (dsz m r k) (dsz m (r + 1) k')
  | three r k k' k'' => Blk5.three r (Dset B₁ B₂ B₃ B₄ B₅ r k) (Dset B₁ B₂ B₃ B₄ B₅ (r + 1) k')
      (Dset B₁ B₂ B₃ B₄ B₅ (r + 2) k'') (dsz m r k) (dsz m (r + 1) k') (dsz m (r + 2) k'')

end BBlk5

/-- The peel order, as a boolean. -/
def bpeelOK (b : BBlk5) : List BPeel5 → Bool
  | [] => true
  | p :: ps => !(b.reads p.row) && ps.all (fun g => !(g.reads p.row)) && p.okb && bpeelOK b ps

namespace BPin5

def evc (q : BPin5) (c : ℕ × ℕ × ℕ × ℕ × ℕ) (p : T5) : Bool :=
  q.peels.all (fun f => f.evc c p) && q.blk.evc c

def bnd (q : BPin5) (m : List ℕ) : ℚ := (q.peels.map (BPeel5.bnd m)).prod * q.blk.bnd m

end BPin5

/-- A dual certificate over the state bits for one mismatch class. -/
structure BitCert5 where
  pins : List BPin5
  K : ℕ
  D : ℕ

/-- The multipliers of the pins that fire. -/
def fired (P : List BPin5) (c : ℕ × ℕ × ℕ × ℕ × ℕ) (p : T5) : ℕ :=
  (P.map fun q => if q.evc c p then q.lam else 0).sum

/-- `Σ λ · bnd`. -/
def lamBnd (P : List BPin5) (m : List ℕ) : ℚ := (P.map fun q => (q.lam : ℚ) * q.bnd m).sum

/-! ### Events as bit masks -/

/-- The row conditions of the peels. -/
def peelConds : List BPeel5 → List (ℕ × ℕ)
  | [] => []
  | BPeel5.ev r k :: ps => (r, k) :: peelConds ps
  | BPeel5.eq _ _ :: ps => peelConds ps

/-- The equalities of the peels. -/
def peelEqs : List BPeel5 → List (ℕ × ℕ)
  | [] => []
  | BPeel5.ev _ _ :: ps => peelEqs ps
  | BPeel5.eq r j :: ps => (r, j) :: peelEqs ps

/-- The index of a code vector. -/
def cidx (c : ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ := c.1 + 5 * c.2.1 + 25 * c.2.2.1 + 125 * c.2.2.2.1 + 625 * c.2.2.2.2

/-- Digit `r` of a code index. -/
def cdig (r ci : ℕ) : ℕ := ci / 5 ^ r % 5

/-- All `3125` code indices. -/
def FULLc : ℕ := 2 ^ 3125 - 1

/-- All `15` patterns. -/
def FULLp : ℕ := 2 ^ 15 - 1

/-- The patterns satisfying an equality, as a mask over the canonical patterns. -/
def pmask (r j : ℕ) : ℕ :=
  (List.range 15).foldr (fun i acc => if rowAt r (canons.getD i (0, 0, 0, 0, 0)) ==
    rowAt j (canons.getD i (0, 0, 0, 0, 0)) then 2 ^ i + acc else acc) 0

theorem pmask_ok : ∀ r < 5, ∀ j < 5, ∀ i < 15, (pmask r j).testBit i =
    (rowAt r (canons.getD i (0, 0, 0, 0, 0)) == rowAt j (canons.getD i (0, 0, 0, 0, 0))) := by
  decide +kernel

/-- The mask of a pin's row conditions, from the row masks `rm`. -/
def bmaskOf (rm : List ℕ) (q : BPin5) : ℕ :=
  (q.blk.conds ++ peelConds q.peels).foldr (fun rk acc => rm.getD (3 * rk.1 + rk.2) 0 &&& acc) FULLc

/-- The mask of a pin's equalities. -/
def emaskOf (q : BPin5) : ℕ := (peelEqs q.peels).foldr (fun rj acc => pmask rj.1 rj.2 &&& acc) FULLp

/-- A well-formed pin with correct masks. -/
def BPin5.okb (rm : List ℕ) (q : BPin5) : Bool :=
  q.blk.okb && bpeelOK q.blk q.peels && q.bm == bmaskOf rm q && q.em == emaskOf q

/-- The check of one row mask. -/
def rmOK (rm : List ℕ) (r k : ℕ) : Bool :=
  (List.range 3125).all fun ci => (rm.getD (3 * r + k) 0).testBit ci == evk k (cdig r ci)

theorem rmOK_spec {rm : List ℕ} {r k : ℕ} (h : rmOK rm r k = true) {ci : ℕ} (hci : ci < 3125) :
    (rm.getD (3 * r + k) 0).testBit ci = evk k (cdig r ci) := by
  have := List.all_eq_true.mp h ci (List.mem_range.mpr hci)
  simpa using this

/-! ### The check -/

/-- The uniform successor counts by orbit. -/
def NUL : List ℕ := [469, 459, 460, 447, 450, 434, 437, 450, 449, 441, 440]

theorem NUL_eq : ∀ o : Fin 11, NUL.getD o 0 = NUo o := by decide +kernel

/-- The orbits of the canonical patterns. -/
def ORBL : List ℕ := [0, 1, 2, 3, 4, 5, 3, 6, 7, 1, 8, 9, 6, 4, 10]

theorem ORBL_eq : ∀ i < 15, ORBL.getD i 0 = (orb (canons.getD i (0, 0, 0, 0, 0)) : ℕ) := by
  decide +kernel

/-- The consecutive intersection from a code pair. -/
def nE5 (m cp ci : ℕ) : ℕ := 3 + kH cp + kX cp + kH ci + kM ci - m

/-- The admissible code vectors of a class. -/
def bvalid5 (m2 m3 m4 m5 c1 c2 c3 c4 c5 : ℕ) : Bool :=
  kM c1 == 0 && kX c5 == 0 &&
  (kM c2 == 0 || 0 < m2) && (kM c3 == 0 || 0 < m3) && (kM c4 == 0 || 0 < m4) &&
  (kM c5 == 0 || 0 < m5) && (kX c1 == 0 || 0 < m2) && (kX c2 == 0 || 0 < m3) &&
  (kX c3 == 0 || 0 < m4) && (kX c4 == 0 || 0 < m5) &&
  decide (m2 ≤ 3 + kH c1 + kX c1 + kH c2 + kM c2) &&
  decide (m3 ≤ 3 + kH c2 + kX c2 + kH c3 + kM c3) &&
  decide (m4 ≤ 3 + kH c3 + kX c3 + kH c4 + kM c4) &&
  decide (m5 ≤ 3 + kH c4 + kX c4 + kH c5 + kM c5)

/-- The multipliers of the pins (already filtered by code) whose equalities hold at pattern
`i`. -/
def firedL (F : List BPin5) (i : ℕ) : ℕ := (F.map fun q => if q.em.testBit i then q.lam else 0).sum

/-- The check at one code index, for every canonical pattern, given the greedy count's positive
and negative parts `P`, `M` and the ratio bounds `Rl`. -/
def stOK5 (C : BitCert5) (F : List BPin5) (P M : ℕ) (Rl : List ℕ) : Bool :=
  (List.range 15).all fun i => decide (0 < Rl.getD (ORBL.getD i 0) 0) &&
    decide ((C.D + C.K) * NUL.getD (ORBL.getD i 0) 0 * Rl.getD (ORBL.getD i 0) 0
        + C.D * 1000000000 * M
      ≤ C.D * 1000000000 * P + firedL F i * NUL.getD (ORBL.getD i 0) 0 * Rl.getD (ORBL.getD i 0) 0)

/-- The check at one code vector. -/
def bitAt5 (m2 m3 m4 m5 : ℕ) (C : BitCert5) (c1 c2 c3 c4 c5 : ℕ) : Bool :=
  !(bvalid5 m2 m3 m4 m5 c1 c2 c3 c4 c5) ||
    stOK5 C (C.pins.filter fun q => q.bm.testBit (cidx (c1, c2, c3, c4, c5)))
      (kapP (4 + kH c1) (4 + kH c2) (4 + kH c3) (4 + kH c4) (4 + kH c5)
        (nE5 m2 c1 c2) (nE5 m3 c2 c3) (nE5 m4 c3 c4) (nE5 m5 c4 c5))
      (kapM (4 + kH c1) (4 + kH c2) (4 + kH c3) (4 + kH c4) (4 + kH c5)
        (nE5 m2 c1 c2) (nE5 m3 c2 c3) (nE5 m4 c3 c4) (nE5 m5 c4 c5))
      (patCerts.getD (nidx (4 + kH c1) (4 + kH c2) (4 + kH c3) (4 + kH c4) (4 + kH c5)) default).R

/-- `p i` for all `i ≤ 4`. -/
def all5k (p : ℕ → Bool) : Bool := p 0 && p 1 && p 2 && p 3 && p 4

theorem all5k_spec {p : ℕ → Bool} (h : all5k p = true) {i : ℕ} (hi : i ≤ 4) : p i = true := by
  simp only [all5k, Bool.and_eq_true] at h
  interval_cases i <;> tauto

/-- The pins of a certificate are well formed and `Σ λ · bnd ≤ K`. -/
def pinsOK5 (rm : List ℕ) (m2 m3 m4 m5 : ℕ) (C : BitCert5) : Bool :=
  decide (0 < C.D) && C.pins.all (BPin5.okb rm) && decide (lamBnd C.pins [m2, m3, m4, m5] ≤ C.K)

/-- The states with first code `c1`. -/
def bitPart5 (m2 m3 m4 m5 : ℕ) (C : BitCert5) (c1 : ℕ) : Bool :=
  all5k (fun c2 => all5k (fun c3 => all5k (fun c4 => all5k (fun c5 =>
    bitAt5 m2 m3 m4 m5 C c1 c2 c3 c4 c5))))

/-- **The certificate check**, split by the first code. -/
def bitOK5 (rm : List ℕ) (m2 m3 m4 m5 : ℕ) (C : BitCert5) : Bool :=
  pinsOK5 rm m2 m3 m4 m5 C && all5k (bitPart5 m2 m3 m4 m5 C)

/-! ### Pointwise classes -/

/-- The largest `NU · R` over the orbits, by size vector. -/
def NURmax (nv : ℕ) : ℕ := ((List.range 11).map fun o =>
  NUL.getD o 0 * (patCerts.getD nv default).R.getD o 0).foldr max 0

/-- **The pointwise check** at one code vector: `V ≥ 0` for every pattern. -/
def ptAt5 (m2 m3 m4 m5 : ℕ) (NM : List ℕ) (c1 c2 c3 c4 c5 : ℕ) : Bool :=
  !(bvalid5 m2 m3 m4 m5 c1 c2 c3 c4 c5) ||
    decide (NM.getD (nidx (4 + kH c1) (4 + kH c2) (4 + kH c3) (4 + kH c4) (4 + kH c5)) 0
        + 1000000000 * kapM (4 + kH c1) (4 + kH c2) (4 + kH c3) (4 + kH c4) (4 + kH c5)
          (nE5 m2 c1 c2) (nE5 m3 c2 c3) (nE5 m4 c3 c4) (nE5 m5 c4 c5)
      ≤ 1000000000 * kapP (4 + kH c1) (4 + kH c2) (4 + kH c3) (4 + kH c4) (4 + kH c5)
          (nE5 m2 c1 c2) (nE5 m3 c2 c3) (nE5 m4 c3 c4) (nE5 m5 c4 c5))

/-- The pointwise check of a class. -/
def ptOK5 (NM : List ℕ) (m2 m3 m4 m5 : ℕ) : Bool :=
  all5k (fun c1 => all5k (fun c2 => all5k (fun c3 => all5k (fun c4 => all5k (fun c5 =>
    ptAt5 m2 m3 m4 m5 NM c1 c2 c3 c4 c5)))))

end GridGen.Five.K5
