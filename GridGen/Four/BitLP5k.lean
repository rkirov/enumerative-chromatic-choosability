/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.State5

/-!
# Height four, `k = 5`: dual certificates over the state bits

`ai_research_notes/H4_K5_ANALYTIC_2026-10-24.md` §3, in the exp form of
`ai_research_notes/H4_K5_REVIEW_2026-10-24.md` (fix 1). A previous column `s` has row codes
(`codes5`) and pattern bits (`pbits`). By `state_bound5k`,
`GB ≥ GU · (1 + V)` with `V = cpat5 · N4g(codes) / nu5 - 1`, a function of the bits.

**Pins.** A pin is a block event (`BBlk`: none, one row, or two adjacent rows, each in one of
the sets `Bᵣ ∖ Bᵣ₋₁`, `Bᵣ ∖ Bᵣ₊₁` or their union) and a list of peels (`BPeel`: a row in such a
set, or an equality of two rows), in an order in which each peeled row is read by no later
factor and not by the block. Its event carries at most `bnd` of the uniform weight
(`pin_sum`, with the set sizes bounded by the mismatches).

**The certificate** (`BitCert`). Integer multipliers `λ` for some pins, a constant `L0` and a
denominator `D`. The kernel check `bitOK` verifies `Σ λ · bnd ≤ L0` and, for every admissible
code vector and pattern, `V ≥ (L0 - Σ_{pins that fire} λ)/D` (in integers). Averaging gives
`Σ GU · V ≥ 0`, hence the seam inequality (`seam_of_bit5k`).
-/

namespace GridGen.Four

open Finset

/-! ### Lists and sets by row -/

/-- The list of a row, and the lists before and after it (an end row is its own neighbour). -/
def Bi4 (B₁ B₂ B₃ B₄ : Finset ℕ) : Fin 4 → Finset ℕ | 0 => B₁ | 1 => B₂ | 2 => B₃ | 3 => B₄
def Bp4 (B₁ B₂ B₃ _B₄ : Finset ℕ) : Fin 4 → Finset ℕ | 0 => B₁ | 1 => B₁ | 2 => B₂ | 3 => B₃
def Bn4 (_B₁ B₂ B₃ B₄ : Finset ℕ) : Fin 4 → Finset ℕ | 0 => B₂ | 1 => B₃ | 2 => B₄ | 3 => B₄

/-- The colour set of a row event: `0` new against the previous list, `1` against the next one,
else either. -/
def Dset (B₁ B₂ B₃ B₄ : Finset ℕ) (r : Fin 4) (k : ℕ) : Finset ℕ :=
  if k = 0 then Bi4 B₁ B₂ B₃ B₄ r \ Bp4 B₁ B₂ B₃ B₄ r
  else if k = 1 then Bi4 B₁ B₂ B₃ B₄ r \ Bn4 B₁ B₂ B₃ B₄ r
  else (Bi4 B₁ B₂ B₃ B₄ r \ Bp4 B₁ B₂ B₃ B₄ r) ∪ (Bi4 B₁ B₂ B₃ B₄ r \ Bn4 B₁ B₂ B₃ B₄ r)

/-- The code of a row. -/
def crow (c : ℕ × ℕ × ℕ × ℕ) : Fin 4 → ℕ | 0 => c.1 | 1 => c.2.1 | 2 => c.2.2.1 | 3 => c.2.2.2

theorem crow_codes (B₁ B₂ B₃ B₄ : Finset ℕ) (s : T4) (r : Fin 4) :
    crow (codes5 B₁ B₂ B₃ B₄ s) r
      = rowCode5 (Bp4 B₁ B₂ B₃ B₄ r) (Bi4 B₁ B₂ B₃ B₄ r) (Bn4 B₁ B₂ B₃ B₄ r) (rowfun r s) := by
  fin_cases r <;> rfl

/-- A row event on a code. -/
def evk (k c : ℕ) : Bool :=
  if k = 0 then cM5 c == 1 else if k = 1 then cX5 c == 1 else (cM5 c == 1 || cX5 c == 1)

theorem evk_code (Bp Bi Bn : Finset ℕ) (x k : ℕ) :
    evk k (rowCode5 Bp Bi Bn x)
      = decide (x ∈ (if k = 0 then Bi \ Bp else if k = 1 then Bi \ Bn
          else (Bi \ Bp) ∪ (Bi \ Bn))) := by
  unfold evk
  rw [cM5_code, cX5_code]
  split_ifs <;> simp_all [Finset.mem_union]

theorem evk_codes (B₁ B₂ B₃ B₄ : Finset ℕ) (s : T4) (r : Fin 4) (k : ℕ) :
    evk k (crow (codes5 B₁ B₂ B₃ B₄ s) r) = decide (rowfun r s ∈ Dset B₁ B₂ B₃ B₄ r k) := by
  rw [crow_codes, evk_code]; rfl

/-- The declared sizes: the mismatch before and after a row. -/
def dprev (m2 m3 m4 : ℕ) : Fin 4 → ℕ | 0 => 0 | 1 => m2 | 2 => m3 | 3 => m4
def dnext (m2 m3 m4 : ℕ) : Fin 4 → ℕ | 0 => m2 | 1 => m3 | 2 => m4 | 3 => 0

def dsz (m2 m3 m4 : ℕ) (r : Fin 4) (k : ℕ) : ℕ :=
  if k = 0 then dprev m2 m3 m4 r else if k = 1 then dnext m2 m3 m4 r
  else dprev m2 m3 m4 r + dnext m2 m3 m4 r

theorem card_sdiff5 {B C : Finset ℕ} (hB : B.card = 5) {m : ℕ} (h : (B ∩ C).card + m = 5) :
    (B \ C).card = m := by
  have := Finset.card_sdiff_add_card_inter B C; omega

theorem dset_card {B₁ B₂ B₃ B₄ : Finset ℕ} (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5)
    (hB₃ : B₃.card = 5) (hB₄ : B₄.card = 5) {m2 m3 m4 : ℕ}
    (c2 : (B₁ ∩ B₂).card + m2 = 5) (c3 : (B₂ ∩ B₃).card + m3 = 5)
    (c4 : (B₃ ∩ B₄).card + m4 = 5) (r : Fin 4) (k : ℕ) :
    (Dset B₁ B₂ B₃ B₄ r k).card ≤ dsz m2 m3 m4 r k := by
  have c2' : (B₂ ∩ B₁).card + m2 = 5 := by rw [inter_comm]; exact c2
  have c3' : (B₃ ∩ B₂).card + m3 = 5 := by rw [inter_comm]; exact c3
  have c4' : (B₄ ∩ B₃).card + m4 = 5 := by rw [inter_comm]; exact c4
  have hp : (Bi4 B₁ B₂ B₃ B₄ r \ Bp4 B₁ B₂ B₃ B₄ r).card = dprev m2 m3 m4 r := by
    fin_cases r
    · simp [Bi4, Bp4, dprev]
    · exact card_sdiff5 hB₂ c2'
    · exact card_sdiff5 hB₃ c3'
    · exact card_sdiff5 hB₄ c4'
  have hn : (Bi4 B₁ B₂ B₃ B₄ r \ Bn4 B₁ B₂ B₃ B₄ r).card = dnext m2 m3 m4 r := by
    fin_cases r
    · exact card_sdiff5 hB₁ c2
    · exact card_sdiff5 hB₂ c3
    · exact card_sdiff5 hB₃ c4
    · simp [Bi4, Bn4, dnext]
  unfold Dset dsz
  split_ifs
  · exact hp.le
  · exact hn.le
  · exact (card_union_le _ _).trans (by rw [hp, hn])

/-! ### Pins over the state bits -/

/-- A peel: a row in a set, or two rows equal. -/
inductive BPeel
  | ev (r : Fin 4) (k : ℕ)
  | eq (r j : Fin 4)

/-- A block: none, one row, or two adjacent rows. -/
inductive BBlk
  | none
  | one (r : Fin 4) (k : ℕ)
  | two (r : Fin 3) (k k' : ℕ)

/-- A pin with its integer multiplier. -/
structure BPin where
  blk : BBlk
  peels : List BPeel
  lam : ℕ

/-- An equality bit from the pattern bits. -/
def eqbit (r j : Fin 4) (e13 e24 e14 : Bool) : Bool :=
  match r.val, j.val with
  | 0, 2 => e13 | 2, 0 => e13 | 1, 3 => e24 | 3, 1 => e24 | 0, 3 => e14 | 3, 0 => e14
  | 0, 0 => true | 1, 1 => true | 2, 2 => true | 3, 3 => true
  | _, _ => false

theorem eqbit_pbits {s : T4} (hs : Proper s) (r j : Fin 4) :
    eqbit r j (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))
      = decide (rowfun r s = rowfun j s) := by
  obtain ⟨p12, p23, p34⟩ := hs
  fin_cases r <;> fin_cases j <;> first | rfl | simp [eqbit, rowfun, p12, p23, p34, Ne.symm p12,
    Ne.symm p23, Ne.symm p34, eq_comm]

namespace BPeel

def row : BPeel → Fin 4 | ev r _ => r | eq r _ => r
def reads : BPeel → Fin 4 → Bool
  | ev r _, i => decide (r = i)
  | eq r j, i => decide (r = i) || decide (j = i)
def okb : BPeel → Bool | ev _ _ => true | eq r j => decide (j ≠ r)

/-- The event on codes and pattern bits. -/
def evc (c : ℕ × ℕ × ℕ × ℕ) (e13 e24 e14 : Bool) : BPeel → Bool
  | ev r k => evk k (crow c r)
  | eq r j => eqbit r j e13 e24 e14

def bnd (m2 m3 m4 : ℕ) : BPeel → ℚ
  | ev r k => min (qrow r * dsz m2 m3 m4 r k) 1
  | eq r _ => qrow r

/-- The factor for actual lists. -/
def fac (B₁ B₂ B₃ B₄ : Finset ℕ) (m2 m3 m4 : ℕ) : BPeel → Fac
  | ev r k => Fac.mem r (Dset B₁ B₂ B₃ B₄ r k) (dsz m2 m3 m4 r k)
  | eq r j => Fac.eqr r j

end BPeel

namespace BBlk

def reads : BBlk → Fin 4 → Bool
  | none, _ => false
  | one r _, i => decide (r = i)
  | two r _ _, i => decide (r.castSucc = i) || decide (r.succ = i)

def evc (c : ℕ × ℕ × ℕ × ℕ) : BBlk → Bool
  | none => true
  | one r k => evk k (crow c r)
  | two r k k' => evk k (crow c r.castSucc) && evk k' (crow c r.succ)

def bnd (m2 m3 m4 : ℕ) : BBlk → ℚ
  | none => 1
  | one r k => βQ (dsz m2 m3 m4 r k) 4 (ℓone r)
  | two r k k' => βQ (dsz m2 m3 m4 r.castSucc k * dsz m2 m3 m4 r.succ k') 12 (ℓtwo r)

def blk (B₁ B₂ B₃ B₄ : Finset ℕ) (m2 m3 m4 : ℕ) : BBlk → Blk
  | none => Blk.none
  | one r k => Blk.one r (Dset B₁ B₂ B₃ B₄ r k) (dsz m2 m3 m4 r k)
  | two r k k' => Blk.two r (Dset B₁ B₂ B₃ B₄ r.castSucc k) (Dset B₁ B₂ B₃ B₄ r.succ k')
      (dsz m2 m3 m4 r.castSucc k) (dsz m2 m3 m4 r.succ k')

end BBlk

/-- The peel order, as a boolean. -/
def bpeelOK (b : BBlk) : List BPeel → Bool
  | [] => true
  | p :: ps => !(b.reads p.row) && ps.all (fun g => !(g.reads p.row)) && p.okb && bpeelOK b ps

namespace BPin

def evc (q : BPin) (c : ℕ × ℕ × ℕ × ℕ) (e13 e24 e14 : Bool) : Bool :=
  q.peels.all (fun p => p.evc c e13 e24 e14) && q.blk.evc c

def bnd (q : BPin) (m2 m3 m4 : ℕ) : ℚ := (q.peels.map (BPeel.bnd m2 m3 m4)).prod * q.blk.bnd m2 m3 m4

end BPin

/-- A dual certificate over the state bits for one mismatch triple. -/
structure BitCert where
  pins : List BPin
  L0 : ℕ
  D : ℕ

/-- The multipliers of the pins that fire. -/
def fired (P : List BPin) (c : ℕ × ℕ × ℕ × ℕ) (e13 e24 e14 : Bool) : ℕ :=
  (P.map fun q => if q.evc c e13 e24 e14 then q.lam else 0).sum

/-- `Σ λ · bnd`. -/
def lamBnd (P : List BPin) (m2 m3 m4 : ℕ) : ℚ := (P.map fun q => (q.lam : ℚ) * q.bnd m2 m3 m4).sum

/-- The pattern constants, as numerators over `10⁷`. -/
def cpN (e13 e24 e14 : Bool) : ℤ :=
  if e13 && e24 then 9622143 else if e13 || e24 then 9634067 else if e14 then 9639939 else 9650610

theorem cpat5_eq (e13 e24 e14 : Bool) : cpat5 e13 e24 e14 = (cpN e13 e24 e14 : ℚ) / 10000000 := by
  cases e13 <;> cases e24 <;> cases e14 <;> norm_num [cpat5, cpN]

/-- The admissible code vectors of a mismatch triple. -/
def bvalid5 (m2 m3 m4 c1 c2 c3 c4 : ℕ) : Bool :=
  cM5 c1 == 0 && cX5 c4 == 0 &&
  (cM5 c2 == 0 || 0 < m2) && (cM5 c3 == 0 || 0 < m3) && (cM5 c4 == 0 || 0 < m4) &&
  (cX5 c1 == 0 || 0 < m2) && (cX5 c2 == 0 || 0 < m3) && (cX5 c3 == 0 || 0 < m4) &&
  decide (m2 ≤ 3 + cH5 c1 + cX5 c1 + cH5 c2 + cM5 c2) &&
  decide (m3 ≤ 3 + cH5 c2 + cX5 c2 + cH5 c3 + cM5 c3) &&
  decide (m4 ≤ 3 + cH5 c3 + cX5 c3 + cH5 c4 + cM5 c4)

/-- The check at one state. -/
def bitAt (m2 m3 m4 : ℕ) (C : BitCert) (c1 c2 c3 c4 : ℕ) (e13 e24 e14 : Bool) : Bool :=
  !(bvalid5 m2 m3 m4 c1 c2 c3 c4) || (e13 && e14) || (e24 && e14) ||
    decide (((C.D : ℤ) + C.L0 - fired C.pins (c1, c2, c3, c4) e13 e24 e14) * 10000000
        * nu5 e13 e24 e14
      ≤ (C.D : ℤ) * cpN e13 e24 e14 * Nst5 m2 m3 m4 c1 c2 c3 c4)

/-- `p i` for all `i ≤ 4`. -/
def all5 (p : ℕ → Bool) : Bool := p 0 && p 1 && p 2 && p 3 && p 4

theorem all5_spec {p : ℕ → Bool} (h : all5 p = true) {i : ℕ} (hi : i ≤ 4) : p i = true := by
  simp only [all5, Bool.and_eq_true] at h
  interval_cases i <;> tauto

def allB (p : Bool → Bool) : Bool := p false && p true

theorem allB_spec {p : Bool → Bool} (h : allB p = true) (b : Bool) : p b = true := by
  simp only [allB, Bool.and_eq_true] at h; cases b <;> tauto

/-- **The certificate check.** -/
def bitOK (m2 m3 m4 : ℕ) (C : BitCert) : Bool :=
  decide (0 < C.D) && C.pins.all (fun q => bpeelOK q.blk q.peels) &&
    decide (lamBnd C.pins m2 m3 m4 ≤ C.L0) &&
    all5 (fun c1 => all5 (fun c2 => all5 (fun c3 => all5 (fun c4 =>
      allB (fun e13 => allB (fun e24 => allB (fun e14 =>
        bitAt m2 m3 m4 C c1 c2 c3 c4 e13 e24 e14)))))))

/-! ### Soundness -/

section sound

variable {w : Wt} {X₁ X₂ X₃ X₄ B₁ B₂ B₃ B₄ : Finset ℕ} {m2 m3 m4 : ℕ}

theorem peel_reads (B₁ B₂ B₃ B₄ : Finset ℕ) (m2 m3 m4 : ℕ) (p : BPeel) :
    (p.fac B₁ B₂ B₃ B₄ m2 m3 m4).reads = p.reads ∧ (p.fac B₁ B₂ B₃ B₄ m2 m3 m4).row = p.row := by
  cases p <;> exact ⟨rfl, rfl⟩

theorem blk_reads (B₁ B₂ B₃ B₄ : Finset ℕ) (m2 m3 m4 : ℕ) (b : BBlk) :
    (b.blk B₁ B₂ B₃ B₄ m2 m3 m4).reads = b.reads := by
  cases b <;> rfl

theorem peelOK_of (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5) (hB₃ : B₃.card = 5)
    (hB₄ : B₄.card = 5) (c2 : (B₁ ∩ B₂).card + m2 = 5) (c3 : (B₂ ∩ B₃).card + m3 = 5)
    (c4 : (B₃ ∩ B₄).card + m4 = 5) (b : BBlk) :
    ∀ ps : List BPeel, bpeelOK b ps = true →
      PeelOK (b.blk B₁ B₂ B₃ B₄ m2 m3 m4).reads (ps.map (BPeel.fac B₁ B₂ B₃ B₄ m2 m3 m4))
  | [], _ => trivial
  | p :: ps, h => by
    simp only [bpeelOK, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.all_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨?_, ?_, ?_, peelOK_of hB₁ hB₂ hB₃ hB₄ c2 c3 c4 b ps h4⟩
    · rw [blk_reads, (peel_reads B₁ B₂ B₃ B₄ m2 m3 m4 p).2]; exact h1
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      rw [(peel_reads B₁ B₂ B₃ B₄ m2 m3 m4 g').1, (peel_reads B₁ B₂ B₃ B₄ m2 m3 m4 p).2]
      have := h2 g' hg'
      simpa using this
    · cases p with
      | ev r k => exact dset_card hB₁ hB₂ hB₃ hB₄ c2 c3 c4 r k
      | eq r j =>
        simp only [BPeel.okb, decide_eq_true_eq] at h3
        exact h3

theorem blk_ok (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5) (hB₃ : B₃.card = 5)
    (hB₄ : B₄.card = 5) (c2 : (B₁ ∩ B₂).card + m2 = 5) (c3 : (B₂ ∩ B₃).card + m3 = 5)
    (c4 : (B₃ ∩ B₄).card + m4 = 5) (b : BBlk) : (b.blk B₁ B₂ B₃ B₄ m2 m3 m4).ok := by
  cases b with
  | none => trivial
  | one r k => exact dset_card hB₁ hB₂ hB₃ hB₄ c2 c3 c4 r k
  | two r k k' =>
    exact ⟨dset_card hB₁ hB₂ hB₃ hB₄ c2 c3 c4 _ k, dset_card hB₁ hB₂ hB₃ hB₄ c2 c3 c4 _ k'⟩

/-- The event of a pin on the codes of a state is its event on the state. -/
theorem pin_evc (B₁ B₂ B₃ B₄ : Finset ℕ) (m2 m3 m4 : ℕ) (q : BPin) {s : T4} (hs : Proper s) :
    q.evc (codes5 B₁ B₂ B₃ B₄ s) (decide (r1 s = r3 s)) (decide (r2 s = r4 s))
        (decide (r1 s = r4 s))
      = (allEv (q.peels.map (BPeel.fac B₁ B₂ B₃ B₄ m2 m3 m4)) s
          && (q.blk.blk B₁ B₂ B₃ B₄ m2 m3 m4).ev s) := by
  unfold BPin.evc allEv
  congr 1
  · rw [List.all_map]
    congr 1
    funext p
    cases p with
    | ev r k => simp only [Function.comp, BPeel.evc, BPeel.fac, Fac.ev, evk_codes]
    | eq r j => simp only [Function.comp, BPeel.evc, BPeel.fac, Fac.ev, eqbit_pbits hs]
  · cases q.blk with
    | none => rfl
    | one r k => simp only [BBlk.evc, BBlk.blk, Blk.ev, evk_codes]
    | two r k k' => simp only [BBlk.evc, BBlk.blk, Blk.ev, evk_codes]

theorem pin_bnd_eq (B₁ B₂ B₃ B₄ : Finset ℕ) (m2 m3 m4 : ℕ) (q : BPin) :
    ((q.peels.map (BPeel.fac B₁ B₂ B₃ B₄ m2 m3 m4)).map Fac.bnd).prod
        * (q.blk.blk B₁ B₂ B₃ B₄ m2 m3 m4).bnd = q.bnd m2 m3 m4 := by
  unfold BPin.bnd
  congr 1
  · rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    cases p <;> rfl
  · cases q.blk <;> rfl

/-- The weight of the states on which the pins fire. -/
theorem sum_fired (hw : InBox 5 w) (h₁ : 4 ≤ X₁.card) (h₂ : 4 ≤ X₂.card) (h₃ : 4 ≤ X₃.card)
    (h₄ : 4 ≤ X₄.card) (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5) (hB₃ : B₃.card = 5)
    (hB₄ : B₄.card = 5) (c2 : (B₁ ∩ B₂).card + m2 = 5) (c3 : (B₂ ∩ B₃).card + m3 = 5)
    (c4 : (B₃ ∩ B₄).card + m4 = 5) :
    ∀ P : List BPin, P.all (fun q => bpeelOK q.blk q.peels) = true →
      ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 5 w s * (fired P (codes5 B₁ B₂ B₃ B₄ s) (decide (r1 s = r3 s))
          (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) : ℝ)
        ≤ ((lamBnd P m2 m3 m4 : ℚ) : ℝ) * ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 5 w s
  | [], _ => by simp [fired, lamBnd]
  | q :: P, hP => by
    simp only [List.all_cons, Bool.and_eq_true] at hP
    have ih := sum_fired hw h₁ h₂ h₃ h₄ hB₁ hB₂ hB₃ hB₄ c2 c3 c4 P hP.2
    have hq := pin_sum hw h₁ h₂ h₃ h₄ (q.blk.blk B₁ B₂ B₃ B₄ m2 m3 m4)
      (blk_ok hB₁ hB₂ hB₃ hB₄ c2 c3 c4 q.blk) (q.peels.map (BPeel.fac B₁ B₂ B₃ B₄ m2 m3 m4))
      (peelOK_of hB₁ hB₂ hB₃ hB₄ c2 c3 c4 q.blk q.peels hP.1)
    rw [pin_bnd_eq] at hq
    have e1 : ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 5 w s * (fired (q :: P) (codes5 B₁ B₂ B₃ B₄ s)
        (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) : ℝ)
        = (q.lam : ℝ) * ∑ s ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => (allEv (q.peels.map
            (BPeel.fac B₁ B₂ B₃ B₄ m2 m3 m4)) t && (q.blk.blk B₁ B₂ B₃ B₄ m2 m3 m4).ev t) = true),
            GU 5 w s
          + ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 5 w s * (fired P (codes5 B₁ B₂ B₃ B₄ s)
            (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) : ℝ) := by
      rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun s hs => ?_)
      rw [← pin_evc B₁ B₂ B₃ B₄ m2 m3 m4 q (proper_of_mem_sts hs)]
      simp only [fired, List.map_cons, List.sum_cons]
      split_ifs <;> push_cast <;> ring
    rw [e1]
    have hl : (0 : ℝ) ≤ q.lam := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hq hl
    simp only [lamBnd, List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast]
    simp only [lamBnd] at ih
    linarith

theorem bvalid_codes (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5) (hB₃ : B₃.card = 5)
    (hB₄ : B₄.card = 5) (c2 : (B₁ ∩ B₂).card + m2 = 5) (c3 : (B₂ ∩ B₃).card + m3 = 5)
    (c4 : (B₃ ∩ B₄).card + m4 = 5) {s : T4} (hs : Proper s) :
    bvalid5 m2 m3 m4 (codes5 B₁ B₂ B₃ B₄ s).1 (codes5 B₁ B₂ B₃ B₄ s).2.1
      (codes5 B₁ B₂ B₃ B₄ s).2.2.1 (codes5 B₁ B₂ B₃ B₄ s).2.2.2 = true := by
  obtain ⟨p12, p23, p34⟩ := hs
  have i2 := card_inter_code5 hB₁ hB₂ c2 B₁ B₃ p12
  have i3 := card_inter_code5 hB₂ hB₃ c3 B₁ B₄ p23
  have i4 := card_inter_code5 hB₃ hB₄ c4 B₂ B₄ p34
  have z1 : cM5 (rowCode5 B₁ B₁ B₂ (r1 s)) = 0 := by rw [cM5_code]; simp
  have z4 : cX5 (rowCode5 B₃ B₄ B₄ (r4 s)) = 0 := by rw [cX5_code]; simp
  have pm : ∀ {Bp Bi Bn : Finset ℕ} {x m : ℕ}, Bi.card = 5 → (Bp ∩ Bi).card + m = 5 →
      (cM5 (rowCode5 Bp Bi Bn x) == 0 || 0 < m) = true := by
    intro Bp Bi Bn x m hBi hm
    rw [cM5_code]
    split_ifs with h
    · have h1 := Finset.card_sdiff_add_card_inter Bi Bp
      rw [Finset.inter_comm] at h1
      have h2 : 0 < (Bi \ Bp).card := Finset.card_pos.mpr ⟨x, h⟩
      simp; omega
    · simp
  have px : ∀ {Bp Bi Bn : Finset ℕ} {x m : ℕ}, Bi.card = 5 → (Bi ∩ Bn).card + m = 5 →
      (cX5 (rowCode5 Bp Bi Bn x) == 0 || 0 < m) = true := by
    intro Bp Bi Bn x m hBi hm
    rw [cX5_code]
    split_ifs with h
    · have h1 := Finset.card_sdiff_add_card_inter Bi Bn
      have h2 : 0 < (Bi \ Bn).card := Finset.card_pos.mpr ⟨x, h⟩
      simp; omega
    · simp
  have t1 : (cM5 (rowCode5 B₁ B₁ B₂ (r1 s)) == 0) = true := by rw [z1]; rfl
  have t2 : (cX5 (rowCode5 B₃ B₄ B₄ (r4 s)) == 0) = true := by rw [z4]; rfl
  have t9 : decide (m2 ≤ 3 + cH5 (rowCode5 B₁ B₁ B₂ (r1 s)) + cX5 (rowCode5 B₁ B₁ B₂ (r1 s))
      + cH5 (rowCode5 B₁ B₂ B₃ (r2 s)) + cM5 (rowCode5 B₁ B₂ B₃ (r2 s))) = true :=
    decide_eq_true (by omega)
  have t10 : decide (m3 ≤ 3 + cH5 (rowCode5 B₁ B₂ B₃ (r2 s)) + cX5 (rowCode5 B₁ B₂ B₃ (r2 s))
      + cH5 (rowCode5 B₂ B₃ B₄ (r3 s)) + cM5 (rowCode5 B₂ B₃ B₄ (r3 s))) = true :=
    decide_eq_true (by omega)
  have t11 : decide (m4 ≤ 3 + cH5 (rowCode5 B₂ B₃ B₄ (r3 s)) + cX5 (rowCode5 B₂ B₃ B₄ (r3 s))
      + cH5 (rowCode5 B₃ B₄ B₄ (r4 s)) + cM5 (rowCode5 B₃ B₄ B₄ (r4 s))) = true :=
    decide_eq_true (by omega)
  show bvalid5 m2 m3 m4 (rowCode5 B₁ B₁ B₂ (r1 s)) (rowCode5 B₁ B₂ B₃ (r2 s))
    (rowCode5 B₂ B₃ B₄ (r3 s)) (rowCode5 B₃ B₄ B₄ (r4 s)) = true
  simp only [bvalid5, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨t1, t2⟩, pm hB₂ c2⟩, pm hB₃ c3⟩, pm hB₄ c4⟩, px hB₁ c2⟩, px hB₂ c3⟩,
    px hB₃ c4⟩, t9⟩, t10⟩, t11⟩

/-- **The seam inequality from a dual certificate over the state bits.** -/
theorem seam_of_bit5k (hw : InBox 5 w) (h₁ : 4 ≤ X₁.card) (h₂ : 4 ≤ X₂.card) (h₃ : 4 ≤ X₃.card)
    (h₄ : 4 ≤ X₄.card) (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5) (hB₃ : B₃.card = 5)
    (hB₄ : B₄.card = 5) (c2 : (B₁ ∩ B₂).card + m2 = 5) (c3 : (B₂ ∩ B₃).card + m3 = 5)
    (c4 : (B₃ ∩ B₄).card + m4 = 5) (C : BitCert) (hC : bitOK m2 m3 m4 C = true) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 5 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄, GB w B₁ B₂ B₃ B₄ s := by
  simp only [bitOK, Bool.and_eq_true, decide_eq_true_eq] at hC
  obtain ⟨⟨⟨hD, hP⟩, hL⟩, hall⟩ := hC
  set Ω := sts X₁ X₂ X₃ X₄ with hΩ
  have hDR : (0 : ℝ) < C.D := by exact_mod_cast hD
  -- the bound for one state
  have hstate : ∀ s ∈ Ω, GU 5 w s * (1 + (((C.L0 : ℤ) - fired C.pins (codes5 B₁ B₂ B₃ B₄ s)
      (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) : ℤ) : ℝ) / C.D)
      ≤ GB w B₁ B₂ B₃ B₄ s := by
    intro s hs
    have hp := proper_of_mem_sts hs
    have hb := state_bound5k hw hB₁ hB₂ hB₃ hB₄ c2 c3 c4 hp
    have hv := bvalid_codes hB₁ hB₂ hB₃ hB₄ c2 c3 c4 hp
    set c := codes5 B₁ B₂ B₃ B₄ s with hc
    set e13 := decide (r1 s = r3 s)
    set e24 := decide (r2 s = r4 s)
    set e14 := decide (r1 s = r4 s)
    have hat : bitAt m2 m3 m4 C c.1 c.2.1 c.2.2.1 c.2.2.2 e13 e24 e14 = true := by
      have l1 := all5_spec hall (i := c.1) (rowCode5_le B₁ B₁ B₂ (r1 s))
      have l2 := all5_spec l1 (i := c.2.1) (rowCode5_le B₁ B₂ B₃ (r2 s))
      have l3 := all5_spec l2 (i := c.2.2.1) (rowCode5_le B₂ B₃ B₄ (r3 s))
      have l4 := all5_spec l3 (i := c.2.2.2) (rowCode5_le B₃ B₄ B₄ (r4 s))
      exact allB_spec (allB_spec (allB_spec l4 e13) e24) e14
    have h13 : (e13 && e14) = false := by
      obtain ⟨-, -, p34⟩ := hp
      simp only [e13, e14, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      by_contra hcon; push_neg at hcon; exact p34 (hcon.1.symm.trans hcon.2)
    have h24 : (e24 && e14) = false := by
      obtain ⟨p12, -, -⟩ := hp
      simp only [e24, e14, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      by_contra hcon; push_neg at hcon; exact p12 (hcon.2.trans hcon.1.symm)
    have hc4 : (c.1, c.2.1, c.2.2.1, c.2.2.2) = c := rfl
    simp only [bitAt, hv, h13, h24, Bool.not_true, Bool.false_or, decide_eq_true_eq, hc4] at hat
    -- reals
    set F : ℤ := (fired C.pins c e13 e24 e14 : ℤ) with hF
    set N : ℤ := Nst5 m2 m3 m4 c.1 c.2.1 c.2.2.1 c.2.2.2 with hN
    have hatR : (((C.D : ℤ) + C.L0 - F) * 10000000 * nu5 e13 e24 e14 : ℝ)
        ≤ ((C.D : ℤ) * cpN e13 e24 e14 * N : ℝ) := by exact_mod_cast hat
    rw [cpat5_eq] at hb
    have hnu : (0 : ℝ) < nu5 e13 e24 e14 := by
      have : (0 : ℤ) < nu5 e13 e24 e14 := by unfold nu5; split_ifs <;> norm_num
      exact_mod_cast this
    have hU := GU_nonneg (by norm_num) hw s
    push_cast at hb hatR
    -- `GU · (D + L0 - F) · 10⁷ · nu ≤ GU · D · cpN · N ≤ D · 10⁷ · nu · GB`
    have k1 : GU 5 w s * ((((C.D : ℝ) + C.L0 - F)) * 10000000 * nu5 e13 e24 e14)
        ≤ GU 5 w s * ((C.D : ℝ) * cpN e13 e24 e14 * N) := mul_le_mul_of_nonneg_left hatR hU
    have k2 : (cpN e13 e24 e14 : ℝ) / 10000000 * N * GU 5 w s * (C.D * 10000000)
        ≤ nu5 e13 e24 e14 * GB w B₁ B₂ B₃ B₄ s * (C.D * 10000000) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    rw [show (1 : ℝ) + (((C.L0 : ℤ) - F : ℤ) : ℝ) / C.D = ((C.D : ℝ) + C.L0 - F) / C.D by
      push_cast; field_simp; ring]
    rw [mul_div_assoc', div_le_iff₀ hDR]
    have k3 : GU 5 w s * ((C.D : ℝ) + C.L0 - F) * C.D * 10000000 * nu5 e13 e24 e14
        ≤ GB w B₁ B₂ B₃ B₄ s * C.D * C.D * 10000000 * nu5 e13 e24 e14 := by
      nlinarith
    have hpos : (0 : ℝ) < C.D * 10000000 * nu5 e13 e24 e14 := by positivity
    nlinarith
  have hsum := Finset.sum_le_sum hstate
  -- averaging
  have hf := sum_fired hw h₁ h₂ h₃ h₄ hB₁ hB₂ hB₃ hB₄ c2 c3 c4 C.pins hP
  set W := ∑ s ∈ Ω, GU 5 w s with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun s _ => GU_nonneg (by norm_num) hw s
  have hLR : ((lamBnd C.pins m2 m3 m4 : ℚ) : ℝ) ≤ C.L0 := by exact_mod_cast hL
  have e : ∑ s ∈ Ω, GU 5 w s * (1 + (((C.L0 : ℤ) - fired C.pins (codes5 B₁ B₂ B₃ B₄ s)
      (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) : ℤ) : ℝ) / C.D)
      = W + ((C.L0 : ℝ) * W - ∑ s ∈ Ω, GU 5 w s * (fired C.pins (codes5 B₁ B₂ B₃ B₄ s)
          (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) : ℝ)) / C.D := by
    rw [hW, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    push_cast; ring
  rw [e] at hsum
  have : 0 ≤ ((C.L0 : ℝ) * W - ∑ s ∈ Ω, GU 5 w s * (fired C.pins (codes5 B₁ B₂ B₃ B₄ s)
      (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) : ℝ)) / C.D := by
    apply div_nonneg _ hDR.le
    nlinarith
  linarith

end sound

end GridGen.Four
