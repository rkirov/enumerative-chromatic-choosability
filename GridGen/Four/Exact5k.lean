/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.BitLP5k
import GridGen.Four.Exact6

/-!
# Height four, `k = 5`: the exact-certificate checker

The `k = 5` version of `GridGen/Four/Exact6.lean`, with the pins of
`ai_research_notes/H4_K5_REVIEW_2026-10-24.md` §5: a row in an atom (the conditional fibre, or
the marginal block of that row), an equality of two rows, and two adjacent rows in a pair of
atoms (the marginal block of the pair) times atoms of the other rows (the conditional fibre), all
peeled in a valid order (`pin_sum`).

A certificate `Spec5k` gives the atom sizes of the lists `B₁, …, B₄`, the Venn sizes, the pins
with integer multipliers, a constant `L0` and a denominator `D`. For a column type `t` (the atom
of each row and the pattern bits) let `Y = L0 - Σ_{pins that fire} λ`. The kernel check `allOk5k`
verifies `D · GB ≥ (D + Y) · GU` on the whole box for every column type passing the capacity
test, and `specOk5k` verifies `Σ λ · bnd ≤ L0` and the Venn sizes. Then `GB ≥ GU (1 + Y/D)` for
every state and `Σ GU · Y ≥ 0` (`exact_seam5k`). The constants: `ρ = 118/125` (`rho_five`) and
the uniform class counts at `ℓ = 3` (`urow5`).
-/

namespace GridGen.Four

open Finset GridGen.Lookback

/-! ### Pins over atoms -/

/-- A peel: a row in an atom, or two rows equal. -/
inductive APeel
  | ev (r : Fin 4) (a : Mem)
  | eq (r j : Fin 4)

/-- A block: none, one row in an atom, or two adjacent rows in atoms. -/
inductive ABlk
  | none
  | one (r : Fin 4) (a : Mem)
  | two (r : Fin 3) (a a' : Mem)

/-- A pin with its integer multiplier. -/
structure APin where
  blk : ABlk
  peels : List APeel
  lam : ℕ

/-- An exact certificate at `k = 5`. -/
structure Spec5k where
  atoms : List (Mem × ℕ)
  venn : Venn
  pins : List APin
  L0 : ℕ
  D : ℕ

namespace APeel

def row : APeel → Fin 4 | ev r _ => r | eq r _ => r
def reads : APeel → Fin 4 → Bool
  | ev r _, i => decide (r = i)
  | eq r j, i => decide (r = i) || decide (j = i)
def okb : APeel → Bool
  | ev _ a => decide (a ≠ mem0)
  | eq r j => decide (j ≠ r)

/-- The event on a column type. -/
def evt (r1 r2 r3 r4 : Mem) (e13 e24 e14 : Bool) : APeel → Bool
  | ev r a => decide (rowsel r1 r2 r3 r4 r = a)
  | eq r j => eqbit r j e13 e24 e14

def bnd (L : List (Mem × ℕ)) : APeel → ℚ
  | ev r a => min (qrow r * asz L a) 1
  | eq r _ => qrow r

def fac (B₁ B₂ B₃ B₄ : Finset ℕ) (L : List (Mem × ℕ)) : APeel → Fac
  | ev r a => Fac.mem r (atomSet B₁ B₂ B₃ B₄ a) (asz L a)
  | eq r j => Fac.eqr r j

end APeel

namespace ABlk

def reads : ABlk → Fin 4 → Bool
  | none, _ => false
  | one r _, i => decide (r = i)
  | two r _ _, i => decide (r.castSucc = i) || decide (r.succ = i)

def okb : ABlk → Bool
  | none => true
  | one _ a => decide (a ≠ mem0)
  | two _ a a' => decide (a ≠ mem0) && decide (a' ≠ mem0)

def evt (r1 r2 r3 r4 : Mem) : ABlk → Bool
  | none => true
  | one r a => decide (rowsel r1 r2 r3 r4 r = a)
  | two r a a' =>
    decide (rowsel r1 r2 r3 r4 r.castSucc = a) && decide (rowsel r1 r2 r3 r4 r.succ = a')

def bnd (L : List (Mem × ℕ)) : ABlk → ℚ
  | none => 1
  | one r a => βQ (asz L a) 4 (ℓone r)
  | two r a a' => βQ (asz L a * asz L a') 12 (ℓtwo r)

def blk (B₁ B₂ B₃ B₄ : Finset ℕ) (L : List (Mem × ℕ)) : ABlk → Blk
  | none => Blk.none
  | one r a => Blk.one r (atomSet B₁ B₂ B₃ B₄ a) (asz L a)
  | two r a a' => Blk.two r (atomSet B₁ B₂ B₃ B₄ a) (atomSet B₁ B₂ B₃ B₄ a') (asz L a) (asz L a')

end ABlk

/-- The peel order, as a boolean. -/
def apeelOK (b : ABlk) : List APeel → Bool
  | [] => true
  | p :: ps => !(b.reads p.row) && ps.all (fun g => !(g.reads p.row)) && p.okb && apeelOK b ps

namespace APin

def evt (q : APin) (r1 r2 r3 r4 : Mem) (e13 e24 e14 : Bool) : Bool :=
  q.peels.all (fun p => p.evt r1 r2 r3 r4 e13 e24 e14) && q.blk.evt r1 r2 r3 r4

def bnd (q : APin) (L : List (Mem × ℕ)) : ℚ := (q.peels.map (APeel.bnd L)).prod * q.blk.bnd L

end APin

/-- The multipliers of the pins that fire on a column type. -/
def afired (P : List APin) (r1 r2 r3 r4 : Mem) (e13 e24 e14 : Bool) : ℕ :=
  (P.map fun q => if q.evt r1 r2 r3 r4 e13 e24 e14 then q.lam else 0).sum

def alamBnd (P : List APin) (L : List (Mem × ℕ)) : ℚ := (P.map fun q => (q.lam : ℚ) * q.bnd L).sum

/-! ### The checks -/

/-- The check for one column type: `D · GB ≥ (D + Y) · GU` on the box, `ρ = 118/125`. -/
def okc5k (sp : Spec5k) (r1 r2 r3 r4 : Mem) (e13 e24 e14 : Bool) : Bool :=
  let cA := cls (dat sp.venn r1 r2 r3 r4 e13 e24 e14)
  let cU := urow5 e13 e24 e14
  let Y : ℤ := (sp.L0 : ℤ) - afired sp.pins r1 r2 r3 r4 e13 e24 e14
  let d0 := (sp.D : ℤ) * cA.1 - ((sp.D : ℤ) + Y) * cU.1
  let d1 := (sp.D : ℤ) * cA.2.1 - ((sp.D : ℤ) + Y) * cU.2.1
  let d2 := (sp.D : ℤ) * cA.2.2.1 - ((sp.D : ℤ) + Y) * cU.2.2.1
  let d3 := (sp.D : ℤ) * cA.2.2.2 - ((sp.D : ℤ) + Y) * cU.2.2.2
  decide (0 ≤ 125 * d0 + min (118 * d1) (125 * d1) + min (118 * d2) (125 * d2)
    + min (118 * d3) (125 * d3))

/-- The atoms a row can lie in, with their sizes; the empty atom gets the vacuous size `4`. -/
def ats5 (sp : Spec5k) : List (Mem × ℕ) := sp.atoms ++ [(mem0, 4)]

/-- The check for all column types with row 1 in the atom `p1`. -/
def rowOk5k (sp : Spec5k) (p1 : Mem × ℕ) : Bool :=
  (ats5 sp).all fun p2 => (ats5 sp).all fun p3 => (ats5 sp).all fun p4 =>
    [false, true].all fun e13 => [false, true].all fun e24 => [false, true].all fun e14 =>
      !valid p1.1 p2.1 p3.1 p4.1 e13 e24 e14
        || !capOk p1.2 p2.2 p3.2 p4.2 p1.1 p2.1 p3.1 p4.1 e13 e24 e14
        || okc5k sp p1.1 p2.1 p3.1 p4.1 e13 e24 e14

/-- **The certificate check** over all column types. -/
def allOk5k (sp : Spec5k) : Bool := (ats5 sp).all (rowOk5k sp)

theorem allOk5k_of (sp : Spec5k) (h : ∀ p ∈ ats5 sp, rowOk5k sp p = true) : allOk5k sp = true :=
  List.all_eq_true.mpr h

/-- The scalar conditions. -/
def specOk5k (sp : Spec5k) : Bool :=
  decide (0 < sp.D) && sp.pins.all (fun q => q.blk.okb && apeelOK q.blk q.peels)
    && decide (alamBnd sp.pins sp.atoms ≤ sp.L0) && vennEqB sp.venn (vennFn (asz sp.atoms))

/-! ### Soundness -/

/-- The facts a certificate needs about the lists: their atom sizes. -/
def AtomsMatch5 (sp : Spec5k) (B₁ B₂ B₃ B₄ : Finset ℕ) : Prop :=
  ∀ m : Mem, m ≠ mem0 → (atomSet B₁ B₂ B₃ B₄ m).card = asz sp.atoms m

section sound

variable {w : Wt} {X₁ X₂ X₃ X₄ B₁ B₂ B₃ B₄ : Finset ℕ}

/-- Every row lies in a listed atom whose size bounds the column's colours there. -/
theorem row_entry5 (sp : Spec5k) (hA : AtomsMatch5 sp B₁ B₂ B₃ B₄) {s : T4} (hs : Proper s)
    (c : ℕ) :
    ∃ p ∈ ats5 sp, p.1 = memv B₁ B₂ B₃ B₄ c ∧
      ndist (memv B₁ B₂ B₃ B₄ c) (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s))
        (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s)) (decide (r1 s = r3 s))
        (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) ≤ p.2 := by
  by_cases h0 : memv B₁ B₂ B₃ B₄ c = mem0
  · refine ⟨(mem0, 4), List.mem_append_right _ (List.mem_singleton.mpr rfl), h0.symm, ?_⟩
    exact ndist_le_four _ _ _ _ _ _ _ _
  · have hc : c ∈ atomSet B₁ B₂ B₃ B₄ (memv B₁ B₂ B₃ B₄ c) := (mem_atomSet h0 c).mp rfl
    have hpos : asz sp.atoms (memv B₁ B₂ B₃ B₄ c) ≠ 0 := by
      rw [← hA _ h0]; exact (Finset.card_pos.mpr ⟨c, hc⟩).ne'
    refine ⟨(memv B₁ B₂ B₃ B₄ c, asz sp.atoms (memv B₁ B₂ B₃ B₄ c)),
      List.mem_append_left _ (asz_mem _ _ hpos), rfl, ?_⟩
    rw [← hA _ h0]
    exact ndist_le_card B₁ B₂ B₃ B₄ hs h0

theorem okc5k_of (sp : Spec5k) (hok : allOk5k sp = true) (hA : AtomsMatch5 sp B₁ B₂ B₃ B₄)
    {s : T4} (hs : Proper s) :
    okc5k sp (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s)) (memv B₁ B₂ B₃ B₄ (r3 s))
      (memv B₁ B₂ B₃ B₄ (r4 s)) (decide (r1 s = r3 s)) (decide (r2 s = r4 s))
      (decide (r1 s = r4 s)) = true := by
  obtain ⟨p1, h1, e1, c1⟩ := row_entry5 sp hA hs (r1 s)
  obtain ⟨p2, h2, e2, c2⟩ := row_entry5 sp hA hs (r2 s)
  obtain ⟨p3, h3, e3, c3⟩ := row_entry5 sp hA hs (r3 s)
  obtain ⟨p4, h4, e4, c4⟩ := row_entry5 sp hA hs (r4 s)
  have hb : ∀ b : Bool, b ∈ [false, true] := by intro b; cases b <;> simp
  unfold allOk5k at hok
  have hrow := List.all_eq_true.mp hok p1 h1
  unfold rowOk5k at hrow
  simp only [List.all_eq_true] at hrow
  have := hrow p2 h2 p3 h3 p4 h4 (decide (r1 s = r3 s)) (hb _) (decide (r2 s = r4 s)) (hb _)
    (decide (r1 s = r4 s)) (hb _)
  rw [e1, e2, e3, e4, valid_of B₁ B₂ B₃ B₄ hs] at this
  have hcap : capOk p1.2 p2.2 p3.2 p4.2 (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s))
      (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s)) (decide (r1 s = r3 s))
      (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) = true := by
    simp only [capOk, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩
  rw [hcap] at this
  simpa using this

theorem lin_min5 {d x : ℝ} (hx0 : 118 / 125 ≤ x) (hx1 : x ≤ 1) :
    min (118 * d) (125 * d) / 125 ≤ d * x := by
  rcases le_total 0 d with hd | hd
  · rw [min_eq_left (by linarith)]; nlinarith
  · rw [min_eq_right (by linarith)]; nlinarith

/-- **The bound for one state from an exact certificate**, `k = 5`. -/
theorem exact_state5k (sp : Spec5k) (hok : allOk5k sp = true) (hsp : specOk5k sp = true)
    (hA : AtomsMatch5 sp B₁ B₂ B₃ B₄) (hw : InBox 5 w) {s : T4} (hs : Proper s) :
    GU 5 w s * (1 + (((sp.L0 : ℤ) - afired sp.pins (memv B₁ B₂ B₃ B₄ (r1 s))
        (memv B₁ B₂ B₃ B₄ (r2 s)) (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s))
        (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) : ℤ) : ℝ) / sp.D)
      ≤ GB w B₁ B₂ B₃ B₄ s := by
  have hc := okc5k_of sp hok hA hs
  simp only [specOk5k, Bool.and_eq_true, decide_eq_true_eq] at hsp
  obtain ⟨⟨⟨hD, -⟩, -⟩, hvenn⟩ := hsp
  have hv : sp.venn = vennOf B₁ B₂ B₃ B₄ := by
    rw [eq_of_vennEqB hvenn, vennOf_eq]
    exact vennFn_congr (fun m hm => (hA m hm).symm)
  set Y : ℤ := (sp.L0 : ℤ) - afired sp.pins (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s))
    (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s)) (decide (r1 s = r3 s))
    (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) with hY
  set cA := cls (dat sp.venn (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s))
    (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s)) (decide (r1 s = r3 s))
    (decide (r2 s = r4 s)) (decide (r1 s = r4 s))) with hcA
  set cU := urow5 (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) with hcU
  have hint : 0 ≤ 125 * ((sp.D : ℤ) * cA.1 - ((sp.D : ℤ) + Y) * cU.1)
      + min (118 * ((sp.D : ℤ) * cA.2.1 - ((sp.D : ℤ) + Y) * cU.2.1))
          (125 * ((sp.D : ℤ) * cA.2.1 - ((sp.D : ℤ) + Y) * cU.2.1))
      + min (118 * ((sp.D : ℤ) * cA.2.2.1 - ((sp.D : ℤ) + Y) * cU.2.2.1))
          (125 * ((sp.D : ℤ) * cA.2.2.1 - ((sp.D : ℤ) + Y) * cU.2.2.1))
      + min (118 * ((sp.D : ℤ) * cA.2.2.2 - ((sp.D : ℤ) + Y) * cU.2.2.2))
          (125 * ((sp.D : ℤ) * cA.2.2.2 - ((sp.D : ℤ) + Y) * cU.2.2.2)) := by
    simpa [okc5k] using hc
  have hGB : GB w B₁ B₂ B₃ B₄ s = (cA.1 : ℝ) + (cA.2.1 : ℝ) * w.a + (cA.2.2.1 : ℝ) * w.b
      + (cA.2.2.2 : ℝ) * w.c := by
    rw [GB_cls, dat_eq B₁ B₂ B₃ B₄ hs, ← hv]
  have hGU : GU 5 w s = (cU.1 : ℝ) + (cU.2.1 : ℝ) * w.a + (cU.2.2.1 : ℝ) * w.b
      + (cU.2.2.2 : ℝ) * w.c := GU_urow5 w hs
  obtain ⟨ha0, ha1, hb0, hb1, hc0, hc1⟩ := hw
  rw [rho_five] at ha0 hb0 hc0
  have hint' : (0 : ℝ) ≤ 125 * ((((sp.D : ℤ) * cA.1 - ((sp.D : ℤ) + Y) * cU.1 : ℤ)) : ℝ)
      + min (118 * ((((sp.D : ℤ) * cA.2.1 - ((sp.D : ℤ) + Y) * cU.2.1 : ℤ)) : ℝ))
          (125 * ((((sp.D : ℤ) * cA.2.1 - ((sp.D : ℤ) + Y) * cU.2.1 : ℤ)) : ℝ))
      + min (118 * ((((sp.D : ℤ) * cA.2.2.1 - ((sp.D : ℤ) + Y) * cU.2.2.1 : ℤ)) : ℝ))
          (125 * ((((sp.D : ℤ) * cA.2.2.1 - ((sp.D : ℤ) + Y) * cU.2.2.1 : ℤ)) : ℝ))
      + min (118 * ((((sp.D : ℤ) * cA.2.2.2 - ((sp.D : ℤ) + Y) * cU.2.2.2 : ℤ)) : ℝ))
          (125 * ((((sp.D : ℤ) * cA.2.2.2 - ((sp.D : ℤ) + Y) * cU.2.2.2 : ℤ)) : ℝ)) := by
    have := (Int.cast_le (R := ℝ)).mpr hint
    push_cast at this ⊢
    simpa [Int.cast_min] using this
  have m1 := lin_min5 (d := ((((sp.D : ℤ) * cA.2.1 - ((sp.D : ℤ) + Y) * cU.2.1 : ℤ)) : ℝ)) ha0 ha1
  have m2 := lin_min5 (d := ((((sp.D : ℤ) * cA.2.2.1 - ((sp.D : ℤ) + Y) * cU.2.2.1 : ℤ)) : ℝ))
    hb0 hb1
  have m3 := lin_min5 (d := ((((sp.D : ℤ) * cA.2.2.2 - ((sp.D : ℤ) + Y) * cU.2.2.2 : ℤ)) : ℝ))
    hc0 hc1
  have key : ((sp.D : ℝ) + Y) * GU 5 w s ≤ (sp.D : ℝ) * GB w B₁ B₂ B₃ B₄ s := by
    rw [hGB, hGU]
    push_cast at m1 m2 m3 hint' ⊢
    nlinarith
  have hDpos : (0 : ℝ) < sp.D := by exact_mod_cast hD
  rw [show (1 : ℝ) + (Y : ℝ) / sp.D = ((sp.D : ℝ) + Y) / sp.D by field_simp, mul_div_assoc',
    div_le_iff₀ hDpos]
  linarith

theorem apeel_reads (B₁ B₂ B₃ B₄ : Finset ℕ) (L : List (Mem × ℕ)) (p : APeel) :
    (p.fac B₁ B₂ B₃ B₄ L).reads = p.reads ∧ (p.fac B₁ B₂ B₃ B₄ L).row = p.row := by
  cases p <;> exact ⟨rfl, rfl⟩

theorem ablk_reads (B₁ B₂ B₃ B₄ : Finset ℕ) (L : List (Mem × ℕ)) (b : ABlk) :
    (b.blk B₁ B₂ B₃ B₄ L).reads = b.reads := by
  cases b <;> rfl

theorem atom_card_le (sp : Spec5k) (hA : AtomsMatch5 sp B₁ B₂ B₃ B₄) {a : Mem} (ha : a ≠ mem0) :
    (atomSet B₁ B₂ B₃ B₄ a).card ≤ asz sp.atoms a := (hA a ha).le

theorem apeelOK_of (sp : Spec5k) (hA : AtomsMatch5 sp B₁ B₂ B₃ B₄) (b : ABlk) :
    ∀ ps : List APeel, apeelOK b ps = true →
      PeelOK (b.blk B₁ B₂ B₃ B₄ sp.atoms).reads (ps.map (APeel.fac B₁ B₂ B₃ B₄ sp.atoms))
  | [], _ => trivial
  | p :: ps, h => by
    simp only [apeelOK, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.all_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨?_, ?_, ?_, apeelOK_of sp hA b ps h4⟩
    · rw [ablk_reads, (apeel_reads B₁ B₂ B₃ B₄ sp.atoms p).2]; exact h1
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      rw [(apeel_reads B₁ B₂ B₃ B₄ sp.atoms g').1, (apeel_reads B₁ B₂ B₃ B₄ sp.atoms p).2]
      have := h2 g' hg'
      simpa using this
    · cases p with
      | ev r a =>
        simp only [APeel.okb, decide_eq_true_eq] at h3
        exact atom_card_le sp hA h3
      | eq r j =>
        simp only [APeel.okb, decide_eq_true_eq] at h3
        exact h3

theorem ablk_ok (sp : Spec5k) (hA : AtomsMatch5 sp B₁ B₂ B₃ B₄) (b : ABlk) (hb : b.okb = true) :
    (b.blk B₁ B₂ B₃ B₄ sp.atoms).ok := by
  cases b with
  | none => trivial
  | one r a =>
    simp only [ABlk.okb, decide_eq_true_eq] at hb
    exact atom_card_le sp hA hb
  | two r a a' =>
    simp only [ABlk.okb, Bool.and_eq_true, decide_eq_true_eq] at hb
    exact ⟨atom_card_le sp hA hb.1, atom_card_le sp hA hb.2⟩

theorem memv_eq_atom {a : Mem} (ha : a ≠ mem0) (r : Fin 4) (s : T4) :
    decide (rowsel (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s)) (memv B₁ B₂ B₃ B₄ (r3 s))
      (memv B₁ B₂ B₃ B₄ (r4 s)) r = a) = decide (rowfun r s ∈ atomSet B₁ B₂ B₃ B₄ a) := by
  rw [rowsel_memv]
  exact decide_eq_decide.mpr (mem_atomSet ha _)

theorem all_congr_mem {α : Type*} (l : List α) (f g : α → Bool) (h : ∀ a ∈ l, f a = g a) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- The event of a pin on the type of a state is its event on the state. -/
theorem apin_evt (sp : Spec5k) (q : APin) (hq : (q.blk.okb && apeelOK q.blk q.peels) = true)
    {s : T4} (hs : Proper s) :
    q.evt (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s)) (memv B₁ B₂ B₃ B₄ (r3 s))
        (memv B₁ B₂ B₃ B₄ (r4 s)) (decide (r1 s = r3 s)) (decide (r2 s = r4 s))
        (decide (r1 s = r4 s))
      = (allEv (q.peels.map (APeel.fac B₁ B₂ B₃ B₄ sp.atoms)) s
          && (q.blk.blk B₁ B₂ B₃ B₄ sp.atoms).ev s) := by
  simp only [Bool.and_eq_true] at hq
  obtain ⟨hb, hp⟩ := hq
  have hpe : ∀ p ∈ q.peels, p.okb = true := by
    clear hb
    generalize q.peels = ps at hp
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [apeelOK, Bool.and_eq_true] at hp
      intro p' hp'
      rcases List.mem_cons.mp hp' with rfl | hp'
      · exact hp.1.2
      · exact ih hp.2 p' hp'
  unfold APin.evt allEv
  congr 1
  · rw [List.all_map]
    refine all_congr_mem _ _ _ (fun p hp' => ?_)
    cases p with
    | ev r a =>
      have ha := hpe _ hp'
      simp only [APeel.okb, decide_eq_true_eq] at ha
      simp only [Function.comp, APeel.evt, APeel.fac, Fac.ev, memv_eq_atom ha]
    | eq r j => simp only [Function.comp, APeel.evt, APeel.fac, Fac.ev, eqbit_pbits hs]
  · cases hq' : q.blk with
    | none => rfl
    | one r a =>
      rw [hq'] at hb
      simp only [ABlk.okb, decide_eq_true_eq] at hb
      simp only [ABlk.evt, ABlk.blk, Blk.ev, memv_eq_atom hb]
    | two r a a' =>
      rw [hq'] at hb
      simp only [ABlk.okb, Bool.and_eq_true, decide_eq_true_eq] at hb
      simp only [ABlk.evt, ABlk.blk, Blk.ev, memv_eq_atom hb.1, memv_eq_atom hb.2]

theorem apin_bnd_eq (B₁ B₂ B₃ B₄ : Finset ℕ) (L : List (Mem × ℕ)) (q : APin) :
    ((q.peels.map (APeel.fac B₁ B₂ B₃ B₄ L)).map Fac.bnd).prod * (q.blk.blk B₁ B₂ B₃ B₄ L).bnd
      = q.bnd L := by
  unfold APin.bnd
  congr 1
  · rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    cases p <;> rfl
  · cases q.blk <;> rfl

theorem sum_afired (sp : Spec5k) (hA : AtomsMatch5 sp B₁ B₂ B₃ B₄) (hw : InBox 5 w)
    (h₁ : 4 ≤ X₁.card) (h₂ : 4 ≤ X₂.card) (h₃ : 4 ≤ X₃.card) (h₄ : 4 ≤ X₄.card) :
    ∀ P : List APin, P.all (fun q => q.blk.okb && apeelOK q.blk q.peels) = true →
      ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 5 w s * (afired P (memv B₁ B₂ B₃ B₄ (r1 s))
          (memv B₁ B₂ B₃ B₄ (r2 s)) (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s))
          (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) : ℝ)
        ≤ ((alamBnd P sp.atoms : ℚ) : ℝ) * ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 5 w s
  | [], _ => by simp [afired, alamBnd]
  | q :: P, hP => by
    simp only [List.all_cons, Bool.and_eq_true] at hP
    obtain ⟨⟨hq1, hq2⟩, hP⟩ := hP
    have ih := sum_afired sp hA hw h₁ h₂ h₃ h₄ P hP
    have hq := pin_sum hw h₁ h₂ h₃ h₄ (q.blk.blk B₁ B₂ B₃ B₄ sp.atoms)
      (ablk_ok sp hA q.blk hq1) (q.peels.map (APeel.fac B₁ B₂ B₃ B₄ sp.atoms))
      (apeelOK_of sp hA q.blk q.peels hq2)
    rw [apin_bnd_eq] at hq
    have e1 : ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 5 w s * (afired (q :: P) (memv B₁ B₂ B₃ B₄ (r1 s))
        (memv B₁ B₂ B₃ B₄ (r2 s)) (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s))
        (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) : ℝ)
        = (q.lam : ℝ) * ∑ s ∈ (sts X₁ X₂ X₃ X₄).filter (fun t => (allEv (q.peels.map
            (APeel.fac B₁ B₂ B₃ B₄ sp.atoms)) t && (q.blk.blk B₁ B₂ B₃ B₄ sp.atoms).ev t) = true),
            GU 5 w s
          + ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 5 w s * (afired P (memv B₁ B₂ B₃ B₄ (r1 s))
            (memv B₁ B₂ B₃ B₄ (r2 s)) (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s))
            (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) : ℝ) := by
      rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun s hs => ?_)
      have hq' : (q.blk.okb && apeelOK q.blk q.peels) = true := by
        simp only [Bool.and_eq_true]; exact ⟨hq1, hq2⟩
      rw [← apin_evt sp q hq' (proper_of_mem_sts hs)]
      simp only [afired, List.map_cons, List.sum_cons]
      split_ifs <;> push_cast <;> ring
    rw [e1]
    have hl : (0 : ℝ) ≤ q.lam := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hq hl
    simp only [alamBnd, List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast]
    simp only [alamBnd] at ih
    linarith

/-- **The seam inequality at `k = 5` from an exact certificate** for lists with the certificate's
atom sizes. -/
theorem exact_seam5k (sp : Spec5k) (hok : allOk5k sp = true) (hsp : specOk5k sp = true)
    (hA : AtomsMatch5 sp B₁ B₂ B₃ B₄) (hw : InBox 5 w) (h₁ : 4 ≤ X₁.card) (h₂ : 4 ≤ X₂.card)
    (h₃ : 4 ≤ X₃.card) (h₄ : 4 ≤ X₄.card) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 5 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄, GB w B₁ B₂ B₃ B₄ s := by
  have hsp' := hsp
  simp only [specOk5k, Bool.and_eq_true, decide_eq_true_eq] at hsp'
  obtain ⟨⟨⟨hD, hP⟩, hL⟩, -⟩ := hsp'
  set Ω := sts X₁ X₂ X₃ X₄ with hΩ
  have hDR : (0 : ℝ) < sp.D := by exact_mod_cast hD
  have hsum := Finset.sum_le_sum (s := Ω) (fun s hs =>
    exact_state5k sp hok hsp hA hw (proper_of_mem_sts (A := X₁) (B := X₂) (C := X₃) (D := X₄) hs))
  have hf := sum_afired sp hA hw h₁ h₂ h₃ h₄ sp.pins hP
  set W := ∑ s ∈ Ω, GU 5 w s with hW
  have hLR : ((alamBnd sp.pins sp.atoms : ℚ) : ℝ) ≤ sp.L0 := by exact_mod_cast hL
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun s _ => GU_nonneg (by norm_num) hw s
  have e : ∑ s ∈ Ω, GU 5 w s * (1 + (((sp.L0 : ℤ) - afired sp.pins (memv B₁ B₂ B₃ B₄ (r1 s))
      (memv B₁ B₂ B₃ B₄ (r2 s)) (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s))
      (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) : ℤ) : ℝ) / sp.D)
      = W + ((sp.L0 : ℝ) * W - ∑ s ∈ Ω, GU 5 w s * (afired sp.pins (memv B₁ B₂ B₃ B₄ (r1 s))
          (memv B₁ B₂ B₃ B₄ (r2 s)) (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s))
          (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) : ℝ)) / sp.D := by
    rw [hW, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    push_cast; ring
  rw [e] at hsum
  have : 0 ≤ ((sp.L0 : ℝ) * W - ∑ s ∈ Ω, GU 5 w s * (afired sp.pins (memv B₁ B₂ B₃ B₄ (r1 s))
      (memv B₁ B₂ B₃ B₄ (r2 s)) (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s))
      (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) : ℝ)) / sp.D := by
    apply div_nonneg _ hDR.le
    nlinarith
  linarith

end sound

end GridGen.Four
