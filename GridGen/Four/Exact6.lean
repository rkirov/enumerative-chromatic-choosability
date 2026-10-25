/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Exact

/-!
# Height four, `k = 6`: the exact-certificate checker

The `k = 6` version of `GridGen/Four/Exact.lean`. A certificate `Spec6` describes the lists
`B₁, …, B₄` by their *atom sizes*: for every nonzero membership vector `m`, the number
`asz sp.atoms m` of colours lying in exactly the lists marked by `m`. The Venn sizes follow
(`vennOf_eq`), so a certificate applies to every system of lists with the same atom sizes
(`exact_seam6`).

New at `k = 6`: a bit-consistent column type can put more distinct colours of the state into an
atom than the atom holds (two colours in an atom of size one), and then its "class counts" are
meaningless and may fail the check. Such types are not realised by any state: the check `allOk6`
skips the types failing the capacity test `capOk`, and `ndist_le_card` proves that actual states
pass it.

The constants: `ρ = 487/500` (`rho_six`), the fibre ratio `q = 1/(3ρ) = 500/1461`, and the
uniform class counts with `ℓ = 4` (`urow6`).
-/

namespace GridGen.Four

open Finset GridGen.Lookback

/-! ### The uniform side at `k = 6` -/

/-- The uniform class coefficients at `k = 6` (`ℓ = 4`), by pattern. -/
def urow6 (e13 e24 e14 : Bool) : ℤ × ℤ × ℤ × ℤ :=
  if e13 && e24 then (21, 136, 52, 168)
  else if e13 || e24 then (17, 127, 55, 174)
  else if e14 then (13, 110, 71, 174)
  else (14, 116, 58, 181)

/-- **The uniform side at `k = 6`, by pattern.** -/
theorem GU_urow6 (w : Wt) {s : T4} (hs : Proper s) :
    GU 6 w s = ((urow6 (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))).1 : ℝ)
      + ((urow6 (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))).2.1 : ℝ)
          * w.a
      + ((urow6 (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))).2.2.1 : ℝ)
          * w.b
      + ((urow6 (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))).2.2.2 : ℝ)
          * w.c := by
  have hs' := hs
  obtain ⟨p12, p23, p34⟩ := hs'
  rcases canon_cases hs with h | h | h | h | h
  · rw [GU_eq_of_canon w h (by decide), GU_0101 (by norm_num) w]
    have b : r3 s = r1 s ∧ r4 s = r2 s := by
      unfold canon at h; simp only [Prod.mk.injEq] at h; split_ifs at h <;> simp_all
    simp [urow6, b.1.symm, b.2.symm, vA, aff]; norm_num
  · rw [GU_eq_of_canon w h (by decide), GU_0102 (by norm_num) w]
    have b : r3 s = r1 s ∧ r4 s ≠ r2 s ∧ r4 s ≠ r1 s := by
      unfold canon at h; simp only [Prod.mk.injEq] at h; split_ifs at h <;> simp_all
    have b2 : r2 s ≠ r4 s := fun e => b.2.1 e.symm
    have b3 : r1 s ≠ r4 s := fun e => b.2.2 e.symm
    simp [urow6, b.1.symm, b2, vB, aff]; norm_num
  · rw [GU_eq_of_canon w h (by decide), GU_0121 (by norm_num) w]
    have b : r3 s ≠ r1 s ∧ r4 s = r2 s := by
      unfold canon at h; simp only [Prod.mk.injEq] at h; split_ifs at h <;> simp_all
    have b1 : r1 s ≠ r3 s := fun e => b.1 e.symm
    have b3 : r1 s ≠ r4 s := fun e => p12 (e.trans b.2)
    simp [urow6, b1, b.2.symm, vB, aff]; norm_num
  · rw [GU_eq_of_canon w h (by decide), GU_0120 (by norm_num) w]
    have b : r3 s ≠ r1 s ∧ r4 s ≠ r2 s ∧ r4 s = r1 s := by
      unfold canon at h; simp only [Prod.mk.injEq] at h; split_ifs at h <;> simp_all
    have b1 : r1 s ≠ r3 s := fun e => b.1 e.symm
    have b2 : r2 s ≠ r4 s := fun e => b.2.1 e.symm
    simp [urow6, b2, b.2.2.symm, Ne.symm p34, vC, aff]; norm_num
  · rw [GU_eq_of_canon w h (by decide), GU_0123 (by norm_num) w]
    have b : r3 s ≠ r1 s ∧ r4 s ≠ r2 s ∧ r4 s ≠ r1 s := by
      unfold canon at h; simp only [Prod.mk.injEq] at h; split_ifs at h <;> simp_all
    have b1 : r1 s ≠ r3 s := fun e => b.1 e.symm
    have b2 : r2 s ≠ r4 s := fun e => b.2.1 e.symm
    have b3 : r1 s ≠ r4 s := fun e => b.2.2 e.symm
    simp [urow6, b1, b2, b3, vD, aff]; norm_num

/-! ### Atom sizes and Venn sizes -/

/-- The empty membership vector (a colour in none of the lists). -/
abbrev mem0 : Mem := (false, false, false, false)

/-- All sixteen membership vectors. -/
def memList : List Mem :=
  [(false, false, false, false), (false, false, false, true), (false, false, true, false),
    (false, false, true, true), (false, true, false, false), (false, true, false, true),
    (false, true, true, false), (false, true, true, true), (true, false, false, false),
    (true, false, false, true), (true, false, true, false), (true, false, true, true),
    (true, true, false, false), (true, true, false, true), (true, true, true, false),
    (true, true, true, true)]

/-- The size of an atom in a list of atoms with sizes (`0` if unlisted). -/
def asz : List (Mem × ℕ) → Mem → ℕ
  | [], _ => 0
  | p :: L, m => if p.1 = m then p.2 else asz L m

theorem asz_mem : ∀ (L : List (Mem × ℕ)) (m : Mem), asz L m ≠ 0 → (m, asz L m) ∈ L
  | [], _, h => absurd rfl h
  | p :: L, m, h => by
    by_cases hp : p.1 = m
    · have e : asz (p :: L) m = p.2 := by simp [asz, hp]
      rw [e, ← hp]; exact List.mem_cons_self
    · have e : asz (p :: L) m = asz L m := by simp [asz, hp]
      rw [e] at h ⊢
      exact List.mem_cons_of_mem _ (asz_mem L m h)

/-- `Σ_m [P m] a m` over the membership vectors. -/
def vsum (P : Mem → Bool) (a : Mem → ℕ) : ℤ :=
  (memList.map fun m => if P m then (a m : ℤ) else 0).sum

/-- The Venn sizes from the atom sizes. -/
def vennFn (a : Mem → ℕ) : Venn :=
  ⟨vsum (fun m => m.1) a, vsum (fun m => m.2.1) a, vsum (fun m => m.2.2.1) a,
    vsum (fun m => m.2.2.2) a, vsum (fun m => m.1 && m.2.1) a, vsum (fun m => m.2.1 && m.2.2.1) a,
    vsum (fun m => m.2.2.1 && m.2.2.2) a, vsum (fun m => m.1 && m.2.2.1) a,
    vsum (fun m => m.2.1 && m.2.2.2) a, vsum (fun m => m.1 && m.2.2.2) a,
    vsum (fun m => m.1 && m.2.1 && m.2.2.1) a, vsum (fun m => m.2.1 && m.2.2.1 && m.2.2.2) a,
    vsum (fun m => m.1 && m.2.1 && m.2.2.2) a, vsum (fun m => m.1 && m.2.2.1 && m.2.2.2) a,
    vsum (fun m => m.1 && m.2.1 && m.2.2.1 && m.2.2.2) a⟩

theorem sum_univ_mem (f : Mem → ℤ) : ∑ m : Mem, f m = (memList.map f).sum := by
  simp [Fintype.sum_prod_type, memList]; ring

theorem atomSet_mem0 (B₁ B₂ B₃ B₄ : Finset ℕ) : atomSet B₁ B₂ B₃ B₄ mem0 = ∅ := by
  ext c
  simp only [atomSet, Finset.mem_filter, Finset.mem_union, memv, Prod.mk.injEq,
    decide_eq_false_iff_not, Finset.notMem_empty, iff_false, not_and]
  tauto

/-- The colours whose membership vector satisfies `P`, counted by atoms. -/
theorem card_filter_memv (B₁ B₂ B₃ B₄ : Finset ℕ) (P : Mem → Bool) :
    ((((B₁ ∪ B₂ ∪ B₃ ∪ B₄).filter fun c => P (memv B₁ B₂ B₃ B₄ c) = true).card : ℕ) : ℤ)
      = vsum P (fun m => (atomSet B₁ B₂ B₃ B₄ m).card) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := memv B₁ B₂ B₃ B₄) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  push_cast
  rw [sum_univ_mem]
  unfold vsum
  congr 1
  apply List.map_congr_left
  intro m _
  have e : ((B₁ ∪ B₂ ∪ B₃ ∪ B₄).filter fun c => P (memv B₁ B₂ B₃ B₄ c) = true).filter
      (fun c => memv B₁ B₂ B₃ B₄ c = m) = if P m then atomSet B₁ B₂ B₃ B₄ m else ∅ := by
    ext c
    by_cases hP : P m = true
    · simp only [hP, ite_true, atomSet, Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hP⟩, h3⟩
    · simp only [hP, Bool.false_eq_true, ite_false, Finset.mem_filter, Finset.notMem_empty,
        iff_false, not_and]
      intro h1 h3; exact hP (h3 ▸ h1.2)
  rw [e]
  split_ifs <;> simp

/-- **The Venn sizes from the atom sizes.** -/
theorem vennOf_eq (B₁ B₂ B₃ B₄ : Finset ℕ) :
    vennOf B₁ B₂ B₃ B₄ = vennFn (fun m => (atomSet B₁ B₂ B₃ B₄ m).card) := by
  have key : ∀ (S : Finset ℕ) (P : Mem → Bool),
      S = (B₁ ∪ B₂ ∪ B₃ ∪ B₄).filter (fun c => P (memv B₁ B₂ B₃ B₄ c) = true) →
      ((S.card : ℕ) : ℤ) = vsum P (fun m => (atomSet B₁ B₂ B₃ B₄ m).card) := by
    intro S P h; rw [h]; exact card_filter_memv B₁ B₂ B₃ B₄ P
  simp only [vennOf, vennFn, Venn.mk.injEq]
  refine ⟨key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_,
    key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_,
    key _ _ ?_⟩ <;>
  · ext c
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_inter, memv, Bool.and_eq_true,
      decide_eq_true_eq]
    tauto

theorem vsum_congr (P : Mem → Bool) (hP : P mem0 = false) {a a' : Mem → ℕ}
    (h : ∀ m, m ≠ mem0 → a m = a' m) : vsum P a = vsum P a' := by
  unfold vsum
  congr 1
  apply List.map_congr_left
  intro m _
  by_cases hm : P m = true
  · have : m ≠ mem0 := by rintro rfl; rw [hP] at hm; exact Bool.false_ne_true hm
    rw [h m this]
  · simp [hm]

theorem vennFn_congr {a a' : Mem → ℕ} (h : ∀ m, m ≠ mem0 → a m = a' m) :
    vennFn a = vennFn a' := by
  simp only [vennFn, Venn.mk.injEq]
  refine ⟨vsum_congr _ rfl h, vsum_congr _ rfl h, vsum_congr _ rfl h, vsum_congr _ rfl h,
    vsum_congr _ rfl h, vsum_congr _ rfl h, vsum_congr _ rfl h, vsum_congr _ rfl h,
    vsum_congr _ rfl h, vsum_congr _ rfl h, vsum_congr _ rfl h, vsum_congr _ rfl h,
    vsum_congr _ rfl h, vsum_congr _ rfl h, vsum_congr _ rfl h⟩

/-- Field-wise equality of Venn data, as a boolean. -/
def vennEqB (v v' : Venn) : Bool :=
  decide (v.x1 = v'.x1) && decide (v.x2 = v'.x2) && decide (v.x3 = v'.x3) && decide (v.x4 = v'.x4)
    && decide (v.x12 = v'.x12) && decide (v.x23 = v'.x23) && decide (v.x34 = v'.x34)
    && decide (v.x13 = v'.x13) && decide (v.x24 = v'.x24) && decide (v.x14 = v'.x14)
    && decide (v.x123 = v'.x123) && decide (v.x234 = v'.x234) && decide (v.x124 = v'.x124)
    && decide (v.x134 = v'.x134) && decide (v.x1234 = v'.x1234)

theorem eq_of_vennEqB {v v' : Venn} (h : vennEqB v v' = true) : v = v' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := v
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := v'
  simp only [vennEqB, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [Venn.mk.injEq]
  tauto

/-! ### Certificates at `k = 6` -/

/-- An exact certificate at `k = 6`: the nonzero atoms with their sizes, the Venn sizes (checked
against the atoms), pins, and the constant `K`, all over the common denominator `D`. -/
structure Spec6 where
  atoms : List (Mem × ℕ)
  venn : Venn
  pins : List Pin
  l13 : ℤ
  l24 : ℤ
  K : ℤ
  D : ℤ

/-- The numerator of the gain `y` of a column, over `D`. -/
def yNum6 (sp : Spec6) (r1 r2 r3 r4 : Mem) (e13 e24 : Bool) : ℤ :=
  sp.K - pinsum sp.pins r1 r2 r3 r4 - bi e13 * sp.l13 - bi e24 * sp.l24

/-- The check for one column type: `(1 - y)·GB ≥ GU` on the box, `ρ = 487/500`. -/
def okc6 (sp : Spec6) (r1 r2 r3 r4 : Mem) (e13 e24 e14 : Bool) : Bool :=
  let cA := cls (dat sp.venn r1 r2 r3 r4 e13 e24 e14)
  let cU := urow6 e13 e24 e14
  let Y := yNum6 sp r1 r2 r3 r4 e13 e24
  let d0 := (sp.D - Y) * cA.1 - sp.D * cU.1
  let d1 := (sp.D - Y) * cA.2.1 - sp.D * cU.2.1
  let d2 := (sp.D - Y) * cA.2.2.1 - sp.D * cU.2.2.1
  let d3 := (sp.D - Y) * cA.2.2.2 - sp.D * cU.2.2.2
  decide (0 ≤ 500 * d0 + min (487 * d1) (500 * d1) + min (487 * d2) (500 * d2)
    + min (487 * d3) (500 * d3))

/-- The integer of a bit, in `ℕ`. -/
def bn6 (b : Bool) : ℕ := if b then 1 else 0

/-- The number of distinct colours of a column in the atom `m`: rows `1, 2` always differ, row 3
is new unless `s₁ = s₃`, row 4 unless `s₂ = s₄` or `s₁ = s₄`. -/
def ndist (m r1 r2 r3 r4 : Mem) (e13 e24 e14 : Bool) : ℕ :=
  bn6 (decide (r1 = m)) + bn6 (decide (r2 = m)) + bn6 (decide (r3 = m) && !e13)
    + bn6 (decide (r4 = m) && !e24 && !e14)

/-- The capacity test: the atom of each row holds the distinct colours the column puts there. -/
def capOk (z1 z2 z3 z4 : ℕ) (r1 r2 r3 r4 : Mem) (e13 e24 e14 : Bool) : Bool :=
  decide (ndist r1 r1 r2 r3 r4 e13 e24 e14 ≤ z1) && decide (ndist r2 r1 r2 r3 r4 e13 e24 e14 ≤ z2)
    && decide (ndist r3 r1 r2 r3 r4 e13 e24 e14 ≤ z3)
    && decide (ndist r4 r1 r2 r3 r4 e13 e24 e14 ≤ z4)

/-- The atoms a row can lie in, with their sizes; the empty atom gets the vacuous size `4`. -/
def ats6 (sp : Spec6) : List (Mem × ℕ) := sp.atoms ++ [(mem0, 4)]

/-- The check for all column types with row 1 in the atom `p1`. -/
def rowOk6 (sp : Spec6) (p1 : Mem × ℕ) : Bool :=
  (ats6 sp).all fun p2 => (ats6 sp).all fun p3 => (ats6 sp).all fun p4 =>
    [false, true].all fun e13 => [false, true].all fun e24 => [false, true].all fun e14 =>
      !valid p1.1 p2.1 p3.1 p4.1 e13 e24 e14
        || !capOk p1.2 p2.2 p3.2 p4.2 p1.1 p2.1 p3.1 p4.1 e13 e24 e14
        || okc6 sp p1.1 p2.1 p3.1 p4.1 e13 e24 e14

/-- **The certificate check** over all column types. -/
def allOk6 (sp : Spec6) : Bool := (ats6 sp).all (rowOk6 sp)

theorem allOk6_of (sp : Spec6) (h : ∀ p ∈ ats6 sp, rowOk6 sp p = true) : allOk6 sp = true :=
  List.all_eq_true.mpr h

/-- The pinned atoms are at most the stated sizes. -/
def pinsOk (L : List (Mem × ℕ)) : List Pin → Bool
  | [] => true
  | p :: P => decide (asz L p.2.1 ≤ p.2.2.2) && pinsOk L P

/-- The scalar conditions: `0 < D`, `|y| < 1`, the averaged gain `K - q Σ λ|R| ≥ 0` with
`q = 500/1461` (`k = 6`), the Venn sizes of the atoms, and the pin sizes. -/
def specOk6 (sp : Spec6) : Bool :=
  decide (0 < sp.D) && decide (sp.K < sp.D) && decide (0 ≤ sp.l13) && decide (0 ≤ sp.l24)
    && lamnonneg sp.pins && decide (0 ≤ sp.D + sp.K - lamsum sp.pins - sp.l13 - sp.l24)
    && decide (500 * (lamsize sp.pins + sp.l13 + sp.l24) ≤ 1461 * sp.K)
    && vennEqB sp.venn (vennFn (asz sp.atoms)) && pinsOk sp.atoms sp.pins

/-! ### Capacity of actual states -/

theorem length_le_card_of_nodup {T : Finset ℕ} {l : List ℕ} (hn : l.Nodup) (hT : ∀ x ∈ l, x ∈ T) :
    l.length ≤ T.card := by
  rw [← List.toFinset_card_of_nodup hn]
  exact Finset.card_le_card (fun x hx => hT x (List.mem_toFinset.mp hx))

/-- The distinct colours of a proper column in `T`, as a list. -/
def clist6 (T : Finset ℕ) (a b c d : ℕ) : List ℕ :=
  (if a ∈ T then [a] else []) ++ (if b ∈ T then [b] else [])
    ++ (if c ∈ T ∧ a ≠ c then [c] else []) ++ (if d ∈ T ∧ b ≠ d ∧ a ≠ d then [d] else [])

/-- The distinct colours of a proper column in a set `T` are at most `|T|`. -/
theorem ndist_le (T : Finset ℕ) {a b c d : ℕ} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) :
    (if a ∈ T then 1 else 0) + (if b ∈ T then 1 else 0) + (if c ∈ T ∧ a ≠ c then 1 else 0)
      + (if d ∈ T ∧ b ≠ d ∧ a ≠ d then 1 else 0) ≤ T.card := by
  have hlen : (clist6 T a b c d).length = (if a ∈ T then 1 else 0) + (if b ∈ T then 1 else 0)
      + (if c ∈ T ∧ a ≠ c then 1 else 0) + (if d ∈ T ∧ b ≠ d ∧ a ≠ d then 1 else 0) := by
    simp only [clist6, List.length_append]
    split_ifs <;> rfl
  rw [← hlen]
  have hba := hab.symm
  have hcb := hbc.symm
  have hdc := hcd.symm
  apply length_le_card_of_nodup
  · unfold clist6
    split_ifs <;> simp only [List.nil_append, List.append_nil, List.cons_append,
      List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false,
      not_false_eq_true, and_true] <;> tauto
  · intro x hx
    unfold clist6 at hx
    simp only [List.mem_append] at hx
    split_ifs at hx <;> simp only [List.mem_singleton, List.not_mem_nil, or_false,
      false_or] at hx <;> rcases hx with (((rfl | rfl) | rfl) | rfl) <;> tauto

theorem bn6_decide (p : Prop) [Decidable p] : bn6 (decide p) = if p then 1 else 0 := by
  unfold bn6; by_cases h : p <;> simp [h]

/-- **Actual states pass the capacity test.** -/
theorem ndist_le_card (B₁ B₂ B₃ B₄ : Finset ℕ) {s : T4} (hs : Proper s) {m : Mem}
    (hm : m ≠ mem0) :
    ndist m (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s)) (memv B₁ B₂ B₃ B₄ (r3 s))
      (memv B₁ B₂ B₃ B₄ (r4 s)) (decide (r1 s = r3 s)) (decide (r2 s = r4 s))
      (decide (r1 s = r4 s)) ≤ (atomSet B₁ B₂ B₃ B₄ m).card := by
  obtain ⟨p12, p23, p34⟩ := hs
  have e : ∀ c, decide (memv B₁ B₂ B₃ B₄ c = m) = decide (c ∈ atomSet B₁ B₂ B₃ B₄ m) := by
    intro c; exact decide_eq_decide.mpr (mem_atomSet hm c)
  have h := ndist_le (atomSet B₁ B₂ B₃ B₄ m) p12 p23 p34
  unfold ndist
  rw [e, e, e, e]
  have q1 : (decide (r3 s ∈ atomSet B₁ B₂ B₃ B₄ m) && !decide (r1 s = r3 s))
      = decide (r3 s ∈ atomSet B₁ B₂ B₃ B₄ m ∧ r1 s ≠ r3 s) := by
    by_cases h1 : r3 s ∈ atomSet B₁ B₂ B₃ B₄ m <;> by_cases h2 : r1 s = r3 s <;> simp [h1, h2]
  have q2 : (decide (r4 s ∈ atomSet B₁ B₂ B₃ B₄ m) && !decide (r2 s = r4 s)
      && !decide (r1 s = r4 s))
      = decide (r4 s ∈ atomSet B₁ B₂ B₃ B₄ m ∧ r2 s ≠ r4 s ∧ r1 s ≠ r4 s) := by
    by_cases h1 : r4 s ∈ atomSet B₁ B₂ B₃ B₄ m <;> by_cases h2 : r2 s = r4 s <;>
      by_cases h3 : r1 s = r4 s <;> simp [h1, h2, h3]
  rw [q1, q2, bn6_decide, bn6_decide, bn6_decide, bn6_decide]
  exact h

theorem ndist_le_four (m r1 r2 r3 r4 : Mem) (e13 e24 e14 : Bool) :
    ndist m r1 r2 r3 r4 e13 e24 e14 ≤ 4 := by
  have : ∀ b, bn6 b ≤ 1 := fun b => by cases b <;> simp [bn6]
  unfold ndist
  have t1 := this (decide (r1 = m)); have t2 := this (decide (r2 = m))
  have t3 := this (decide (r3 = m) && !e13); have t4 := this (decide (r4 = m) && !e24 && !e14)
  omega

/-! ### The bound for one state -/

/-- The facts a certificate needs about the lists: their atom sizes. -/
def AtomsMatch (sp : Spec6) (B₁ B₂ B₃ B₄ : Finset ℕ) : Prop :=
  ∀ m : Mem, m ≠ mem0 → (atomSet B₁ B₂ B₃ B₄ m).card = asz sp.atoms m

/-- Every row lies in a listed atom whose size bounds the column's colours there. -/
theorem row_entry (sp : Spec6) {B₁ B₂ B₃ B₄ : Finset ℕ} (hA : AtomsMatch sp B₁ B₂ B₃ B₄)
    {s : T4} (hs : Proper s) (c : ℕ) :
    ∃ p ∈ ats6 sp, p.1 = memv B₁ B₂ B₃ B₄ c ∧
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

theorem okc6_of (sp : Spec6) (hok : allOk6 sp = true) {B₁ B₂ B₃ B₄ : Finset ℕ}
    (hA : AtomsMatch sp B₁ B₂ B₃ B₄) {s : T4} (hs : Proper s) :
    okc6 sp (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s)) (memv B₁ B₂ B₃ B₄ (r3 s))
      (memv B₁ B₂ B₃ B₄ (r4 s)) (decide (r1 s = r3 s)) (decide (r2 s = r4 s))
      (decide (r1 s = r4 s)) = true := by
  obtain ⟨p1, h1, e1, c1⟩ := row_entry sp hA hs (r1 s)
  obtain ⟨p2, h2, e2, c2⟩ := row_entry sp hA hs (r2 s)
  obtain ⟨p3, h3, e3, c3⟩ := row_entry sp hA hs (r3 s)
  obtain ⟨p4, h4, e4, c4⟩ := row_entry sp hA hs (r4 s)
  have hb : ∀ b : Bool, b ∈ [false, true] := by intro b; cases b <;> simp
  unfold allOk6 at hok
  have hrow := List.all_eq_true.mp hok p1 h1
  unfold rowOk6 at hrow
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

theorem lin_min6 {d x : ℝ} (hx0 : 487 / 500 ≤ x) (hx1 : x ≤ 1) :
    min (487 * d) (500 * d) / 500 ≤ d * x := by
  rcases le_total 0 d with hd | hd
  · rw [min_eq_left (by linarith)]; nlinarith
  · rw [min_eq_right (by linarith)]; nlinarith

/-- **The bound for one state from an exact certificate**, `k = 6`. -/
theorem exact_state6 (sp : Spec6) (hok : allOk6 sp = true) (hsp : specOk6 sp = true)
    {B₁ B₂ B₃ B₄ : Finset ℕ} (hA : AtomsMatch sp B₁ B₂ B₃ B₄)
    {w : Wt} (hw : InBox 6 w) {s : T4} (hs : Proper s) :
    GU 6 w s * (1 + (yNum6 sp (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s))
        (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s)) (decide (r1 s = r3 s))
        (decide (r2 s = r4 s)) : ℝ) / sp.D)
      ≤ GB w B₁ B₂ B₃ B₄ s := by
  have hc := okc6_of sp hok hA hs
  simp only [specOk6, Bool.and_eq_true, decide_eq_true_eq] at hsp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hD, hKD⟩, h13⟩, h24⟩, hL⟩, hlow⟩, -⟩, hvenn⟩, -⟩ := hsp
  have hv : sp.venn = vennOf B₁ B₂ B₃ B₄ := by
    rw [eq_of_vennEqB hvenn, vennOf_eq]
    exact vennFn_congr (fun m hm => (hA m hm).symm)
  set Y := yNum6 sp (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s))
    (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s)) (decide (r1 s = r3 s))
    (decide (r2 s = r4 s)) with hY
  -- `-D ≤ Y < D`
  have hYb : -sp.D ≤ Y ∧ Y < sp.D := by
    obtain ⟨p0, p1⟩ := pinsum_bounds sp.pins hL (memv B₁ B₂ B₃ B₄ (r1 s))
      (memv B₁ B₂ B₃ B₄ (r2 s)) (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s))
    have b13 : 0 ≤ bi (decide (r1 s = r3 s)) ∧ bi (decide (r1 s = r3 s)) ≤ 1 := by
      unfold bi; split_ifs <;> norm_num
    have b24 : 0 ≤ bi (decide (r2 s = r4 s)) ∧ bi (decide (r2 s = r4 s)) ≤ 1 := by
      unfold bi; split_ifs <;> norm_num
    rw [hY, yNum6]
    constructor <;> nlinarith
  -- the integer inequality
  set cA := cls (dat sp.venn (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s))
    (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s)) (decide (r1 s = r3 s))
    (decide (r2 s = r4 s)) (decide (r1 s = r4 s))) with hcA
  set cU := urow6 (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) with hcU
  have hint : 0 ≤ 500 * ((sp.D - Y) * cA.1 - sp.D * cU.1)
      + min (487 * ((sp.D - Y) * cA.2.1 - sp.D * cU.2.1))
          (500 * ((sp.D - Y) * cA.2.1 - sp.D * cU.2.1))
      + min (487 * ((sp.D - Y) * cA.2.2.1 - sp.D * cU.2.2.1))
          (500 * ((sp.D - Y) * cA.2.2.1 - sp.D * cU.2.2.1))
      + min (487 * ((sp.D - Y) * cA.2.2.2 - sp.D * cU.2.2.2))
          (500 * ((sp.D - Y) * cA.2.2.2 - sp.D * cU.2.2.2)) := by
    simpa [okc6] using hc
  -- the real counts
  have hGB : GB w B₁ B₂ B₃ B₄ s = (cA.1 : ℝ) + (cA.2.1 : ℝ) * w.a + (cA.2.2.1 : ℝ) * w.b
      + (cA.2.2.2 : ℝ) * w.c := by
    rw [GB_cls, dat_eq B₁ B₂ B₃ B₄ hs, ← hv]
  have hGU : GU 6 w s = (cU.1 : ℝ) + (cU.2.1 : ℝ) * w.a + (cU.2.2.1 : ℝ) * w.b
      + (cU.2.2.2 : ℝ) * w.c := GU_urow6 w hs
  have hw' := hw
  obtain ⟨ha0, ha1, hb0, hb1, hc0, hc1⟩ := hw
  rw [rho_six] at ha0 hb0 hc0
  have hint' : (0 : ℝ) ≤ 500 * (((sp.D - Y) * cA.1 - sp.D * cU.1 : ℤ) : ℝ)
      + min (487 * (((sp.D - Y) * cA.2.1 - sp.D * cU.2.1 : ℤ) : ℝ))
          (500 * (((sp.D - Y) * cA.2.1 - sp.D * cU.2.1 : ℤ) : ℝ))
      + min (487 * (((sp.D - Y) * cA.2.2.1 - sp.D * cU.2.2.1 : ℤ) : ℝ))
          (500 * (((sp.D - Y) * cA.2.2.1 - sp.D * cU.2.2.1 : ℤ) : ℝ))
      + min (487 * (((sp.D - Y) * cA.2.2.2 - sp.D * cU.2.2.2 : ℤ) : ℝ))
          (500 * (((sp.D - Y) * cA.2.2.2 - sp.D * cU.2.2.2 : ℤ) : ℝ)) := by
    have := (Int.cast_le (R := ℝ)).mpr hint
    push_cast at this ⊢
    simpa [Int.cast_min] using this
  have m1 := lin_min6 (d := (((sp.D - Y) * cA.2.1 - sp.D * cU.2.1 : ℤ) : ℝ)) ha0 ha1
  have m2 := lin_min6 (d := (((sp.D - Y) * cA.2.2.1 - sp.D * cU.2.2.1 : ℤ) : ℝ)) hb0 hb1
  have m3 := lin_min6 (d := (((sp.D - Y) * cA.2.2.2 - sp.D * cU.2.2.2 : ℤ) : ℝ)) hc0 hc1
  have key : (sp.D : ℝ) * GU 6 w s ≤ ((sp.D : ℝ) - Y) * GB w B₁ B₂ B₃ B₄ s := by
    rw [hGB, hGU]
    push_cast at m1 m2 m3 hint' ⊢
    nlinarith
  -- `GU (1 + y) ≤ GB`
  have hDpos : (0 : ℝ) < sp.D := by exact_mod_cast hD
  have hY1 : (-(sp.D : ℝ)) ≤ Y := by exact_mod_cast hYb.1
  have hGB0 : 0 ≤ GB w B₁ B₂ B₃ B₄ s := by
    unfold GB G
    exact Finset.sum_nonneg (fun t _ => (rho_pos' (by norm_num)).le.trans (gw_mem hw' t).1)
  have hYsq : (0 : ℝ) ≤ (Y : ℝ) ^ 2 := sq_nonneg _
  have hDY : (0 : ℝ) ≤ (sp.D : ℝ) + Y := by linarith
  have hfin : GU 6 w s * ((sp.D : ℝ) + Y) * sp.D ≤ GB w B₁ B₂ B₃ B₄ s * (sp.D : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left key hDY
    nlinarith [mul_nonneg hYsq hGB0]
  rw [show (1 : ℝ) + (Y : ℝ) / sp.D = ((sp.D : ℝ) + Y) / sp.D by field_simp, mul_div_assoc',
    div_le_iff₀ hDpos]
  nlinarith

/-! ### Averaging -/

theorem qk_six_val : qk 6 = 500 / 1461 := by
  rw [qk, rho_six]; norm_num

theorem pin_sizes (sp : Spec6) {B₁ B₂ B₃ B₄ : Finset ℕ} (hA : AtomsMatch sp B₁ B₂ B₃ B₄) :
    ∀ P : List Pin, lamnonneg P = true → pinsOk sp.atoms P = true →
      ∀ p ∈ P, ((atomSet B₁ B₂ B₃ B₄ p.2.1).card : ℤ) ≤ p.2.2.2
  | [], _, _ => by simp
  | p :: P, hL, hP => by
    simp only [lamnonneg, Bool.and_eq_true, decide_eq_true_eq] at hL
    simp only [pinsOk, Bool.and_eq_true, decide_eq_true_eq] at hP
    intro p' hp'
    rcases List.mem_cons.mp hp' with rfl | hp'
    · rw [hA _ hL.1.2]; exact_mod_cast hP.1
    · exact pin_sizes sp hA P hL.2 hP.2 p' hp'

/-- **The seam inequality at `k = 6` from an exact certificate** for lists with the certificate's
atom sizes. -/
theorem exact_seam6 (sp : Spec6) (hok : allOk6 sp = true) (hsp : specOk6 sp = true)
    {B₁ B₂ B₃ B₄ : Finset ℕ} (hA : AtomsMatch sp B₁ B₂ B₃ B₄)
    {w : Wt} (hw : InBox 6 w) {X₁ X₂ X₃ X₄ : Finset ℕ}
    (hX₁ : 6 - 1 ≤ X₁.card) (hX₂ : 6 - 1 ≤ X₂.card) (hX₃ : 6 - 1 ≤ X₃.card)
    (hX₄ : 6 - 1 ≤ X₄.card) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 6 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄, GB w B₁ B₂ B₃ B₄ s := by
  have hsp' := hsp
  simp only [specOk6, Bool.and_eq_true, decide_eq_true_eq] at hsp'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hD, -⟩, h13⟩, h24⟩, hL⟩, -⟩, hK⟩, -⟩, hpins⟩ := hsp'
  have hsize := pin_sizes sp hA sp.pins hL hpins
  have hq0 : (0 : ℝ) < qk 6 := by rw [qk_six_val]; norm_num
  have hRq : 1 / rho 6 = ((6 - 3 : ℕ) : ℝ) * qk 6 := by rw [qk_six_val, rho_six]; norm_num
  have hm : (0 : ℝ) < ((6 - 3 : ℕ) : ℝ) := by norm_num
  set m : ℝ := ((6 - 3 : ℕ) : ℝ) with hm_def
  set Ω := sts X₁ X₂ X₃ X₄ with hΩ
  set u : T4 → ℝ := GU 6 w with hu
  have hu0 : ∀ t, 0 ≤ u t := GU_nonneg (by norm_num) hw
  set q := qk 6 with hq
  have hR0 : 0 ≤ m * q := (mul_pos hm hq0).le
  have hR : ∀ t ∈ Ω, ∀ t' ∈ Ω, u t ≤ (m * q) * u t' := fun t ht t' ht' => by
    rw [← hRq]; exact GU_ratio (by norm_num) hw (proper_of_mem_sts ht) (proper_of_mem_sts ht')
  have hf : ∀ i : Fin 4, ∀ c, m * ∑ t ∈ Ω.filter (fun t => rowfun i t = c), u t
      ≤ (m * q) * ∑ t ∈ Ω, u t := by
    intro i c
    fin_cases i
    · exact fibre_sts1 u hu0 (fun t => r1 t = c) hX₁ hX₂ hX₃ hX₄ hR0 hR (fun _ => c)
        (fun _ _ => rfl) (fun _ h => h)
    · exact fibre_sts2 u hu0 (fun t => r2 t = c) hX₁ hX₂ hX₃ hX₄ hR0 hR (fun _ => c)
        (fun _ _ => rfl) (fun _ h => h)
    · exact fibre_sts3 u hu0 (fun t => r3 t = c) hX₁ hX₂ hX₃ hX₄ hR0 hR (fun _ => c)
        (fun _ _ => rfl) (fun _ h => h)
    · exact fibre_sts4 u hu0 (fun t => r4 t = c) hX₁ hX₂ hX₃ hX₄ hR0 hR (fun _ => c)
        (fun _ _ => rfl) (fun _ h => h)
  set Y : T4 → ℤ := fun s => yNum6 sp (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s))
    (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s)) (decide (r1 s = r3 s))
    (decide (r2 s = r4 s)) with hYdef
  have hDpos : (0 : ℝ) < sp.D := by exact_mod_cast hD
  have hsum : ∑ s ∈ Ω, u s * (1 + (Y s : ℝ) / sp.D) ≤ ∑ s ∈ Ω, GB w B₁ B₂ B₃ B₄ s :=
    Finset.sum_le_sum (fun s hs => exact_state6 sp hok hsp hA hw (proper_of_mem_sts hs))
  suffices h : 0 ≤ ∑ s ∈ Ω, u s * (Y s : ℝ) by
    have e : ∑ s ∈ Ω, u s * (1 + (Y s : ℝ) / sp.D)
        = ∑ s ∈ Ω, u s + (∑ s ∈ Ω, u s * (Y s : ℝ)) / sp.D := by
      rw [Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    have : 0 ≤ (∑ s ∈ Ω, u s * (Y s : ℝ)) / sp.D := div_nonneg h hDpos.le
    linarith
  set W := ∑ s ∈ Ω, u s with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun s _ => hu0 s)
  set P := ∑ s ∈ Ω, u s * (pinsum sp.pins (memv B₁ B₂ B₃ B₄ (r1 s)) (memv B₁ B₂ B₃ B₄ (r2 s))
    (memv B₁ B₂ B₃ B₄ (r3 s)) (memv B₁ B₂ B₃ B₄ (r4 s)) : ℝ) with hP
  set C13 := ∑ s ∈ Ω, u s * c13 s with hC13
  set C24 := ∑ s ∈ Ω, u s * c24 s with hC24
  have e : ∑ s ∈ Ω, u s * (Y s : ℝ)
      = (sp.K : ℝ) * W - P - (sp.l13 : ℝ) * C13 - (sp.l24 : ℝ) * C24 := by
    rw [hW, hP, hC13, hC24]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [hYdef, yNum6]
    push_cast
    rw [bi_cast, bi_cast]
    unfold c13 c24
    ring
  rw [e]
  have bP := pins_avg u hu0 hm hq0.le hf B₁ B₂ B₃ B₄ sp.pins hL hsize
  have bC13 : m * C13 ≤ (m * q) * W := by
    rw [hC13]
    have : ∑ s ∈ Ω, u s * c13 s = ∑ s ∈ Ω.filter (fun t => r1 t = r3 t), u s := by
      rw [← sum_mul_ite]; rfl
    rw [this]
    exact fibre_sts1 u hu0 (fun t => r1 t = r3 t) hX₁ hX₂ hX₃ hX₄ hR0 hR r3
      (fun _ _ => rfl) (fun _ h => h)
  have bC24 : m * C24 ≤ (m * q) * W := by
    rw [hC24]
    have : ∑ s ∈ Ω, u s * c24 s = ∑ s ∈ Ω.filter (fun t => r2 t = r4 t), u s := by
      rw [← sum_mul_ite]; rfl
    rw [this]
    exact fibre_sts2 u hu0 (fun t => r2 t = r4 t) hX₁ hX₂ hX₃ hX₄ hR0 hR r4
      (fun _ _ => rfl) (fun _ h => h)
  have c13' : C13 ≤ q * W := le_of_mul_le_mul_left (bC13.trans_eq (by ring)) hm
  have c24' : C24 ≤ q * W := le_of_mul_le_mul_left (bC24.trans_eq (by ring)) hm
  have h13' : (0 : ℝ) ≤ sp.l13 := by exact_mod_cast h13
  have h24' : (0 : ℝ) ≤ sp.l24 := by exact_mod_cast h24
  have hK' : (500 : ℝ) * ((lamsize sp.pins : ℝ) + sp.l13 + sp.l24) ≤ 1461 * sp.K := by
    exact_mod_cast hK
  have hqv : q = 500 / 1461 := qk_six_val
  have i1 := mul_le_mul_of_nonneg_left c13' h13'
  have i2 := mul_le_mul_of_nonneg_left c24' h24'
  have i3 : (500 / 1461 : ℝ) * ((lamsize sp.pins : ℝ) + sp.l13 + sp.l24) * W ≤ (sp.K : ℝ) * W :=
    mul_le_mul_of_nonneg_right (by linarith) hW0
  rw [hqv] at bP i1 i2
  nlinarith

end GridGen.Four
