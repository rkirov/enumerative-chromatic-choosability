/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.K4.Point
import GridGen.Four.Dispatch

/-!
# Height four at `k = 4`: shapes from atom sizes

A next column `B` is described, up to renaming its colours, by the fifteen sizes of the nonempty
atoms of its Venn diagram (Codex's (OpenAI) "Venn shapes", `ai_research_notes/cx/h4k4b/NOTE.md`):
`atomsOf B`, in the order of `memList.tail` used by `GridGen/Four/Dispatch.lean`. `shOf xs` is
the shape with these atom sizes and the Venn sizes they determine, and every `B` with
`atomsOf B = xs` has the shape `shOf xs` (`shapeOf_atoms`).

`CertAt xs` is the classification for the next columns with atom sizes `xs`. The chain trees
(`certAt_of_chain`) and the pointwise certificates (`certAt_of_pw`) prove it, and it passes to the
reversed shape (`certAt_of_rev`), since the seam vector and the bad patterns are invariant under
reversing the rows.
-/

namespace GridGen.Four.K4

open Finset GridGen.Four

/-- The atom sizes of a column, in the order of `memList.tail`. -/
def atomsOf (B : Col) : List ℕ :=
  memList.tail.map fun m => (atomSet B.1 B.2.1 B.2.2.1 B.2.2.2 m).card

/-- The atom sizes by four-bit mask (bit `j` for row `j + 1`). -/
def nList (xs : List ℕ) : List ℕ :=
  [0, xs.getD 7 0, xs.getD 3 0, xs.getD 11 0, xs.getD 1 0, xs.getD 9 0, xs.getD 5 0, xs.getD 13 0,
    xs.getD 0 0, xs.getD 8 0, xs.getD 4 0, xs.getD 12 0, xs.getD 2 0, xs.getD 10 0, xs.getD 6 0,
    xs.getD 14 0]

/-- The Venn sizes from the atom sizes by mask. -/
def vnOf (n : List ℕ) : VN :=
  ⟨n.getD 1 0 + n.getD 3 0 + n.getD 5 0 + n.getD 7 0 + n.getD 9 0 + n.getD 11 0 + n.getD 13 0 + n.getD 15 0,
    n.getD 2 0 + n.getD 3 0 + n.getD 6 0 + n.getD 7 0 + n.getD 10 0 + n.getD 11 0 + n.getD 14 0 + n.getD 15 0,
    n.getD 4 0 + n.getD 5 0 + n.getD 6 0 + n.getD 7 0 + n.getD 12 0 + n.getD 13 0 + n.getD 14 0 + n.getD 15 0,
    n.getD 8 0 + n.getD 9 0 + n.getD 10 0 + n.getD 11 0 + n.getD 12 0 + n.getD 13 0 + n.getD 14 0 + n.getD 15 0,
    n.getD 3 0 + n.getD 7 0 + n.getD 11 0 + n.getD 15 0,
    n.getD 6 0 + n.getD 7 0 + n.getD 14 0 + n.getD 15 0,
    n.getD 12 0 + n.getD 13 0 + n.getD 14 0 + n.getD 15 0,
    n.getD 5 0 + n.getD 7 0 + n.getD 13 0 + n.getD 15 0,
    n.getD 10 0 + n.getD 11 0 + n.getD 14 0 + n.getD 15 0,
    n.getD 9 0 + n.getD 11 0 + n.getD 13 0 + n.getD 15 0,
    n.getD 7 0 + n.getD 15 0,
    n.getD 14 0 + n.getD 15 0,
    n.getD 11 0 + n.getD 15 0,
    n.getD 13 0 + n.getD 15 0,
    n.getD 15 0⟩

/-- **The shape with the atom sizes `xs`.** -/
def shOf (xs : List ℕ) : Sh := ⟨nList xs, vnOf (nList xs)⟩

/-- The atom sizes of the reversed column. -/
def revX (xs : List ℕ) : List ℕ :=
  [xs.getD 7 0, xs.getD 3 0, xs.getD 11 0, xs.getD 1 0, xs.getD 9 0, xs.getD 5 0, xs.getD 13 0,
    xs.getD 0 0, xs.getD 8 0, xs.getD 4 0, xs.getD 12 0, xs.getD 2 0, xs.getD 10 0, xs.getD 6 0,
    xs.getD 14 0]


/-! ### Every column has its shape -/

theorem mIdx_inj : ∀ a b c d a' b' c' d' : Bool,
    mIdx (a, b, c, d) = mIdx (a', b', c', d') → (a, b, c, d) = (a', b', c', d') := by decide

theorem atomN_eq (B : Col) (r : Mem) : atomN B (mIdx r) = atomSet B.1 B.2.1 B.2.2.1 B.2.2.2 r := by
  ext c
  unfold atomN atomSet uni mv
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    revert h2
    obtain ⟨a, b, c', d⟩ := r
    generalize memv B.1 B.2.1 B.2.2.1 B.2.2.2 c = mm
    obtain ⟨a', b', c'', d'⟩ := mm
    exact mIdx_inj _ _ _ _ _ _ _ _
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]⟩

theorem atoms_shOf (B : Col) : ∀ m, 0 < m → m < 16 →
    (atomN B m).card = (shOf (atomsOf B)).na m := by
  intro m h0 h16
  interval_cases m
  · rw [show (1 : ℕ) = mIdx (true, false, false, false) from rfl, atomN_eq]; rfl
  · rw [show (2 : ℕ) = mIdx (false, true, false, false) from rfl, atomN_eq]; rfl
  · rw [show (3 : ℕ) = mIdx (true, true, false, false) from rfl, atomN_eq]; rfl
  · rw [show (4 : ℕ) = mIdx (false, false, true, false) from rfl, atomN_eq]; rfl
  · rw [show (5 : ℕ) = mIdx (true, false, true, false) from rfl, atomN_eq]; rfl
  · rw [show (6 : ℕ) = mIdx (false, true, true, false) from rfl, atomN_eq]; rfl
  · rw [show (7 : ℕ) = mIdx (true, true, true, false) from rfl, atomN_eq]; rfl
  · rw [show (8 : ℕ) = mIdx (false, false, false, true) from rfl, atomN_eq]; rfl
  · rw [show (9 : ℕ) = mIdx (true, false, false, true) from rfl, atomN_eq]; rfl
  · rw [show (10 : ℕ) = mIdx (false, true, false, true) from rfl, atomN_eq]; rfl
  · rw [show (11 : ℕ) = mIdx (true, true, false, true) from rfl, atomN_eq]; rfl
  · rw [show (12 : ℕ) = mIdx (false, false, true, true) from rfl, atomN_eq]; rfl
  · rw [show (13 : ℕ) = mIdx (true, false, true, true) from rfl, atomN_eq]; rfl
  · rw [show (14 : ℕ) = mIdx (false, true, true, true) from rfl, atomN_eq]; rfl
  · rw [show (15 : ℕ) = mIdx (true, true, true, true) from rfl, atomN_eq]; rfl

theorem venn_shOf (B : Col) : (shOf (atomsOf B)).I.toVenn = vennOf B.1 B.2.1 B.2.2.1 B.2.2.2 := by
  rw [vennOf_eq]
  simp only [shOf, vnOf, nList, atomsOf, memList, VN.toVenn, vennFn, vsum, List.tail_cons,
    List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero, List.sum_cons,
    List.sum_nil, Venn.mk.injEq]
  push_cast
  simp only [Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, if_true, if_false,
    Bool.false_eq_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

/-- **Every column of four four-lists has the shape of its atom sizes.** -/
theorem shapeOf_atoms {B : Col} (hB : CardsIn 4 4 B) : ShapeOf B (shOf (atomsOf B)) :=
  ⟨hB, venn_shOf B, atoms_shOf B⟩

/-! ### Certified atom sizes -/

/-- **The classification for the next columns with atom sizes `xs`.** -/
def CertAt (xs : List ℕ) : Prop :=
  ∀ B : Col, CardsIn 4 4 B → atomsOf B = xs →
    ∀ Y : Col, CardsIn 3 4 Y → ¬ Bad Y B → RaysOK (dvec Y B)

theorem certAt_of_chain {xs : List ℕ} {gs : List (Node × V5)}
    (hgs : ∀ p ∈ gs, GoodSh (shOf xs) p.1 p.2) {T : CT} (h : chainOK (shOf xs) gs T = true) :
    CertAt xs := by
  intro B hB hx Y hY _
  subst hx
  exact raysOK_of_chainOK (shapeOf_atoms hB) hgs h hY

theorem certAt_of_pwGo {xs : List ℕ} {ctab : ℕ → List (VN × VN)} (hct : CtabOK ctab)
    {rows : List (List (VN × VN))} (hrows : ∀ q < 80, ctab q = rows.getD q [])
    {certs : List PC} (h : pwGo (shOf xs) 0 rows certs = true) : CertAt xs := by
  intro B hB hx Y _ _
  subst hx
  exact raysOK_of_pwGo (shapeOf_atoms hB) hct hrows h Y

theorem certAt_of_pw {xs : List ℕ} {ctab : ℕ → List (VN × VN)} (hct : CtabOK ctab)
    {certs : List PC} (h : pwOK (shOf xs) ctab certs = true) : CertAt xs := by
  intro B hB hx Y _ _
  subst hx
  exact raysOK_of_pwOK (shapeOf_atoms hB) hct h Y


/-! ### Reversal -/

theorem atomSet_rev (B₁ B₂ B₃ B₄ : Finset ℕ) (a b c d : Bool) :
    atomSet B₄ B₃ B₂ B₁ (a, b, c, d) = atomSet B₁ B₂ B₃ B₄ (d, c, b, a) := by
  ext x
  simp only [atomSet, memv, Finset.mem_filter, Finset.mem_union, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨by tauto, h5, h4, h3, h2⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨by tauto, h5, h4, h3, h2⟩

theorem atomsOf_rev (B : Col) : atomsOf (revC B) = revX (atomsOf B) := by
  simp only [atomsOf, revC, revX, memList, List.tail_cons, List.map_cons, List.map_nil,
    List.getD_cons_succ, List.getD_cons_zero, atomSet_rev]

theorem cards_rev {lo hi : ℕ} {Y : Col} (h : CardsIn lo hi Y) : CardsIn lo hi (revC Y) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h4, h3, h2, h1⟩

theorem dist5_swap {x y z a b : ℕ} (h : Dist5 x y z a b) : Dist5 x y z b a := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := h
  exact ⟨d1, d2, d3, d7, d8, d9, d4, d5, d6, Ne.symm d10⟩

/-- The bad patterns are closed under reversal. -/
theorem bad_of_rev {Y B : Col} (h : Bad (revC Y) (revC B)) : Bad Y B := by
  rcases h with h | h | h
  · exact Or.inr (Or.inl h)
  · left; unfold BadR at h; rwa [revC_revC, revC_revC] at h
  · right; right
    obtain ⟨x, y, z, a, b, hd, hB, hY⟩ := h
    refine ⟨x, y, z, b, a, dist5_swap hd, ?_, ?_⟩
    · rw [← revC_revC B, hB]; rfl
    · rw [← revC_revC Y, hY]; rfl

/-- **A certificate of the reversed atom sizes certifies the atom sizes.** -/
theorem certAt_of_rev {xs : List ℕ} (h : CertAt (revX xs)) : CertAt xs := by
  intro B hB hx Y hY hbad
  have := h (revC B) (cards_rev hB) (by rw [atomsOf_rev, hx]) (revC Y) (cards_rev hY)
    (fun hb => hbad (bad_of_rev hb))
  rwa [dvec_rev] at this

end GridGen.Four.K4
