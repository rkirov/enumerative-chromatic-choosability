/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.Graph

/-!
# The all-`U` injection (milestone 3 of the height-three `k = 3` entropy proof)

Kirov–Naimi's `k = 3` argument for `P₃ □ Pₙ` splits three ways.  This file discharges the third,
purely combinatorial case: a three-list assignment `L` in which **every column has type `U`** —
all three row-lists in a column are equal to a common three-element palette `A c`.

For such an assignment we build, column by column along the path, a family of *gauge* relabellings
`g c : {0,1,2} → A c` (bijections), compatible across each seam in the sense that adjacent columns
never identify two distinct residues.  Coordinatewise relabelling then injects every constant-list
(`{0,1,2}`) grid colouring into an `L`-colouring, so

    colConst 3 ≤ col L      (`Grid3.AllU.colConst_le_col_of_allU`).

The gauge across one seam extends the identity on `A c ∩ A c'` to a bijection `A c ≃ A c'`; such a
bijection maps `A c \ A c'` into `A c' \ A c`, which is exactly what forbids a cross-seam collision.
The compatibility only ever involves *adjacent* palettes, so no global colour saturation is needed
— the walk along the path is enough.
-/

open SimpleGraph Finset ListColoring
open scoped SimpleGraph

namespace Grid3.AllU

/-! ### A per-column bijection `{0,1,2} → A` -/

/-- The `p`-th element (in increasing order) of a three-element palette `A`, for `p < 3`. -/
noncomputable def enum (A : Finset ℕ) (h : A.card = 3) (p : ℕ) : ℕ :=
  if hp : p < 3 then A.orderEmbOfFin h ⟨p, hp⟩ else 0

lemma enum_mem (A : Finset ℕ) (h : A.card = 3) {p : ℕ} (hp : p < 3) : enum A h p ∈ A := by
  simp only [enum, dif_pos hp]; exact A.orderEmbOfFin_mem h _

lemma enum_inj (A : Finset ℕ) (h : A.card = 3) {p q : ℕ} (hp : p < 3) (hq : q < 3)
    (heq : enum A h p = enum A h q) : p = q := by
  simp only [enum, dif_pos hp, dif_pos hq] at heq
  have := (A.orderEmbOfFin h).injective heq
  simpa using this

/-! ### The one-seam gauge: extend the identity on `C ∩ B` to a bijection `C ≃ B` -/

lemma sdiff_card_eq (C B : Finset ℕ) (h : C.card = B.card) : (C \ B).card = (B \ C).card := by
  have h1 : (C \ B).card + (C ∩ B).card = C.card := Finset.card_sdiff_add_card_inter C B
  have h2 : (B \ C).card + (B ∩ C).card = B.card := Finset.card_sdiff_add_card_inter B C
  rw [Finset.inter_comm B C] at h2
  omega

/-- A bijection `C \ B ≃ B \ C` (both have the same cardinality when `|C| = |B|`). -/
noncomputable def gEquiv (C B : Finset ℕ) (h : C.card = B.card) : ↥(C \ B) ≃ ↥(B \ C) :=
  (C \ B).equivFin.trans ((finCongr (sdiff_card_eq C B h)).trans (B \ C).equivFin.symm)

/-- The gauge `C → B`: identity on `C ∩ B`, and the bijection `gEquiv` on `C \ B`. -/
noncomputable def gauge (C B : Finset ℕ) (h : C.card = B.card) (x : ℕ) : ℕ :=
  if _ : x ∈ C ∩ B then x
  else if hx2 : x ∈ C \ B then ((gEquiv C B h ⟨x, hx2⟩ : ↥(B \ C)) : ℕ)
  else x

lemma gauge_fix {C B : Finset ℕ} (h : C.card = B.card) {x : ℕ} (hx : x ∈ C ∩ B) :
    gauge C B h x = x := by
  simp only [gauge, dif_pos hx]

lemma gauge_eq_sdiff {C B : Finset ℕ} (h : C.card = B.card) {x : ℕ} (hx : x ∈ C \ B) :
    gauge C B h x = ((gEquiv C B h ⟨x, hx⟩ : ↥(B \ C)) : ℕ) := by
  have h1 : x ∉ C ∩ B := fun hi => (Finset.mem_sdiff.mp hx).2 (Finset.mem_inter.mp hi).2
  simp only [gauge, dif_neg h1, dif_pos hx]

lemma gauge_mem {C B : Finset ℕ} (h : C.card = B.card) {x : ℕ} (hx : x ∈ C) :
    gauge C B h x ∈ B := by
  by_cases hxB : x ∈ B
  · rw [gauge_fix h (Finset.mem_inter.mpr ⟨hx, hxB⟩)]; exact hxB
  · rw [gauge_eq_sdiff h (Finset.mem_sdiff.mpr ⟨hx, hxB⟩)]
    exact (Finset.mem_sdiff.mp (gEquiv C B h ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxB⟩⟩).2).1

lemma gauge_notmem {C B : Finset ℕ} (h : C.card = B.card) {x : ℕ} (hx : x ∈ C \ B) :
    gauge C B h x ∉ C := by
  rw [gauge_eq_sdiff h hx]
  exact fun hc => (Finset.mem_sdiff.mp (gEquiv C B h ⟨x, hx⟩).2).2 hc

lemma gauge_inj {C B : Finset ℕ} (h : C.card = B.card) {x y : ℕ}
    (hx : x ∈ C) (hy : y ∈ C) (heq : gauge C B h x = gauge C B h y) : x = y := by
  by_cases hxB : x ∈ B <;> by_cases hyB : y ∈ B
  · rw [gauge_fix h (Finset.mem_inter.mpr ⟨hx, hxB⟩),
        gauge_fix h (Finset.mem_inter.mpr ⟨hy, hyB⟩)] at heq
    exact heq
  · exfalso
    rw [gauge_fix h (Finset.mem_inter.mpr ⟨hx, hxB⟩)] at heq
    exact gauge_notmem h (Finset.mem_sdiff.mpr ⟨hy, hyB⟩) (heq ▸ hx)
  · exfalso
    rw [gauge_fix h (Finset.mem_inter.mpr ⟨hy, hyB⟩)] at heq
    exact gauge_notmem h (Finset.mem_sdiff.mpr ⟨hx, hxB⟩) (heq.symm ▸ hy)
  · rw [gauge_eq_sdiff h (Finset.mem_sdiff.mpr ⟨hx, hxB⟩),
        gauge_eq_sdiff h (Finset.mem_sdiff.mpr ⟨hy, hyB⟩)] at heq
    have h2 : gEquiv C B h ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxB⟩⟩
        = gEquiv C B h ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyB⟩⟩ := Subtype.ext heq
    have h3 := (gEquiv C B h).injective h2
    exact Subtype.ext_iff.mp h3

/-! ### The gauge family along the whole path -/

/-- **Existence of a compatible gauge family.**  For any assignment of three-element palettes to
the columns of `pathG n`, there is a family `g` of column relabellings that (i) lands in the
palette, (ii) is injective on `{0,1,2}` per column, and (iii) never identifies distinct residues
across a seam. -/
lemma exists_gauge : ∀ (n : ℕ) (A : PathV n → Finset ℕ), (∀ c, (A c).card = 3) →
    ∃ g : PathV n → ℕ → ℕ,
      (∀ c p, p < 3 → g c p ∈ A c) ∧
      (∀ c p q, p < 3 → q < 3 → g c p = g c q → p = q) ∧
      (∀ c c', (pathG n).Adj c c' → ∀ p q, p < 3 → q < 3 → p ≠ q → g c p ≠ g c' q) := by
  intro n
  induction n with
  | zero =>
      intro A hA
      refine ⟨fun c => enum (A c) (hA c), fun c p hp => enum_mem (A c) (hA c) hp,
        fun c p q hp hq he => enum_inj (A c) (hA c) hp hq he, ?_⟩
      intro c c' hadj
      exfalso; exact hadj
  | succ n ih =>
      intro A hA
      obtain ⟨g', hmem', hinj', hgauge'⟩ := ih (fun v => A (some v)) (fun v => hA (some v))
      have hCB : (A (some (pathEnd n))).card = (A none).card := by
        rw [hA (some (pathEnd n)), hA none]
      refine ⟨fun c p => c.rec (gauge (A (some (pathEnd n))) (A none) hCB (g' (pathEnd n) p))
                (fun v => g' v p), ?_, ?_, ?_⟩
      · -- membership
        intro c p hp
        cases c with
        | none => exact gauge_mem hCB (hmem' (pathEnd n) p hp)
        | some v => exact hmem' v p hp
      · -- injectivity per column
        intro c p q hp hq he
        cases c with
        | none =>
            exact hinj' (pathEnd n) p q hp hq
              (gauge_inj hCB (hmem' (pathEnd n) p hp) (hmem' (pathEnd n) q hq) he)
        | some v => exact hinj' v p q hp hq he
      · -- seam compatibility
        intro c c' hadj p q hp hq hpq
        cases c with
        | none =>
            cases c' with
            | none => exfalso; exact hadj
            | some w =>
                have hw : w = pathEnd n := hadj
                subst hw
                show gauge (A (some (pathEnd n))) (A none) hCB (g' (pathEnd n) p)
                  ≠ g' (pathEnd n) q
                have hXC := hmem' (pathEnd n) p hp
                have hZC := hmem' (pathEnd n) q hq
                have hXZ : g' (pathEnd n) p ≠ g' (pathEnd n) q :=
                  fun he => hpq (hinj' (pathEnd n) p q hp hq he)
                intro hcontra
                by_cases hXB : g' (pathEnd n) p ∈ A none
                · rw [gauge_fix hCB (Finset.mem_inter.mpr ⟨hXC, hXB⟩)] at hcontra
                  exact hXZ hcontra
                · apply gauge_notmem hCB (Finset.mem_sdiff.mpr ⟨hXC, hXB⟩)
                  rw [hcontra]; exact hZC
        | some v =>
            cases c' with
            | none =>
                have hw : v = pathEnd n := hadj
                subst hw
                show g' (pathEnd n) p
                  ≠ gauge (A (some (pathEnd n))) (A none) hCB (g' (pathEnd n) q)
                have hXC := hmem' (pathEnd n) p hp
                have hZC := hmem' (pathEnd n) q hq
                have hXZ : g' (pathEnd n) p ≠ g' (pathEnd n) q :=
                  fun he => hpq (hinj' (pathEnd n) p q hp hq he)
                intro hcontra
                by_cases hZB : g' (pathEnd n) q ∈ A none
                · rw [gauge_fix hCB (Finset.mem_inter.mpr ⟨hZC, hZB⟩)] at hcontra
                  exact hXZ hcontra
                · exact gauge_notmem hCB (Finset.mem_sdiff.mpr ⟨hZC, hZB⟩) (hcontra ▸ hXC)
            | some w =>
                have hadj' : (pathG n).Adj v w := hadj
                exact hgauge' v w hadj' p q hp hq hpq

/-! ### The injection -/

private lemma lt_three_of_mem_constList {n : ℕ}
    {f : PathV 2 × PathV n → ℕ}
    (hf : f ∈ (pathG 2 □ pathG n).colorings (constList (PathV 2 × PathV n) 3))
    (v : PathV 2 × PathV n) : f v < 3 := by
  rw [colorings, Finset.mem_filter, Fintype.mem_piFinset] at hf
  have := hf.1 v
  rwa [constList_apply, Finset.mem_range] at this

/-- **The gauge family gives the count inequality.**  Given a compatible gauge family for the
palettes of `L`, coordinatewise relabelling injects constant-list colourings into `L`-colourings. -/
theorem col_ge_of_gauge (n : ℕ) (L : ListAssignment (PathV 2 × PathV n))
    (A : PathV n → Finset ℕ) (hLA : ∀ r c, L (r, c) = A c)
    (g : PathV n → ℕ → ℕ)
    (hmem : ∀ c p, p < 3 → g c p ∈ A c)
    (hinj : ∀ c p q, p < 3 → q < 3 → g c p = g c q → p = q)
    (hgauge : ∀ c c', (pathG n).Adj c c' → ∀ p q, p < 3 → q < 3 → p ≠ q → g c p ≠ g c' q) :
    (pathG 2 □ pathG n).colConst 3 ≤ (pathG 2 □ pathG n).col L := by
  classical
  show ((pathG 2 □ pathG n).colorings (constList (PathV 2 × PathV n) 3)).card
      ≤ ((pathG 2 □ pathG n).colorings L).card
  refine Finset.card_le_card_of_injOn (fun f v => g v.2 (f v)) ?_ ?_
  · -- maps constant-list colourings into `L`-colourings
    intro f hf
    rw [Finset.mem_coe] at hf
    have hlt := lt_three_of_mem_constList hf
    have hprop : (pathG 2 □ pathG n).IsProperColoring f := by
      rw [colorings, Finset.mem_filter] at hf; exact hf.2
    rw [Finset.mem_coe, colorings, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨?_, ?_⟩
    · -- membership in the lists
      intro v
      obtain ⟨r, c⟩ := v
      rw [hLA r c]
      exact hmem c (f (r, c)) (hlt (r, c))
    · -- properness
      intro u w hadj he
      rw [boxProd_adj] at hadj
      rcases hadj with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · -- vertical seam: same column (`ha : rows adjacent`, `hb : u.2 = w.2`)
        have huw : (pathG 2 □ pathG n).Adj u w :=
          boxProd_adj.mpr (Or.inl ⟨ha, hb⟩)
        have he2 : g u.2 (f u) = g u.2 (f w) := by
          have h0 : g u.2 (f u) = g w.2 (f w) := he
          rw [← hb] at h0; exact h0
        exact hprop huw (hinj u.2 (f u) (f w) (hlt u) (hlt w) he2)
      · -- horizontal seam: same row, adjacent columns (`ha : cols adjacent`, `hb : u.1 = w.1`)
        have huw : (pathG 2 □ pathG n).Adj u w :=
          boxProd_adj.mpr (Or.inr ⟨ha, hb⟩)
        exact hgauge u.2 w.2 ha (f u) (f w) (hlt u) (hlt w) (hprop huw) he
  · -- injectivity of the relabelling
    intro f hf f' hf' heq
    rw [Finset.mem_coe] at hf hf'
    have hlt := lt_three_of_mem_constList hf
    have hlt' := lt_three_of_mem_constList hf'
    funext v
    obtain ⟨r, c⟩ := v
    have hcol : g c (f (r, c)) = g c (f' (r, c)) := congrFun heq (r, c)
    exact hinj c (f (r, c)) (f' (r, c)) (hlt (r, c)) (hlt' (r, c)) hcol

/-! ### Milestone 3 -/

/-- **The all-`U` case.**  If every column of the three-list assignment `L` is type `U` — all three
row-lists in each column agree — then the constant assignment does not beat `L`:
`colConst 3 ≤ col L`. -/
theorem colConst_le_col_of_allU (n : ℕ) (L : ListAssignment (PathV 2 × PathV n))
    (h3 : IsNListAssignment L 3)
    (hU : ∀ (r : PathV 2) (c : PathV n), L (r, c) = L (rowT, c)) :
    (pathG 2 □ pathG n).colConst 3 ≤ (pathG 2 □ pathG n).col L := by
  set A : PathV n → Finset ℕ := fun c => L (rowT, c) with hAdef
  have hA : ∀ c, (A c).card = 3 := fun c => h3 (rowT, c)
  have hLA : ∀ r c, L (r, c) = A c := fun r c => hU r c
  obtain ⟨g, hmem, hinj, hgauge⟩ := exists_gauge n A hA
  exact col_ge_of_gauge n L A hLA g hmem hinj hgauge

end Grid3.AllU
