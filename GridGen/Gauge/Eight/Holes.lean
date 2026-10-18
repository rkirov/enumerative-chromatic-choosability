/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Labelling

/-!
# Transpositions through holes

At a row edge the moves realize a permutation that sends the lower row's labels of the shared
colours to the upper row's. Every mismatched shared colour is new in one of the two rows. Its
label there is a *star label*: no colour of that row's seam column carries it as a key. Such a
label is a *hole*.

`realizeH` builds the transpositions one at a time, from the first applied. Each transposition
contains a hole of the upper row, or a current hole of the lower row. A transposition `(x, y)`
relabels the rows below the edge, so the lower row's holes move with it. A move with a hole
leaves the two-cell crossing path at the edge only one of its two label phases
(`Eight/Bad8.lean`).

The count is unchanged: at most one transposition per mismatched colour (`rhoH_spec`). Every
mismatched colour is new in the lower row or lies in the vertical difference of the old column,
so the moves at an edge number at most `h_{v+1} + |A_{v+1} \ A_v|` (`length_rhoH_le`).
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

/-! ### Hole conditions on transposition lists -/

/-- Every transposition of the list contains a label outside `T` (a hole of the upper row), or a
label that no current lower-row label reaches. The lower row's labels are `B`, moved by the
transpositions applied before (the tail of the list). -/
def HoleOK (T B : ℕ → Prop) : List (ℕ × ℕ) → Prop
  | [] => True
  | p :: ts => ((¬ T p.1 ∨ ¬ T p.2) ∨ (∀ z, B z → comp ts z ≠ p.1) ∨ (∀ z, B z → comp ts z ≠ p.2)) ∧
      HoleOK T B ts

theorem holeOK_append {T B : ℕ → Prop} (p : ℕ × ℕ)
    (hp : (¬ T p.1 ∨ ¬ T p.2) ∨ (∀ z, B z → z ≠ p.1) ∨ (∀ z, B z → z ≠ p.2)) :
    ∀ ts : List (ℕ × ℕ), HoleOK T (fun w => B (Equiv.swap p.1 p.2 w)) ts →
      HoleOK T B (ts ++ [p]) := by
  intro ts
  induction ts with
  | nil => intro _; exact ⟨hp, trivial⟩
  | cons q ts ih =>
      rintro ⟨hq, hts⟩
      refine ⟨?_, ih hts⟩
      rcases hq with hq | hq | hq
      · exact Or.inl hq
      · right; left
        intro z hz
        show comp (ts ++ [p]) z ≠ q.1
        rw [comp_append, comp_cons, comp_nil]
        exact hq _ (by simpa using hz)
      · right; right
        intro z hz
        show comp (ts ++ [p]) z ≠ q.2
        rw [comp_append, comp_cons, comp_nil]
        exact hq _ (by simpa using hz)

/-- **Realization through holes.** If every mismatch has a hole at one end (`h c` outside `T`, or
`g c` outside `B`), the mismatches are realized by at most as many transpositions, each through a
hole. -/
theorem realizeH (k : ℕ) : ∀ (r : ℕ) (T B : ℕ → Prop) (C : Finset ℕ) (g h : ℕ → ℕ),
    Set.InjOn g C → Set.InjOn h C → (∀ c ∈ C, g c < k) → (∀ c ∈ C, h c < k) →
    (∀ c ∈ C, g c ≠ h c → ¬ T (h c) ∨ ¬ B (g c)) →
    (C.filter fun c => g c ≠ h c).card ≤ r →
      ∃ ts : List (ℕ × ℕ), ts.length ≤ (C.filter fun c => g c ≠ h c).card ∧ Small k ts ∧
        (∀ c ∈ C, comp ts (g c) = h c) ∧ HoleOK T B ts := by
  intro r
  induction r with
  | zero =>
      intro T B C g h _ _ _ _ _ hr
      refine ⟨[], by simp, fun _ hp => by simp at hp, fun c hc => ?_, trivial⟩
      have : c ∉ C.filter fun c => g c ≠ h c := by
        rw [card_eq_zero.mp (Nat.le_zero.mp hr)]; exact notMem_empty c
      rw [mem_filter] at this
      show g c = h c
      by_contra hne; exact this ⟨hc, hne⟩
  | succ r ih =>
      intro T B C g h hg hh hgk hhk hhole hr
      by_cases h0 : (C.filter fun c => g c ≠ h c) = ∅
      · refine ⟨[], by simp, fun _ hp => by simp at hp, fun c hc => ?_, trivial⟩
        have : c ∉ C.filter fun c => g c ≠ h c := by rw [h0]; exact notMem_empty c
        rw [mem_filter] at this
        show g c = h c
        by_contra hne; exact this ⟨hc, hne⟩
      obtain ⟨c₀, hc₀⟩ := nonempty_iff_ne_empty.mpr h0
      rw [mem_filter] at hc₀
      set a := g c₀
      set b := h c₀
      set g' : ℕ → ℕ := fun c => Equiv.swap a b (g c)
      have hg' : Set.InjOn g' C := fun c hc c' hc' e => hg hc hc' ((Equiv.swap a b).injective e)
      have hgk' : ∀ c ∈ C, g' c < k := by
        intro c hc
        simp only [g']
        rcases eq_or_ne (g c) a with e | e
        · rw [e, Equiv.swap_apply_left]; exact hhk c₀ hc₀.1
        rcases eq_or_ne (g c) b with e' | e'
        · rw [e', Equiv.swap_apply_right]; exact hgk c₀ hc₀.1
        · rw [Equiv.swap_apply_of_ne_of_ne e e']; exact hgk c hc
      -- the mismatches of `g', h` are those of `g, h` without `c₀`
      have hsub : (C.filter fun c => g' c ≠ h c) ⊆ (C.filter fun c => g c ≠ h c).erase c₀ := by
        intro c hc
        rw [mem_filter] at hc
        rw [mem_erase, mem_filter]
        refine ⟨fun e => ?_, hc.1, fun e => hc.2 ?_⟩
        · subst e; apply hc.2; simp [g', a, b]
        · simp only [g']
          rw [e]
          have hca : h c ≠ a := fun e' => by
            have := hg hc₀.1 hc.1 (e.trans e').symm
            subst this; exact hc₀.2 e
          have hcb : h c ≠ b := fun e' => by
            have := hh hc.1 hc₀.1 e'
            subst this; exact hc₀.2 e
          rw [Equiv.swap_apply_of_ne_of_ne hca hcb]
      have hcard : (C.filter fun c => g' c ≠ h c).card ≤ r := by
        have := card_le_card hsub
        rw [card_erase_of_mem (mem_filter.mpr hc₀)] at this
        omega
      have hhole' : ∀ c ∈ C, g' c ≠ h c → ¬ T (h c) ∨ ¬ (fun w => B (Equiv.swap a b w)) (g' c) := by
        intro c hc hne
        have hne' : g c ≠ h c := by
          intro e
          have : c ∉ C.filter fun c => g' c ≠ h c := fun hm => by
            have := hsub hm
            rw [mem_erase, mem_filter] at this
            exact this.2.2 e
          exact this (mem_filter.mpr ⟨hc, hne⟩)
        simpa [g'] using hhole c hc hne'
      obtain ⟨ts, hlen, hsmall, hts, hok⟩ :=
        ih T (fun w => B (Equiv.swap a b w)) C g' h hg' hh hgk' hhk hhole' hcard
      refine ⟨ts ++ [(a, b)], ?_, ?_, fun c hc => ?_, ?_⟩
      · rw [List.length_append, List.length_singleton]
        have := card_le_card hsub
        rw [card_erase_of_mem (mem_filter.mpr hc₀)] at this
        have hpos : 0 < (C.filter fun c => g c ≠ h c).card :=
          card_pos.mpr ⟨c₀, mem_filter.mpr hc₀⟩
        omega
      · intro p hp
        rw [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact hsmall p hp
        · exact ⟨hgk c₀ hc₀.1, hhk c₀ hc₀.1⟩
      · rw [comp_append, comp_cons, comp_nil]
        exact hts c hc
      · refine holeOK_append (a, b) ?_ ts hok
        rcases hhole c₀ hc₀.1 hc₀.2 with h1 | h1
        · exact Or.inl (Or.inr h1)
        · exact Or.inr (Or.inl fun z hz e => h1 (by subst e; exact hz))

/-! ### Glueing through holes -/

section GlueH

variable (k : ℕ) (Ax Bx : ℕ → Finset ℕ) (βx : ℕ → ℕ → ℕ)

/-- The labels of row `v`'s staying colours, after the conjugation `pl`. -/
def imgT (v : ℕ) (pl : List (ℕ × ℕ)) (z : ℕ) : Prop := ∃ a ∈ Bx v ∩ Ax v, comp pl (βx v a) = z

/-- The hypotheses of `realizeH` at the edge below row `v`. -/
def RGoodH (v : ℕ) (pl : List (ℕ × ℕ)) : Prop :=
  RGood k (Bx v ∩ Bx (v + 1)) (fun c => comp pl (βx (v + 1) c)) (fun c => comp pl (βx v c)) ∧
    ∀ c ∈ Bx v ∩ Bx (v + 1), comp pl (βx (v + 1) c) ≠ comp pl (βx v c) →
      ¬ imgT Ax Bx βx v pl (comp pl (βx v c)) ∨ ¬ imgT Ax Bx βx (v + 1) pl (comp pl (βx (v + 1) c))

/-- The transpositions at the edge below row `v`, through holes. -/
noncomputable def rhoH (v : ℕ) (pl : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  if h : RGoodH k Ax Bx βx v pl
  then Classical.choose (realizeH k _ (imgT Ax Bx βx v pl) (imgT Ax Bx βx (v + 1) pl)
    (Bx v ∩ Bx (v + 1)) _ _ h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2 h.2 le_rfl)
  else []

/-- The accumulated conjugation of row `v`. -/
noncomputable def piLH : ℕ → List (ℕ × ℕ)
  | 0 => []
  | v + 1 => rhoH k Ax Bx βx v (piLH v) ++ piLH v

/-- **The glued labelling, through holes.** -/
noncomputable def glueLabH (v : ℕ) (a : ℕ) : ℕ := comp (piLH k Ax Bx βx v) (βx v a)

variable {k Ax Bx βx}

/-- Mismatches sit at colours new in one of the two rows. -/
def NewMis (Ax Bx : ℕ → Finset ℕ) (βx : ℕ → ℕ → ℕ) : Prop :=
  ∀ v, ∀ c ∈ Bx v ∩ Bx (v + 1), βx (v + 1) c ≠ βx v c → c ∉ Ax v ∨ c ∉ Ax (v + 1)

theorem not_imgT (hR : RowLab k Bx βx) {v : ℕ} {pl : List (ℕ × ℕ)} {c : ℕ} (hc : c ∈ Bx v)
    (hn : c ∉ Ax v) : ¬ imgT Ax Bx βx v pl (comp pl (βx v c)) := by
  rintro ⟨a, ha, e⟩
  rw [mem_inter] at ha
  have := (hR v).1 ha.1 hc (comp_injective pl e)
  subst this; exact hn ha.2

theorem rgoodH (hR : RowLab k Bx βx) (hN : NewMis Ax Bx βx) {pl : List (ℕ × ℕ)} (hpl : Small k pl)
    (v : ℕ) : RGoodH k Ax Bx βx v pl := by
  refine ⟨rgood hR hpl v, fun c hc hne => ?_⟩
  have hne' : βx (v + 1) c ≠ βx v c := fun e => hne (by rw [e])
  rw [mem_inter] at hc
  rcases hN v c (mem_inter.mpr hc) hne' with h | h
  · exact Or.inl (not_imgT hR hc.1 h)
  · exact Or.inr (not_imgT hR hc.2 h)

theorem rhoH_spec (hR : RowLab k Bx βx) (hN : NewMis Ax Bx βx) {pl : List (ℕ × ℕ)}
    (hpl : Small k pl) (v : ℕ) :
    (rhoH k Ax Bx βx v pl).length ≤ ((Bx v ∩ Bx (v + 1)).filter
        fun c => comp pl (βx (v + 1) c) ≠ comp pl (βx v c)).card ∧
      Small k (rhoH k Ax Bx βx v pl) ∧ (∀ c ∈ Bx v ∩ Bx (v + 1),
        comp (rhoH k Ax Bx βx v pl) (comp pl (βx (v + 1) c)) = comp pl (βx v c)) ∧
      HoleOK (imgT Ax Bx βx v pl) (imgT Ax Bx βx (v + 1) pl) (rhoH k Ax Bx βx v pl) := by
  have h := rgoodH hR hN hpl v
  unfold rhoH
  rw [dite_eq_left h]
  exact Classical.choose_spec (realizeH k _ (imgT Ax Bx βx v pl) (imgT Ax Bx βx (v + 1) pl)
    (Bx v ∩ Bx (v + 1)) _ _ h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2 h.2 le_rfl)

theorem small_piLH (hR : RowLab k Bx βx) (hN : NewMis Ax Bx βx) :
    ∀ v, Small k (piLH k Ax Bx βx v)
  | 0 => fun _ hp => by simp [piLH] at hp
  | v + 1 => by
      intro p hp
      simp only [piLH, List.mem_append] at hp
      rcases hp with hp | hp
      · exact (rhoH_spec hR hN (small_piLH hR hN v) v).2.1 p hp
      · exact small_piLH hR hN v p hp

/-- **Vertical consistency of the glued labelling.** -/
theorem glueLabH_vc (hR : RowLab k Bx βx) (hN : NewMis Ax Bx βx) (v : ℕ) {c : ℕ}
    (hc : c ∈ Bx v ∩ Bx (v + 1)) : glueLabH k Ax Bx βx (v + 1) c = glueLabH k Ax Bx βx v c := by
  unfold glueLabH
  simp only [piLH]
  rw [comp_append]
  exact (rhoH_spec hR hN (small_piLH hR hN v) v).2.2.1 c hc

theorem glueLabH_injOn (hR : RowLab k Bx βx) (v : ℕ) : Set.InjOn (glueLabH k Ax Bx βx v) (Bx v) :=
  fun _ ha _ ha' e => (hR v).1 ha ha' (comp_injective _ e)

theorem glueLabH_lt (hR : RowLab k Bx βx) (hN : NewMis Ax Bx βx) (v : ℕ) {a : ℕ}
    (ha : a ∈ Bx v) : glueLabH k Ax Bx βx v a < k :=
  comp_lt (small_piLH hR hN v) ((hR v).2 a ha)

/-- Mismatches of the row labellings are new in the lower row, or lie in the vertical difference
of the old column. -/
theorem card_mismatchH_le (hN : NewMis Ax Bx βx) (v : ℕ) :
    ((Bx v ∩ Bx (v + 1)).filter fun c => βx (v + 1) c ≠ βx v c).card ≤
      (Bx (v + 1) \ Ax (v + 1)).card + (Ax (v + 1) \ Ax v).card := by
  refine le_trans (card_le_card ?_) (card_union_le _ _)
  intro c hc
  rw [mem_filter] at hc
  rw [mem_union, mem_sdiff, mem_sdiff]
  rcases hN v c hc.1 hc.2 with h | h
  · by_cases h1 : c ∈ Ax (v + 1)
    · exact Or.inr ⟨h1, h⟩
    · exact Or.inl ⟨(mem_inter.mp hc.1).2, h1⟩
  · exact Or.inl ⟨(mem_inter.mp hc.1).2, h⟩

/-- **The moves at one edge.** -/
theorem length_rhoH_le (hR : RowLab k Bx βx) (hN : NewMis Ax Bx βx) (v : ℕ) :
    (rhoH k Ax Bx βx v (piLH k Ax Bx βx v)).length ≤
      (Bx (v + 1) \ Ax (v + 1)).card + (Ax (v + 1) \ Ax v).card := by
  refine le_trans (rhoH_spec hR hN (small_piLH hR hN v) v).1 (le_trans (le_of_eq ?_)
    (card_mismatchH_le hN v))
  congr 1
  ext c
  simp only [mem_filter]
  exact and_congr_right fun _ =>
    ⟨fun h e => h (by rw [e]), fun h e => h (comp_injective _ e)⟩

/-! ### The moves, through holes -/

/-- Process the row edges `0, …, e - 1` in order, with the hole transpositions. -/
noncomputable def applyAllH {m : ℕ} : ℕ → (Fin m → ℕ → ℕ) → Fin m → ℕ → ℕ
  | 0, M => M
  | e + 1, M => applyEdge e (rhoH k Ax Bx βx e (piLH k Ax Bx βx e)) (applyAllH e M)

theorem applyAllH_eq {m : ℕ} (M : Fin m → ℕ → ℕ) : ∀ e (u : Fin m) (a : ℕ),
    applyAllH (k := k) (Ax := Ax) (Bx := Bx) (βx := βx) e M u a =
      comp (piLH k Ax Bx βx (min u.val e)) (M u a)
  | 0, u, a => by simp [applyAllH, piLH, comp]
  | e + 1, u, a => by
      simp only [applyAllH]
      rw [applyEdge_eq]
      simp only
      split_ifs with h
      · rw [applyAllH_eq M e u a, show min u.val e = e by omega,
          show min u.val (e + 1) = e + 1 by omega, piLH, comp_append]
      · rw [applyAllH_eq M e u a, show min u.val e = u.val by omega,
          show min u.val (e + 1) = u.val by omega]

end GlueH

end GridGen.Gauge
