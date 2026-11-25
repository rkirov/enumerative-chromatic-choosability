/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.TagBuiltV

/-!
# Graphs built by ears, pendant edges and reorientations

The induction of `Outerplanar/TagBuiltV.lean` with a fourth step: **reorienting an edge**, i.e.
exchanging the demands carried by its two orientations. This is sound for class systems whose
classes are invariant under transposing a profile (`ClassSys.Transposable`); all the classes of
`Outerplanar/SevenEven.lean` are (`Outerplanar/SevenSwap.lean`).

It is what the cut-vertex bookkeeping needs: a new block `B` at a cut vertex `x` starts with a
pendant edge `xw`, whose demand is carried by `(x, w)`; after a reorientation it is carried by
`(w, x)`, so that what hangs at `w` (the other blocks at `w`) can be moved onto it by further
pendant steps at `w`, and `B` is then built by ears from the edge `(w, x)`.

* `swapTags R tg u v` — the demands of `(u, v)` and `(v, u)` exchanged.
* `tagBound_swap` — a reorientation keeps the weighted lower bound.
* `TagBuiltW` — built from nothing by single edges starting a new component (`comp`, with the
  glue on its two orientations; `edge` is the first one), isolated vertices (`iso`), ears, pendant
  edges and reorientations; `tagBound_comp`, `tagBound_iso` — a new component multiplies the two
  sides of the weighted lower bound.
* **`ecc_three_of_tagBuiltW`** — sound rules give 3-ECC.

Part of the formalization of the seven-even-face theorem with cut vertices (research note
`ai_research_notes/OUTERPLANAR_SEVEN_AND_CUTS_2026-11-23.md`, another AI session of this
repository's collaboration); formalized by Claude.
-/

namespace Outerplanar

open Finset

/-- The classes of `R` are invariant under transposing a profile. -/
def ClassSys.Transposable (R : ClassSys) : Prop :=
  ∀ t S T W A, R.cls t S T W A → R.cls t T S (fun d c => W c d) A

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The demands of `(u, v)` and `(v, u)` exchanged. -/
def swapTags (R : ClassSys) (tg : V → V → R.Tag) (u v : V) : V → V → R.Tag := fun a b =>
  if a = u ∧ b = v then tg v u else if a = v ∧ b = u then tg u v else tg a b

/-- The tags after a new component `uv`. -/
def compTags (R : ClassSys) (tg : V → V → R.Tag) (u v : V) (t₁ t₂ : R.Tag) : V → V → R.Tag :=
  fun a b => if a = u ∧ b = v then t₁ else if a = v ∧ b = u then t₂ else tg a b

/-- Built from nothing by single edges, isolated vertices, ears, pendant edges and
reorientations, following the rules. -/
inductive TagBuiltW (R : ClassSys) (rule : R.Tag → (m : ℕ) → (Fin (m + 1) → R.Tag) → Prop)
    (glue : R.Tag → R.Tag → Prop) (vrule : R.Tag → R.Tag → R.Tag → Prop) :
    Finset V → (V → V → R.Tag) → Prop
  | edge (u v : V) (huv : G.Adj u v) (t₁ t₂ : R.Tag) (hg : glue t₁ t₂) :
      TagBuiltW R rule glue vrule {u, v} (edgeTags R u v t₁ t₂)
  | face (S : Finset V) (tg : V → V → R.Tag) (m : ℕ) (u v : V) (x : Fin m → V)
      (he : IsEar G S u v x) (τ : Fin (m + 1) → R.Tag) (hr : rule (tg u v) m τ)
      (hS : TagBuiltW R rule glue vrule S tg) :
      TagBuiltW R rule glue vrule (S ∪ univ.image x) (earTags R S tg u v x τ)
  | pendant (S : Finset V) (tg : V → V → R.Tag) (v y w : V) (hv : v ∈ S) (hy : y ∈ S)
      (hvy : G.Adj v y) (hw : w ∉ S) (hwv : G.Adj w v) (huniq : ∀ z ∈ S, G.Adj w z → z = v)
      (t₀ t₁ : R.Tag) (hr : vrule (tg v y) t₀ t₁) (hS : TagBuiltW R rule glue vrule S tg) :
      TagBuiltW R rule glue vrule (insert w S) (pendTags R tg v y w t₀ t₁)
  | swap (S : Finset V) (tg : V → V → R.Tag) (u v : V) (hu : u ∈ S) (hv : v ∈ S)
      (huv : G.Adj u v) (hS : TagBuiltW R rule glue vrule S tg) :
      TagBuiltW R rule glue vrule S (swapTags R tg u v)
  | empty (tg : V → V → R.Tag) : TagBuiltW R rule glue vrule ∅ tg
  | iso (S : Finset V) (tg : V → V → R.Tag) (x : V) (hx : x ∉ S) (h : ∀ z ∈ S, ¬ G.Adj x z)
      (hS : TagBuiltW R rule glue vrule S tg) : TagBuiltW R rule glue vrule (insert x S) tg
  | comp (S : Finset V) (tg : V → V → R.Tag) (u v : V) (hu : u ∉ S) (hv : v ∉ S)
      (huv : G.Adj u v) (hiso : ∀ z ∈ S, ¬ G.Adj u z ∧ ¬ G.Adj v z) (t₁ t₂ : R.Tag)
      (hg : glue t₁ t₂) (hS : TagBuiltW R rule glue vrule S tg) :
      TagBuiltW R rule glue vrule (insert u (insert v S)) (compTags R tg u v t₁ t₂)

variable {G}

/-- The involution of ordered pairs exchanging `(u, v)` and `(v, u)`. -/
theorem adjPairs_swap_mem {S : Finset V} {u v : V} (hu : u ∈ S) (hv : v ∈ S) (huv : G.Adj u v)
    (p : V × V) : p ∈ adjPairs G S ↔ Equiv.swap (u, v) (v, u) p ∈ adjPairs G S := by
  by_cases h1 : p = (u, v)
  · subst h1
    rw [Equiv.swap_apply_left]
    simp only [mem_adjPairs]
    exact ⟨fun _ => ⟨hv, hu, huv.symm⟩, fun _ => ⟨hu, hv, huv⟩⟩
  · by_cases h2 : p = (v, u)
    · subst h2
      rw [Equiv.swap_apply_right]
      simp only [mem_adjPairs]
      exact ⟨fun _ => ⟨hu, hv, huv⟩, fun _ => ⟨hv, hu, huv.symm⟩⟩
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- **A reorientation keeps the weighted lower bound.** -/
theorem tagBound_swap {R : ClassSys} (hswap : R.Transposable) {S : Finset V}
    {tg : V → V → R.Tag} {u v : V} (hu : u ∈ S) (hv : v ∈ S) (huv : G.Adj u v)
    (ih : TagBound G R S tg) : TagBound G R S (swapTags R tg u v) := by
  intro L Ω A hcard hΩ hA hinv
  have hne : u ≠ v := huv.ne
  set σ := Equiv.swap (u, v) (v, u) with hσ
  set Ω' : V → V → ℕ → ℕ → ℝ := fun a b =>
    if a = u ∧ b = v then fun c d => Ω v u d c
    else if a = v ∧ b = u then fun c d => Ω u v d c else Ω a b with hΩ'
  set A' : V → V → ℝ := fun a b => A (σ (a, b)).1 (σ (a, b)).2 with hA'
  have key := ih L Ω' A' hcard
    (fun a b c d => by simp only [hΩ']; split_ifs <;> exact hΩ _ _ _ _)
    (fun a b => hA _ _)
    (fun a ha b hb hab => by
      by_cases h1 : a = u ∧ b = v
      · obtain ⟨rfl, rfl⟩ := h1
        have := hinv b hb a ha hab.symm
        simp only [swapTags, show ¬ (b = a ∧ a = b) from fun h => hne h.2, ite_false,
          and_self, ite_true] at this
        simp only [hΩ', hA', and_self, ite_true, hσ, Equiv.swap_apply_left]
        exact hswap _ _ _ _ _ this
      · by_cases h2 : a = v ∧ b = u
        · obtain ⟨rfl, rfl⟩ := h2
          have := hinv b hb a ha hab.symm
          simp only [swapTags, and_self, ite_true] at this
          simp only [hΩ', hA', h1, and_self, ite_true, ite_false, hσ, Equiv.swap_apply_right]
          exact hswap _ _ _ _ _ this
        · have := hinv a ha b hb hab
          simp only [swapTags, h1, h2, ite_false] at this
          have hp1 : (a, b) ≠ (u, v) := fun e => h1 ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
          have hp2 : (a, b) ≠ (v, u) := fun e => h2 ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
          simp only [hΩ', hA', h1, h2, ite_false, hσ, Equiv.swap_apply_of_ne_of_ne hp1 hp2]
          exact this)
  have hZ : ZG G S L (fun _ _ => 1) Ω' = ZG G S L (fun _ _ => 1) Ω := by
    unfold ZG
    refine Finset.sum_congr rfl fun f _ => ?_
    congr 1
    refine Finset.prod_equiv σ (adjPairs_swap_mem hu hv huv) fun p _ => ?_
    by_cases h1 : p = (u, v)
    · subst h1
      simp [hΩ', hσ, Equiv.swap_apply_left]
    · by_cases h2 : p = (v, u)
      · subst h2
        simp [hΩ', hσ, Equiv.swap_apply_right, hne, Ne.symm hne]
      · have h1' : ¬ (p.1 = u ∧ p.2 = v) := fun h => h1 (Prod.ext h.1 h.2)
        have h2' : ¬ (p.1 = v ∧ p.2 = u) := fun h => h2 (Prod.ext h.1 h.2)
        simp only [hΩ', h1', h2', ite_false, hσ, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hP : ∏ p ∈ adjPairs G S, A' p.1 p.2 = ∏ p ∈ adjPairs G S, A p.1 p.2 :=
    Finset.prod_equiv σ (adjPairs_swap_mem hu hv huv) fun p _ => rfl
  rw [hZ, hP] at key
  exact key

theorem tagBound_empty {R : ClassSys} (tg : V → V → R.Tag) : TagBound G R ∅ tg := by
  intro L Ω A _ _ _ _
  have h : adjPairs G (∅ : Finset V) = ∅ := by simp [adjPairs]
  rw [ZG_empty, ZG_empty, h, Finset.prod_empty, mul_one]

/-- **An isolated vertex.** -/
theorem tagBound_iso {R : ClassSys} {S : Finset V} {tg : V → V → R.Tag} {x : V} (hx : x ∉ S)
    (hiso : ∀ z ∈ S, ¬ G.Adj x z) (ih : TagBound G R S tg) : TagBound G R (insert x S) tg := by
  intro L Ω A hcard hΩ hA hinv
  have key := ih L Ω A (fun z hz => hcard z (mem_insert_of_mem hz)) hΩ hA
    (fun a ha b hb hab => hinv a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) hab)
  rw [ZG_const_insert_isolated G 3 hx hiso, adjPairs_insert_isolated G hiso,
    ZG_insert_isolated G hx hiso]
  have : ∑ c ∈ L x, (fun (_ : V) (_ : ℕ) => (1 : ℝ)) x c = 3 := by
    simp [hcard x (mem_insert_self x S)]
  rw [this]
  push_cast
  nlinarith [ZG_const_nonneg G 3 S, Finset.prod_pos fun p (_ : p ∈ adjPairs G S) => hA p.1 p.2]

/-- **A new component: a single edge.** -/
theorem tagBound_comp {R : ClassSys} {S : Finset V} {tg : V → V → R.Tag} {u v : V} (hu : u ∉ S)
    (hv : v ∉ S) (huv : G.Adj u v) (hiso : ∀ z ∈ S, ¬ G.Adj u z ∧ ¬ G.Adj v z) {t₁ t₂ : R.Tag}
    (hg : R.GlueSound t₁ t₂) (ih : TagBound G R S tg) :
    TagBound G R (insert u (insert v S)) (compTags R tg u v t₁ t₂) := by
  intro L Ω A hcard hΩ hA hinv
  have hne : u ≠ v := huv.ne
  have hu' : u ∉ insert v S := by simp [hne, hu]
  have hvS : v ∈ insert v S := mem_insert_self v S
  have huniq : ∀ z ∈ insert v S, G.Adj u z → z = v := by
    intro z hz h
    rcases mem_insert.mp hz with rfl | hz
    · rfl
    · exact absurd h (hiso z hz).1
  have hviso : ∀ z ∈ S, ¬ G.Adj v z := fun z hz => (hiso z hz).2
  have hmemS : ∀ z ∈ S, z ∈ insert u (insert v S) := fun z hz =>
    mem_insert_of_mem (mem_insert_of_mem hz)
  have key := ih L Ω A (fun z hz => hcard z (hmemS z hz)) hΩ hA
    (fun a ha b hb hab => by
      have := hinv a (hmemS a ha) b (hmemS b hb) hab
      have hau : a ≠ u := fun e => hu (e ▸ ha)
      have hav : a ≠ v := fun e => hv (e ▸ ha)
      simpa [compTags, hau, hav] using this)
  have huS : u ∈ insert u (insert v S) := mem_insert_self _ _
  have hvS' : v ∈ insert u (insert v S) := mem_insert_of_mem hvS
  have h1 := hinv u huS v hvS' huv
  have h2 := hinv v hvS' u huS huv.symm
  have e1 : compTags R tg u v t₁ t₂ u v = t₁ := by simp [compTags]
  have e2 : compTags R tg u v t₁ t₂ v u = t₂ := by simp [compTags, Ne.symm hne]
  rw [e1] at h1
  rw [e2] at h2
  have hglue := hg (L u) (L v) (Ω u v) (Ω v u) (A u v) (A v u) (hcard u huS) (hcard v hvS')
    (hΩ u v) (hΩ v u) (hA u v) (hA v u) h1 h2
  -- the partition function
  set F : ℕ → ℝ := fun d => ∑ c ∈ L u, Ω v u d c * Ω u v c d * 1 with hF
  have hZ : ZG G (insert u (insert v S)) L (fun _ _ => 1) Ω
      = ZG G S L (fun _ _ => 1) Ω * ∑ d ∈ L v, ∑ c ∈ L u, Ω v u d c * Ω u v c d := by
    rw [ZG_insert_pendant G hu' hvS huv huniq,
      ← ZG_update_vertex G hvS L (fun _ _ => 1) Ω F, ZG_insert_isolated G hv hviso]
    congr 1
    · unfold ZG
      refine Finset.sum_congr rfl fun f _ => ?_
      congr 1
      refine Finset.prod_congr rfl fun z hz => ?_
      have : z ≠ v := fun e => hv (e ▸ hz)
      simp [this]
    · simp [hF]
  rw [hZ, ZG_const_insert_pendant G 3 hu' hvS huv huniq, ZG_const_insert_isolated G 3 hv hviso,
    prod_adjPairs_insert_pendant G hu' hvS huv huniq (fun p => A p.1 p.2),
    adjPairs_insert_isolated G hviso]
  have hP := Finset.prod_pos fun p (_ : p ∈ adjPairs G S) => hA p.1 p.2
  have hC := ZG_const_nonneg G 3 S
  have hAA := mul_pos (hA u v) (hA v u)
  calc ZG G S (fun _ => range 3) (fun _ _ => 1) neProfile * ((3 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) - 1)
        * (A u v * (A v u * ∏ p ∈ adjPairs G S, A p.1 p.2))
      = (ZG G S (fun _ => range 3) (fun _ _ => 1) neProfile * ∏ p ∈ adjPairs G S, A p.1 p.2)
        * (6 * (A u v * A v u)) := by push_cast; ring
    _ ≤ ZG G S L (fun _ _ => 1) Ω * ∑ d ∈ L v, ∑ c ∈ L u, Ω v u d c * Ω u v c d :=
        mul_le_mul key hglue (by positivity) ((mul_nonneg hC hP.le).trans key)

theorem tagBound_of_tagBuiltW {R : ClassSys}
    {rule : R.Tag → (m : ℕ) → (Fin (m + 1) → R.Tag) → Prop} {glue : R.Tag → R.Tag → Prop}
    {vrule : R.Tag → R.Tag → R.Tag → Prop}
    (hsound : ∀ t m τ, rule t m τ → R.RuleSound t m τ)
    (hglue : ∀ t₁ t₂, glue t₁ t₂ → R.GlueSound t₁ t₂)
    (hvert : ∀ t t₀ t₁, vrule t t₀ t₁ → R.VertexSound t t₀ t₁) (hswap : R.Transposable)
    {S : Finset V} {tg : V → V → R.Tag} (h : TagBuiltW G R rule glue vrule S tg) :
    TagBound G R S tg := by
  induction h with
  | edge u v huv t₁ t₂ hg => exact tagBound_edge huv (hglue _ _ hg)
  | face S tg m u v x he τ hr hS ih => exact tagBound_face hsound he hr ih
  | pendant S tg v y w hv hy hvy hw hwv huniq t₀ t₁ hr hS ih =>
    exact tagBound_pendant hv hy hvy hw hwv huniq (hvert _ _ _ hr) ih
  | swap S tg u v hu hv huv hS ih => exact tagBound_swap hswap hu hv huv ih
  | empty tg => exact tagBound_empty tg
  | iso S tg x hx h hS ih => exact tagBound_iso hx h ih
  | comp S tg u v hu hv huv hiso t₁ t₂ hg hS ih => exact tagBound_comp hu hv huv hiso (hglue _ _ hg) ih

variable (G)

/-- **Graphs built by ears, pendant edges and reorientations with sound rules are 3-ECC.** -/
theorem ecc_three_of_tagBuiltW {R : ClassSys}
    {rule : R.Tag → (m : ℕ) → (Fin (m + 1) → R.Tag) → Prop} {glue : R.Tag → R.Tag → Prop}
    {vrule : R.Tag → R.Tag → R.Tag → Prop}
    (hsound : ∀ t m τ, rule t m τ → R.RuleSound t m τ)
    (hglue : ∀ t₁ t₂, glue t₁ t₂ → R.GlueSound t₁ t₂)
    (hvert : ∀ t t₀ t₁, vrule t t₀ t₁ → R.VertexSound t t₀ t₁) (hswap : R.Transposable)
    {tg : V → V → R.Tag} (h : TagBuiltW G R rule glue vrule univ tg) : G.ECCAt 3 := by
  intro L hL
  have key := tagBound_of_tagBuiltW hsound hglue hvert hswap h L neProfile (fun _ _ => 1)
    (fun x _ => hL x) (fun _ _ c d => by unfold neProfile; split_ifs <;> norm_num)
    (fun _ _ => one_pos)
    (fun a _ b _ _ => R.of_dom _ _ _ _ _ zero_le_one (dominant_ne (L a) (L b)))
  rw [Finset.prod_const_one, mul_one, ZG_univ_eq_col, ZG_univ_eq_col] at key
  have key' : (G.colConst 3 : ℝ) ≤ (G.col L : ℝ) := key
  exact_mod_cast key'

end Outerplanar
