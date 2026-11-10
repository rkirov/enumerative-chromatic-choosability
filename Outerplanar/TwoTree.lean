/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.SixFamily
import Outerplanar.Seed
import Mathlib.Tactic.IntervalCases

/-!
# A 2-tree as the seed of the graph induction, at three colours

`TwoTreeOn G S` says that the induced subgraph on `S` is a 2-tree: it is built from an edge by
repeatedly adding a vertex joined to exactly the two ends of an existing edge (the same edge may
be used again, so books of triangles are included, and so are all triangulated polygons).

The weighted lower bound `ZGBound G 3` holds on a 2-tree (`zgBound_twoTree`). The proof is the
*six-family*: for lists of three colours there are six proper list colourings that are matched
on every edge (`Matched`, `sixFam_of_twoTree`), so that they are distinct and every colour of
every list is used by exactly two of them. It is carried along the construction by
`Matched.extend`. The pair profiles are bounded below by their rank-one minorants, whose
factors have product one on the lists and so disappear from the product of the six weights;
the arithmetic–geometric mean inequality on the six colourings then gives six times the
geometric means, and a 2-tree has exactly six proper colourings from three colours
(`ZG_const_twoTree`).

With `ZG_ge_from` this allows any 2-tree — any number of triangles, as long as they form one
triangulated region — in a graph built by pendant vertices and ears of at least two vertices on
edges. This is a result of this repository's 2026-11 AI research collaboration; the paper proof
is the section "Fourth pass" of `ai_research_notes/OUTERPLANAR_K3_TRIANGLES_2026-11-10.md`.
-/

set_option linter.unusedSectionVars false

namespace Outerplanar

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The induced subgraph on `S` is a 2-tree: an edge, then vertices joined to exactly the two
ends of an existing edge. -/
inductive TwoTreeOn : Finset V → Prop
  | edge (u w : V) (h : G.Adj u w) : TwoTreeOn {u, w}
  | add (S : Finset V) (v u w : V) (hv : v ∉ S) (hu : u ∈ S) (hw : w ∈ S) (huw : G.Adj u w)
      (hS : TwoTreeOn S) (hnb : ∀ y ∈ S, G.Adj v y ↔ y = u ∨ y = w) : TwoTreeOn (insert v S)

variable {G}

theorem TwoTreeOn.exists_edge {S : Finset V} (h : TwoTreeOn G S) :
    ∃ u ∈ S, ∃ w ∈ S, G.Adj u w := by
  cases h with
  | edge u w huw => exact ⟨u, by simp, w, by simp, huw⟩
  | add S v u w hv hu hw huw hS hnb =>
    exact ⟨u, mem_insert_of_mem hu, w, mem_insert_of_mem hw, huw⟩

theorem TwoTreeOn.exists_adj {S : Finset V} (h : TwoTreeOn G S) :
    ∀ x ∈ S, ∃ y ∈ S, G.Adj x y := by
  induction h with
  | edge u w huw =>
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact ⟨w, by simp, huw⟩
    · rw [mem_singleton] at hx
      subst hx
      exact ⟨u, by simp, huw.symm⟩
  | add S v u w hv hu hw huw hS hnb ih =>
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact ⟨u, mem_insert_of_mem hu, (hnb u hu).mpr (Or.inl rfl)⟩
    · obtain ⟨y, hy, hxy⟩ := ih x hx
      exact ⟨y, mem_insert_of_mem hy, hxy⟩

/-! ### Adding a vertex on an edge -/

section AddVertex

variable {S : Finset V} {v u w : V} (hv : v ∉ S) (hu : u ∈ S) (hw : w ∈ S) (huw : G.Adj u w)
  (hnb : ∀ y ∈ S, G.Adj v y ↔ y = u ∨ y = w)

include hu hw hnb in
theorem adjPairs_insert_two :
    adjPairs G (insert v S)
      = insert (v, u) (insert (u, v) (insert (v, w) (insert (w, v) (adjPairs G S)))) := by
  ext ⟨a, b⟩
  simp only [mem_adjPairs, mem_insert, Prod.mk.injEq]
  constructor
  · rintro ⟨ha | ha, hb | hb, hab⟩
    · subst ha; subst hb; exact absurd rfl hab.ne
    · subst ha
      rcases (hnb b hb).mp hab with h | h
      · exact Or.inl ⟨rfl, h⟩
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))
    · subst hb
      rcases (hnb a ha).mp hab.symm with h | h
      · exact Or.inr (Or.inl ⟨h, rfl⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ha, hb, hab⟩)))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨ha, hb, hab⟩)
    · exact ⟨Or.inl rfl, Or.inr hu, (hnb _ hu).mpr (Or.inl rfl)⟩
    · exact ⟨Or.inr hu, Or.inl rfl, ((hnb _ hu).mpr (Or.inl rfl)).symm⟩
    · exact ⟨Or.inl rfl, Or.inr hw, (hnb _ hw).mpr (Or.inr rfl)⟩
    · exact ⟨Or.inr hw, Or.inl rfl, ((hnb _ hw).mpr (Or.inr rfl)).symm⟩
    · exact ⟨Or.inr ha, Or.inr hb, hab⟩

include hv hu hw huw hnb in
theorem prod_adjPairs_insert_two (g : V × V → ℝ) :
    ∏ p ∈ adjPairs G (insert v S), g p
      = g (v, u) * (g (u, v) * (g (v, w) * (g (w, v) * ∏ p ∈ adjPairs G S, g p))) := by
  have hvu : v ≠ u := fun h => hv (h ▸ hu)
  have hvw : v ≠ w := fun h => hv (h ▸ hw)
  have huw' : u ≠ w := huw.ne
  have h1 : (v, u) ∉ insert (u, v) (insert (v, w) (insert (w, v) (adjPairs G S))) := by
    simp [mem_adjPairs, hvu, hvw, huw', hv]
  have h2 : (u, v) ∉ insert (v, w) (insert (w, v) (adjPairs G S)) := by
    simp [mem_adjPairs, hvu.symm, hvw, huw', hv]
  have h3 : (v, w) ∉ insert (w, v) (adjPairs G S) := by
    simp [mem_adjPairs, hvw, hv]
  have h4 : (w, v) ∉ adjPairs G S := by
    simp [mem_adjPairs, hv]
  rw [adjPairs_insert_two hu hw hnb, Finset.prod_insert h1, Finset.prod_insert h2,
    Finset.prod_insert h3, Finset.prod_insert h4]

include hv hu hw huw hnb in
theorem term_update_two (ω : V → ℕ → ℝ) (Ω : V → V → ℕ → ℕ → ℝ) (f : V → ℕ) (c : ℕ) :
    term G (insert v S) ω Ω (Function.update f v c)
      = term G S ω Ω f * ((Ω v u c (f u) * Ω u v (f u) c * (Ω v w c (f w) * Ω w v (f w) c))
          * ω v c) := by
  have huv : u ≠ v := fun h => hv (h ▸ hu)
  have hwv : w ≠ v := fun h => hv (h ▸ hw)
  unfold term
  rw [Finset.prod_insert hv, prod_adjPairs_insert_two hv hu hw huw hnb
      (fun p => Ω p.1 p.2 (Function.update f v c p.1) (Function.update f v c p.2)),
    prod_update_of_notMem hv, prod_adjPairs_update_of_notMem G hv]
  simp only [Function.update_self, Function.update_of_ne huv, Function.update_of_ne hwv]
  ring

theorem sum_ne_two (v u w : V) {x y : ℕ} (hx : x ∈ range 3) (hy : y ∈ range 3) (hxy : x ≠ y) :
    ∑ c ∈ range 3, ((neProfile v u c x * neProfile u v x c
      * (neProfile v w c y * neProfile w v y c)) * (1 : ℝ)) = 1 := by
  rw [mem_range] at hx hy
  interval_cases x <;> interval_cases y <;> simp_all [neProfile, Finset.sum_range_succ]

include hv hu hw huw hnb in
/-- Adding a vertex on an edge does not change the number of proper colourings from three
colours. -/
theorem ZG_const_insert_two :
    ZG G (insert v S) (fun _ => range 3) (fun _ _ => 1) neProfile
      = ZG G S (fun _ => range 3) (fun _ _ => 1) neProfile := by
  rw [ZG_eq_sum_term, sum_assignments_insert hv, ZG_eq_sum_term]
  refine Finset.sum_congr rfl fun f hf => ?_
  simp only [term_update_two hv hu hw huw hnb]
  rw [← Finset.mul_sum]
  by_cases hfe : f u = f w
  · have h0 : term G S (fun _ _ => 1) neProfile f = 0 := by
      unfold term
      rw [mul_eq_zero]
      right
      exact Finset.prod_eq_zero (i := (u, w)) ((mem_adjPairs G).mpr ⟨hu, hw, huw⟩)
        (by simp [neProfile, hfe])
    rw [h0, zero_mul]
  · rw [sum_ne_two v u w ((mem_assignments.mp hf).1 u hu) ((mem_assignments.mp hf).1 w hw) hfe,
      mul_one]

end AddVertex

variable (G) in
theorem ZG_const_edge {u w : V} (huw : G.Adj u w) :
    ZG G {u, w} (fun _ => range 3) (fun _ _ => 1) neProfile = 6 := by
  have hw : ({w} : Finset V) = insert w ∅ := by simp
  rw [ZG_const_insert_pendant G 3 (x := u) (y := w) (S := {w}) (by simp [huw.ne])
      (by simp) huw (fun z hz _ => mem_singleton.mp hz), hw,
    ZG_const_insert_isolated G 3 (Finset.notMem_empty w)
      (fun z hz => absurd hz (Finset.notMem_empty z)), ZG_empty]
  norm_num

/-- A 2-tree has six proper colourings from three colours. -/
theorem ZG_const_twoTree {S : Finset V} (h : TwoTreeOn G S) :
    ZG G S (fun _ => range 3) (fun _ _ => 1) neProfile = 6 := by
  induction h with
  | edge u w huw => exact ZG_const_edge G huw
  | add S v u w hv hu hw huw hS hnb ih => rw [ZG_const_insert_two hv hu hw huw hnb, ih]

/-! ### The six-family -/

variable (G) in
/-- Six proper list colourings of `S`, matched on every edge. -/
def SixFam (S : Finset V) (L : V → Finset ℕ) : Prop :=
  ∃ f : Fin 6 → V → ℕ, (∀ i, f i ∈ assignments S L) ∧
    (∀ i, ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → f i x ≠ f i y) ∧
    ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → Matched (L x) (L y) (fun i => f i x) (fun i => f i y)

/-- **The six-family of a 2-tree.** -/
theorem sixFam_of_twoTree (L : V → Finset ℕ) {S : Finset V} (h : TwoTreeOn G S) :
    (∀ x ∈ S, (L x).card = 3) → SixFam G S L := by
  induction h with
  | edge u w huw =>
    intro hL
    obtain ⟨p, q, hp, hq, hpq, hM⟩ := exists_matched (hL u (by simp)) (hL w (by simp))
    obtain ⟨f, hfu, hfw, hf0⟩ : ∃ f : Fin 6 → V → ℕ, (∀ i, f i u = p i) ∧ (∀ i, f i w = q i) ∧
        ∀ i z, z ≠ u → z ≠ w → f i z = 0 :=
      ⟨fun i z => if z = u then p i else if z = w then q i else 0, by simp,
        by simp [huw.ne'], by intro i z h1 h2; simp [h1, h2]⟩
    have hMu : Matched (L u) (L w) (fun i => f i u) (fun i => f i w) := by
      rw [funext hfu, funext hfw]
      exact hM
    refine ⟨f, fun i => mem_assignments.mpr ⟨fun z hz => ?_, fun z hz => ?_⟩,
      fun i x hx y hy hxy => ?_, fun x hx y hy hxy => ?_⟩
    · rcases mem_insert.mp hz with rfl | hz
      · rw [hfu]; exact hp i
      · rw [mem_singleton] at hz
        subst hz
        rw [hfw]; exact hq i
    · rw [mem_insert, mem_singleton, not_or] at hz
      exact hf0 i z hz.1 hz.2
    · rw [mem_insert, mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy.ne
      · rw [hfu, hfw]; exact hpq i
      · rw [hfu, hfw]; exact (hpq i).symm
      · exact absurd rfl hxy.ne
    · rw [mem_insert, mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy.ne
      · exact hMu
      · exact hMu.symm
      · exact absurd rfl hxy.ne
  | add S v u w hv hu hw huw hS hnb ih =>
    intro hL
    obtain ⟨f, hfa, hfp, hfm⟩ := ih fun x hx => hL x (mem_insert_of_mem hx)
    obtain ⟨g, hgm, hgu, hgw, hMu, hMw⟩ := Matched.extend (hL v (mem_insert_self v S))
      (fun i => hfp i u hu w hw huw) (hfm u hu w hw huw)
    obtain ⟨f', hf'⟩ : ∃ f' : Fin 6 → V → ℕ, ∀ i, f' i = Function.update (f i) v (g i) :=
      ⟨_, fun _ => rfl⟩
    have hold : ∀ i, ∀ x ∈ S, f' i x = f i x := fun i x hx => by
      rw [hf', Function.update_of_ne (ne_of_mem_of_not_mem hx hv)]
    have hnew : ∀ i, f' i v = g i := fun i => by rw [hf', Function.update_self]
    have holdf : ∀ x ∈ S, (fun i => f' i x) = fun i => f i x :=
      fun x hx => funext fun i => hold i x hx
    have hnewf : (fun i => f' i v) = g := funext hnew
    refine ⟨f',
      fun i => mem_assignments.mpr ⟨fun z hz => ?_, fun z hz => ?_⟩,
      fun i x hx y hy hxy => ?_, fun x hx y hy hxy => ?_⟩
    · rcases mem_insert.mp hz with rfl | hz
      · rw [hnew]; exact hgm i
      · rw [hold i z hz]; exact (mem_assignments.mp (hfa i)).1 z hz
    · rw [mem_insert, not_or] at hz
      rw [hf', Function.update_of_ne hz.1]
      exact (mem_assignments.mp (hfa i)).2 z hz.2
    · rcases mem_insert.mp hx with rfl | hx' <;> rcases mem_insert.mp hy with rfl | hy'
      · exact absurd rfl hxy.ne
      · rw [hnew, hold i y hy']
        rcases (hnb y hy').mp hxy with rfl | rfl
        · exact hgu i
        · exact hgw i
      · rw [hnew, hold i x hx']
        rcases (hnb x hx').mp hxy.symm with rfl | rfl
        · exact (hgu i).symm
        · exact (hgw i).symm
      · rw [hold i x hx', hold i y hy']
        exact hfp i x hx' y hy' hxy
    · rcases mem_insert.mp hx with rfl | hx' <;> rcases mem_insert.mp hy with rfl | hy'
      · exact absurd rfl hxy.ne
      · rw [hnewf, holdf y hy']
        rcases (hnb y hy').mp hxy with rfl | rfl
        · exact hMu
        · exact hMw
      · rw [hnewf, holdf x hx']
        rcases (hnb x hx').mp hxy.symm with rfl | rfl
        · exact hMu.symm
        · exact hMw.symm
      · rw [holdf x hx', holdf y hy']
        exact hfm x hx' y hy' hxy

/-! ### The weighted lower bound on a 2-tree -/

/-- The arithmetic–geometric mean inequality for six positive numbers whose product is a sixth
power. -/
theorem six_mul_le_sum {t : Fin 6 → ℝ} (ht : ∀ i, 0 < t i) {P : ℝ} (hP : 0 < P)
    (h : ∏ i, t i = P ^ 6) : 6 * P ≤ ∑ i, t i := by
  obtain ⟨v, hv⟩ : ∃ v : ℕ → ℝ, ∀ j, v j = if h : j < 6 then t ⟨j, h⟩ else 1 :=
    ⟨_, fun _ => rfl⟩
  have hvi : ∀ i : Fin 6, v i = t i := fun i => by simp [hv]
  have hvpos : ∀ c ∈ range 6, 0 < v c := fun c _ => by
    rw [hv]
    split_ifs
    · exact ht _
    · exact one_pos
  have ham := card_mul_gmean_le_sum (F := range 6) (v := v) ⟨0, by simp⟩ hvpos
  have hpow := gmean_pow (F := range 6) (v := v) ⟨0, by simp⟩ hvpos
  rw [card_range] at ham hpow
  rw [← Fin.prod_univ_eq_prod_range, Finset.prod_congr rfl fun i _ => hvi i, h] at hpow
  have hg : gmean (range 6) v = P :=
    (pow_left_inj₀ (gmean_pos _ _).le hP.le (by norm_num)).mp hpow
  rw [hg, ← Fin.sum_univ_eq_sum_range, Finset.sum_congr rfl fun i _ => hvi i] at ham
  exact_mod_cast ham

/-- **The seed bound**: the weighted lower bound for three colours holds on a 2-tree. -/
theorem zgBound_twoTree {S : Finset V} (h : TwoTreeOn G S) : ZGBound G 3 S := by
  intro L ω Ω A hcard hω hΩ hA hpot
  obtain ⟨f, hfa, hfp, hfm⟩ := sixFam_of_twoTree L h hcard
  have hfL : ∀ i, ∀ x ∈ S, f i x ∈ L x := fun i => (mem_assignments.mp (hfa i)).1
  -- every colour of every list is used twice, and the six colourings are distinct
  have hbal : ∀ x ∈ S, ∀ F : ℕ → ℝ, ∏ i, F (f i x) = (∏ c ∈ L x, F c) ^ 2 := by
    intro x hx F
    obtain ⟨y, hy, hxy⟩ := h.exists_adj x hx
    exact (hfm x hx y hy hxy).prod_left (hcard x hx) F
  have hfinj : Function.Injective f := by
    obtain ⟨u, hu, w, hw, huw⟩ := h.exists_edge
    intro i i' e
    exact (hfm u hu w hw huw).injective (congrFun e u) (congrFun e w)
  -- the potentials of the ordered pairs
  have hex : ∀ x y, ∃ a b : ℕ → ℝ, (x ∈ S ∧ y ∈ S ∧ G.Adj x y) →
      ((∀ c ∈ L x, 0 < a c) ∧ (∀ d ∈ L y, 0 < b d) ∧ ∏ c ∈ L x, a c = 1 ∧
        ∏ d ∈ L y, b d = 1 ∧
        ∀ c ∈ L x, ∀ d ∈ L y, c ≠ d → A x y * (a c * b d) ≤ Ω x y c d) := by
    intro x y
    by_cases hxy : x ∈ S ∧ y ∈ S ∧ G.Adj x y
    · obtain ⟨a, b, hab⟩ := hpot x hxy.1 y hxy.2.1 hxy.2.2
      exact ⟨a, b, fun _ => hab⟩
    · exact ⟨fun _ => 1, fun _ => 1, fun h => absurd h hxy⟩
  choose a b hab using hex
  -- the six rank-one terms
  obtain ⟨t, ht⟩ : ∃ t : Fin 6 → ℝ, ∀ i, t i = (∏ x ∈ S, ω x (f i x)) *
      ∏ p ∈ adjPairs G S, (a p.1 p.2 (f i p.1) * b p.1 p.2 (f i p.2)) := ⟨_, fun _ => rfl⟩
  have hωpos : ∀ i, 0 < ∏ x ∈ S, ω x (f i x) := fun i =>
    Finset.prod_pos fun x hx => hω x hx _ (hfL i x hx)
  have habpos : ∀ i, ∀ p ∈ adjPairs G S,
      0 < a p.1 p.2 (f i p.1) * b p.1 p.2 (f i p.2) := by
    intro i p hp
    have hp' := (mem_adjPairs G).mp hp
    obtain ⟨h1, h2, -⟩ := hab p.1 p.2 hp'
    exact mul_pos (h1 _ (hfL i _ hp'.1)) (h2 _ (hfL i _ hp'.2.1))
  have htpos : ∀ i, 0 < t i := fun i => by
    rw [ht]
    exact mul_pos (hωpos i) (Finset.prod_pos (habpos i))
  have hgpos : 0 < ∏ x ∈ S, gmean (L x) (ω x) := Finset.prod_pos fun x _ => gmean_pos _ _
  -- their product: the potentials cancel
  have hprod : ∏ i, t i = (∏ x ∈ S, gmean (L x) (ω x)) ^ 6 := by
    have e1 : ∏ i, ∏ x ∈ S, ω x (f i x) = (∏ x ∈ S, gmean (L x) (ω x)) ^ 6 := by
      rw [Finset.prod_comm, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun x hx => ?_
      rw [hbal x hx (ω x),
        ← gmean_pow (card_pos.mp (by rw [hcard x hx]; norm_num)) (hω x hx), hcard x hx]
      ring
    have e2 : ∏ i, ∏ p ∈ adjPairs G S, (a p.1 p.2 (f i p.1) * b p.1 p.2 (f i p.2)) = 1 := by
      rw [Finset.prod_comm]
      refine Finset.prod_eq_one fun p hp => ?_
      have hp' := (mem_adjPairs G).mp hp
      obtain ⟨-, -, h3, h4, -⟩ := hab p.1 p.2 hp'
      rw [Finset.prod_mul_distrib, hbal p.1 hp'.1 (a p.1 p.2), hbal p.2 hp'.2.1 (b p.1 p.2),
        h3, h4]
      norm_num
    rw [Finset.prod_congr rfl fun i _ => ht i, Finset.prod_mul_distrib, e1, e2, mul_one]
  have hsum := six_mul_le_sum htpos hgpos hprod
  -- each of the six colourings dominates its rank-one term
  have hAnn : 0 ≤ ∏ p ∈ adjPairs G S, A p.1 p.2 := Finset.prod_nonneg fun p _ => (hA _ _).le
  have hterm : ∀ i, (∏ p ∈ adjPairs G S, A p.1 p.2) * t i ≤ term G S ω Ω (f i) := by
    intro i
    have hle : ∏ p ∈ adjPairs G S, A p.1 p.2 * (a p.1 p.2 (f i p.1) * b p.1 p.2 (f i p.2))
        ≤ ∏ p ∈ adjPairs G S, Ω p.1 p.2 (f i p.1) (f i p.2) := by
      refine Finset.prod_le_prod₀ (fun p hp => (mul_pos (hA _ _) (habpos i p hp)).le)
        fun p hp => ?_
      have hp' := (mem_adjPairs G).mp hp
      exact (hab p.1 p.2 hp').2.2.2.2 _ (hfL i _ hp'.1) _ (hfL i _ hp'.2.1)
        (hfp i _ hp'.1 _ hp'.2.1 hp'.2.2)
    rw [Finset.prod_mul_distrib] at hle
    rw [ht]
    unfold term
    calc (∏ p ∈ adjPairs G S, A p.1 p.2) * ((∏ x ∈ S, ω x (f i x)) *
          ∏ p ∈ adjPairs G S, (a p.1 p.2 (f i p.1) * b p.1 p.2 (f i p.2)))
        = (∏ x ∈ S, ω x (f i x)) * ((∏ p ∈ adjPairs G S, A p.1 p.2) *
          ∏ p ∈ adjPairs G S, (a p.1 p.2 (f i p.1) * b p.1 p.2 (f i p.2))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hle (hωpos i).le
  rw [ZG_const_twoTree h, ZG_eq_sum_term]
  calc 6 * (∏ x ∈ S, gmean (L x) (ω x)) * ∏ p ∈ adjPairs G S, A p.1 p.2
      ≤ (∏ p ∈ adjPairs G S, A p.1 p.2) * ∑ i, t i := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left hsum hAnn
    _ = ∑ i, (∏ p ∈ adjPairs G S, A p.1 p.2) * t i := Finset.mul_sum _ _ _
    _ ≤ ∑ i, term G S ω Ω (f i) := Finset.sum_le_sum fun i _ => hterm i
    _ = ∑ F ∈ univ.image f, term G S ω Ω F :=
        (Finset.sum_image fun i _ j _ e => hfinj e).symm
    _ ≤ ∑ F ∈ assignments S L, term G S ω Ω F := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun F hF => ?_) fun F hF _ => ?_
        · obtain ⟨i, -, rfl⟩ := mem_image.mp hF
          exact hfa i
        · have hF' := mem_assignments.mp hF
          exact mul_nonneg (Finset.prod_nonneg fun x hx => (hω x hx _ (hF'.1 x hx)).le)
            (Finset.prod_nonneg fun p _ => hΩ _ _ _ _)

end Outerplanar
