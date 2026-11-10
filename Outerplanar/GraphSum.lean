/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.GraphDefs
import Outerplanar.FaceDefs

/-!
# The graph induction of the outerplanar ECC proof: sums over assignments

This file is part of the graph induction of the outerplanar ECC proof, a result of this
repository's 2026-11 AI research collaboration. It contains the bookkeeping identities for the
weighted partition function `ZG`:

* `sum_assignments_insert`, `sum_assignments_union` — splitting a sum over the assignments of a
  vertex set when one new vertex, or an injective family of new vertices, is added;
* `ZG_insert_isolated`, `ZG_insert_pendant` — adding a vertex with no, or with exactly one,
  neighbour among the old vertices;
* `ZG_ear` — adding an ear on an edge: the ear acts as the pair profile `faceSum` on that edge;
* `ZG_update_vertex`, `ZG_update_pair` — absorbing a factor into a vertex weight or into the
  profile of one ordered pair.
-/

set_option linter.unusedSectionVars false

namespace Outerplanar

open Finset

section Generic

theorem prod_mul_at {α M : Type*} [DecidableEq α] [CommMonoid M] (s : Finset α) {p₀ : α}
    (h : p₀ ∈ s) (g : α → M) (w : M) :
    ∏ p ∈ s, (if p = p₀ then g p * w else g p) = (∏ p ∈ s, g p) * w := by
  have h1 : ∀ p ∈ s, (if p = p₀ then g p * w else g p) = g p * (if p = p₀ then w else 1) := by
    intro p _
    split_ifs <;> simp
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_ite_eq', ite_eq_left h]

variable {α : Type*} {m : ℕ}

theorem consSnoc_zero (a b : α) (g : Fin m → α) (i : Fin (m + 2)) (h : i.val = 0) :
    (Fin.cons a (Fin.snoc g b) : Fin (m + 2) → α) i = a := by
  obtain rfl : i = 0 := Fin.ext h
  simp

theorem consSnoc_last (a b : α) (g : Fin m → α) (i : Fin (m + 2)) (h : i.val = m + 1) :
    (Fin.cons a (Fin.snoc g b) : Fin (m + 2) → α) i = b := by
  obtain rfl : i = Fin.succ (Fin.last m) := Fin.ext (by simp [h])
  simp

theorem consSnoc_mid (a b : α) (g : Fin m → α) (i : Fin (m + 2)) (j : Fin m)
    (h : i.val = j.val + 1) : (Fin.cons a (Fin.snoc g b) : Fin (m + 2) → α) i = g j := by
  obtain rfl : i = Fin.succ (Fin.castSucc j) := Fin.ext (by simp [h])
  simp

end Generic

variable {V : Type} [Fintype V] [DecidableEq V]

theorem mem_assignments {S : Finset V} {L : V → Finset ℕ} {f : V → ℕ} :
    f ∈ assignments S L ↔ (∀ z ∈ S, f z ∈ L z) ∧ ∀ z, z ∉ S → f z = 0 := by
  simp only [assignments, Fintype.mem_piFinset]
  constructor
  · intro h
    exact ⟨fun z hz => by simpa [hz] using h z, fun z hz => by simpa [hz] using h z⟩
  · rintro ⟨h1, h2⟩ z
    by_cases hz : z ∈ S
    · simpa [hz] using h1 z hz
    · simpa [hz] using h2 z hz

/-- Splitting off one new vertex. -/
theorem sum_assignments_insert {S : Finset V} {x : V} (hx : x ∉ S) (L : V → Finset ℕ)
    (Φ : (V → ℕ) → ℝ) :
    ∑ F ∈ assignments (insert x S) L, Φ F
      = ∑ f ∈ assignments S L, ∑ c ∈ L x, Φ (Function.update f x c) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun p => Function.update p.1 x p.2)
    (fun F => (Function.update F x 0, F x)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨f, c⟩ hp
    rw [mem_product, mem_assignments] at hp
    obtain ⟨⟨h1, h2⟩, hc⟩ := hp
    rw [mem_assignments]
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · by_cases hzx : z = x
      · subst hzx; simpa using hc
      · rw [Function.update_of_ne hzx]
        exact h1 z ((mem_insert.mp hz).resolve_left hzx)
    · rw [mem_insert, not_or] at hz
      rw [Function.update_of_ne hz.1]
      exact h2 z hz.2
  · intro F hF
    rw [mem_assignments] at hF
    obtain ⟨h1, h2⟩ := hF
    rw [mem_product, mem_assignments]
    refine ⟨⟨fun z hz => ?_, fun z hz => ?_⟩, h1 x (mem_insert_self x S)⟩
    · have hzx : z ≠ x := fun h => hx (h ▸ hz)
      simp only [Function.update_of_ne hzx]
      exact h1 z (mem_insert_of_mem hz)
    · by_cases hzx : z = x
      · subst hzx; simp
      · simp only [Function.update_of_ne hzx]
        exact h2 z (by simp [hzx, hz])
  · rintro ⟨f, c⟩ hp
    rw [mem_product, mem_assignments] at hp
    have hfx : f x = 0 := hp.1.2 x hx
    refine Prod.ext ?_ (by simp)
    simp only [Function.update_idem]
    rw [← hfx, Function.update_eq_self]
  · intro F _
    simp
  · intro p _
    rfl

/-- Splitting off an injective family of new vertices. -/
theorem sum_assignments_union {ι : Type} [Fintype ι] [DecidableEq ι] {S : Finset V} {e : ι → V}
    (he : Function.Injective e) (heS : ∀ i, e i ∉ S) (L : V → Finset ℕ) (Φ : (V → ℕ) → ℝ) :
    ∑ F ∈ assignments (S ∪ univ.image e) L, Φ F
      = ∑ f ∈ assignments S L, ∑ h ∈ Fintype.piFinset (fun i => L (e i)),
          Φ (Function.extend e h f) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun p => Function.extend e p.2 p.1)
    (fun F => (fun z => if z ∈ S then F z else 0, F ∘ e)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨f, h⟩ hp
    rw [mem_product, mem_assignments, Fintype.mem_piFinset] at hp
    obtain ⟨⟨h1, h2⟩, hh⟩ := hp
    rw [mem_assignments]
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · by_cases hze : ∃ i, e i = z
      · obtain ⟨i, rfl⟩ := hze
        simp only [he.extend_apply]
        exact hh i
      · simp only [Function.extend_apply' _ _ _ hze]
        rcases mem_union.mp hz with hz | hz
        · exact h1 z hz
        · obtain ⟨i, _, rfl⟩ := mem_image.mp hz
          exact absurd ⟨i, rfl⟩ hze
    · have hze : ¬ ∃ i, e i = z := by
        rintro ⟨i, rfl⟩
        exact hz (mem_union_right _ (mem_image_of_mem _ (mem_univ i)))
      simp only [Function.extend_apply' _ _ _ hze]
      exact h2 z fun hzS => hz (mem_union_left _ hzS)
  · intro F hF
    rw [mem_assignments] at hF
    obtain ⟨h1, h2⟩ := hF
    rw [mem_product, mem_assignments, Fintype.mem_piFinset]
    refine ⟨⟨fun z hz => ?_, fun z hz => ?_⟩, fun i => ?_⟩
    · simp only [ite_eq_left hz]
      exact h1 z (mem_union_left _ hz)
    · simp only [ite_eq_right hz]
    · exact h1 (e i) (mem_union_right _ (mem_image_of_mem _ (mem_univ i)))
  · rintro ⟨f, h⟩ hp
    rw [mem_product, mem_assignments] at hp
    refine Prod.ext ?_ ?_
    · funext z
      by_cases hz : z ∈ S
      · have hze : ¬ ∃ i, e i = z := by
          rintro ⟨i, rfl⟩
          exact heS i hz
        simp only [ite_eq_left hz, Function.extend_apply' _ _ _ hze]
      · simp only [ite_eq_right hz]
        exact (hp.1.2 z hz).symm
    · funext i
      simp only [Function.comp_apply, he.extend_apply]
  · intro F hF
    rw [mem_assignments] at hF
    funext z
    by_cases hze : ∃ i, e i = z
    · obtain ⟨i, rfl⟩ := hze
      simp only [he.extend_apply, Function.comp_apply]
    · simp only [Function.extend_apply' _ _ _ hze]
      by_cases hz : z ∈ S
      · simp only [ite_eq_left hz]
      · simp only [ite_eq_right hz]
        refine (hF.2 z fun hzU => ?_).symm
        rcases mem_union.mp hzU with h | h
        · exact hz h
        · obtain ⟨i, _, rfl⟩ := mem_image.mp h
          exact hze ⟨i, rfl⟩
  · intro p _
    rfl

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem mem_adjPairs {S : Finset V} {p : V × V} :
    p ∈ adjPairs G S ↔ p.1 ∈ S ∧ p.2 ∈ S ∧ G.Adj p.1 p.2 := by
  simp only [adjPairs, mem_filter, mem_product, and_assoc]

/-- The weight of one assignment. -/
noncomputable def term (S : Finset V) (ω : V → ℕ → ℝ) (Ω : V → V → ℕ → ℕ → ℝ) (f : V → ℕ) : ℝ :=
  (∏ z ∈ S, ω z (f z)) * ∏ p ∈ adjPairs G S, Ω p.1 p.2 (f p.1) (f p.2)

theorem ZG_eq_sum_term (S : Finset V) (L : V → Finset ℕ) (ω : V → ℕ → ℝ)
    (Ω : V → V → ℕ → ℕ → ℝ) : ZG G S L ω Ω = ∑ f ∈ assignments S L, term G S ω Ω f := rfl

/-! ### Absorbing a factor into a weight or into a profile -/

theorem ZG_update_vertex {S : Finset V} {y : V} (hy : y ∈ S) (L : V → Finset ℕ)
    (ω : V → ℕ → ℝ) (Ω : V → V → ℕ → ℕ → ℝ) (F : ℕ → ℝ) :
    ZG G S L (fun z => if z = y then fun d => ω y d * F d else ω z) Ω
      = ∑ f ∈ assignments S L, term G S ω Ω f * F (f y) := by
  rw [ZG_eq_sum_term]
  refine Finset.sum_congr rfl fun f _ => ?_
  unfold term
  have h1 : ∏ z ∈ S, (if z = y then fun d => ω y d * F d else ω z) (f z)
      = (∏ z ∈ S, ω z (f z)) * F (f y) := by
    rw [← prod_mul_at S hy (fun z => ω z (f z)) (F (f y))]
    refine Finset.prod_congr rfl fun z _ => ?_
    by_cases hz : z = y
    · subst hz; simp
    · simp [hz]
  rw [h1]
  ring

theorem ZG_update_pair {S : Finset V} {u v : V} (huv : (u, v) ∈ adjPairs G S)
    (L : V → Finset ℕ) (ω : V → ℕ → ℝ) (Ω : V → V → ℕ → ℕ → ℝ) (F : ℕ → ℕ → ℝ) :
    ZG G S L ω (fun a b => if a = u ∧ b = v then fun c d => Ω u v c d * F c d else Ω a b)
      = ∑ f ∈ assignments S L, term G S ω Ω f * F (f u) (f v) := by
  rw [ZG_eq_sum_term]
  refine Finset.sum_congr rfl fun f _ => ?_
  unfold term
  have h1 : ∏ p ∈ adjPairs G S,
        (if p.1 = u ∧ p.2 = v then fun c d => Ω u v c d * F c d else Ω p.1 p.2) (f p.1) (f p.2)
      = (∏ p ∈ adjPairs G S, Ω p.1 p.2 (f p.1) (f p.2)) * F (f u) (f v) := by
    rw [← prod_mul_at (adjPairs G S) huv (fun p => Ω p.1 p.2 (f p.1) (f p.2)) (F (f u) (f v))]
    refine Finset.prod_congr rfl fun p _ => ?_
    by_cases hp : p = (u, v)
    · subst hp; simp
    · have hp' : ¬ (p.1 = u ∧ p.2 = v) := fun h => hp (Prod.ext h.1 h.2)
      rw [ite_eq_right hp', ite_eq_right hp]
  rw [h1]
  ring

/-- The same, for a product of constants over the ordered pairs. -/
theorem prod_adjPairs_update {S : Finset V} {u v : V} (huv : (u, v) ∈ adjPairs G S)
    (A : V → V → ℝ) (C : ℝ) :
    ∏ p ∈ adjPairs G S, (fun a b => if a = u ∧ b = v then A u v * C else A a b) p.1 p.2
      = (∏ p ∈ adjPairs G S, A p.1 p.2) * C := by
  rw [← prod_mul_at (adjPairs G S) huv (fun p => A p.1 p.2) C]
  refine Finset.prod_congr rfl fun p _ => ?_
  by_cases hp : p = (u, v)
  · subst hp; simp
  · have hp' : ¬ (p.1 = u ∧ p.2 = v) := fun h => hp (Prod.ext h.1 h.2)
    simp only [ite_eq_right hp', ite_eq_right hp]

/-! ### Adding one vertex -/

theorem adjPairs_insert_isolated {S : Finset V} {x : V} (h : ∀ z ∈ S, ¬ G.Adj x z) :
    adjPairs G (insert x S) = adjPairs G S := by
  ext ⟨a, b⟩
  simp only [mem_adjPairs, mem_insert]
  constructor
  · rintro ⟨ha | ha, hb | hb, hab⟩
    · subst ha; subst hb; exact absurd rfl hab.ne
    · subst ha; exact absurd hab (h b hb)
    · subst hb; exact absurd hab.symm (h a ha)
    · exact ⟨ha, hb, hab⟩
  · rintro ⟨ha, hb, hab⟩
    exact ⟨Or.inr ha, Or.inr hb, hab⟩

theorem adjPairs_insert_pendant {S : Finset V} {x y : V} (hy : y ∈ S) (hxy : G.Adj x y)
    (h : ∀ z ∈ S, G.Adj x z → z = y) :
    adjPairs G (insert x S) = insert (x, y) (insert (y, x) (adjPairs G S)) := by
  ext ⟨a, b⟩
  simp only [mem_adjPairs, mem_insert, Prod.mk.injEq]
  constructor
  · rintro ⟨ha | ha, hb | hb, hab⟩
    · subst ha; subst hb; exact absurd rfl hab.ne
    · subst ha; exact Or.inl ⟨rfl, h b hb hab⟩
    · subst hb; exact Or.inr (Or.inl ⟨h a ha hab.symm, rfl⟩)
    · exact Or.inr (Or.inr ⟨ha, hb, hab⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨ha, hb, hab⟩)
    · exact ⟨Or.inl rfl, Or.inr hy, hxy⟩
    · exact ⟨Or.inr hy, Or.inl rfl, hxy.symm⟩
    · exact ⟨Or.inr ha, Or.inr hb, hab⟩

theorem prod_update_of_notMem {S : Finset V} {x : V} (hx : x ∉ S) (ω : V → ℕ → ℝ) (f : V → ℕ)
    (c : ℕ) : ∏ z ∈ S, ω z (Function.update f x c z) = ∏ z ∈ S, ω z (f z) :=
  Finset.prod_congr rfl fun z hz => by
    rw [Function.update_of_ne (ne_of_mem_of_not_mem hz hx)]

theorem prod_adjPairs_update_of_notMem {S : Finset V} {x : V} (hx : x ∉ S)
    (Ω : V → V → ℕ → ℕ → ℝ) (f : V → ℕ) (c : ℕ) :
    ∏ p ∈ adjPairs G S, Ω p.1 p.2 (Function.update f x c p.1) (Function.update f x c p.2)
      = ∏ p ∈ adjPairs G S, Ω p.1 p.2 (f p.1) (f p.2) :=
  Finset.prod_congr rfl fun p hp => by
    rw [mem_adjPairs] at hp
    rw [Function.update_of_ne (ne_of_mem_of_not_mem hp.1 hx),
      Function.update_of_ne (ne_of_mem_of_not_mem hp.2.1 hx)]

theorem term_update_isolated {S : Finset V} {x : V} (hx : x ∉ S) (h : ∀ z ∈ S, ¬ G.Adj x z)
    (ω : V → ℕ → ℝ) (Ω : V → V → ℕ → ℕ → ℝ) (f : V → ℕ) (c : ℕ) :
    term G (insert x S) ω Ω (Function.update f x c) = term G S ω Ω f * ω x c := by
  unfold term
  rw [Finset.prod_insert hx, adjPairs_insert_isolated G h, prod_update_of_notMem hx,
    prod_adjPairs_update_of_notMem G hx, Function.update_self]
  ring

theorem prod_adjPairs_insert_pendant {S : Finset V} {x y : V} (hx : x ∉ S) (hy : y ∈ S)
    (hxy : G.Adj x y) (h : ∀ z ∈ S, G.Adj x z → z = y) (g : V × V → ℝ) :
    ∏ p ∈ adjPairs G (insert x S), g p = g (x, y) * (g (y, x) * ∏ p ∈ adjPairs G S, g p) := by
  have hyx : y ≠ x := ne_of_mem_of_not_mem hy hx
  have h1 : (x, y) ∉ insert (y, x) (adjPairs G S) := by
    rw [mem_insert, mem_adjPairs, Prod.mk.injEq]
    rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact hyx h.symm
    · exact hx h
  have h2 : (y, x) ∉ adjPairs G S := by
    rw [mem_adjPairs]
    exact fun h => hx h.2.1
  rw [adjPairs_insert_pendant G hy hxy h, Finset.prod_insert h1, Finset.prod_insert h2]

theorem term_update_pendant {S : Finset V} {x y : V} (hx : x ∉ S) (hy : y ∈ S)
    (hxy : G.Adj x y) (h : ∀ z ∈ S, G.Adj x z → z = y)
    (ω : V → ℕ → ℝ) (Ω : V → V → ℕ → ℕ → ℝ) (f : V → ℕ) (c : ℕ) :
    term G (insert x S) ω Ω (Function.update f x c)
      = term G S ω Ω f * ((Ω y x (f y) c * Ω x y c (f y)) * ω x c) := by
  have hyx : y ≠ x := ne_of_mem_of_not_mem hy hx
  unfold term
  rw [Finset.prod_insert hx, prod_adjPairs_insert_pendant G hx hy hxy h
      (fun p => Ω p.1 p.2 (Function.update f x c p.1) (Function.update f x c p.2)),
    prod_update_of_notMem hx, prod_adjPairs_update_of_notMem G hx]
  simp only [Function.update_self, Function.update_of_ne hyx]
  ring

theorem ZG_insert_isolated {S : Finset V} {x : V} (hx : x ∉ S) (h : ∀ z ∈ S, ¬ G.Adj x z)
    (L : V → Finset ℕ) (ω : V → ℕ → ℝ) (Ω : V → V → ℕ → ℕ → ℝ) :
    ZG G (insert x S) L ω Ω = ZG G S L ω Ω * ∑ c ∈ L x, ω x c := by
  rw [ZG_eq_sum_term, ZG_eq_sum_term, sum_assignments_insert hx, Finset.sum_mul]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => term_update_isolated G hx h ω Ω f c

theorem ZG_insert_pendant {S : Finset V} {x y : V} (hx : x ∉ S) (hy : y ∈ S)
    (hxy : G.Adj x y) (h : ∀ z ∈ S, G.Adj x z → z = y)
    (L : V → Finset ℕ) (ω : V → ℕ → ℝ) (Ω : V → V → ℕ → ℕ → ℝ) :
    ZG G (insert x S) L ω Ω = ∑ f ∈ assignments S L,
      term G S ω Ω f * ∑ c ∈ L x, (Ω y x (f y) c * Ω x y c (f y)) * ω x c := by
  rw [ZG_eq_sum_term, sum_assignments_insert hx]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => term_update_pendant G hx hy hxy h ω Ω f c

/-! ### Adding an ear -/

/-- The data of an ear `u, x 0, …, x (m - 1), v` on the edge `uv` of the vertex set `S`. -/
structure IsEar (S : Finset V) {m : ℕ} (u v : V) (x : Fin m → V) : Prop where
  hm : 1 ≤ m
  hu : u ∈ S
  hv : v ∈ S
  huv : G.Adj u v
  hinj : Function.Injective x
  hxS : ∀ j, x j ∉ S
  hold : ∀ j, ∀ y ∈ S, G.Adj (x j) y ↔ (j.val = 0 ∧ y = u) ∨ (j.val + 1 = m ∧ y = v)
  hnew : ∀ j j', G.Adj (x j) (x j') ↔ j.val + 1 = j'.val ∨ j'.val + 1 = j.val

/-- The path `u, x 0, …, x (m - 1), v`. -/
def earPath {m : ℕ} (u v : V) (x : Fin m → V) : Fin (m + 2) → V := Fin.cons u (Fin.snoc x v)

/-- The profile of the `j`-th edge of the path of an ear: both orientations. -/
def earE {m : ℕ} (Ω : V → V → ℕ → ℕ → ℝ) (u v : V) (x : Fin m → V) (j : Fin (m + 1)) :
    ℕ → ℕ → ℝ := fun c d =>
  Ω (earPath u v x j.castSucc) (earPath u v x j.succ) c d
    * Ω (earPath u v x j.succ) (earPath u v x j.castSucc) d c

section Ear

variable {S : Finset V} {m : ℕ} {u v : V} {x : Fin m → V}

theorem earPath_zero (u v : V) (x : Fin m → V) (i : Fin (m + 2)) (h : i.val = 0) :
    earPath u v x i = u := consSnoc_zero u v x i h

theorem earPath_last (u v : V) (x : Fin m → V) (i : Fin (m + 2)) (h : i.val = m + 1) :
    earPath u v x i = v := consSnoc_last u v x i h

theorem earPath_mid (u v : V) (x : Fin m → V) (i : Fin (m + 2)) (j : Fin m)
    (h : i.val = j.val + 1) : earPath u v x i = x j := consSnoc_mid u v x i j h

theorem earPath_cases (u v : V) (x : Fin m → V) (i : Fin (m + 2)) :
    (i.val = 0 ∧ earPath u v x i = u) ∨ (i.val = m + 1 ∧ earPath u v x i = v) ∨
      ∃ j : Fin m, i.val = j.val + 1 ∧ earPath u v x i = x j := by
  by_cases h0 : i.val = 0
  · exact Or.inl ⟨h0, earPath_zero u v x i h0⟩
  by_cases hl : i.val = m + 1
  · exact Or.inr (Or.inl ⟨hl, earPath_last u v x i hl⟩)
  · have hi := i.isLt
    have hj : i.val = (⟨i.val - 1, by omega⟩ : Fin m).val + 1 := by simp only; omega
    exact Or.inr (Or.inr ⟨_, hj, earPath_mid u v x i _ hj⟩)

variable {G}

theorem IsEar.ne (h : IsEar G S u v x) : u ≠ v := h.huv.ne

theorem IsEar.earPath_injective (h : IsEar G S u v x) : Function.Injective (earPath u v x) := by
  intro i i' hii
  apply Fin.ext
  rcases earPath_cases u v x i with ⟨h1, e1⟩ | ⟨h1, e1⟩ | ⟨j, h1, e1⟩ <;>
    rcases earPath_cases u v x i' with ⟨h2, e2⟩ | ⟨h2, e2⟩ | ⟨j', h2, e2⟩ <;>
    rw [e1, e2] at hii
  · omega
  · exact absurd hii h.ne
  · exact absurd (hii ▸ h.hu) (h.hxS j')
  · exact absurd hii.symm h.ne
  · omega
  · exact absurd (hii ▸ h.hv) (h.hxS j')
  · exact absurd (hii ▸ h.hu) (h.hxS j)
  · exact absurd (hii ▸ h.hv) (h.hxS j)
  · have := h.hinj hii
    subst this
    omega

theorem IsEar.earPath_mem (h : IsEar G S u v x) (i : Fin (m + 2)) :
    earPath u v x i ∈ S ∪ univ.image x := by
  rcases earPath_cases u v x i with ⟨_, e⟩ | ⟨_, e⟩ | ⟨j, _, e⟩ <;> rw [e]
  · exact mem_union_left _ h.hu
  · exact mem_union_left _ h.hv
  · exact mem_union_right _ (mem_image_of_mem _ (mem_univ j))

theorem IsEar.earPath_adj (h : IsEar G S u v x) (j : Fin (m + 1)) :
    G.Adj (earPath u v x j.castSucc) (earPath u v x j.succ) := by
  have hm := h.hm
  have hj := j.isLt
  by_cases h0 : j.val = 0
  · rw [earPath_zero u v x _ (by simpa using h0),
      earPath_mid u v x _ ⟨0, by omega⟩ (by simpa using h0)]
    exact ((h.hold ⟨0, by omega⟩ u h.hu).mpr (Or.inl ⟨rfl, rfl⟩)).symm
  by_cases hl : j.val = m
  · rw [earPath_mid u v x _ ⟨m - 1, by omega⟩ (by simp only [Fin.val_castSucc]; omega),
      earPath_last u v x _ (by simpa using hl)]
    exact (h.hold ⟨m - 1, by omega⟩ v h.hv).mpr (Or.inr ⟨by simp only; omega, rfl⟩)
  · rw [earPath_mid u v x _ ⟨j.val - 1, by omega⟩ (by simp only [Fin.val_castSucc]; omega),
      earPath_mid u v x _ ⟨j.val, by omega⟩ (by simp)]
    exact (h.hnew _ _).mpr (Or.inl (by simp only; omega))

theorem IsEar.earPath_not_both (h : IsEar G S u v x) (j : Fin (m + 1)) :
    ¬ (earPath u v x j.castSucc ∈ S ∧ earPath u v x j.succ ∈ S) := by
  have hm := h.hm
  have hj := j.isLt
  rintro ⟨h1, h2⟩
  by_cases h0 : j.val = 0
  · rw [earPath_mid u v x _ ⟨0, by omega⟩ (by simpa using h0)] at h2
    exact h.hxS _ h2
  · rw [earPath_mid u v x _ ⟨j.val - 1, by omega⟩ (by simp only [Fin.val_castSucc]; omega)] at h1
    exact h.hxS _ h1

theorem IsEar.adjPairs_eq (h : IsEar G S u v x) :
    adjPairs G (S ∪ univ.image x) = adjPairs G S ∪
      (univ.image (fun j : Fin (m + 1) => (earPath u v x j.castSucc, earPath u v x j.succ)) ∪
        univ.image (fun j : Fin (m + 1) => (earPath u v x j.succ, earPath u v x j.castSucc))) := by
  have hm := h.hm
  ext ⟨a, b⟩
  simp only [mem_adjPairs, mem_union, mem_image, mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨ha, hb, hab⟩
    rcases ha with ha | ⟨j, rfl⟩ <;> rcases hb with hb | ⟨j', rfl⟩
    · exact Or.inl ⟨ha, hb, hab⟩
    · have hj' := j'.isLt
      rcases (h.hold j' a ha).mp hab.symm with ⟨hj, rfl⟩ | ⟨hj, rfl⟩
      · exact Or.inr (Or.inl ⟨⟨0, by omega⟩, earPath_zero a v x _ (by simp),
          earPath_mid a v x _ j' (by simp [hj])⟩)
      · exact Or.inr (Or.inr ⟨Fin.last m, earPath_last u a x _ (by simp),
          earPath_mid u a x _ j' (by simp only [Fin.val_castSucc, Fin.val_last]; omega)⟩)
    · have hj' := j.isLt
      rcases (h.hold j b hb).mp hab with ⟨hj, rfl⟩ | ⟨hj, rfl⟩
      · exact Or.inr (Or.inr ⟨⟨0, by omega⟩, earPath_mid b v x _ j (by simp [hj]),
          earPath_zero b v x _ (by simp)⟩)
      · exact Or.inr (Or.inl ⟨Fin.last m,
          earPath_mid u b x _ j (by simp only [Fin.val_castSucc, Fin.val_last]; omega),
          earPath_last u b x _ (by simp)⟩)
    · have hj := j.isLt
      have hj' := j'.isLt
      rcases (h.hnew j j').mp hab with hjj | hjj
      · exact Or.inr (Or.inl ⟨⟨j.val + 1, by omega⟩, earPath_mid u v x _ j (by simp),
          earPath_mid u v x _ j' (by simp only [Fin.val_succ]; omega)⟩)
      · exact Or.inr (Or.inr ⟨⟨j'.val + 1, by omega⟩,
          earPath_mid u v x _ j (by simp only [Fin.val_succ]; omega),
          earPath_mid u v x _ j' (by simp)⟩)
  · have hmem : ∀ i, earPath u v x i ∈ S ∨ ∃ j, x j = earPath u v x i := by
      intro i
      rcases mem_union.mp (h.earPath_mem i) with hi | hi
      · exact Or.inl hi
      · obtain ⟨j, _, hj⟩ := mem_image.mp hi
        exact Or.inr ⟨j, hj⟩
    rintro (⟨ha, hb, hab⟩ | ⟨j, rfl, rfl⟩ | ⟨j, rfl, rfl⟩)
    · exact ⟨Or.inl ha, Or.inl hb, hab⟩
    · exact ⟨hmem _, hmem _, h.earPath_adj j⟩
    · exact ⟨hmem _, hmem _, (h.earPath_adj j).symm⟩

theorem IsEar.prod_adjPairs (h : IsEar G S u v x) (g : V × V → ℝ) :
    ∏ p ∈ adjPairs G (S ∪ univ.image x), g p = (∏ p ∈ adjPairs G S, g p) *
      ∏ j : Fin (m + 1), g (earPath u v x j.castSucc, earPath u v x j.succ)
        * g (earPath u v x j.succ, earPath u v x j.castSucc) := by
  have hP := h.earPath_injective
  have hd1 : Disjoint (adjPairs G S)
      (univ.image (fun j : Fin (m + 1) => (earPath u v x j.castSucc, earPath u v x j.succ)) ∪
        univ.image (fun j : Fin (m + 1) => (earPath u v x j.succ, earPath u v x j.castSucc))) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    rw [mem_adjPairs] at hp
    rcases mem_union.mp hp' with hp' | hp'
    · obtain ⟨j, _, rfl⟩ := mem_image.mp hp'
      exact h.earPath_not_both j ⟨hp.1, hp.2.1⟩
    · obtain ⟨j, _, rfl⟩ := mem_image.mp hp'
      exact h.earPath_not_both j ⟨hp.2.1, hp.1⟩
  have hd2 : Disjoint
      (univ.image (fun j : Fin (m + 1) => (earPath u v x j.castSucc, earPath u v x j.succ)))
      (univ.image (fun j : Fin (m + 1) => (earPath u v x j.succ, earPath u v x j.castSucc))) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    obtain ⟨j, _, rfl⟩ := mem_image.mp hp
    obtain ⟨j', _, hj'⟩ := mem_image.mp hp'
    rw [Prod.mk.injEq] at hj'
    have e1 := congrArg Fin.val (hP hj'.1)
    have e2 := congrArg Fin.val (hP hj'.2)
    simp only [Fin.val_succ, Fin.val_castSucc] at e1 e2
    omega
  have hi1 : Function.Injective
      (fun j : Fin (m + 1) => (earPath u v x j.castSucc, earPath u v x j.succ)) := by
    intro j j' hjj
    rw [Prod.mk.injEq] at hjj
    exact Fin.castSucc_injective _ (hP hjj.1)
  have hi2 : Function.Injective
      (fun j : Fin (m + 1) => (earPath u v x j.succ, earPath u v x j.castSucc)) := by
    intro j j' hjj
    rw [Prod.mk.injEq] at hjj
    exact Fin.castSucc_injective _ (hP hjj.2)
  rw [h.adjPairs_eq, Finset.prod_union hd1, Finset.prod_union hd2,
    Finset.prod_image fun a _ b _ hab => hi1 hab, Finset.prod_image fun a _ b _ hab => hi2 hab,
    Finset.prod_mul_distrib]

theorem IsEar.term_extend (h : IsEar G S u v x) (ω : V → ℕ → ℝ) (Ω : V → V → ℕ → ℕ → ℝ)
    (f : V → ℕ) (g : Fin m → ℕ) :
    term G (S ∪ univ.image x) ω Ω (Function.extend x g f) = term G S ω Ω f *
      ((∏ j, ω (x j) (g j)) * ∏ j : Fin (m + 1),
        earE Ω u v x j (pathCol (f u) (f v) g j.castSucc) (pathCol (f u) (f v) g j.succ)) := by
  have hFS : ∀ z ∈ S, Function.extend x g f z = f z := by
    intro z hz
    refine Function.extend_apply' _ _ _ ?_
    rintro ⟨j, rfl⟩
    exact h.hxS j hz
  have hFx : ∀ j, Function.extend x g f (x j) = g j := fun j => h.hinj.extend_apply _ _ _
  have hFP : ∀ i, Function.extend x g f (earPath u v x i) = pathCol (f u) (f v) g i := by
    intro i
    unfold pathCol
    rcases earPath_cases u v x i with ⟨hi, e⟩ | ⟨hi, e⟩ | ⟨j, hi, e⟩ <;> rw [e]
    · rw [consSnoc_zero _ _ _ i hi, hFS u h.hu]
    · rw [consSnoc_last _ _ _ i hi, hFS v h.hv]
    · rw [consSnoc_mid _ _ _ i j hi, hFx j]
  have hdisj : Disjoint S (univ.image x) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨j, _, rfl⟩ := mem_image.mp hz'
    exact h.hxS j hz
  unfold term
  rw [Finset.prod_union hdisj, Finset.prod_image fun a _ b _ hab => h.hinj hab,
    h.prod_adjPairs (fun p => Ω p.1 p.2 (Function.extend x g f p.1) (Function.extend x g f p.2))]
  have e1 : ∏ z ∈ S, ω z (Function.extend x g f z) = ∏ z ∈ S, ω z (f z) :=
    Finset.prod_congr rfl fun z hz => by rw [hFS z hz]
  have e2 : ∏ j, ω (x j) (Function.extend x g f (x j)) = ∏ j, ω (x j) (g j) :=
    Finset.prod_congr rfl fun j _ => by rw [hFx j]
  have e3 : ∏ p ∈ adjPairs G S, Ω p.1 p.2 (Function.extend x g f p.1) (Function.extend x g f p.2)
      = ∏ p ∈ adjPairs G S, Ω p.1 p.2 (f p.1) (f p.2) :=
    Finset.prod_congr rfl fun p hp => by
      rw [mem_adjPairs] at hp
      rw [hFS _ hp.1, hFS _ hp.2.1]
  rw [e1, e2, e3]
  simp only [hFP, earE]
  ring

/-- **Adding an ear.** The ear acts on the edge `uv` as the pair profile `faceSum`. -/
theorem IsEar.ZG_eq (h : IsEar G S u v x) (L : V → Finset ℕ) (ω : V → ℕ → ℝ)
    (Ω : V → V → ℕ → ℕ → ℝ) :
    ZG G (S ∪ univ.image x) L ω Ω = ∑ f ∈ assignments S L, term G S ω Ω f *
      faceSum (fun j => L (x j)) (fun j => ω (x j)) (earE Ω u v x) (f u) (f v) := by
  rw [ZG_eq_sum_term, sum_assignments_union h.hinj h.hxS]
  refine Finset.sum_congr rfl fun f _ => ?_
  unfold faceSum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun g _ => h.term_extend ω Ω f g

end Ear

end Outerplanar
