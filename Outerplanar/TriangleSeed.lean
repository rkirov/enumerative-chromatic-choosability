/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.TriangleCap
import Outerplanar.Seed

/-!
# A triangle as the seed of the graph induction, at three colours

For three pairwise adjacent vertices `t 0`, `t 1`, `t 2`, the weighted lower bound `ZGBound G 3`
holds on the vertex set of the triangle (`zgBound_triangle`). The pair profiles are bounded
below by their rank-one minorants, whose two factors are absorbed into the vertex weights (they
have product one on the lists, so the geometric means do not change); what remains is the
weighted number of proper colourings of the triangle, which is at least six times the geometric
means by `triCover_capGE`.

With `ZG_ge_from` this allows one triangle in a graph built by pendant vertices and ears of at
least two vertices on edges.
-/

set_option linter.unusedSectionVars false

namespace Outerplanar

open Finset

/-! ### Sums and products over `Fin 3` -/

theorem prod_offDiag_three (g : Fin 3 → Fin 3 → ℝ) :
    ∏ q ∈ (univ : Finset (Fin 3)).offDiag, g q.1 q.2
      = g 0 1 * g 0 2 * (g 1 0 * g 1 2) * (g 2 0 * g 2 1) := by
  rw [show (univ : Finset (Fin 3)).offDiag = {(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)}
    from by decide]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  ring

theorem sum_piFinset_three (D : Fin 3 → Finset ℕ) (Φ : (Fin 3 → ℕ) → ℝ) :
    ∑ h ∈ Fintype.piFinset D, Φ h = ∑ a ∈ D 0, ∑ b ∈ D 1, ∑ c ∈ D 2, Φ ![a, b, c] := by
  have hR : (∑ a ∈ D 0, ∑ b ∈ D 1, ∑ c ∈ D 2, Φ ![a, b, c])
      = ∑ p ∈ D 0 ×ˢ D 1 ×ˢ D 2, Φ ![p.1, p.2.1, p.2.2] := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_product]
  rw [hR]
  refine Finset.sum_nbij' (fun h => (h 0, h 1, h 2)) (fun p => ![p.1, p.2.1, p.2.2])
    ?_ ?_ ?_ ?_ ?_
  · intro h hh
    rw [Fintype.mem_piFinset] at hh
    simp only [mem_product]
    exact ⟨hh 0, hh 1, hh 2⟩
  · rintro ⟨a, b, c⟩ hp
    simp only [mem_product] at hp
    rw [Fintype.mem_piFinset]
    intro i
    fin_cases i
    · exact hp.1
    · exact hp.2.1
    · exact hp.2.2
  · intro h _
    funext i
    fin_cases i <;> rfl
  · rintro ⟨a, b, c⟩ _
    rfl
  · intro h _
    congr 1
    funext i
    fin_cases i <;> rfl

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (t : Fin 3 → V) (ht : Function.Injective t) (hadj : ∀ i j, i ≠ j → G.Adj (t i) (t j))

include ht hadj

/-! ### The partition function of a triangle -/

/-- The ordered pairs of adjacent vertices of a triangle. -/
theorem adjPairs_image_tri :
    adjPairs G (univ.image t) = (univ : Finset (Fin 3)).offDiag.image (Prod.map t t) := by
  ext ⟨a, b⟩
  rw [mem_adjPairs]
  constructor
  · rintro ⟨h1, h2, h⟩
    dsimp only at h1 h2 h
    obtain ⟨i, -, hi⟩ := mem_image.mp h1
    obtain ⟨j, -, hj⟩ := mem_image.mp h2
    subst hi
    subst hj
    exact mem_image.mpr ⟨(i, j),
      mem_offDiag.mpr ⟨mem_univ _, mem_univ _, fun hij => h.ne (congrArg t hij)⟩, rfl⟩
  · intro h
    obtain ⟨⟨i, j⟩, hq, hqe⟩ := mem_image.mp h
    have hij := (mem_offDiag.mp hq).2.2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hqe
    exact ⟨mem_image_of_mem _ (mem_univ _), mem_image_of_mem _ (mem_univ _), hadj i j hij⟩

/-- The partition function of a triangle, as a sum over the colourings of its three vertices. -/
theorem ZG_image_tri (L : V → Finset ℕ) (ω : V → ℕ → ℝ) (Ω : V → V → ℕ → ℕ → ℝ) :
    ZG G (univ.image t) L ω Ω = ∑ h ∈ Fintype.piFinset (fun i => L (t i)),
      (∏ i, ω (t i) (h i))
        * ∏ q ∈ (univ : Finset (Fin 3)).offDiag, Ω (t q.1) (t q.2) (h q.1) (h q.2) := by
  have h0 : assignments (∅ : Finset V) L = {fun _ => 0} := by
    ext f
    rw [mem_assignments, mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      funext z
      exact h z (Finset.notMem_empty z)
    · rintro rfl
      exact ⟨fun z hz => absurd hz (Finset.notMem_empty z), fun _ _ => rfl⟩
  have key := sum_assignments_union (S := ∅) ht (fun i => Finset.notMem_empty _) L
    (fun F => (∏ x ∈ univ.image t, ω x (F x))
      * ∏ p ∈ (univ : Finset (Fin 3)).offDiag.image (Prod.map t t), Ω p.1 p.2 (F p.1) (F p.2))
  rw [Finset.empty_union, h0, Finset.sum_singleton] at key
  unfold ZG
  rw [adjPairs_image_tri G t ht hadj]
  refine key.trans (Finset.sum_congr rfl fun h _ => ?_)
  have hext : ∀ i, Function.extend t h (fun _ => 0) (t i) = h i := fun i =>
    ht.extend_apply h _ i
  rw [Finset.prod_image (fun a _ b _ hab => ht hab),
    Finset.prod_image (fun a _ b _ hab => (ht.prodMap ht) hab)]
  simp only [Prod.map_fst, Prod.map_snd, hext]

/-- A triangle has six proper colourings from three colours. -/
theorem ZG_const_tri :
    ZG G (univ.image t) (fun _ => range 3) (fun _ _ => 1) neProfile = 6 := by
  rw [ZG_image_tri G t ht hadj, sum_piFinset_three]
  have hterm : ∀ a b c : ℕ, (∏ _i : Fin 3, (1 : ℝ))
      * ∏ q ∈ (univ : Finset (Fin 3)).offDiag,
          neProfile (t q.1) (t q.2) (![a, b, c] q.1) (![a, b, c] q.2)
      = if a ≠ b ∧ a ≠ c ∧ b ≠ c then 1 else 0 := by
    intro a b c
    rw [Finset.prod_const_one, one_mul,
      prod_offDiag_three fun i j => neProfile (t i) (t j) (![a, b, c] i) (![a, b, c] j)]
    simp only [neProfile, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    by_cases h1 : a = b <;> by_cases h2 : a = c <;> by_cases h3 : b = c <;>
      simp [h1, h2, h3, eq_comm]
  simp only [hterm, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-! ### The weighted lower bound on a triangle -/

/-- **The seed bound**: the weighted lower bound for three colours holds on a triangle. -/
theorem zgBound_triangle : ZGBound G 3 (univ.image t) := by
  intro L ω Ω A hcard hω hΩ hA hpot
  have hmem : ∀ i, t i ∈ univ.image t := fun i => mem_image_of_mem _ (mem_univ i)
  -- the potentials of the six ordered pairs
  have hex : ∀ i j : Fin 3, ∃ a b : ℕ → ℝ, i ≠ j →
      ((∀ c ∈ L (t i), 0 < a c) ∧ (∀ d ∈ L (t j), 0 < b d) ∧ ∏ c ∈ L (t i), a c = 1 ∧
        ∏ d ∈ L (t j), b d = 1 ∧ ∀ c ∈ L (t i), ∀ d ∈ L (t j), c ≠ d →
          A (t i) (t j) * (a c * b d) ≤ Ω (t i) (t j) c d) := by
    intro i j
    by_cases hij : i = j
    · exact ⟨fun _ => 1, fun _ => 1, fun h => absurd hij h⟩
    · obtain ⟨a, b, h⟩ := hpot _ (hmem i) _ (hmem j) (hadj i j hij)
      exact ⟨a, b, fun _ => h⟩
  choose α β hαβ using hex
  -- what the edge to `t j` puts on the vertex `t i`
  obtain ⟨u, hu⟩ : ∃ u : Fin 3 → Fin 3 → ℕ → ℝ, ∀ i j c, u i j c = α i j c * β j i c :=
    ⟨_, fun _ _ _ => rfl⟩
  have hupos : ∀ i j, i ≠ j → ∀ c ∈ L (t i), 0 < u i j c := fun i j hij c hc => by
    rw [hu]
    exact mul_pos ((hαβ i j hij).1 c hc) ((hαβ j i (Ne.symm hij)).2.1 c hc)
  have huprod : ∀ i j, i ≠ j → ∏ c ∈ L (t i), u i j c = 1 := fun i j hij => by
    rw [Finset.prod_congr rfl fun c _ => hu i j c, Finset.prod_mul_distrib, (hαβ i j hij).2.2.1,
      (hαβ j i (Ne.symm hij)).2.2.2.1, one_mul]
  obtain ⟨w', hw'⟩ : ∃ w' : Fin 3 → ℕ → ℝ,
      ∀ i c, w' i c = ω (t i) c * (u i (i + 1) c * u i (i + 2) c) := ⟨_, fun _ _ => rfl⟩
  have h1 : ∀ i : Fin 3, i ≠ i + 1 := by decide
  have h2 : ∀ i : Fin 3, i ≠ i + 2 := by decide
  have hfin : ∀ i j : Fin 3, i ≠ j → j = i + 1 ∨ i = j + 1 := by decide
  have huu : ∀ i, ∀ c ∈ L (t i), 0 < u i (i + 1) c * u i (i + 2) c := fun i c hc =>
    mul_pos (hupos i _ (h1 i) c hc) (hupos i _ (h2 i) c hc)
  have hw'pos : ∀ i, ∀ c ∈ L (t i), 0 < w' i c := fun i c hc => by
    rw [hw']
    exact mul_pos (hω _ (hmem i) c hc) (huu i c hc)
  have hgm : ∀ i, gmean (L (t i)) (w' i) = gmean (L (t i)) (ω (t i)) := by
    intro i
    rw [show w' i = fun c => ω (t i) c * (u i (i + 1) c * u i (i + 2) c) from funext (hw' i),
      gmean_mul (v := ω (t i)) (u := fun c => u i (i + 1) c * u i (i + 2) c)
        (hω _ (hmem i)) (huu i),
      gmean_mul (v := u i (i + 1)) (u := u i (i + 2)) (hupos i _ (h1 i)) (hupos i _ (h2 i)),
      gmean_eq_one (hupos i _ (h1 i)) (huprod i _ (h1 i)),
      gmean_eq_one (hupos i _ (h2 i)) (huprod i _ (h2 i)), mul_one, mul_one]
  -- the capacity of the triangle
  have hcap := (triCover_capGE (fun i => L (t i)) (fun i => hcard _ (hmem i)) (fun _ => 0)).le_Z
    (fun i _ => Finset.card_pos.mp (by
      have := hcard _ (hmem i)
      show 0 < (L (t i)).card
      omega)) (w := w') (fun i _ => hw'pos i)
  have hcap' : 6 * ∏ i, gmean (L (t i)) (ω (t i))
      ≤ (triCover fun i => L (t i)).Z univ (fun _ => 0) w' := by
    refine le_of_eq_of_le ?_ hcap
    congr 1
    exact Finset.prod_congr rfl fun i _ => (hgm i).symm
  rw [ZG_const_tri G t ht hadj, ZG_image_tri G t ht hadj, adjPairs_image_tri G t ht hadj,
    Finset.prod_image (fun a _ b _ hab => ht hab),
    Finset.prod_image (fun a _ b _ hab => (ht.prodMap ht) hab)]
  simp only [Prod.map_fst, Prod.map_snd]
  have hAnn : 0 ≤ ∏ q ∈ (univ : Finset (Fin 3)).offDiag, A (t q.1) (t q.2) :=
    Finset.prod_nonneg fun q _ => (hA _ _).le
  have e01 : (0 : Fin 3) + 1 = 1 := by decide
  have e02 : (0 : Fin 3) + 2 = 2 := by decide
  have e11 : (1 : Fin 3) + 1 = 2 := by decide
  have e12 : (1 : Fin 3) + 2 = 0 := by decide
  have e21 : (2 : Fin 3) + 1 = 0 := by decide
  have e22 : (2 : Fin 3) + 2 = 1 := by decide
  calc 6 * (∏ i, gmean (L (t i)) (ω (t i)))
        * ∏ q ∈ (univ : Finset (Fin 3)).offDiag, A (t q.1) (t q.2)
      = (∏ q ∈ (univ : Finset (Fin 3)).offDiag, A (t q.1) (t q.2))
          * (6 * ∏ i, gmean (L (t i)) (ω (t i))) := by ring
    _ ≤ (∏ q ∈ (univ : Finset (Fin 3)).offDiag, A (t q.1) (t q.2))
          * (triCover fun i => L (t i)).Z univ (fun _ => 0) w' :=
        mul_le_mul_of_nonneg_left hcap' hAnn
    _ = ∑ f ∈ (triCover fun i => L (t i)).cols univ (fun _ => 0),
          (∏ q ∈ (univ : Finset (Fin 3)).offDiag, A (t q.1) (t q.2)) * ∏ i, w' i (f i) := by
        rw [Cover.Z, Finset.mul_sum]
    _ ≤ ∑ f ∈ (triCover fun i => L (t i)).cols univ (fun _ => 0),
          (∏ i, ω (t i) (f i))
            * ∏ q ∈ (univ : Finset (Fin 3)).offDiag, Ω (t q.1) (t q.2) (f q.1) (f q.2) := by
        refine Finset.sum_le_sum fun f hf => ?_
        have hf' := (triCover fun i => L (t i)).mem_cols.mp hf
        have hfL : ∀ i, f i ∈ L (t i) := fun i => (hf'.1 i).1 (mem_univ i)
        have hne : ∀ i, f i ≠ f (i + 1) := fun i => hf'.2 i (mem_univ _) (mem_univ _)
        have hne' : ∀ i j, i ≠ j → f i ≠ f j := by
          intro i j hij
          rcases hfin i j hij with h | h
          · rw [h]; exact hne i
          · rw [h]; exact (hne j).symm
        have hΩle : ∏ q ∈ (univ : Finset (Fin 3)).offDiag,
              A (t q.1) (t q.2) * (α q.1 q.2 (f q.1) * β q.1 q.2 (f q.2))
            ≤ ∏ q ∈ (univ : Finset (Fin 3)).offDiag, Ω (t q.1) (t q.2) (f q.1) (f q.2) := by
          refine Finset.prod_le_prod₀ (fun q hq => ?_) (fun q hq => ?_)
          · have hq' := (mem_offDiag.mp hq).2.2
            exact (mul_pos (hA _ _) (mul_pos ((hαβ _ _ hq').1 _ (hfL _))
              ((hαβ _ _ hq').2.1 _ (hfL _)))).le
          · have hq' := (mem_offDiag.mp hq).2.2
            exact (hαβ _ _ hq').2.2.2.2 _ (hfL _) _ (hfL _) (hne' _ _ hq')
        have hpot3 : ∏ q ∈ (univ : Finset (Fin 3)).offDiag,
              α q.1 q.2 (f q.1) * β q.1 q.2 (f q.2)
            = ∏ i, (u i (i + 1) (f i) * u i (i + 2) (f i)) := by
          rw [prod_offDiag_three fun i j => α i j (f i) * β i j (f j), Fin.prod_univ_three]
          simp only [hu, e01, e02, e11, e12, e21, e22]
          ring
        rw [Finset.prod_mul_distrib, hpot3] at hΩle
        have hωnn : 0 ≤ ∏ i, ω (t i) (f i) :=
          Finset.prod_nonneg fun i _ => (hω _ (hmem i) _ (hfL i)).le
        calc (∏ q ∈ (univ : Finset (Fin 3)).offDiag, A (t q.1) (t q.2)) * ∏ i, w' i (f i)
            = (∏ i, ω (t i) (f i))
                * ((∏ q ∈ (univ : Finset (Fin 3)).offDiag, A (t q.1) (t q.2))
                  * ∏ i, (u i (i + 1) (f i) * u i (i + 2) (f i))) := by
              rw [Finset.prod_congr rfl fun i _ => hw' i (f i), Finset.prod_mul_distrib]
              ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hΩle hωnn
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun f hf => ?_) (fun h hh _ => ?_)
        · exact Fintype.mem_piFinset.mpr fun i =>
            ((((triCover fun i => L (t i)).mem_cols.mp hf).1 i).1 (mem_univ i))
        · exact mul_nonneg (Finset.prod_nonneg fun i _ =>
            (hω _ (hmem i) _ (Fintype.mem_piFinset.mp hh i)).le)
            (Finset.prod_nonneg fun q _ => hΩ _ _ _ _)

end Outerplanar
