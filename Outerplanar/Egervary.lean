import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

/-!
# Egerváry's theorem, in multiplicative form

The main statement is `Outerplanar.exists_potentials`. Let `S` and `T` be two `k`-sets of colours,
`k ≥ 3`, and let `W c d > 0` be a weight on the *allowed* pairs `(c, d) ∈ S × T`, `c ≠ d`. If every
perfect matching `σ : S → T` inside the allowed pairs has `∏ c ∈ S, W c (σ c) ≥ 1`, then `W`
dominates a rank-one matrix on the allowed pairs: there are positive `a` on `S` and `b` on `T` with
`∏ a = ∏ b = 1` and `a c * b d ≤ W c d`.

After taking logarithms this is the classical theorem of Egerváry (1931), that is, linear
programming duality for the assignment problem: the minimum weight of a perfect matching equals the
maximum of `∑ u + ∑ v` over the potentials with `u c + v d ≤ m c d` on the allowed pairs. It is
used by the outerplanar ECC proof (`ai_research_notes/OUTERPLANAR_PROOF_DRAFT_2026-11-09.md`,
section 2).

## The proof

The additive statement is `Outerplanar.exists_additive_potentials`, for two finite types and an
arbitrary relation of allowed pairs, under the hypothesis that every allowed pair lies in a perfect
matching of allowed pairs.

* `exists_max_feasible`: the dual objective `∑ u + ∑ v` attains its maximum over the feasible
  potentials. The objective and the constraints only depend on the numbers `u a + v b` at the
  allowed pairs; in those coordinates the feasible points with objective at least a given value
  form a closed bounded set (a linear subspace of a finite-dimensional space is closed, and each
  coordinate is bounded below because its pair lies in a perfect matching).
* `exists_tight_injective`: at a maximiser the graph of tight pairs `u a + v b = m a b` satisfies
  Hall's condition. Otherwise there is a set `X` with fewer than `|X|` tight neighbours, and raising
  `u` on `X` while lowering `v` on the neighbours by a small `ε` stays feasible and increases the
  objective.
* A perfect matching of tight pairs has weight exactly `∑ u + ∑ v`, which is therefore
  nonnegative.

`exists_derangement_through` supplies the hypothesis on allowed pairs in the situation of the main
statement: for `k ≥ 3`, every pair `c ≠ d` lies in a bijection `S → T` without fixed points.
-/

namespace Outerplanar

open Finset

section Abstract

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Finitely many real numbers have a common positive lower bound for the positive ones among
them. -/
theorem exists_pos_le_of_pos {ι : Type*} [Finite ι] (f : ι → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, 0 < f i → ε ≤ f i := by
  classical
  cases nonempty_fintype ι
  by_cases h : (univ.filter fun i => 0 < f i).Nonempty
  · obtain ⟨i, hi, hmin⟩ := (univ.filter fun i => 0 < f i).exists_min_image f h
    exact ⟨f i, (mem_filter.1 hi).2, fun j hj => hmin j (mem_filter.2 ⟨mem_univ _, hj⟩)⟩
  · exact ⟨1, one_pos, fun i hi => (h ⟨i, mem_filter.2 ⟨mem_univ _, hi⟩⟩).elim⟩

/-- The Hungarian step. At potentials maximising `∑ u + ∑ v` subject to `u a + v b ≤ m a b` on the
allowed pairs, the tight allowed pairs contain a matching that saturates `α`. -/
theorem exists_tight_injective (R : α → β → Prop) (m : α → β → ℝ) (u : α → ℝ) (v : β → ℝ)
    (hfeas : ∀ a b, R a b → u a + v b ≤ m a b)
    (hmax : ∀ (u' : α → ℝ) (v' : β → ℝ), (∀ a b, R a b → u' a + v' b ≤ m a b) →
      ∑ a, u' a + ∑ b, v' b ≤ ∑ a, u a + ∑ b, v b) :
    ∃ f : α → β, Function.Injective f ∧ ∀ a, R a (f a) ∧ u a + v (f a) = m a (f a) := by
  classical
  let t : α → Finset β := fun a => univ.filter fun b => R a b ∧ u a + v b = m a b
  have key : ∀ X : Finset α, X.card ≤ (X.biUnion t).card := by
    intro X
    by_contra hlt
    push Not at hlt
    obtain ⟨ε, hε, hεle⟩ :=
      exists_pos_le_of_pos (fun p : α × β => m p.1 p.2 - (u p.1 + v p.2))
    set N := X.biUnion t with hN
    have hf := hmax (fun a => u a + if a ∈ X then ε else 0)
      (fun b => v b - if b ∈ N then ε else 0) ?_
    · have h1 : ∑ a, (u a + if a ∈ X then ε else 0) = ∑ a, u a + X.card * ε := by
        rw [sum_add_distrib]; simp
      have h2 : ∑ b, (v b - if b ∈ N then ε else 0) = ∑ b, v b - N.card * ε := by
        rw [sum_sub_distrib]; simp
      rw [h1, h2] at hf
      have h3 : (N.card : ℝ) + 1 ≤ X.card := by exact_mod_cast hlt
      nlinarith
    · intro a b hab
      by_cases ha : a ∈ X
      · by_cases hb : b ∈ N
        · simp only [ha, hb, ite_true]; linarith [hfeas a b hab]
        · have hnt : u a + v b ≠ m a b := fun h =>
            hb (mem_biUnion.2 ⟨a, ha, mem_filter.2 ⟨mem_univ _, hab, h⟩⟩)
          have hlt' : 0 < m a b - (u a + v b) :=
            sub_pos.2 (lt_of_le_of_ne (hfeas a b hab) hnt)
          have := hεle (a, b) hlt'
          simp only [ha, hb, ite_true, ite_false]; linarith
      · simp only [ha, ite_false]
        split_ifs <;> linarith [hfeas a b hab]
  obtain ⟨f, hinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 key
  exact ⟨f, hinj, fun a => (mem_filter.1 (hf a)).2⟩

/-- The dual of the assignment problem attains its maximum, provided every allowed pair lies in a
perfect matching of allowed pairs (and there is at least one such matching, `e0`). -/
theorem exists_max_feasible (R : α → β → Prop) (m : α → β → ℝ)
    (e0 : α ≃ β) (he0 : ∀ a, R a (e0 a))
    (hcov : ∀ a b, R a b → ∃ e : α ≃ β, e a = b ∧ ∀ x, R x (e x)) :
    ∃ (u : α → ℝ) (v : β → ℝ), (∀ a b, R a b → u a + v b ≤ m a b) ∧
      ∀ (u' : α → ℝ) (v' : β → ℝ), (∀ a b, R a b → u' a + v' b ≤ m a b) →
        ∑ a, u' a + ∑ b, v' b ≤ ∑ a, u a + ∑ b, v b := by
  classical
  let I := {p : α × β // R p.1 p.2}
  let L : ((α → ℝ) × (β → ℝ)) →ₗ[ℝ] (I → ℝ) :=
    { toFun := fun w p => w.1 p.1.1 + w.2 p.1.2
      map_add' := by intro x y; ext p; simp; ring
      map_smul' := by intro c x; ext p; simp; ring }
  have hL : ∀ w p, L w p = w.1 p.1.1 + w.2 p.1.2 := fun _ _ => rfl
  have hsum : ∀ (e : α ≃ β) (he : ∀ x, R x (e x)) (w : (α → ℝ) × (β → ℝ)),
      ∑ a, L w ⟨(a, e a), he a⟩ = ∑ a, w.1 a + ∑ b, w.2 b := by
    intro e he w
    simp only [hL, sum_add_distrib]
    congr 1
    exact Equiv.sum_comp e w.2
  let F : (I → ℝ) → ℝ := fun y => ∑ a, y ⟨(a, e0 a), he0 a⟩
  have hF : Continuous F := continuous_finsetSum _ fun a _ => continuous_apply _
  have hFL : ∀ w : (α → ℝ) × (β → ℝ), F (L w) = ∑ a, w.1 a + ∑ b, w.2 b := hsum e0 he0
  let M : ℝ := ∑ a, ∑ b, |m a b|
  have hM : ∀ a b, |m a b| ≤ M := fun a b =>
    (single_le_sum (f := fun b => |m a b|) (fun _ _ => abs_nonneg _) (mem_univ b)).trans
      (single_le_sum (f := fun a => ∑ b, |m a b|)
        (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ a))
  let w0 : (α → ℝ) × (β → ℝ) := (fun _ => -M, fun _ => 0)
  have hw0 : ∀ p : I, L w0 p ≤ m p.1.1 p.1.2 := by
    intro p
    simp only [hL, w0]
    linarith [hM p.1.1 p.1.2, neg_abs_le (m p.1.1 p.1.2)]
  let Φ₀ : ℝ := F (L w0)
  let K : Set (I → ℝ) :=
    ((LinearMap.range L : Set (I → ℝ)) ∩ {y | ∀ p : I, y p ≤ m p.1.1 p.1.2}) ∩ {y | Φ₀ ≤ F y}
  have hKclosed : IsClosed K := by
    refine ((LinearMap.range L).closed_of_finiteDimensional.inter ?_).inter
      (isClosed_le continuous_const hF)
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun p => isClosed_le (continuous_apply p) continuous_const
  have hKbox : K ⊆ Set.pi Set.univ fun p : I => Set.Icc (Φ₀ - M) (m p.1.1 p.1.2) := by
    rintro y ⟨⟨⟨w, rfl⟩, hy⟩, hΦ⟩ p _
    refine ⟨?_, hy p⟩
    obtain ⟨⟨a, b⟩, hab⟩ := p
    obtain ⟨e, rfl, he⟩ := hcov a b hab
    have h1 : F (L w) = ∑ x, L w ⟨(x, e x), he x⟩ := by rw [hsum e he, hFL]
    have h2 : ∑ x, L w ⟨(x, e x), he x⟩ =
        L w ⟨(a, e a), he a⟩ + ∑ x ∈ univ.erase a, L w ⟨(x, e x), he x⟩ :=
      (add_sum_erase _ _ (mem_univ a)).symm
    have h3 : ∑ x ∈ univ.erase a, L w ⟨(x, e x), he x⟩ ≤ ∑ x ∈ univ.erase a, |m x (e x)| :=
      sum_le_sum fun x _ => (hy _).trans (le_abs_self _)
    have h4 : ∑ x ∈ univ.erase a, |m x (e x)| ≤ ∑ x, |m x (e x)| :=
      sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ => abs_nonneg _
    have h5 : ∑ x, |m x (e x)| ≤ M :=
      sum_le_sum fun x _ =>
        single_le_sum (f := fun b => |m x b|) (fun _ _ => abs_nonneg _) (mem_univ (e x))
    have hΦ' : Φ₀ ≤ F (L w) := hΦ
    show Φ₀ - M ≤ L w ⟨(a, e a), he a⟩
    linarith
  have hKne : K.Nonempty := ⟨L w0, ⟨⟨⟨w0, rfl⟩, hw0⟩, le_refl Φ₀⟩⟩
  have hKc : IsCompact K :=
    IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_Icc) hKclosed hKbox
  obtain ⟨y, ⟨⟨⟨w, rfl⟩, hy⟩, -⟩, hmax⟩ := hKc.exists_isMaxOn hKne hF.continuousOn
  refine ⟨w.1, w.2, fun a b hab => hy ⟨(a, b), hab⟩, fun u' v' h' => ?_⟩
  have e1 : F (L (u', v')) = ∑ a, u' a + ∑ b, v' b := hFL (u', v')
  have e2 : F (L w) = ∑ a, w.1 a + ∑ b, w.2 b := hFL w
  by_cases hc : Φ₀ ≤ F (L (u', v'))
  · have hmem : L (u', v') ∈ K := ⟨⟨⟨_, rfl⟩, fun p => h' _ _ p.2⟩, hc⟩
    have := isMaxOn_iff.1 hmax _ hmem
    linarith
  · push Not at hc
    have hmem : L w0 ∈ K := ⟨⟨⟨w0, rfl⟩, hw0⟩, le_refl Φ₀⟩
    have h6 : Φ₀ ≤ F (L w) := isMaxOn_iff.1 hmax _ hmem
    linarith

/-- **Egerváry's theorem** (the inequality that is not obvious), additive form. If every allowed
pair lies in a perfect matching of allowed pairs, and every such matching has nonnegative weight,
then there are potentials `u`, `v` with `u a + v b ≤ m a b` on the allowed pairs and
`∑ u + ∑ v ≥ 0`. -/
theorem exists_additive_potentials (R : α → β → Prop) (m : α → β → ℝ)
    (hcov : ∀ a b, R a b → ∃ e : α ≃ β, e a = b ∧ ∀ x, R x (e x))
    (hB : ∀ e : α ≃ β, (∀ x, R x (e x)) → 0 ≤ ∑ x, m x (e x)) :
    ∃ (u : α → ℝ) (v : β → ℝ), (∀ a b, R a b → u a + v b ≤ m a b) ∧
      0 ≤ ∑ a, u a + ∑ b, v b := by
  by_cases h : ∃ a b, R a b
  · obtain ⟨a, b, hab⟩ := h
    obtain ⟨e0, -, he0⟩ := hcov a b hab
    obtain ⟨u, v, hfeas, hmax⟩ := exists_max_feasible R m e0 he0 hcov
    obtain ⟨f, hinj, hf⟩ := exists_tight_injective R m u v hfeas hmax
    have hbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, Fintype.card_congr e0⟩
    have h0 := hB (Equiv.ofBijective f hbij) (fun x => (hf x).1)
    refine ⟨u, v, hfeas, ?_⟩
    have h1 : ∑ x, m x (Equiv.ofBijective f hbij x) =
        ∑ x, (u x + v (Equiv.ofBijective f hbij x)) :=
      sum_congr rfl fun x _ => ((hf x).2).symm
    rw [h1, sum_add_distrib, Equiv.sum_comp (Equiv.ofBijective f hbij) v] at h0
    exact h0
  · push Not at h
    exact ⟨0, 0, fun a b hab => (h a b hab).elim, by simp⟩

end Abstract

/-- For two sets of colours of the same size at least three, every pair of distinct colours
`a ∈ S`, `b ∈ T` lies in a bijection `S → T` without fixed points. -/
theorem exists_derangement_through {S T : Finset ℕ} (hST : S.card = T.card) (hS : 3 ≤ S.card)
    (a : S) (b : T) (hab : (a : ℕ) ≠ b) :
    ∃ e : S ≃ T, e a = b ∧ ∀ x : S, (x : ℕ) ≠ e x := by
  classical
  have key : ∀ n : ℕ, ∀ e : S ≃ T, e a = b →
      (univ.filter fun x : S => (e x : ℕ) = x).card ≤ n →
      ∃ e' : S ≃ T, e' a = b ∧ ∀ x : S, (x : ℕ) ≠ e' x := by
    intro n
    induction n with
    | zero =>
      intro e hea hn
      refine ⟨e, hea, fun x hx => ?_⟩
      have hmem : x ∈ univ.filter fun x : S => (e x : ℕ) = x :=
        mem_filter.2 ⟨mem_univ _, hx.symm⟩
      rw [Nat.le_zero, card_eq_zero] at hn
      rw [hn] at hmem
      exact absurd hmem (notMem_empty _)
    | succ n ih =>
      intro e hea hn
      by_cases hfix : ∃ x : S, (e x : ℕ) = x
      · obtain ⟨x, hx⟩ := hfix
        have hxa : x ≠ a := by
          rintro rfl
          rw [hea] at hx
          exact hab hx.symm
        obtain ⟨y, hya, hyx⟩ : ∃ y : S, y ≠ a ∧ y ≠ x := by
          by_contra hno
          push Not at hno
          have hsub : (univ : Finset S) ⊆ {a, x} := fun y _ => by
            by_cases h : y = a
            · simp [h]
            · simp [hno y h]
          have h1 := card_le_card hsub
          have h2 : ({a, x} : Finset S).card ≤ 2 := card_le_two
          rw [card_univ, Fintype.card_coe] at h1
          omega
        refine ih ((Equiv.swap x y).trans e) ?_ ?_
        · simp [Equiv.swap_apply_of_ne_of_ne hxa.symm hya.symm, hea]
        · have hsub : (univ.filter fun z : S => (((Equiv.swap x y).trans e) z : ℕ) = z) ⊆
              (univ.filter fun z : S => (e z : ℕ) = z).erase x := by
            intro z hz
            have hz2 := (mem_filter.1 hz).2
            rw [mem_erase, mem_filter]
            by_cases hzx : z = x
            · rw [hzx] at hz2
              simp only [Equiv.trans_apply, Equiv.swap_apply_left] at hz2
              exact absurd (e.injective (Subtype.ext (hz2.trans hx.symm))) hyx
            · by_cases hzy : z = y
              · rw [hzy] at hz2
                simp only [Equiv.trans_apply, Equiv.swap_apply_right] at hz2
                exact absurd (Subtype.ext (hz2.symm.trans hx)) hyx
              · simp only [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hzx hzy] at hz2
                exact ⟨hzx, mem_univ _, hz2⟩
          have hxmem : x ∈ univ.filter fun z : S => (e z : ℕ) = z :=
            mem_filter.2 ⟨mem_univ _, hx⟩
          have h1 := card_le_card hsub
          rw [card_erase_of_mem hxmem] at h1
          omega
      · push Not at hfix
        exact ⟨e, hea, fun x hx => hfix x hx.symm⟩
  let e0 : S ≃ T := Fintype.equivOfCardEq (by simpa using hST)
  exact key _ (e0.trans (Equiv.swap (e0 a) b)) (by simp) le_rfl

/-- **Egerváry's theorem**, multiplicative form. Let `S`, `T` be two `k`-sets of colours, `k ≥ 3`,
and call a pair `(c, d) ∈ S × T` allowed when `c ≠ d`. If every perfect matching `σ` inside the
allowed pairs has `∏ c ∈ S, W c (σ c) ≥ 1`, then on the allowed pairs `W` dominates a rank-one
matrix `a c * b d` with `∏ a = ∏ b = 1`. -/
theorem exists_potentials {k : ℕ} (hk : 3 ≤ k) (S T : Finset ℕ) (hS : S.card = k) (hT : T.card = k)
    (W : ℕ → ℕ → ℝ) (hpos : ∀ c ∈ S, ∀ d ∈ T, c ≠ d → 0 < W c d)
    (hB : ∀ σ : ℕ → ℕ, Set.BijOn σ S T → (∀ c ∈ S, σ c ≠ c) → 1 ≤ ∏ c ∈ S, W c (σ c)) :
    ∃ a b : ℕ → ℝ, (∀ c ∈ S, 0 < a c) ∧ (∀ d ∈ T, 0 < b d) ∧
      ∏ c ∈ S, a c = 1 ∧ ∏ d ∈ T, b d = 1 ∧ ∀ c ∈ S, ∀ d ∈ T, c ≠ d → a c * b d ≤ W c d := by
  classical
  have hB' : ∀ e : S ≃ T, (∀ x : S, (x : ℕ) ≠ e x) → 0 ≤ ∑ x : S, Real.log (W x (e x)) := by
    intro e he
    let σ : ℕ → ℕ := fun c => if h : c ∈ S then (e ⟨c, h⟩ : ℕ) else 0
    have hσ : ∀ (c : ℕ) (hc : c ∈ S), σ c = e ⟨c, hc⟩ := fun c hc => dite_eq_left hc
    have hbij : Set.BijOn σ S T := by
      refine ⟨fun c hc => ?_, fun c hc c' hc' h => ?_, fun d hd => ?_⟩
      · rw [hσ c hc]; exact (e ⟨c, hc⟩).2
      · rw [hσ c hc, hσ c' hc'] at h
        exact congrArg Subtype.val (e.injective (Subtype.ext h))
      · refine ⟨(e.symm ⟨d, hd⟩ : ℕ), (e.symm ⟨d, hd⟩).2, ?_⟩
        rw [hσ _ (e.symm ⟨d, hd⟩).2]
        simp
    have h1 := hB σ hbij fun c hc => by rw [hσ c hc]; exact (he ⟨c, hc⟩).symm
    have h2 : ∏ c ∈ S, W c (σ c) = ∏ x : S, W x (e x) := by
      rw [← Finset.prod_coe_sort]
      exact prod_congr rfl fun x _ => by rw [hσ x x.2]
    rw [h2] at h1
    rw [← Real.log_prod (s := univ) (f := fun x : S => W x (e x))
      fun x _ => (hpos x x.2 _ (e x).2 (he x)).ne']
    exact Real.log_nonneg h1
  obtain ⟨u, v, hfeas, hΦ⟩ := exists_additive_potentials (α := S) (β := T)
    (fun a b => (a : ℕ) ≠ b) (fun a b => Real.log (W a b))
    (fun a b hab => exists_derangement_through (hS.trans hT.symm) (hS ▸ hk) a b hab) hB'
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 (by omega)
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have hshift : 0 ≤ (∑ a, u a) / k + (∑ b, v b) / k := by
    rw [← add_div]; exact div_nonneg hΦ hkpos.le
  refine ⟨fun c => if h : c ∈ S then Real.exp (u ⟨c, h⟩ - (∑ a, u a) / k) else 1,
    fun d => if h : d ∈ T then Real.exp (v ⟨d, h⟩ - (∑ b, v b) / k) else 1, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc; simp only [dite_eq_left hc]; exact Real.exp_pos _
  · intro d hd; simp only [dite_eq_left hd]; exact Real.exp_pos _
  · rw [← Finset.prod_coe_sort]
    have h1 : ∀ c : S, (if h : (c : ℕ) ∈ S then Real.exp (u ⟨c, h⟩ - (∑ a, u a) / k) else 1) =
        Real.exp (u c - (∑ a, u a) / k) := fun c => by rw [dite_eq_left c.2]
    simp only [h1]
    rw [← Real.exp_sum, sum_sub_distrib, sum_const, card_univ, Fintype.card_coe, hS,
      nsmul_eq_mul, mul_div_cancel₀ _ hkne, sub_self, Real.exp_zero]
  · rw [← Finset.prod_coe_sort]
    have h1 : ∀ d : T, (if h : (d : ℕ) ∈ T then Real.exp (v ⟨d, h⟩ - (∑ b, v b) / k) else 1) =
        Real.exp (v d - (∑ b, v b) / k) := fun d => by rw [dite_eq_left d.2]
    simp only [h1]
    rw [← Real.exp_sum, sum_sub_distrib, sum_const, card_univ, Fintype.card_coe, hT,
      nsmul_eq_mul, mul_div_cancel₀ _ hkne, sub_self, Real.exp_zero]
  · intro c hc d hd hcd
    simp only [dite_eq_left hc, dite_eq_left hd]
    rw [← Real.exp_add]
    have h1 := hfeas ⟨c, hc⟩ ⟨d, hd⟩ hcd
    have hW := hpos c hc d hd hcd
    calc Real.exp (u ⟨c, hc⟩ - (∑ a, u a) / k + (v ⟨d, hd⟩ - (∑ b, v b) / k))
        ≤ Real.exp (Real.log (W c d)) := Real.exp_le_exp.2 (by linarith)
      _ = W c d := Real.exp_log hW

end Outerplanar
