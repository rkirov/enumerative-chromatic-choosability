/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.PolymerUpperRoot

/-!
# The lower deletion ratio with the neighbour-pair blocks kept

At a root `v` with neighbour set `N` in `U`, the rooted block sum is at least minus the even-block
harm, `-k x O_n z (U - v)` with `n ≥ |N|` ports. Two families of blocks do better than that, given
the upper ratio `z C ≤ k x z (C - u)` on proper subsets:

* an edge `{v, u}` recovers its deficiency, `t d_{vu} (x / k) z (U - v)`, since
  `z (U ∖ {v, u}) ≥ z (U - v) / (k x)`;
* a neighbour pair `{v, u, w}` is a positive block worth at least
  `(x / k - t (d_{vu} + d_{vw}) x³) z (U - v)`, since `z (U ∖ {v, u, w}) ≥ z (U - v) / (k x)²`.

Each edge lies in `|N| - 1` pairs, so when `(n - 1) x³ ≤ x / k` the recovered edge deficiencies
pay for the pairs' and the root ratio gains `C(|N|, 2) x / k`. The argument is the
neighbour-pair refinement proposed by Codex (OpenAI); see `PolymerPairCertificate.lean`.
-/

namespace GridGen.Polymer

open SimpleGraph Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in
/-- Double counting: each element lies in at most `|N| - 1` two-element subsets. -/
theorem sum_powersetCard_two_le (N : Finset V) (f : V → ℝ) (hf : ∀ u, 0 ≤ f u) :
    ∑ p ∈ N.powersetCard 2, ∑ u ∈ p, f u ≤ ((N.card : ℝ) - 1) * ∑ u ∈ N, f u := by
  classical
  have h1 : ∀ p ∈ N.powersetCard 2, ∑ u ∈ p, f u = ∑ u ∈ N, if u ∈ p then f u else 0 := by
    intro p hp
    rw [← Finset.sum_filter]
    congr 1
    ext u
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨(Finset.mem_powersetCard.mp hp).1 h, h⟩, fun h => h.2⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (hf u)
  have hsub : (N.powersetCard 2).filter (fun p => u ∈ p) ⊆
      (N.erase u).image (fun w => ({u, w} : Finset V)) := by
    intro p hp
    obtain ⟨hp2, hup⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpN, hcard⟩ := Finset.mem_powersetCard.mp hp2
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
    simp only [Finset.mem_insert, Finset.mem_singleton] at hup
    simp only [Finset.mem_image, Finset.mem_erase]
    rcases hup with rfl | rfl
    · exact ⟨b, ⟨hab.symm, hpN (by simp)⟩, rfl⟩
    · exact ⟨a, ⟨hab, hpN (by simp)⟩, Finset.pair_comm _ _⟩
  have hc := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Finset.card_erase_of_mem hu] at hc
  have : (((N.powersetCard 2).filter (fun p => u ∈ p)).card : ℝ) ≤ ((N.card - 1 : ℕ) : ℝ) := by
    exact_mod_cast hc
  rw [Nat.cast_sub (Finset.card_pos.mpr ⟨u, hu⟩)] at this
  simpa using this

/-- Deleting a neighbour of a deleted vertex is a small deletion. -/
theorem smallIn_erase_of_adj {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D) (C : Finset V) {v u : V}
    (hvu : G.Adj v u) (hv : v ∉ C) : smallIn G (D - 1) C u := by
  unfold smallIn
  have hsub : C.filter (G.Adj u) ⊆ (G.neighborFinset u).erase v := by
    intro y hy
    obtain ⟨hyC, hyu⟩ := Finset.mem_filter.mp hy
    refine Finset.mem_erase.mpr ⟨?_, (G.mem_neighborFinset u y).mpr hyu⟩
    rintro rfl
    exact hv hyC
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem ((G.mem_neighborFinset u v).mpr hvu.symm),
    G.card_neighborFinset_eq_degree] at hcard
  have := hdeg u
  omega

/-- Every rooted block is at least minus its harm, compared with `z (U - v)` by peeling. -/
theorem graphActivity_block_ge_neg_harm {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {x t : ℝ} (hx : 0 ≤ x) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : Finset V) {v : V} (hv : v ∈ U) (z : Finset V → ℝ) (hz : ∀ A, A ⊂ U → 0 ≤ z A)
    (hmono : ∀ C u, C ⊂ U → u ∈ C → smallIn G (D - 1) C u → z (C.erase u) ≤ z C)
    {S : Finset V} (hS : S ∈ rootedBlocks U v) :
    0 ≤ graphActivity G L k x S t * z (U \ S) + rootHarm G k x S * z (U.erase v) := by
  obtain ⟨hSU, hvS, hcard⟩ := mem_rootedBlocks hS
  have hne : S.Nonempty := ⟨v, hvS⟩
  have hH := rootHarm_nonneg G k hx S
  have hUv : U.erase v ⊂ U := Finset.erase_ssubset hv
  have hZ0 := hz _ hUv
  by_cases hw : 0 ≤ graphActivity G L k x S t
  · exact add_nonneg (mul_nonneg hw (hz _ (sdiff_ssubset_of_mem hv hvS))) (mul_nonneg hH hZ0)
  · push Not at hw
    have hbes : (blockEdgeSets G S).Nonempty := by
      by_contra hb
      rw [Finset.not_nonempty_iff_eq_empty] at hb
      simp [graphActivity, blockCoefficient, hb] at hw
    obtain ⟨T, hT⟩ := hbes
    have hch := peelChain_of_mem_blockEdgeSets G hdeg hT U {v}
      (Finset.singleton_subset_iff.mpr hvS) (Finset.singleton_nonempty v)
    rw [Finset.sdiff_singleton_eq_erase] at hch
    have hle : z (U \ S) ≤ z (U.erase v) := hch.le z fun C u hC hu hs =>
      hmono C u (lt_of_le_of_lt hC hUv) hu hs
    have hlow := neg_rootHarm_le G hL hx ht hne
    nlinarith [mul_le_mul_of_nonpos_left hle hw.le]

/-- **The plain lower ratio at a root with at most `n` neighbours.** -/
theorem graphActivity_root_lower_plain {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {x₀ e o r : ℝ} (hc : ParityCert D x₀ e o r)
    {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {x t : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x₀) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : Finset V) {v : V} (hv : v ∈ U) {n : ℕ} (hn : (U.filter (G.Adj v)).card ≤ n)
    (z : Finset V → ℝ) (hz : ∀ A, A ⊂ U → 0 ≤ z A)
    (hrec : z U = (k : ℝ) * x * z (U.erase v) +
      ∑ S ∈ rootedBlocks U v, graphActivity G L k x S t * z (U \ S))
    (hmono : ∀ C u, C ⊂ U → u ∈ C → smallIn G (D - 1) C u → z (C.erase u) ≤ z C) :
    (k : ℝ) * x * (1 - (parityPower (1 + x₀ * o) (x₀ * e) n).2) * z (U.erase v) ≤ z U := by
  have hsum := Finset.sum_nonneg fun S hS =>
    graphActivity_block_ge_neg_harm G hdeg hL hx ht U hv z hz hmono (S := S) hS
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
  have hharm := mul_le_mul_of_nonneg_right (rootHarm_sum_le G hdeg hc k hx hxx U hv hn)
    (hz _ (Finset.erase_ssubset hv))
  rw [hrec]
  nlinarith

/-- **The lower ratio at a root with the pair blocks kept.** -/
theorem graphActivity_pair_root_lower {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {x₀ e o r : ℝ} (hc : ParityCert D x₀ e o r)
    {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {x t : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x₀) (hkx : 0 < (k : ℝ) * x) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : Finset V) {v : V} (hv : v ∈ U) {n : ℕ} (hn : (U.filter (G.Adj v)).card ≤ n)
    (hpd : ((n : ℝ) - 1) * x ^ 3 ≤ x / k)
    (z : Finset V → ℝ) (hz : ∀ A, A ⊂ U → 0 ≤ z A)
    (hrec : z U = (k : ℝ) * x * z (U.erase v) +
      ∑ S ∈ rootedBlocks U v, graphActivity G L k x S t * z (U \ S))
    (hmono : ∀ C u, C ⊂ U → u ∈ C → smallIn G (D - 1) C u → z (C.erase u) ≤ z C)
    (hup : ∀ C u, C ⊂ U → u ∈ C → z C ≤ (k : ℝ) * x * z (C.erase u)) :
    ((k : ℝ) * x * (1 - (parityPower (1 + x₀ * o) (x₀ * e) n).2) +
        (((U.filter (G.Adj v)).card.choose 2 : ℕ) : ℝ) * (x / k)) * z (U.erase v) ≤ z U := by
  classical
  set N := U.filter (G.Adj v) with hN
  set Z := z (U.erase v) with hZ
  set a := (k : ℝ) * x with ha
  have hk : (0 : ℝ) < k := by
    by_contra h; push Not at h
    have : (k : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
    rw [ha, this, zero_mul] at hkx; exact lt_irrefl _ hkx
  have hZ0 : 0 ≤ Z := hz _ (Finset.erase_ssubset hv)
  have hUv : U.erase v ⊂ U := Finset.erase_ssubset hv
  have hvN : v ∉ N := by simp [hN]
  have hNU : ∀ u ∈ N, u ∈ U ∧ G.Adj v u := fun u hu => Finset.mem_filter.mp hu
  let f : Finset V → ℝ := fun S => graphActivity G L k x S t * z (U \ S)
  let h : Finset V → ℝ := fun S => f S + rootHarm G k x S * Z
  -- (1) every rooted block is at least minus its harm
  have hgen : ∀ S ∈ rootedBlocks U v, 0 ≤ h S := fun S hS =>
    graphActivity_block_ge_neg_harm G hdeg hL hx ht U hv z hz hmono hS
  -- (2) the edges at the root
  have hedge : ∀ u ∈ N, t * listDeficiency L k {v, u} * (x / k) * Z ≤ h {v, u} := by
    intro u hu
    obtain ⟨huU, hadj⟩ := hNU u hu
    have hset : U \ {v, u} = (U.erase v).erase u := by
      ext y; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_erase]; tauto
    have huUv : u ∈ U.erase v := Finset.mem_erase.mpr ⟨hadj.ne.symm, huU⟩
    have hsm := smallIn_erase_of_adj G hdeg (U.erase v) hadj (Finset.notMem_erase v U)
    have hle : z (U \ {v, u}) ≤ Z := by rw [hset]; exact hmono _ u hUv huUv hsm
    have hge : Z ≤ a * z (U \ {v, u}) := by rw [hset]; exact hup _ u hUv huUv
    have hharm : (k : ℝ) * x ^ 2 ≤ rootHarm G k x {v, u} := by
      have h2 : ({v, u} : Finset V).card = 2 := Finset.card_pair hadj.ne
      have htrees : (1 : ℝ) ≤ (spanningTreeSets G {v, u}).card := by
        have := blockCoefficient_abs_le_trees G {v, u}
        rwa [blockCoefficient_pair_of_adj G hadj, abs_neg, abs_one] at this
      simp only [rootHarm, h2, even_two, ite_true, Finset.sum_const, nsmul_eq_mul]
      norm_num
      nlinarith [mul_nonneg (le_of_lt hk) (sq_nonneg x)]
    have hd0 := listDeficiency_nonneg hL (S := {v, u}) ⟨v, by simp⟩
    have htd : 0 ≤ t * listDeficiency L k {v, u} := mul_nonneg ht.1 hd0
    simp only [h, f]
    rw [graphActivity_pair_of_adj G x t hadj]
    -- t d x² z' ≥ t d (x / k) Z, from Z ≤ k x z'
    have hrec' : t * listDeficiency L k {v, u} * (x / k) * Z ≤
        t * listDeficiency L k {v, u} * x ^ 2 * z (U \ {v, u}) := by
      have : (x / k) * Z ≤ x ^ 2 * z (U \ {v, u}) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hk]
        nlinarith [mul_le_mul_of_nonneg_left hge hx]
      nlinarith [mul_le_mul_of_nonneg_left this htd]
    have hzz := hz (U \ {v, u}) (sdiff_ssubset_of_mem hv (by simp))
    nlinarith [mul_le_mul_of_nonneg_left hle (mul_nonneg (le_of_lt hk) (sq_nonneg x)),
      mul_le_mul_of_nonneg_right hharm hZ0]
  -- (3) the neighbour pairs
  have hpair : ∀ p ∈ N.powersetCard 2,
      (x / k) * Z - t * (∑ u ∈ p, listDeficiency L k {v, u}) * x ^ 3 * Z ≤ h (insert v p) := by
    intro p hp
    obtain ⟨hpN, hcard⟩ := Finset.mem_powersetCard.mp hp
    obtain ⟨u, w, huw, rfl⟩ := Finset.card_eq_two.mp hcard
    obtain ⟨huU, hu⟩ := hNU u (hpN (by simp))
    obtain ⟨hwU, hw⟩ := hNU w (hpN (by simp))
    have hS : insert v ({u, w} : Finset V) = {v, u, w} := rfl
    rw [hS, Finset.sum_pair huw]
    have hset : U \ {v, u, w} = ((U.erase v).erase u).erase w := by
      ext y; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_erase]; tauto
    have huUv : u ∈ U.erase v := Finset.mem_erase.mpr ⟨hu.ne.symm, huU⟩
    have hwUvu : w ∈ (U.erase v).erase u :=
      Finset.mem_erase.mpr ⟨huw.symm, Finset.mem_erase.mpr ⟨hw.ne.symm, hwU⟩⟩
    have hUvu : (U.erase v).erase u ⊂ U := lt_of_le_of_lt (Finset.erase_subset _ _) hUv
    have hsmu := smallIn_erase_of_adj G hdeg (U.erase v) hu (Finset.notMem_erase v U)
    have hsmw := smallIn_erase_of_adj G hdeg ((U.erase v).erase u) hw
      (fun h => Finset.notMem_erase v U (Finset.mem_of_mem_erase h))
    have hle1 := hmono _ u hUv huUv hsmu
    have hle2 := hmono _ w hUvu hwUvu hsmw
    have hge1 := hup _ u hUv huUv
    have hge2 := hup _ w hUvu hwUvu
    set z3 := z (((U.erase v).erase u).erase w)
    have hz3 : 0 ≤ z3 := hz _ (lt_of_le_of_lt (Finset.erase_subset _ _) hUvu)
    have hle : z3 ≤ Z := hle2.trans hle1
    have hge : Z ≤ a * (a * z3) := hge1.trans (mul_le_mul_of_nonneg_left hge2 (le_of_lt hkx))
    have hact := graphActivity_triple_ge G hL hx ht hu hw huw
    have hharm0 : rootHarm G k x {v, u, w} = 0 := by
      have h3 : ({v, u, w} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hu.ne, hw.ne]), Finset.card_pair huw]
      simp [rootHarm, h3, show ¬ Even 3 by decide]
    simp only [h, f, hharm0, zero_mul, add_zero]
    rw [hset]
    have hdu := listDeficiency_nonneg hL (S := {v, u}) ⟨v, by simp⟩
    have hdw := listDeficiency_nonneg hL (S := {v, w}) ⟨v, by simp⟩
    set dd := listDeficiency L k {v, u} + listDeficiency L k {v, w}
    have htd : 0 ≤ t * dd := mul_nonneg ht.1 (add_nonneg hdu hdw)
    -- k x³ z3 ≥ (x / k) Z
    have hmain : (x / k) * Z ≤ (k : ℝ) * x ^ 3 * z3 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hk]
      have : x * Z ≤ x * (a * (a * z3)) := mul_le_mul_of_nonneg_left hge hx
      nlinarith
    calc (x / k) * Z - t * dd * x ^ 3 * Z
        ≤ (k : ℝ) * x ^ 3 * z3 - t * dd * x ^ 3 * z3 := by
          nlinarith [mul_le_mul_of_nonneg_left hle (mul_nonneg htd (pow_nonneg hx 3))]
      _ = ((k : ℝ) - t * dd) * x ^ 3 * z3 := by ring
      _ ≤ graphActivity G L k x {v, u, w} t * z3 := mul_le_mul_of_nonneg_right hact hz3
  -- (4) assemble
  have hQ2 : N.image (fun u => ({v, u} : Finset V)) ⊆ rootedBlocks U v := by
    intro S hS
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨huU, hadj⟩ := hNU u hu
    simp only [rootedBlocks, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, by simp, (Finset.card_pair hadj.ne).ge⟩
    intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl <;> assumption
  have hQ3 : (N.powersetCard 2).image (insert v) ⊆ rootedBlocks U v := by
    intro S hS
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨hpN, hcard⟩ := Finset.mem_powersetCard.mp hp
    simp only [rootedBlocks, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.insert_subset hv fun y hy => (hNU y (hpN hy)).1, by simp, ?_⟩
    rw [Finset.card_insert_of_notMem (fun h => hvN (hpN h)), hcard]; omega
  have hinj2 : Set.InjOn (fun u => ({v, u} : Finset V)) (N : Set V) :=
    (pair_injOn U v).mono fun u hu => Finset.mem_coe.mpr
      (Finset.mem_erase.mpr ⟨(hNU u hu).2.ne.symm, (hNU u hu).1⟩)
  have hinj3 : Set.InjOn (insert v) ((N.powersetCard 2 : Finset (Finset V)) : Set (Finset V)) := by
    intro p hp q hq hpq
    have hvp : v ∉ p := fun h => hvN ((Finset.mem_powersetCard.mp hp).1 h)
    have hvq : v ∉ q := fun h => hvN ((Finset.mem_powersetCard.mp hq).1 h)
    rw [← Finset.erase_insert hvp, ← Finset.erase_insert hvq]
    exact congrArg (fun S => Finset.erase S v) hpq
  have hdisj : Disjoint (N.image (fun u => ({v, u} : Finset V)))
      ((N.powersetCard 2).image (insert v)) := by
    rw [Finset.disjoint_left]
    intro S hS2 hS3
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hS2
    obtain ⟨p, hp, hpS⟩ := Finset.mem_image.mp hS3
    have h3 : (insert v p).card = 3 := by
      rw [Finset.card_insert_of_notMem (fun h => hvN ((Finset.mem_powersetCard.mp hp).1 h)),
        (Finset.mem_powersetCard.mp hp).2]
    rw [hpS, Finset.card_pair (hNU u hu).2.ne] at h3
    omega
  have hsum : ∑ S ∈ rootedBlocks U v, h S ≥
      ∑ u ∈ N, t * listDeficiency L k {v, u} * (x / k) * Z +
        ∑ p ∈ N.powersetCard 2,
          ((x / k) * Z - t * (∑ u ∈ p, listDeficiency L k {v, u}) * x ^ 3 * Z) := by
    calc ∑ S ∈ rootedBlocks U v, h S
        ≥ ∑ S ∈ N.image (fun u => ({v, u} : Finset V)) ∪ (N.powersetCard 2).image (insert v),
          h S := Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset hQ2 hQ3)
            (fun S hS _ => hgen S hS)
      _ = ∑ u ∈ N, h {v, u} + ∑ p ∈ N.powersetCard 2, h (insert v p) := by
          rw [Finset.sum_union hdisj, Finset.sum_image hinj2, Finset.sum_image hinj3]
      _ ≥ _ := add_le_add (Finset.sum_le_sum hedge) (Finset.sum_le_sum hpair)
  -- the deficiency terms net to something nonnegative
  have hdc := sum_powersetCard_two_le N (fun u => listDeficiency L k {v, u})
    (fun u => listDeficiency_nonneg hL (S := {v, u}) ⟨v, by simp⟩)
  have hD0 : 0 ≤ ∑ u ∈ N, listDeficiency L k {v, u} :=
    Finset.sum_nonneg fun u _ => listDeficiency_nonneg hL (S := {v, u}) ⟨v, by simp⟩
  have hNn : ((N.card : ℝ) - 1) * x ^ 3 ≤ x / k := by
    have : (N.card : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [pow_nonneg hx 3]
  have hpairs : ∑ p ∈ N.powersetCard 2,
      ((x / k) * Z - t * (∑ u ∈ p, listDeficiency L k {v, u}) * x ^ 3 * Z) =
      ((N.card.choose 2 : ℕ) : ℝ) * (x / k) * Z -
        t * x ^ 3 * Z * ∑ p ∈ N.powersetCard 2, ∑ u ∈ p, listDeficiency L k {v, u} := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul,
      Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun p _ => by ring
  have hedges : ∑ u ∈ N, t * listDeficiency L k {v, u} * (x / k) * Z =
      t * (x / k) * Z * ∑ u ∈ N, listDeficiency L k {v, u} := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by ring
  have hnet : 0 ≤ t * (x / k) * Z * ∑ u ∈ N, listDeficiency L k {v, u} -
      t * x ^ 3 * Z * ∑ p ∈ N.powersetCard 2, ∑ u ∈ p, listDeficiency L k {v, u} := by
    have htZ : 0 ≤ t * Z := mul_nonneg ht.1 hZ0
    have h1 : x ^ 3 * ∑ p ∈ N.powersetCard 2, ∑ u ∈ p, listDeficiency L k {v, u} ≤
        (x / k) * ∑ u ∈ N, listDeficiency L k {v, u} := by
      calc _ ≤ x ^ 3 * (((N.card : ℝ) - 1) * ∑ u ∈ N, listDeficiency L k {v, u}) :=
            mul_le_mul_of_nonneg_left hdc (pow_nonneg hx 3)
        _ = (((N.card : ℝ) - 1) * x ^ 3) * ∑ u ∈ N, listDeficiency L k {v, u} := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hNn hD0
    nlinarith [mul_le_mul_of_nonneg_left h1 htZ]
  -- the harm
  have hharm := rootHarm_sum_le G hdeg hc k hx hxx U hv hn
  have hsplit : ∑ S ∈ rootedBlocks U v, h S =
      ∑ S ∈ rootedBlocks U v, graphActivity G L k x S t * z (U \ S) +
        (∑ S ∈ rootedBlocks U v, rootHarm G k x S) * Z := by
    simp only [h, f, Finset.sum_add_distrib, Finset.sum_mul]
  rw [hrec]
  have hHZ := mul_le_mul_of_nonneg_right hharm hZ0
  nlinarith [hsum, hsplit, hpairs, hedges, hnet]

end GridGen.Polymer
