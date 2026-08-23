/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.LeafPeeling
import Cacti.Absorb
import Cacti.Uniform
import Cacti.Bridge
import Cacti.CyclePair
import Cacti.CutVertex

/-!
# The block induction: statement and transport steps

The `k ≥ 4` cactus theorem (handoff §6, UM-107/108) is a strong induction on the vertex count
carrying the pair invariant: for pair-dominant weights, the weighted rooted profile is
pair-bounded by the uniform normalizer times the weight normalizers. This file packages the
transport steps the induction consumes, and runs the induction.

* `rootedWcol_one` / `rootedWcol_const_at` / `rootedWcol_of_card_eq_one` — weight
  specializations, the last of them the one-vertex evaluation both base cases run on;
* `rootedCol_pendant_uniform` — the uniform side of pendant absorption carries factor `k - 1`;
* `pendant_weight_dominant` — pendant absorption preserves pair-dominance with normalizer
  `(k-1) · W x · W u` (the bridge inequality, squared);
* `edge_pair_base` — the single-edge base case, the pair-invariant counterpart of `gm_edge_base`;
* `rootedCol_absorb_uniform` — the uniform side of absorption at a cut vertex;
* `pair_bound_of_cut` — the cut-vertex step: the pair bound on both sides of a split gives the
  pair bound for the whole;
* `cactus_pair_bound` — the induction itself.

The structural dichotomy it rests on — a cactus with no pendant vertex is a single cycle, or
splits at a cut vertex — is `exists_cut_split_or_cyclic_index`, proved here from
`Cacti/CutVertex.lean` and `exists_iso_closePath_of_two_regular`. Everything in this file is
proved outright, with no unproved step: the whole induction is complete.
-/

namespace ListColoring

open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Trivial weights recover the rooted count. -/
theorem rootedWcol_one (L : ListAssignment V) (r : V) (c : ℕ) :
    rootedWcol G L (fun _ _ => 1) r c = rootedCol G L r c := by
  rw [rootedWcol, rootedCol]
  simp

/-- A weight constant at one vertex and trivial elsewhere extracts as a factor. -/
theorem rootedWcol_const_at (L : ListAssignment V) (u : V) (m : ℕ) (r : V) (c : ℕ) :
    rootedWcol G L (fun v _ => if v = u then m else 1) r c = m * rootedCol G L r c := by
  rw [rootedWcol, rootedCol, Finset.card_eq_sum_ones, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [Finset.prod_ite_eq' Finset.univ u (fun _ => m)]
  simp

/-- **Pair-dominance is preserved by pendant absorption**: if the weights at `x` and at `u`
are pair-dominant on `k`-lists over `W x` and `W u`, the absorbed weight
`d ↦ w u d · ∑_{e ∈ L x, e ≠ d} w x e` is pair-dominant over `(k-1) · W x · W u`. -/
theorem pendant_weight_dominant {k : ℕ} (hk : 3 ≤ k) {Lx Lu : Finset ℕ}
    (hLx : Lx.card = k) {wx wu : ℕ → ℕ} {Wx Wu : ℕ}
    (hdx : ∀ c ∈ Lx, ∀ d ∈ Lx, c ≠ d → Wx ^ 2 ≤ wx c * wx d)
    (hdu : ∀ c ∈ Lu, ∀ d ∈ Lu, c ≠ d → Wu ^ 2 ≤ wu c * wu d) :
    ∀ c ∈ Lu, ∀ d ∈ Lu, c ≠ d →
      ((k - 1) * Wx * Wu) ^ 2 ≤
        (wu c * ∑ e ∈ Lx.filter (· ≠ c), wx e) * (wu d * ∑ e ∈ Lx.filter (· ≠ d), wx e) := by
  intro c hc d hd hcd
  have hsum : ∀ c', (k - 1) * Wx ≤ ∑ e ∈ Lx.filter (· ≠ c'), wx e := by
    intro c'
    by_cases hc' : c' ∈ Lx
    · have h := bridge_sum_ge hk hLx hdx hc'
      calc (k - 1) * Wx ≤ ∑ e ∈ Lx.erase c', wx e := h
        _ = ∑ e ∈ Lx.filter (· ≠ c'), wx e := by
            congr 1
            ext e
            simp [Finset.mem_erase, Finset.mem_filter, and_comm]
    · -- with `c' ∉ Lx` the filter contains any erase; the erase bound applies
      obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ ∈ Lx := Finset.card_pos.mp (by omega) |>.imp fun _ h => h
      calc (k - 1) * Wx ≤ ∑ e ∈ Lx.erase c₀, wx e := bridge_sum_ge hk hLx hdx hc₀
        _ ≤ ∑ e ∈ Lx.filter (· ≠ c'), wx e :=
            Finset.sum_le_sum_of_subset (fun e he => Finset.mem_filter.mpr
              ⟨Finset.mem_of_mem_erase he,
                fun heq => hc' (heq ▸ Finset.mem_of_mem_erase he)⟩)
  calc ((k - 1) * Wx * Wu) ^ 2
      = (Wu ^ 2) * (((k - 1) * Wx) * ((k - 1) * Wx)) := by ring
    _ ≤ (wu c * wu d) * ((∑ e ∈ Lx.filter (· ≠ c), wx e) * (∑ e ∈ Lx.filter (· ≠ d), wx e)) := by
        exact Nat.mul_le_mul (hdu c hc d hd hcd) (Nat.mul_le_mul (hsum c) (hsum d))
    _ = (wu c * ∑ e ∈ Lx.filter (· ≠ c), wx e) * (wu d * ∑ e ∈ Lx.filter (· ≠ d), wx e) := by
        ring

/-- Rooted weighted count of a one-vertex graph: the weight of the root's colour. -/
theorem rootedWcol_of_card_eq_one {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h1 : Fintype.card V = 1)
    (L : ListAssignment V) (w : V → ℕ → ℕ) (r : V) {c : ℕ} (hc : c ∈ L r) :
    rootedWcol G L w r c = w r c := by
  have hsub : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  rw [rootedWcol]
  have hset : (G.colorings L).filter (fun f => f r = c) = {fun _ => c} := by
    ext f
    simp only [Finset.mem_filter, SimpleGraph.mem_colorings_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hmem, hprop⟩, hr⟩
      funext v
      rw [Subsingleton.elim v r, hr]
    · rintro rfl
      refine ⟨⟨fun v => ?_, fun v u hadj => ?_⟩, rfl⟩
      · rw [Subsingleton.elim v r]; exact hc
      · exact absurd (Subsingleton.elim v u) hadj.ne
  rw [hset, Finset.sum_singleton]
  rw [show (Finset.univ : Finset V) = {r} from by
    ext v; simp [Subsingleton.elim v r]]
  rw [Finset.prod_singleton]

section PendantPrereqs

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
/-- The uniform side of pendant absorption: the factor is exactly `k - 1`. -/
theorem rootedCol_pendant_uniform {x u : V} (hxu : G.Adj x u)
    (huniq : ∀ y, G.Adj x y → y = u) {r : V} (hrx : r ≠ x) {k : ℕ} (hk : 1 ≤ k) (c : ℕ) :
    rootedCol G (constList V k) r c =
      (k - 1) * rootedCol (G.induce {y | y ≠ x}) (fun v => constList V k v.val) ⟨r, hrx⟩ c := by
  have hu : u ∈ {y : V | y ≠ x} := hxu.ne'
  have h := rootedWcol_pendant (G := G) hxu huniq hrx (constList V k) (fun _ _ => 1) c
  rw [rootedWcol_one] at h
  rw [h]
  calc rootedWcol (G.induce {y | y ≠ x}) (fun v => constList V k v.val)
        (fun v d => if v.val = u then
            (fun _ => 1) d * ∑ e ∈ (constList V k x).filter (· ≠ d), (fun _ _ => 1) x e
          else (fun _ _ => 1) v.val d) ⟨r, hrx⟩ c
      = rootedWcol (G.induce {y | y ≠ x}) (fun v => constList V k v.val)
          (fun v _ => if v = (⟨u, hu⟩ : {y : V // y ≠ x}) then k - 1 else 1) ⟨r, hrx⟩ c := by
        refine rootedWcol_weight_congr (fun v d hd => ?_) _ _
        by_cases hvu : v.val = u
        · rw [if_pos hvu, if_pos (Subtype.ext hvu)]
          simp only [one_mul]
          rw [Finset.sum_const, smul_eq_mul, mul_one]
          have hd' : d ∈ Finset.range k := hd
          rw [show (constList V k x).filter (· ≠ d) = (Finset.range k).erase d from by
            ext e
            simp [Finset.mem_erase, Finset.mem_filter, and_comm, constList_apply]]
          rw [Finset.card_erase_of_mem hd', Finset.card_range]
        · rw [if_neg hvu, if_neg (fun h => hvu (congrArg Subtype.val h))]
    _ = (k - 1) * rootedCol (G.induce {y | y ≠ x}) (fun v => constList V k v.val)
          ⟨r, hrx⟩ c :=
        rootedWcol_const_at _ _ _ _ _

/-- **The single-edge base of the pair induction** at general `k`: on two adjacent vertices the
rooted profile is `c ↦ w r c · ∑_{e ∀ c} w x e`, and `pendant_weight_dominant` clears the uniform
factor `(k - 1)` — the same computation `gm_edge_base` performs for the GM invariant. -/
theorem edge_pair_base (hcard : Fintype.card V = 2) (hG : IsCactus G) {k : ℕ} (hk : 4 ≤ k)
    (L : ListAssignment V) (hL : IsNListAssignment L k) (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v : V, ∀ c ∈ L v, ∀ d ∈ L v, c ≠ d → (W v) ^ 2 ≤ w v c * w v d) (r : V)
    (c d : ℕ) (hc : c ∈ L r) (hd : d ∈ L r) (hcd : c ≠ d) :
    (rootedCol G (constList V k) r 0 * ∏ v, W v) ^ 2
      ≤ rootedWcol G L w r c * rootedWcol G L w r d := by
  classical
  obtain ⟨x, hxr⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) r
  have hrx : r ≠ x := fun h => hxr h.symm
  have huniv : (Finset.univ : Finset V) = {r, x} := by
    refine (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_).symm
    rw [Finset.card_univ, hcard, Finset.card_insert_of_notMem (by simpa using hrx),
      Finset.card_singleton]
  have hcard1 : Fintype.card {y : V // y ≠ x} = 1 := by
    have hcong := Fintype.card_congr (delOptionEquiv x)
    rw [Fintype.card_option] at hcong
    omega
  -- the two vertices are adjacent, and `x` is a pendant with neighbour `r`
  have hxu : G.Adj x r := by
    obtain ⟨Wk⟩ := hG.1.preconnected x r
    have hnil : ¬ Wk.Nil := Walk.not_nil_of_ne hxr
    have hadj := Wk.adj_snd hnil
    have hmem : Wk.snd ∈ ({r, x} : Finset V) := huniv ▸ Finset.mem_univ _
    rcases Finset.mem_insert.mp hmem with h | h
    · rwa [h] at hadj
    · rw [Finset.mem_singleton] at h
      exact absurd (h ▸ hadj) (G.irrefl)
  have huniq : ∀ y, G.Adj x y → y = r := by
    intro y hy
    have hmem : y ∈ ({r, x} : Finset V) := huniv ▸ Finset.mem_univ _
    rcases Finset.mem_insert.mp hmem with h | h
    · exact h
    · rw [Finset.mem_singleton] at h
      exact absurd (h ▸ hy) (G.irrefl)
  -- the rooted profile of an edge, and its uniform count
  have hprof : ∀ a ∈ L r, rootedWcol G L w r a
      = w r a * ∑ e ∈ (L x).filter (· ≠ a), w x e := by
    intro a ha
    rw [rootedWcol_pendant hxu huniq hrx L w a,
      rootedWcol_of_card_eq_one hcard1 _ _ ⟨r, hrx⟩ ha]
    simp
  have hA : rootedCol G (constList V k) r 0 = k - 1 := by
    have h0 : (0 : ℕ) ∈ constList V k (⟨r, hrx⟩ : {y : V // y ≠ x}).val := by
      simp [constList_apply, Finset.mem_range]
      omega
    have hone := rootedWcol_of_card_eq_one (G := G.induce {y : V | y ≠ x}) hcard1
      (fun v => constList V k v.val) (fun _ _ => 1) ⟨r, hrx⟩ h0
    rw [rootedWcol_one] at hone
    rw [rootedCol_pendant_uniform hxu huniq hrx (by omega) 0, hone, Nat.mul_one]
  have hprodV : (∏ v, W v) = W r * W x := by
    rw [huniv, Finset.prod_insert (by simpa using hrx), Finset.prod_singleton]
  rw [hA, hprodV, hprof c hc, hprof d hd]
  calc ((k - 1) * (W r * W x)) ^ 2
      = ((k - 1) * W x * W r) ^ 2 := by ring
    _ ≤ _ := pendant_weight_dominant (by omega) (hL x)
          (fun a ha b hb hab => hdom x a ha b hb hab)
          (fun a ha b hb hab => hdom r a ha b hb hab) c hc d hd hcd


/-- The uniform side of absorption at a cut vertex: the `B`-side uniform count factors out,
since by colour symmetry it does not depend on the colour at the cut vertex. -/
theorem rootedCol_absorb_uniform {A B : Set V} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    {u : V} (huA : u ∈ A) (huB : u ∈ B) (hcover : ∀ v, v ∈ A ∨ v ∈ B)
    (hmeet : ∀ v, v ∈ A → v ∈ B → v = u)
    (hedge : ∀ x y, G.Adj x y → (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    {r : V} (hrA : r ∈ A) {k : ℕ} (hk : 1 ≤ k) (c : ℕ) :
    rootedCol G (constList V k) r c =
      rootedCol (G.induce B) (constList B k) ⟨u, huB⟩ 0 *
        rootedCol (G.induce A) (constList A k) ⟨r, hrA⟩ c := by
  have h := rootedWcol_absorb huA huB hcover hmeet hedge hrA (constList V k) (fun _ _ => 1) c
  rw [rootedWcol_one] at h
  rw [h]
  have hzero : (0 : ℕ) ∈ Finset.range k := Finset.mem_range.mpr (by omega)
  calc rootedWcol (G.induce A) (fun v => constList V k v.val)
        (fun v d => if v.val = u then
            (1 : ℕ) * rootedWcol (G.induce B) (fun x => constList V k x.val)
              (fun x _ => if x.val = u then 1 else 1) ⟨u, huB⟩ d
          else 1) ⟨r, hrA⟩ c
      = rootedWcol (G.induce A) (fun v => constList V k v.val)
          (fun v _ => if v = (⟨u, huA⟩ : A) then
              rootedCol (G.induce B) (fun x => constList V k x.val) ⟨u, huB⟩ 0
            else 1) ⟨r, hrA⟩ c := by
        refine rootedWcol_weight_congr (fun v d hd => ?_) _ _
        by_cases hvu : v.val = u
        · rw [if_pos hvu, if_pos (Subtype.ext hvu), one_mul]
          rw [rootedWcol_weight_congr (fun _ _ _ => ite_self 1) _ _, rootedWcol_one]
          exact rootedCol_constList_eq (G.induce B) k ⟨u, huB⟩ hd hzero
        · rw [if_neg hvu, if_neg (fun hv => hvu (congrArg Subtype.val hv))]
    _ = _ := rootedWcol_const_at _ _ _ _ _

/-- **The cut-vertex step**: with `V` split at `u` into `A` and `B` and the root in `A`, the
pair bound on both sides gives the pair bound for `G`. The `B` side is absorbed into the weight
at `u`, where its uniform count times its normalizer product becomes the new normalizer. -/
theorem pair_bound_of_cut {A B : Set V} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    {u : V} (huA : u ∈ A) (huB : u ∈ B) (hcover : ∀ v, v ∈ A ∨ v ∈ B)
    (hmeet : ∀ v, v ∈ A → v ∈ B → v = u)
    (hedge : ∀ x y, G.Adj x y → (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    {r : V} (hrA : r ∈ A) {k : ℕ} (hk : 1 ≤ k)
    (L : ListAssignment V) (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, ∀ c ∈ L v, ∀ d ∈ L v, c ≠ d → (W v) ^ 2 ≤ w v c * w v d)
    (hBside : ∀ (wB : B → ℕ → ℕ) (WB : B → ℕ),
      (∀ x, ∀ c ∈ L x.val, ∀ d ∈ L x.val, c ≠ d → (WB x) ^ 2 ≤ wB x c * wB x d) →
      ∀ c ∈ L u, ∀ d ∈ L u, c ≠ d →
        (rootedCol (G.induce B) (constList B k) ⟨u, huB⟩ 0 * ∏ x, WB x) ^ 2 ≤
          rootedWcol (G.induce B) (fun x => L x.val) wB ⟨u, huB⟩ c *
            rootedWcol (G.induce B) (fun x => L x.val) wB ⟨u, huB⟩ d)
    (hAside : ∀ (wA : A → ℕ → ℕ) (WA : A → ℕ),
      (∀ v, ∀ c ∈ L v.val, ∀ d ∈ L v.val, c ≠ d → (WA v) ^ 2 ≤ wA v c * wA v d) →
      ∀ c ∈ L r, ∀ d ∈ L r, c ≠ d →
        (rootedCol (G.induce A) (constList A k) ⟨r, hrA⟩ 0 * ∏ v, WA v) ^ 2 ≤
          rootedWcol (G.induce A) (fun v => L v.val) wA ⟨r, hrA⟩ c *
            rootedWcol (G.induce A) (fun v => L v.val) wA ⟨r, hrA⟩ d) :
    ∀ c ∈ L r, ∀ d ∈ L r, c ≠ d →
      (rootedCol G (constList V k) r 0 * ∏ v, W v) ^ 2 ≤
        rootedWcol G L w r c * rootedWcol G L w r d := by
  intro c hc d hd hcd
  -- the `B` side, with `u`'s own weight charged to the `A` side
  have hB := hBside (fun x e => if x.val = u then 1 else w x.val e)
    (fun x => if x.val = u then 1 else W x.val) (by
      intro x c' hc' d' hd' hcd'
      by_cases hxu : x.val = u
      · rw [if_pos hxu, if_pos hxu, if_pos hxu]
        omega
      · rw [if_neg hxu, if_neg hxu, if_neg hxu]
        exact hdom x.val c' hc' d' hd' hcd')
  -- the absorbed weight at `u` is still pair-dominant, over the `B`-side normalizer
  have hA := hAside
    (fun v d' => if v.val = u then
        w u d' * rootedWcol (G.induce B) (fun x => L x.val)
          (fun x e => if x.val = u then 1 else w x.val e) ⟨u, huB⟩ d'
      else w v.val d')
    (fun v => if v.val = u then
        W u * (rootedCol (G.induce B) (constList B k) ⟨u, huB⟩ 0 *
          ∏ x : B, (if x.val = u then 1 else W x.val))
      else W v.val)
    (by
      intro v c' hc' d' hd' hcd'
      by_cases hvu : v.val = u
      · rw [if_pos hvu, if_pos hvu, if_pos hvu]
        have h1 := hdom u c' (hvu ▸ hc') d' (hvu ▸ hd') hcd'
        have h2 := hB c' (hvu ▸ hc') d' (hvu ▸ hd') hcd'
        calc (W u * (rootedCol (G.induce B) (constList B k) ⟨u, huB⟩ 0 *
                ∏ x : B, (if x.val = u then 1 else W x.val))) ^ 2
            = W u ^ 2 * (rootedCol (G.induce B) (constList B k) ⟨u, huB⟩ 0 *
                ∏ x : B, (if x.val = u then 1 else W x.val)) ^ 2 := by ring
          _ ≤ (w u c' * w u d') *
              (rootedWcol (G.induce B) (fun x => L x.val)
                  (fun x e => if x.val = u then 1 else w x.val e) ⟨u, huB⟩ c' *
                rootedWcol (G.induce B) (fun x => L x.val)
                  (fun x e => if x.val = u then 1 else w x.val e) ⟨u, huB⟩ d') :=
              Nat.mul_le_mul h1 h2
          _ = _ := by ring
      · rw [if_neg hvu, if_neg hvu, if_neg hvu]
        exact hdom v.val c' hc' d' hd' hcd') c hc d hd hcd
  -- rewrite the goal through absorption, then match the normalizer products
  rw [rootedWcol_absorb huA huB hcover hmeet hedge hrA L w c,
    rootedWcol_absorb huA huB hcover hmeet hedge hrA L w d,
    rootedCol_absorb_uniform huA huB hcover hmeet hedge hrA (by omega : 1 ≤ k) 0,
    cut_normalizer_eq huA huB hcover hmeet W
      (rootedCol (G.induce A) (constList A k) ⟨r, hrA⟩ 0)
      (rootedCol (G.induce B) (constList B k) ⟨u, huB⟩ 0)]
  exact hA

end PendantPrereqs

section MainInduction

/-- A cyclic indexing rooted at `r`, including the lower bound that rules out degenerate cycles. -/
abbrev CactusCyclicIndex (G : SimpleGraph V) (r : V) : Prop :=
  ∃ (m : ℕ) (ix : Fin (m + 1) ≃ V), 2 ≤ m ∧ ix 0 = r ∧
    ∀ i j : Fin (m + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1)

/-- **The structural dichotomy for cacti** (handoff §6.5): a cactus in which no vertex is
pendant either splits at a cut vertex into two smaller cacti, or is a single cycle — indexed
from any prescribed root.

With every degree at least two, a graph all of whose degrees are exactly two is a cycle
(`exists_iso_closePath_of_two_regular`), which the cyclic index reads off; otherwise some vertex
has degree at least three and `exists_cut_split_of_three_le_degree` splits the graph. -/
theorem exists_cut_split_or_cyclic_index {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hG : IsCactus G) (hdeg : ∀ v : V, 2 ≤ G.degree v)
    (r : V) : CactusCutSplit G r ∨ CactusCyclicIndex G r := by
  by_cases h3 : ∃ u : V, 3 ≤ G.degree u
  · obtain ⟨u, hu⟩ := h3
    exact Or.inl (exists_cut_split_of_three_le_degree hG hu r)
  · -- every degree is exactly two: the graph is a cycle, and the index rotates to the root
    push Not at h3
    have hdeg2 : ∀ v : V, G.degree v = 2 := fun v => by
      have h1 := h3 v
      have h2 := hdeg v
      omega
    obtain ⟨m, hm, ⟨e⟩⟩ := exists_iso_closePath_of_two_regular hG.1 hdeg2
    obtain ⟨ix, hix0, hadj⟩ := exists_cyclic_index hm e r
    exact Or.inr ⟨m, ix, hm, hix0, hadj⟩

/-- **The structural trichotomy** for a cactus on at least three vertices: it splits at a cut
vertex — the edge at a pendant vertex, or a genuine cut vertex — or it is a single cycle,
indexed from any prescribed root. This is the form the induction consumes when it does not
separate the pendant cases by hand. -/
theorem exists_cut_split_or_cyclic_index_of_three_le {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hG : IsCactus G) (hcard : 3 ≤ Fintype.card V)
    (r : V) : CactusCutSplit G r ∨ CactusCyclicIndex G r := by
  by_cases hleaf : ∃ x : V, G.degree x = 1
  · obtain ⟨x, hx⟩ := hleaf
    exact Or.inl (exists_leaf_cut_split hG hx hcard r)
  · push Not at hleaf
    have hnt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    refine exists_cut_split_or_cyclic_index hG (fun v => ?_) r
    have hpos : 0 < G.degree v := hG.1.preconnected.degree_pos_of_nontrivial v
    have h1 : G.degree v ≠ 1 := hleaf v
    omega

/-- **The pair-invariant induction** (UM-107/108, `k ≥ 4`): on a cactus with pair-dominant
weights, the weighted rooted profile is pair-bounded by the uniform normalizer times the
product of the weight normalizers.

Case structure: one-vertex base; pendant absorption away from the root; the bridge at the
root; and a cactus of minimum degree two, where `exists_cut_split_or_cyclic_index` either
splits at a cut vertex — `pair_bound_of_cut` and two uses of the induction hypothesis — or
presents the graph as a single cycle, closed by `cycle_pair_bound_index` (UM-106 + UM-107). -/
theorem cactus_pair_bound :
    ∀ (n : ℕ) (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n → ∀ {k : ℕ}, 4 ≤ k → IsCactus G →
      ∀ (L : ListAssignment V), IsNListAssignment L k →
      ∀ (w : V → ℕ → ℕ) (W : V → ℕ),
        (∀ v, ∀ c ∈ L v, ∀ d ∈ L v, c ≠ d → (W v) ^ 2 ≤ w v c * w v d) →
      ∀ (r : V), ∀ c ∈ L r, ∀ d ∈ L r, c ≠ d →
        (rootedCol G (constList V k) r 0 * ∏ v, W v) ^ 2 ≤
          (rootedWcol G L w r c) * (rootedWcol G L w r d) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro V _ _ G _ hcard k hk hG L hL w W hdom r c hc d hd hcd
    rcases Nat.lt_or_ge n 2 with hn | hn
    · -- base: at most one vertex (zero is impossible: `r` inhabits `V`)
      have h1 : Fintype.card V = 1 := by
        have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨r⟩
        omega
      rw [rootedWcol_of_card_eq_one h1 L w r hc, rootedWcol_of_card_eq_one h1 L w r hd]
      have hA : rootedCol G (constList V k) r 0 = 1 := by
        have h0 : (0 : ℕ) ∈ constList V k r := by
          simp [constList_apply, Finset.mem_range]
          omega
        have h2 := rootedWcol_of_card_eq_one (G := G) h1 (constList V k) (fun _ _ => 1) r h0
        rw [rootedWcol_one] at h2
        exact h2
      haveI hsub : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h1)
      have hprod : (∏ v, W v) = W r := by
        rw [show (Finset.univ : Finset V) = {r} from by
          ext v; simp [Subsingleton.elim v r]]
        rw [Finset.prod_singleton]
      rw [hA, hprod, one_mul]
      exact hdom r c hc d hd hcd
    · rcases Nat.lt_or_ge n 3 with hn2 | hn2
      · -- two vertices: a single edge
        have h2 : Fintype.card V = 2 := by omega
        exact edge_pair_base h2 hG hk L hL w W hdom r c d hc hd hcd
      · -- at least three vertices: leaf and cut-vertex splits, or a cycle
        rcases exists_cut_split_or_cyclic_index_of_three_le hG (by omega) r with
          ⟨u, A, B, dA, dB, hrA, huA, huB, hcover, hmeet, hedge, ⟨a, haA, hau⟩,
            ⟨b, hbB, hbu⟩, hcA, hcB⟩ | ⟨m, ix, hm, hix0, hadj⟩
        · -- a cut vertex (a pendant edge is `exists_leaf_cut_split`'s instance of one):
          -- absorb the `B` side into the weight at `u`, recurse on both sides
          have hbA : b ∉ A := fun h => hbu (hmeet b h hbB)
          have haB : a ∉ B := fun h => hau (hmeet a haA h)
          refine pair_bound_of_cut huA huB hcover hmeet hedge hrA (by omega) L w W hdom ?_ ?_
            c hc d hd hcd
          · intro wB WB hdomB c' hc' d' hd' hcd'
            exact IH _ (by rw [← hcard]; exact Fintype.card_subtype_lt (x := a) haB) _
              (G.induce B) rfl hk hcB _ (fun x => hL x.val) wB WB hdomB
              ⟨u, huB⟩ c' hc' d' hd' hcd'
          · intro wA WA hdomA c' hc' d' hd' hcd'
            exact IH _ (by rw [← hcard]; exact Fintype.card_subtype_lt (x := b) hbA) _
              (G.induce A) rfl hk hcA _ (fun v => hL v.val) wA WA hdomA
              ⟨r, hrA⟩ c' hc' d' hd' hcd'
        · -- a single cycle: the weighted cycle pair theorem closes it
          rw [← hix0] at hc hd ⊢
          exact cycle_pair_bound_index hm ix hadj hk L hL w W hdom c hc d hd hcd

end MainInduction



end ListColoring
