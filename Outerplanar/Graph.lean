/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.GraphDefs
import Outerplanar.FaceClosed
import Outerplanar.GraphSum
import Outerplanar.GraphCount

/-!
# The graph induction of the outerplanar ECC proof

This file is the graph induction of the outerplanar ECC proof, a result of this repository's
2026-11 AI research collaboration (`ai_research_notes/OUTERPLANAR_PROOF_DRAFT_2026-11-09.md`,
section 1, reorganised as an induction over the removal of pendant vertices and ears).

`ZG_ge` is the weighted lower bound: for a vertex set built by pendant vertices and ears on
edges, the weighted partition function is at least the constant-list count times the geometric
means of the vertex weights and the constants of the pair profiles. The three steps are

* a new isolated vertex: AM–GM (`card_mul_gmean_le_sum`);
* a new vertex with one neighbour `y`: it is absorbed into the weight of `y`, by root dominance
  (`HasPot.gmean_le`);
* an ear on the edge `uv`: it is absorbed into the profile of the ordered pair `(u, v)`, by the
  closure of the invariant under faces (`FaceClosed`).

`ecc_of_earBuilt` specialises to unit weights and the profile of an ordinary edge.
-/

set_option linter.unusedSectionVars false

namespace Outerplanar

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Small facts -/

theorem ZG_empty (L : V → Finset ℕ) (ω : V → ℕ → ℝ) (Ω : V → V → ℕ → ℕ → ℝ) :
    ZG G ∅ L ω Ω = 1 := by
  have h : adjPairs G (∅ : Finset V) = ∅ := by simp [adjPairs]
  simp [ZG, assignments, h]

theorem ZG_const_nonneg (k : ℕ) (S : Finset V) :
    0 ≤ ZG G S (fun _ => range k) (fun _ _ => 1) neProfile := by
  unfold ZG
  refine Finset.sum_nonneg fun f _ => mul_nonneg (Finset.prod_nonneg fun _ _ => zero_le_one)
    (Finset.prod_nonneg fun p _ => ?_)
  unfold neProfile
  split_ifs <;> norm_num

theorem faceSum_nonneg {m : ℕ} (Li : Fin m → Finset ℕ) (ω : Fin m → ℕ → ℝ)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hω : ∀ j, ∀ c ∈ Li j, 0 ≤ ω j c) (hE : ∀ j c d, 0 ≤ E j c d)
    (c d : ℕ) : 0 ≤ faceSum Li ω E c d := by
  unfold faceSum
  refine Finset.sum_nonneg fun g hg => mul_nonneg (Finset.prod_nonneg fun j _ => ?_)
    (Finset.prod_nonneg fun j _ => hE _ _ _)
  exact hω j _ (Fintype.mem_piFinset.mp hg j)

theorem faceConst_pos {k : ℕ} (hk : 3 ≤ k) (m : ℕ) :
    0 < (((k : ℝ) - 1) ^ (m + 1) - (-1) ^ (m + 1)) / k := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : (1 : ℝ) < ((k : ℝ) - 1) ^ (m + 1) := one_lt_pow₀ (by linarith) (Nat.succ_ne_zero m)
  have h2 : (-1 : ℝ) ^ (m + 1) ≤ 1 := by
    rcases neg_one_pow_eq_or ℝ (m + 1) with h | h
    · rw [h]
    · rw [h]; norm_num
  exact div_pos (by linarith) (by linarith)

/-- The weight a pendant piece puts on its root is positive. -/
theorem HasPot.sum_pos {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {A : ℝ} (h : HasPot S T W A)
    (hA : 0 < A) (hT : 2 ≤ T.card) (hW0 : ∀ c d, 0 ≤ W c d) {ω : ℕ → ℝ}
    (hω : ∀ d ∈ T, 0 < ω d) {c : ℕ} (hc : c ∈ S) : 0 < ∑ d ∈ T, W c d * ω d := by
  obtain ⟨a, b, ha, hb, -, -, hW⟩ := h
  obtain ⟨d, hd, hdc⟩ := Finset.exists_mem_ne (by omega : 1 < T.card) c
  have h1 : 0 < W c d := lt_of_lt_of_le (mul_pos hA (mul_pos (ha c hc) (hb d hd)))
    (hW c hc d hd (Ne.symm hdc))
  exact Finset.sum_pos' (fun e he => mul_nonneg (hW0 c e) (hω e he).le)
    ⟨d, hd, mul_pos h1 (hω d hd)⟩

theorem pathList_eq_earPath {m : ℕ} (L : V → Finset ℕ) (u v : V) (x : Fin m → V)
    (i : Fin (m + 2)) :
    pathList (L u) (L v) (fun j => L (x j)) i = L (earPath u v x i) := by
  unfold pathList
  rcases earPath_cases u v x i with ⟨hi, e⟩ | ⟨hi, e⟩ | ⟨j, hi, e⟩ <;> rw [e]
  · exact consSnoc_zero _ _ _ i hi
  · exact consSnoc_last _ _ _ i hi
  · exact consSnoc_mid _ _ _ i j hi

/-! ### The constant-list counts -/

theorem ZG_const_insert_isolated (k : ℕ) {S : Finset V} {x : V} (hx : x ∉ S)
    (h : ∀ z ∈ S, ¬ G.Adj x z) :
    ZG G (insert x S) (fun _ => range k) (fun _ _ => 1) neProfile
      = ZG G S (fun _ => range k) (fun _ _ => 1) neProfile * k := by
  rw [ZG_insert_isolated G hx h]
  simp

theorem ZG_const_insert_pendant (k : ℕ) {S : Finset V} {x y : V} (hx : x ∉ S) (hy : y ∈ S)
    (hxy : G.Adj x y) (h : ∀ z ∈ S, G.Adj x z → z = y) :
    ZG G (insert x S) (fun _ => range k) (fun _ _ => 1) neProfile
      = ZG G S (fun _ => range k) (fun _ _ => 1) neProfile * ((k : ℝ) - 1) := by
  rw [ZG_insert_pendant G hx hy hxy h, ZG_eq_sum_term, Finset.sum_mul]
  refine Finset.sum_congr rfl fun f hf => ?_
  have hfy : f y ∈ range k := (mem_assignments.mp hf).1 y hy
  congr 1
  exact sum_neSq hfy

theorem IsEar.ZG_const {S : Finset V} {m : ℕ} {u v : V} {x : Fin m → V} (h : IsEar G S u v x)
    {k : ℕ} (hk : 1 ≤ k) :
    ZG G (S ∪ univ.image x) (fun _ => range k) (fun _ _ => 1) neProfile
      = ZG G S (fun _ => range k) (fun _ _ => 1) neProfile
        * ((((k : ℝ) - 1) ^ (m + 1) - (-1) ^ (m + 1)) / k) := by
  rw [h.ZG_eq, ZG_eq_sum_term, Finset.sum_mul]
  refine Finset.sum_congr rfl fun f hf => ?_
  have hfu : f u ∈ range k := (mem_assignments.mp hf).1 u h.hu
  have hfv : f v ∈ range k := (mem_assignments.mp hf).1 v h.hv
  by_cases hfuv : f u = f v
  · have h0 : term G S (fun _ _ => 1) neProfile f = 0 := by
      unfold term
      have hmem : (u, v) ∈ adjPairs G S := (mem_adjPairs G).mpr ⟨h.hu, h.hv, h.huv⟩
      rw [Finset.prod_eq_zero hmem (by simp [neProfile, hfuv]), mul_zero]
    rw [h0, zero_mul, zero_mul]
  · congr 1
    exact pathCount_of_ne hk m hfu hfv hfuv

/-! ### The three steps -/

variable {G}

theorem step_isolated {k : ℕ} (hk : 3 ≤ k) {S : Finset V} {x : V} (hx : x ∉ S)
    (hiso : ∀ z ∈ S, ¬ G.Adj x z) (L : V → Finset ℕ) (ω : V → ℕ → ℝ)
    (Ω : V → V → ℕ → ℕ → ℝ) (A : V → V → ℝ)
    (hcard : (L x).card = k) (hω : ∀ c ∈ L x, 0 < ω x c) (hA : ∀ x y, 0 < A x y)
    (ih : ZG G S (fun _ => range k) (fun _ _ => 1) neProfile
          * (∏ z ∈ S, gmean (L z) (ω z)) * ∏ p ∈ adjPairs G S, A p.1 p.2 ≤ ZG G S L ω Ω) :
    ZG G (insert x S) (fun _ => range k) (fun _ _ => 1) neProfile
        * (∏ z ∈ insert x S, gmean (L z) (ω z)) * ∏ p ∈ adjPairs G (insert x S), A p.1 p.2
      ≤ ZG G (insert x S) L ω Ω := by
  rw [ZG_const_insert_isolated G k hx hiso, ZG_insert_isolated G hx hiso L ω Ω, Finset.prod_insert hx,
    adjPairs_insert_isolated G hiso]
  have hne : (L x).Nonempty := by rw [← Finset.card_pos]; omega
  have hgm := card_mul_gmean_le_sum hne hω
  rw [hcard] at hgm
  have h0 : 0 ≤ ZG G S (fun _ => range k) (fun _ _ => 1) neProfile
      * (∏ z ∈ S, gmean (L z) (ω z)) * ∏ p ∈ adjPairs G S, A p.1 p.2 :=
    mul_nonneg (mul_nonneg (ZG_const_nonneg G k S)
      (Finset.prod_nonneg fun z _ => (gmean_pos _ _).le)) (Finset.prod_nonneg fun p _ => (hA _ _).le)
  have hkg : 0 ≤ (k : ℝ) * gmean (L x) (ω x) :=
    mul_nonneg (Nat.cast_nonneg k) (gmean_pos _ _).le
  calc ZG G S (fun _ => range k) (fun _ _ => 1) neProfile * k
        * (gmean (L x) (ω x) * ∏ z ∈ S, gmean (L z) (ω z)) * ∏ p ∈ adjPairs G S, A p.1 p.2
      = (ZG G S (fun _ => range k) (fun _ _ => 1) neProfile
          * (∏ z ∈ S, gmean (L z) (ω z)) * ∏ p ∈ adjPairs G S, A p.1 p.2)
          * ((k : ℝ) * gmean (L x) (ω x)) := by ring
    _ ≤ ZG G S L ω Ω * ∑ c ∈ L x, ω x c := mul_le_mul ih hgm hkg (h0.trans ih)

theorem step_pendant {k : ℕ} (hk : 3 ≤ k) {S : Finset V} {x y : V} (hx : x ∉ S) (hy : y ∈ S)
    (hxy : G.Adj x y) (huniq : ∀ z ∈ S, G.Adj x z → z = y) (L : V → Finset ℕ) (ω : V → ℕ → ℝ)
    (Ω : V → V → ℕ → ℕ → ℝ) (A : V → V → ℝ)
    (hcard : ∀ z ∈ insert x S, (L z).card = k) (hω : ∀ z ∈ insert x S, ∀ c ∈ L z, 0 < ω z c)
    (hΩ : ∀ x y c d, 0 ≤ Ω x y c d) (hA : ∀ x y, 0 < A x y)
    (hpot : ∀ a ∈ insert x S, ∀ b ∈ insert x S, G.Adj a b →
      HasPot (L a) (L b) (Ω a b) (A a b))
    (ih : ∀ ω' : V → ℕ → ℝ, (∀ z ∈ S, ∀ c ∈ L z, 0 < ω' z c) →
      ZG G S (fun _ => range k) (fun _ _ => 1) neProfile
          * (∏ z ∈ S, gmean (L z) (ω' z)) * ∏ p ∈ adjPairs G S, A p.1 p.2 ≤ ZG G S L ω' Ω) :
    ZG G (insert x S) (fun _ => range k) (fun _ _ => 1) neProfile
        * (∏ z ∈ insert x S, gmean (L z) (ω z)) * ∏ p ∈ adjPairs G (insert x S), A p.1 p.2
      ≤ ZG G (insert x S) L ω Ω := by
  have hxm : x ∈ insert x S := mem_insert_self x S
  have hym : y ∈ insert x S := mem_insert_of_mem hy
  -- the weight the new vertex puts on `y`
  have hW : HasPot (L y) (L x) (fun d c => Ω y x d c * Ω x y c d) (A y x * A x y) :=
    HasPot.mul (hA y x).le (hA x y).le (hpot y hym x hxm hxy.symm) (hpot x hxm y hym hxy).swap
  have hW0 : ∀ d c, 0 ≤ Ω y x d c * Ω x y c d := fun d c => mul_nonneg (hΩ _ _ _ _) (hΩ _ _ _ _)
  have hAA : 0 < A y x * A x y := mul_pos (hA y x) (hA x y)
  have hFpos : ∀ d ∈ L y, 0 < ∑ c ∈ L x, (Ω y x d c * Ω x y c d) * ω x c := fun d hd =>
    hW.sum_pos hAA (by rw [hcard x hxm]; omega) hW0 (hω x hxm) hd
  have hroot := hW.gmean_le (k := k) (by omega) (hcard y hym) (hcard x hxm) hAA hW0 (hω x hxm)
  have ih' := ih (fun z => if z = y then
      fun d => ω y d * ∑ c ∈ L x, (Ω y x d c * Ω x y c d) * ω x c else ω z) (by
    intro z hz c hc
    by_cases hzy : z = y
    · subst hzy
      simp only [ite_true]
      exact mul_pos (hω z hym c hc) (hFpos c hc)
    · simp only [hzy, ite_false]
      exact hω z (mem_insert_of_mem hz) c hc)
  have hZ : ZG G (insert x S) L ω Ω = ZG G S L (fun z => if z = y then
      fun d => ω y d * ∑ c ∈ L x, (Ω y x d c * Ω x y c d) * ω x c else ω z) Ω := by
    rw [ZG_insert_pendant G hx hy hxy huniq,
      ZG_update_vertex G hy L ω Ω (fun d => ∑ c ∈ L x, (Ω y x d c * Ω x y c d) * ω x c)]
  have hgm : ∏ z ∈ S, gmean (L z) ((fun z => if z = y then
        fun d => ω y d * ∑ c ∈ L x, (Ω y x d c * Ω x y c d) * ω x c else ω z) z)
      = (∏ z ∈ S, gmean (L z) (ω z))
        * gmean (L y) (fun d => ∑ c ∈ L x, (Ω y x d c * Ω x y c d) * ω x c) := by
    rw [← prod_mul_at S hy (fun z => gmean (L z) (ω z))]
    refine Finset.prod_congr rfl fun z _ => ?_
    by_cases hzy : z = y
    · subst hzy
      simp only [ite_true]
      exact gmean_mul (hω z hym) hFpos
    · simp only [hzy, ite_false]
  rw [hgm] at ih'
  rw [hZ, ZG_const_insert_pendant G k hx hy hxy huniq, Finset.prod_insert hx,
    prod_adjPairs_insert_pendant G hx hy hxy huniq (fun p => A p.1 p.2)]
  have h0 : 0 ≤ ZG G S (fun _ => range k) (fun _ _ => 1) neProfile
      * (∏ z ∈ S, gmean (L z) (ω z)) * ∏ p ∈ adjPairs G S, A p.1 p.2 :=
    mul_nonneg (mul_nonneg (ZG_const_nonneg G k S)
      (Finset.prod_nonneg fun z _ => (gmean_pos _ _).le)) (Finset.prod_nonneg fun p _ => (hA _ _).le)
  refine le_trans ?_ ih'
  calc ZG G S (fun _ => range k) (fun _ _ => 1) neProfile * ((k : ℝ) - 1)
        * (gmean (L x) (ω x) * ∏ z ∈ S, gmean (L z) (ω z))
        * (A x y * (A y x * ∏ p ∈ adjPairs G S, A p.1 p.2))
      = (ZG G S (fun _ => range k) (fun _ _ => 1) neProfile
          * (∏ z ∈ S, gmean (L z) (ω z)) * ∏ p ∈ adjPairs G S, A p.1 p.2)
          * (((k : ℝ) - 1) * (A y x * A x y) * gmean (L x) (ω x)) := by ring
    _ ≤ (ZG G S (fun _ => range k) (fun _ _ => 1) neProfile
          * (∏ z ∈ S, gmean (L z) (ω z)) * ∏ p ∈ adjPairs G S, A p.1 p.2)
          * gmean (L y) (fun d => ∑ c ∈ L x, (Ω y x d c * Ω x y c d) * ω x c) :=
        mul_le_mul_of_nonneg_left hroot h0
    _ = _ := by ring

theorem step_ear {k m : ℕ} (hk : 3 ≤ k) (hface : FaceClosed k m) {S : Finset V} {u v : V}
    {x : Fin m → V} (he : IsEar G S u v x) (L : V → Finset ℕ) (ω : V → ℕ → ℝ)
    (Ω : V → V → ℕ → ℕ → ℝ) (A : V → V → ℝ)
    (hcard : ∀ z ∈ S ∪ univ.image x, (L z).card = k)
    (hω : ∀ z ∈ S ∪ univ.image x, ∀ c ∈ L z, 0 < ω z c)
    (hΩ : ∀ x y c d, 0 ≤ Ω x y c d) (hA : ∀ x y, 0 < A x y)
    (hpot : ∀ a ∈ S ∪ univ.image x, ∀ b ∈ S ∪ univ.image x, G.Adj a b →
      HasPot (L a) (L b) (Ω a b) (A a b))
    (ih : ∀ (Ω' : V → V → ℕ → ℕ → ℝ) (A' : V → V → ℝ), (∀ x y c d, 0 ≤ Ω' x y c d) →
      (∀ x y, 0 < A' x y) →
      (∀ a ∈ S, ∀ b ∈ S, G.Adj a b → HasPot (L a) (L b) (Ω' a b) (A' a b)) →
      ZG G S (fun _ => range k) (fun _ _ => 1) neProfile
          * (∏ z ∈ S, gmean (L z) (ω z)) * ∏ p ∈ adjPairs G S, A' p.1 p.2 ≤ ZG G S L ω Ω') :
    ZG G (S ∪ univ.image x) (fun _ => range k) (fun _ _ => 1) neProfile
        * (∏ z ∈ S ∪ univ.image x, gmean (L z) (ω z))
        * ∏ p ∈ adjPairs G (S ∪ univ.image x), A p.1 p.2
      ≤ ZG G (S ∪ univ.image x) L ω Ω := by
  have hxm : ∀ j, x j ∈ S ∪ univ.image x := fun j =>
    mem_union_right _ (mem_image_of_mem _ (mem_univ j))
  have huvm : (u, v) ∈ adjPairs G S := (mem_adjPairs G).mpr ⟨he.hu, he.hv, he.huv⟩
  -- the invariant on the edges of the path
  have hE : ∀ j : Fin (m + 1),
      HasPot (pathList (L u) (L v) (fun j => L (x j)) j.castSucc)
        (pathList (L u) (L v) (fun j => L (x j)) j.succ) (earE Ω u v x j)
        (A (earPath u v x j.castSucc) (earPath u v x j.succ)
          * A (earPath u v x j.succ) (earPath u v x j.castSucc)) := by
    intro j
    rw [pathList_eq_earPath, pathList_eq_earPath]
    exact HasPot.mul (hA _ _).le (hA _ _).le
      (hpot _ (he.earPath_mem _) _ (he.earPath_mem _) (he.earPath_adj j))
      (hpot _ (he.earPath_mem _) _ (he.earPath_mem _) (he.earPath_adj j).symm).swap
  have hF := hface (L u) (L v) (fun j => L (x j)) (hcard u (mem_union_left _ he.hu))
    (hcard v (mem_union_left _ he.hv)) (fun j => hcard (x j) (hxm j)) (fun j => ω (x j))
    (fun j => hω (x j) (hxm j)) (earE Ω u v x)
    (fun j c d => mul_nonneg (hΩ _ _ _ _) (hΩ _ _ _ _))
    (fun j => A (earPath u v x j.castSucc) (earPath u v x j.succ)
      * A (earPath u v x j.succ) (earPath u v x j.castSucc))
    (fun j => mul_pos (hA _ _) (hA _ _)) hE
  have hC : 0 < (((k : ℝ) - 1) ^ (m + 1) - (-1) ^ (m + 1)) / k
      * (∏ j : Fin (m + 1), A (earPath u v x j.castSucc) (earPath u v x j.succ)
          * A (earPath u v x j.succ) (earPath u v x j.castSucc))
      * ∏ j, gmean (L (x j)) (ω (x j)) :=
    mul_pos (mul_pos (faceConst_pos hk m) (Finset.prod_pos fun j _ => mul_pos (hA _ _) (hA _ _)))
      (Finset.prod_pos fun j _ => gmean_pos _ _)
  have hF0 : ∀ c d, 0 ≤ faceSum (fun j => L (x j)) (fun j => ω (x j)) (earE Ω u v x) c d :=
    faceSum_nonneg _ _ _ (fun j c hc => (hω (x j) (hxm j) c hc).le)
      (fun j c d => mul_nonneg (hΩ _ _ _ _) (hΩ _ _ _ _))
  have ih' := ih
    (fun a b => if a = u ∧ b = v then fun c d => Ω u v c d
      * faceSum (fun j => L (x j)) (fun j => ω (x j)) (earE Ω u v x) c d else Ω a b)
    (fun a b => if a = u ∧ b = v then A u v
      * ((((k : ℝ) - 1) ^ (m + 1) - (-1) ^ (m + 1)) / k
      * (∏ j : Fin (m + 1), A (earPath u v x j.castSucc) (earPath u v x j.succ)
          * A (earPath u v x j.succ) (earPath u v x j.castSucc))
      * ∏ j, gmean (L (x j)) (ω (x j))) else A a b)
    (by
      intro a b c d
      by_cases hab : a = u ∧ b = v
      · simp only [hab, and_self, ite_true]
        exact mul_nonneg (hΩ _ _ _ _) (hF0 c d)
      · simp only [hab, ite_false]
        exact hΩ _ _ _ _)
    (by
      intro a b
      by_cases hab : a = u ∧ b = v
      · simp only [hab, and_self, ite_true]
        exact mul_pos (hA _ _) hC
      · simp only [hab, ite_false]
        exact hA _ _)
    (by
      intro a ha b hb hadj
      by_cases hab : a = u ∧ b = v
      · obtain ⟨rfl, rfl⟩ := hab
        simp only [and_self, ite_true]
        exact HasPot.mul (hA _ _).le hC.le
          (hpot a (mem_union_left _ ha) b (mem_union_left _ hb) hadj) hF
      · simp only [hab, ite_false]
        exact hpot a (mem_union_left _ ha) b (mem_union_left _ hb) hadj)
  rw [prod_adjPairs_update G huvm A, ZG_update_pair G huvm L ω Ω, ← he.ZG_eq] at ih'
  have hdisj : Disjoint S (univ.image x) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨j, _, rfl⟩ := mem_image.mp hz'
    exact he.hxS j hz
  rw [he.ZG_const G (by omega : 1 ≤ k), Finset.prod_union hdisj,
    Finset.prod_image fun a _ b _ hab => he.hinj hab, he.prod_adjPairs (fun p => A p.1 p.2)]
  refine le_of_eq_of_le ?_ ih'
  ring

/-! ### The main theorems -/

variable (G)

/-- The weighted lower bound for graphs built by pendant vertices and ears on edges. -/
theorem ZG_ge {k m₀ : ℕ} (hk : 3 ≤ k) (hface : ∀ m, 1 ≤ m → m₀ ≤ m → FaceClosed k m)
    {S : Finset V} (hS : EarBuilt G m₀ S) :
    ∀ (L : V → Finset ℕ) (ω : V → ℕ → ℝ) (Ω : V → V → ℕ → ℕ → ℝ) (A : V → V → ℝ),
      (∀ x ∈ S, (L x).card = k) → (∀ x ∈ S, ∀ c ∈ L x, 0 < ω x c) →
      (∀ x y c d, 0 ≤ Ω x y c d) → (∀ x y, 0 < A x y) →
      (∀ x ∈ S, ∀ y ∈ S, G.Adj x y → HasPot (L x) (L y) (Ω x y) (A x y)) →
      ZG G S (fun _ => range k) (fun _ _ => 1) neProfile
          * (∏ x ∈ S, gmean (L x) (ω x)) * ∏ p ∈ adjPairs G S, A p.1 p.2
        ≤ ZG G S L ω Ω := by
  induction hS with
  | empty =>
    intro L ω Ω A _ _ _ _ _
    have h : adjPairs G (∅ : Finset V) = ∅ := by simp [adjPairs]
    rw [ZG_empty, ZG_empty, h]
    simp
  | pendant S x hx hS hdeg ih =>
    intro L ω Ω A hcard hω hΩ hA hpot
    have hsub : ∀ z ∈ S, z ∈ insert x S := fun z hz => mem_insert_of_mem hz
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdeg with h0 | h1
    · have hiso : ∀ z ∈ S, ¬ G.Adj x z := by
        intro z hz hadj
        have : z ∈ S.filter (G.Adj x) := mem_filter.mpr ⟨hz, hadj⟩
        rw [Finset.card_eq_zero.mp h0] at this
        exact absurd this (Finset.notMem_empty z)
      exact step_isolated hk hx hiso L ω Ω A (hcard x (mem_insert_self x S))
        (hω x (mem_insert_self x S)) hA
        (ih L ω Ω A (fun z hz => hcard z (hsub z hz)) (fun z hz => hω z (hsub z hz)) hΩ hA
          fun a ha b hb => hpot a (hsub a ha) b (hsub b hb))
    · obtain ⟨y, hy⟩ := Finset.card_eq_one.mp h1
      have hyS : y ∈ S ∧ G.Adj x y := by
        have : y ∈ S.filter (G.Adj x) := by rw [hy]; exact mem_singleton_self y
        exact mem_filter.mp this
      have huniq : ∀ z ∈ S, G.Adj x z → z = y := by
        intro z hz hadj
        have : z ∈ S.filter (G.Adj x) := mem_filter.mpr ⟨hz, hadj⟩
        rw [hy] at this
        exact mem_singleton.mp this
      exact step_pendant hk hx hyS.1 hyS.2 huniq L ω Ω A hcard hω hΩ hA hpot
        fun ω' hω' => ih L ω' Ω A (fun z hz => hcard z (hsub z hz)) hω' hΩ hA
          fun a ha b hb => hpot a (hsub a ha) b (hsub b hb)
  | ear S m hm hm₀ u v hu hv huv x hinj hxS hS hold hnew ih =>
    intro L ω Ω A hcard hω hΩ hA hpot
    have he : IsEar G S u v x := ⟨hm, hu, hv, huv, hinj, hxS, hold, hnew⟩
    exact step_ear hk (hface m hm hm₀) he L ω Ω A hcard hω hΩ hA hpot
      fun Ω' A' hΩ' hA' hpot' => ih L ω Ω' A'
        (fun z hz => hcard z (mem_union_left _ hz)) (fun z hz => hω z (mem_union_left _ hz))
        hΩ' hA' hpot'

/-- With unit weights and the profile of an ordinary edge, `ZG` counts the proper colourings. -/
theorem ZG_univ_eq_col (L : V → Finset ℕ) :
    ZG G univ L (fun _ _ => 1) neProfile = (G.col L : ℝ) := by
  have ha : assignments (univ : Finset V) L = Fintype.piFinset L := by simp [assignments]
  unfold ZG SimpleGraph.col SimpleGraph.colorings
  rw [ha, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_const_one, one_mul]
  by_cases hp : G.IsProperColoring f
  · rw [ite_eq_left hp, Nat.cast_one]
    refine Finset.prod_eq_one fun p hp' => ?_
    have := hp ((mem_adjPairs G).mp hp').2.2
    simp [neProfile, this]
  · rw [ite_eq_right hp, Nat.cast_zero]
    have : ∃ a b, G.Adj a b ∧ f a = f b := by
      by_contra hne
      exact hp fun a b hab hfab => hne ⟨a, b, hab, hfab⟩
    obtain ⟨a, b, hab, hfab⟩ := this
    exact Finset.prod_eq_zero (i := (a, b))
      ((mem_adjPairs G).mpr ⟨mem_univ a, mem_univ b, hab⟩) (by simp [neProfile, hfab])

/-- Graphs built by pendant vertices and ears on edges are `k`-ECC, given closure under faces. -/
theorem ecc_of_earBuilt {k m₀ : ℕ} (hk : 3 ≤ k) (hface : ∀ m, 1 ≤ m → m₀ ≤ m → FaceClosed k m)
    (h : EarBuilt G m₀ univ) : G.ECCAt k := by
  intro L hL
  have key := ZG_ge G hk hface h L (fun _ _ => 1) neProfile (fun _ _ => 1) (fun x _ => hL x)
    (fun _ _ _ _ => one_pos) (fun _ _ c d => by unfold neProfile; split_ifs <;> norm_num)
    (fun _ _ => one_pos) (fun x _ y _ _ => hasPot_ne (L x) (L y))
  have hg : ∀ x ∈ (univ : Finset V), gmean (L x) (fun _ => (1 : ℝ)) = 1 := fun x _ =>
    gmean_eq_one (fun _ _ => one_pos) (by simp)
  rw [Finset.prod_congr rfl hg, Finset.prod_const_one, Finset.prod_const_one, mul_one, mul_one,
    ZG_univ_eq_col, ZG_univ_eq_col] at key
  have key' : (G.colConst k : ℝ) ≤ (G.col L : ℝ) := key
  exact_mod_cast key'

end Outerplanar
