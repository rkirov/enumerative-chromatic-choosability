/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Capacity
import Outerplanar.Egervary
import Outerplanar.FaceDefs

/-!
# The face operation preserves the invariant

This is section 2 of the proof draft `ai_research_notes/OUTERPLANAR_PROOF_DRAFT_2026-11-09.md`:
the reduction of the face operation to the capacity lemma, through Egerváry's theorem. It is a
result of this repository's 2026-11 AI research collaboration.

A face is a path `u, x 0, …, x (m - 1), v` closed by the root edge `uv`. If every edge of the path
carries a pair profile dominating a rank-one matrix (`HasPot`), then so does the profile
`faceSum` of the face, with the constant `lam k (m + 1) / k` times the product of the constants
of the edges and of the geometric means of the interior weights.

The proof: the potentials of the edges turn into vertex weights (`faceSum_ge`), leaving the
weighted number `pathY` of proper colourings of the path with prescribed ends. For a
fixed-point-free bijection `σ` the sum of `t c * pathY c (σ c)` is the weighted number of
colourings of a cover of the cycle of length `m + 1` (`faceCover`, `faceCover_Z`), which the
capacity lemma bounds from below (`capacity_sum`); choosing `t` gives the bijection inequality
(`prod_pathY_ge`), and Egerváry's theorem (`exists_potentials`) turns it back into potentials.
-/

namespace Outerplanar

open Finset

variable {m : ℕ}

/-! ### The path: indexing -/

theorem pathList_castSucc_zero (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ) :
    pathList Lu Lv Li (0 : Fin (m + 1)).castSucc = Lu := by
  simp [pathList]

theorem pathList_succ_castSucc (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ) (i : Fin m) :
    pathList Lu Lv Li i.castSucc.succ = Li i := by
  simp [pathList]

theorem pathList_castSucc_succ (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ) (i : Fin m) :
    pathList Lu Lv Li i.succ.castSucc = Li i := by
  rw [← Fin.succ_castSucc, pathList_succ_castSucc]

theorem pathList_succ_last (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ) :
    pathList Lu Lv Li (Fin.last m).succ = Lv := by
  simp [pathList]

theorem pathCol_castSucc_zero (c d : ℕ) (g : Fin m → ℕ) :
    pathCol c d g (0 : Fin (m + 1)).castSucc = c := by
  simp [pathCol]

theorem pathCol_succ_castSucc (c d : ℕ) (g : Fin m → ℕ) (i : Fin m) :
    pathCol c d g i.castSucc.succ = g i := by
  simp [pathCol]

theorem pathCol_castSucc_succ (c d : ℕ) (g : Fin m → ℕ) (i : Fin m) :
    pathCol c d g i.succ.castSucc = g i := by
  rw [← Fin.succ_castSucc, pathCol_succ_castSucc]

theorem pathCol_succ_last (c d : ℕ) (g : Fin m → ℕ) :
    pathCol c d g (Fin.last m).succ = d := by
  simp [pathCol]

theorem pathCol_mem {Lu Lv : Finset ℕ} {Li : Fin m → Finset ℕ} {c d : ℕ} {g : Fin m → ℕ}
    (hc : c ∈ Lu) (hd : d ∈ Lv) (hg : ∀ i, g i ∈ Li i) (j : Fin (m + 2)) :
    pathCol c d g j ∈ pathList Lu Lv Li j := by
  refine Fin.cases ?_ (fun j' => ?_) j
  · simpa [pathCol, pathList] using hc
  · refine Fin.lastCases ?_ (fun i => ?_) j'
    · rw [pathCol_succ_last, pathList_succ_last]
      exact hd
    · rw [pathCol_succ_castSucc, pathList_succ_castSucc]
      exact hg i

/-- The colouring of the path read along its first `m + 1` vertices. -/
theorem pathCol_castSucc (f : Fin (m + 1) → ℕ) (d : ℕ) (j : Fin (m + 1)) :
    pathCol (f 0) d (Fin.tail f) j.castSucc = f j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [pathCol_castSucc_zero]
  · rw [pathCol_castSucc_succ]
    rfl

/-- The colouring of the path read along its last `m + 1` vertices. -/
theorem pathCol_succ (f : Fin (m + 1) → ℕ) (d : ℕ) (j : Fin (m + 1)) :
    pathCol (f 0) d (Fin.tail f) j.succ = if j = Fin.last m then d else f (j + 1) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [pathCol_succ_last, ite_eq_left rfl]
  · rw [pathCol_succ_castSucc, ite_eq_right (Fin.castSucc_ne_last i), Fin.coeSucc_eq_succ]
    rfl

/-- Regrouping a product over the edges of the path by vertices. -/
theorem prod_edge_split (f h : Fin (m + 1) → ℝ) :
    ∏ j, (f j * h j) = f 0 * h (Fin.last m) * ∏ i : Fin m, (h i.castSucc * f i.succ) := by
  rw [Finset.prod_mul_distrib, Fin.prod_univ_succ f, Fin.prod_univ_castSucc h,
    Finset.prod_mul_distrib]
  ring

/-- With at least three colours per list the interior of the path can be coloured properly,
whatever the two distinct colours of its ends. -/
theorem exists_proper : ∀ (m : ℕ) (Li : Fin m → Finset ℕ), (∀ i, 3 ≤ (Li i).card) →
    ∀ c d : ℕ, c ≠ d → ∃ g : Fin m → ℕ, (∀ i, g i ∈ Li i) ∧
      ∀ j : Fin (m + 1), pathCol c d g j.castSucc ≠ pathCol c d g j.succ
  | 0, _, _, c, d, hcd => ⟨Fin.elim0, fun i => i.elim0, fun j => by
      have hj : j = Fin.last 0 := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
      subst hj
      rw [pathCol_succ_last]
      simpa [pathCol] using hcd⟩
  | m + 1, Li, hLi, c, d, hcd => by
      obtain ⟨x, hx, hxc, hxd⟩ : ∃ x ∈ Li 0, x ≠ c ∧ x ≠ d := by
        have hpos : 0 < (((Li 0).erase c).erase d).card := by
          have h1 := Finset.pred_card_le_card_erase (s := Li 0) (a := c)
          have h2 := Finset.pred_card_le_card_erase (s := (Li 0).erase c) (a := d)
          have h3 := hLi 0
          omega
        obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
        simp only [Finset.mem_erase] at hx
        exact ⟨x, hx.2.2, hx.2.1, hx.1⟩
      obtain ⟨g', hg', hp⟩ := exists_proper m (Fin.tail Li) (fun i => hLi i.succ) x d hxd
      have hcons : pathCol c d (Fin.cons x g' : Fin (m + 1) → ℕ)
          = Fin.cons c (pathCol x d g') := by
        simp only [pathCol, Fin.cons_snoc_eq_snoc_cons]
      refine ⟨Fin.cons x g', fun i => ?_, fun j => ?_⟩
      · refine Fin.cases ?_ (fun i' => ?_) i
        · simpa using hx
        · rw [Fin.cons_succ]
          exact hg' i'
      · rw [hcons]
        refine Fin.cases ?_ (fun j' => ?_) j
        · simpa [pathCol] using hxc.symm
        · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
          exact hp j'

/-! ### The weighted number of proper colourings of the path -/

open Classical in
/-- The weighted number of proper colourings of the path with ends coloured `c` and `d`. -/
noncomputable def pathY (Li : Fin m → Finset ℕ) (v : Fin m → ℕ → ℝ) (c d : ℕ) : ℝ :=
  ∑ g ∈ (Fintype.piFinset Li).filter
      (fun g => ∀ j : Fin (m + 1), pathCol c d g j.castSucc ≠ pathCol c d g j.succ),
    ∏ i, v i (g i)

theorem pathY_pos {Li : Fin m → Finset ℕ} (hLi : ∀ i, 3 ≤ (Li i).card) {v : Fin m → ℕ → ℝ}
    (hv : ∀ i, ∀ x ∈ Li i, 0 < v i x) {c d : ℕ} (hcd : c ≠ d) : 0 < pathY Li v c d := by
  classical
  obtain ⟨g, hg, hp⟩ := exists_proper m Li hLi c d hcd
  rw [pathY]
  refine Finset.sum_pos (fun g hg => Finset.prod_pos fun i _ =>
    hv i _ (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hg).1 i)) ⟨g, ?_⟩
  exact Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr hg, hp⟩

/-- **Potentials on the edges become vertex weights.** -/
theorem faceSum_ge {Lu Lv : Finset ℕ} {Li : Fin m → Finset ℕ} {ω : Fin m → ℕ → ℝ}
    (hω : ∀ j, ∀ c ∈ Li j, 0 < ω j c) {E : Fin (m + 1) → ℕ → ℕ → ℝ}
    (hE0 : ∀ j c d, 0 ≤ E j c d) {A : Fin (m + 1) → ℝ} (hA : ∀ j, 0 ≤ A j)
    {a b : Fin (m + 1) → ℕ → ℝ}
    (ha : ∀ j, ∀ c ∈ pathList Lu Lv Li j.castSucc, 0 < a j c)
    (hb : ∀ j, ∀ d ∈ pathList Lu Lv Li j.succ, 0 < b j d)
    (hW : ∀ j, ∀ c ∈ pathList Lu Lv Li j.castSucc, ∀ d ∈ pathList Lu Lv Li j.succ, c ≠ d →
      A j * (a j c * b j d) ≤ E j c d)
    {c d : ℕ} (hc : c ∈ Lu) (hd : d ∈ Lv) :
    (∏ j, A j) * (a 0 c * b (Fin.last m) d) *
        pathY Li (fun i x => ω i x * (b i.castSucc x * a i.succ x)) c d
      ≤ faceSum Li ω E c d := by
  classical
  rw [faceSum, pathY, Finset.mul_sum]
  refine le_trans (Finset.sum_le_sum fun g hg => ?_)
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun g hg _ =>
      mul_nonneg (Finset.prod_nonneg fun j _ => (hω j _ (Fintype.mem_piFinset.mp hg j)).le)
        (Finset.prod_nonneg fun j _ => hE0 _ _ _))
  obtain ⟨hgm, hp⟩ := Finset.mem_filter.mp hg
  have hgm' := Fintype.mem_piFinset.mp hgm
  have hmem := pathCol_mem (Li := Li) hc hd hgm'
  have h1 : ∏ j : Fin (m + 1),
        (A j * (a j (pathCol c d g j.castSucc) * b j (pathCol c d g j.succ)))
      ≤ ∏ j : Fin (m + 1), E j (pathCol c d g j.castSucc) (pathCol c d g j.succ) :=
    Finset.prod_le_prod₀
      (fun j _ => mul_nonneg (hA j) (mul_pos (ha j _ (hmem _)) (hb j _ (hmem _))).le)
      (fun j _ => hW j _ (hmem _) _ (hmem _) (hp j))
  have h2 : ∏ j : Fin (m + 1),
        (A j * (a j (pathCol c d g j.castSucc) * b j (pathCol c d g j.succ)))
      = (∏ j, A j) * (a 0 c * b (Fin.last m) d *
          ∏ i : Fin m, (b i.castSucc (g i) * a i.succ (g i))) := by
    rw [Finset.prod_mul_distrib, prod_edge_split (fun j => a j (pathCol c d g j.castSucc))
      (fun j => b j (pathCol c d g j.succ))]
    simp only [pathCol_succ_castSucc, pathCol_castSucc_succ, pathCol_castSucc_zero,
      pathCol_succ_last]
  rw [h2] at h1
  calc (∏ j, A j) * (a 0 c * b (Fin.last m) d) *
        ∏ i, (ω i (g i) * (b i.castSucc (g i) * a i.succ (g i)))
      = (∏ j, ω j (g j)) * ((∏ j, A j) * (a 0 c * b (Fin.last m) d *
          ∏ i : Fin m, (b i.castSucc (g i) * a i.succ (g i)))) := by
        rw [Finset.prod_mul_distrib]
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1
        (Finset.prod_nonneg fun j _ => (hω j _ (hgm' j)).le)

/-! ### The cover of the cycle -/

/-- The cover of the cycle of length `m + 1` attached to a face and a bijection `σ` between the
lists of the ends of its root edge: equal colours are matched along the path, and the colour
`σ y` over the last interior vertex is matched with `y` over the vertex `0`. -/
def faceCover (Lu : Finset ℕ) (Li : Fin m → Finset ℕ) (σ : ℕ → ℕ) : Cover (m + 1) where
  F := Fin.cons Lu Li
  M i x y := if i = Fin.last m then y ∈ Lu ∧ x = σ y else x = y

theorem faceCover_F_zero (Lu : Finset ℕ) (Li : Fin m → Finset ℕ) (σ : ℕ → ℕ) :
    (faceCover Lu Li σ).F 0 = Lu := by
  simp [faceCover]

theorem faceCover_F_succ (Lu : Finset ℕ) (Li : Fin m → Finset ℕ) (σ : ℕ → ℕ) (i : Fin m) :
    (faceCover Lu Li σ).F i.succ = Li i := by
  simp [faceCover]

theorem faceCover_M_last {Lu : Finset ℕ} {Li : Fin m → Finset ℕ} {σ : ℕ → ℕ} {x y : ℕ} :
    (faceCover Lu Li σ).M (Fin.last m) x y ↔ y ∈ Lu ∧ x = σ y := by
  simp [faceCover]

theorem faceCover_M_of_ne {Lu : Finset ℕ} {Li : Fin m → Finset ℕ} {σ : ℕ → ℕ} {i : Fin (m + 1)}
    (hi : i ≠ Fin.last m) {x y : ℕ} : (faceCover Lu Li σ).M i x y ↔ x = y := by
  simp [faceCover, hi]

theorem faceCover_card {k : ℕ} {Lu : Finset ℕ} {Li : Fin m → Finset ℕ} (σ : ℕ → ℕ)
    (hLu : Lu.card = k) (hLi : ∀ j, (Li j).card = k) (i : Fin (m + 1)) :
    ((faceCover Lu Li σ).F i).card = k := by
  refine Fin.cases ?_ (fun i' => ?_) i
  · rw [faceCover_F_zero, hLu]
  · rw [faceCover_F_succ, hLi]

theorem faceCover_isMatching {Lu : Finset ℕ} (Li : Fin m → Finset ℕ) {σ : ℕ → ℕ}
    (hinj : Set.InjOn σ Lu) : (faceCover Lu Li σ).IsMatching := by
  intro i
  by_cases hi : i = Fin.last m
  · subst hi
    refine ⟨fun x _ y _ y' _ h h' => ?_, fun x _ x' _ y _ h h' => ?_⟩
    · rw [faceCover_M_last] at h h'
      exact hinj h.1 h'.1 (h.2.symm.trans h'.2)
    · rw [faceCover_M_last] at h h'
      exact h.2.trans h'.2.symm
  · refine ⟨fun x _ y _ y' _ h h' => ?_, fun x _ x' _ y _ h h' => ?_⟩
    · rw [faceCover_M_of_ne hi] at h h'
      exact h.symm.trans h'
    · rw [faceCover_M_of_ne hi] at h h'
      exact h.trans h'.symm

theorem faceCover_noClosedThread {Lu : Finset ℕ} (Li : Fin m → Finset ℕ) {σ : ℕ → ℕ}
    (hfix : ∀ c ∈ Lu, σ c ≠ c) : (faceCover Lu Li σ).NoClosedThread := by
  rintro ⟨f, -, hM⟩
  have hconst : ∀ i, f i = f 0 := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
      have h := (faceCover_M_of_ne (Fin.castSucc_ne_last i)).mp (hM i.castSucc)
      rw [Fin.coeSucc_eq_succ] at h
      rw [← h, ih]
  have hl := faceCover_M_last.mp (hM (Fin.last m))
  rw [Fin.last_add_one] at hl
  exact hfix _ hl.1 (hl.2.symm.trans (hconst _))

/-- The colourings of the cover are the proper colourings of the path from `c` to `σ c`. -/
theorem mem_cols_faceCover {Lu : Finset ℕ} {Li : Fin m → Finset ℕ} {σ : ℕ → ℕ}
    {b f : Fin (m + 1) → ℕ} :
    f ∈ (faceCover Lu Li σ).cols univ b ↔ f 0 ∈ Lu ∧ (∀ i, Fin.tail f i ∈ Li i) ∧
      ∀ j : Fin (m + 1), pathCol (f 0) (σ (f 0)) (Fin.tail f) j.castSucc
        ≠ pathCol (f 0) (σ (f 0)) (Fin.tail f) j.succ := by
  have key : f 0 ∈ Lu → ((∀ i, ¬ (faceCover Lu Li σ).M i (f i) (f (i + 1))) ↔
      ∀ j : Fin (m + 1), pathCol (f 0) (σ (f 0)) (Fin.tail f) j.castSucc
        ≠ pathCol (f 0) (σ (f 0)) (Fin.tail f) j.succ) := by
    intro h0
    refine forall_congr' fun j => ?_
    rw [pathCol_castSucc, pathCol_succ]
    by_cases hj : j = Fin.last m
    · subst hj
      rw [ite_eq_left rfl, faceCover_M_last, Fin.last_add_one]
      exact ⟨fun h h' => h ⟨h0, h'⟩, fun h h' => h h'.2⟩
    · rw [ite_eq_right hj, faceCover_M_of_ne hj]
  rw [Cover.mem_cols]
  constructor
  · rintro ⟨h1, h2⟩
    have h0 : f 0 ∈ Lu := by
      have := (h1 0).1 (mem_univ _)
      rwa [faceCover_F_zero] at this
    refine ⟨h0, fun i => ?_, (key h0).mp fun i => h2 i (mem_univ _) (mem_univ _)⟩
    have := (h1 i.succ).1 (mem_univ _)
    rwa [faceCover_F_succ] at this
  · rintro ⟨h0, h1, h2⟩
    refine ⟨fun i => ⟨fun _ => ?_, fun h => absurd (mem_univ i) h⟩,
      fun i _ _ => (key h0).mpr h2 i⟩
    refine Fin.cases ?_ (fun i' => ?_) i
    · rw [faceCover_F_zero]
      exact h0
    · rw [faceCover_F_succ]
      exact h1 i'

/-- The weighted number of colourings of the cover, in terms of the path. -/
theorem faceCover_Z (Lu : Finset ℕ) (Li : Fin m → Finset ℕ) (σ : ℕ → ℕ) (b : Fin (m + 1) → ℕ)
    (t : ℕ → ℝ) (v : Fin m → ℕ → ℝ) :
    (faceCover Lu Li σ).Z univ b (Fin.cons t v : Fin (m + 1) → ℕ → ℝ)
      = ∑ c ∈ Lu, t c * pathY Li v c (σ c) := by
  classical
  rw [Cover.Z]
  simp only [pathY, Finset.mul_sum]
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun f _ => (⟨f 0, Fin.tail f⟩ : (_ : ℕ) × (Fin m → ℕ)))
    (fun x _ => (Fin.cons x.1 x.2 : Fin (m + 1) → ℕ)) ?_ ?_ ?_ ?_ ?_
  · intro f hf
    obtain ⟨h0, h1, h2⟩ := mem_cols_faceCover.mp hf
    exact Finset.mem_sigma.mpr ⟨h0, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr h1, h2⟩⟩
  · rintro ⟨c, g⟩ hx
    obtain ⟨h0, hx'⟩ := Finset.mem_sigma.mp hx
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hx'
    refine mem_cols_faceCover.mpr ?_
    simp only [Fin.cons_zero, Fin.tail_cons]
    exact ⟨h0, Fintype.mem_piFinset.mp h1, h2⟩
  · intro f _
    exact Fin.cons_self_tail f
  · rintro ⟨c, g⟩ _
    simp
  · intro f _
    rw [Fin.prod_univ_succ]
    rfl

/-! ### The bijection inequality -/

/-- The capacity lemma, read on the path. -/
theorem capacity_sum {k : ℕ} (hk : 3 ≤ k) (hCL : CL k (m + 1)) {Lu : Finset ℕ}
    {Li : Fin m → Finset ℕ} (hLu : Lu.card = k) (hLi : ∀ j, (Li j).card = k) {σ : ℕ → ℕ}
    (hinj : Set.InjOn σ Lu) (hfix : ∀ c ∈ Lu, σ c ≠ c) {v : Fin m → ℕ → ℝ}
    (hv : ∀ i, ∀ x ∈ Li i, 0 < v i x) {t : ℕ → ℝ} (ht : ∀ c ∈ Lu, 0 < t c) :
    lam k (m + 1) * (gmean Lu t * ∏ i, gmean (Li i) (v i))
      ≤ ∑ c ∈ Lu, t c * pathY Li v c (σ c) := by
  have hcard := faceCover_card (Li := Li) σ hLu hLi
  have h := (hCL (faceCover Lu Li σ) hcard (faceCover_isMatching Li hinj)
    (faceCover_noClosedThread Li hfix) (fun _ => 0)).le_Z
    (w := (Fin.cons t v : Fin (m + 1) → ℕ → ℝ))
    (fun i _ => by rw [← Finset.card_pos, hcard i]; omega)
    (fun i _ => by
      refine Fin.cases ?_ (fun i' => ?_) i
      · rw [faceCover_F_zero]
        exact ht
      · rw [faceCover_F_succ]
        exact hv i')
  rw [faceCover_Z, Fin.prod_univ_succ] at h
  simpa only [faceCover_F_zero, faceCover_F_succ, Fin.cons_zero, Fin.cons_succ] using h

/-- **The bijection inequality for the path**, from the capacity lemma. -/
theorem prod_pathY_ge {k : ℕ} (hk : 3 ≤ k) (hCL : CL k (m + 1)) {Lu : Finset ℕ}
    {Li : Fin m → Finset ℕ} (hLu : Lu.card = k) (hLi : ∀ j, (Li j).card = k) {σ : ℕ → ℕ}
    (hinj : Set.InjOn σ Lu) (hfix : ∀ c ∈ Lu, σ c ≠ c) {v : Fin m → ℕ → ℝ}
    (hv : ∀ i, ∀ x ∈ Li i, 0 < v i x) :
    (lam k (m + 1) / k * ∏ i, gmean (Li i) (v i)) ^ k ≤ ∏ c ∈ Lu, pathY Li v c (σ c) := by
  have hY : ∀ c ∈ Lu, 0 < pathY Li v c (σ c) := fun c hc =>
    pathY_pos (fun i => by rw [hLi i]; exact hk) hv (hfix c hc).symm
  have hne : Lu.Nonempty := by rw [← Finset.card_pos, hLu]; omega
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have ht : ∀ c ∈ Lu, 0 < (pathY Li v c (σ c))⁻¹ := fun c hc => inv_pos.mpr (hY c hc)
  have h := capacity_sum hk hCL hLu hLi hinj hfix hv ht
  have hsum : ∑ c ∈ Lu, (pathY Li v c (σ c))⁻¹ * pathY Li v c (σ c) = k := by
    rw [Finset.sum_congr rfl fun c hc => inv_mul_cancel₀ (hY c hc).ne', Finset.sum_const, hLu,
      nsmul_eq_mul, mul_one]
  rw [hsum] at h
  have hG : gmean Lu (fun c => (pathY Li v c (σ c))⁻¹) * gmean Lu (fun c => pathY Li v c (σ c))
      = 1 := by
    rw [← gmean_mul ht hY]
    exact gmean_eq_one (fun c hc => mul_pos (ht c hc) (hY c hc))
      (Finset.prod_eq_one fun c hc => inv_mul_cancel₀ (hY c hc).ne')
  have hpow := gmean_pow hne hY
  rw [hLu] at hpow
  rw [← hpow]
  set G := gmean Lu (fun c => pathY Li v c (σ c)) with hGdef
  set T := gmean Lu (fun c => (pathY Li v c (σ c))⁻¹) with hTdef
  set Γ := ∏ i, gmean (Li i) (v i) with hΓdef
  have hGpos : 0 < G := gmean_pos _ _
  have hΓpos : 0 < Γ := Finset.prod_pos fun i _ => gmean_pos _ _
  have hlam : 0 < lam k (m + 1) := lam_pos hk (by omega)
  have h1 : lam k (m + 1) * Γ ≤ k * G := by
    calc lam k (m + 1) * Γ = lam k (m + 1) * (T * Γ) * G := by
          rw [show lam k (m + 1) * (T * Γ) * G = lam k (m + 1) * Γ * (T * G) by ring, hG, mul_one]
      _ ≤ k * G := mul_le_mul_of_nonneg_right h hGpos.le
  refine pow_le_pow_left₀ (by positivity) ?_ k
  rw [div_mul_eq_mul_div, div_le_iff₀ hkpos]
  linarith

/-! ### The theorem -/

/-- **Closure of the invariant under the face operation**, given the capacity lemma. -/
theorem face_hasPot {k m : ℕ} (hk : 3 ≤ k) (hm : 1 ≤ m) (hCL : CL k (m + 1))
    (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ) (hLu : Lu.card = k) (hLv : Lv.card = k)
    (hLi : ∀ j, (Li j).card = k) (ω : Fin m → ℕ → ℝ) (hω : ∀ j, ∀ c ∈ Li j, 0 < ω j c)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 < A j)
    (hE : ∀ j : Fin (m + 1),
      HasPot (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    HasPot Lu Lv (faceSum Li ω E)
      (lam k (m + 1) / k * (∏ j, A j) * ∏ j, gmean (Li j) (ω j)) := by
  have _ := hm
  choose a b ha hb hpa hpb hW using hE
  -- the potentials at the interior vertices
  have hbi : ∀ i : Fin m, ∀ x ∈ Li i, 0 < b i.castSucc x := fun i x hx =>
    hb i.castSucc x (by rw [pathList_succ_castSucc]; exact hx)
  have hai : ∀ i : Fin m, ∀ x ∈ Li i, 0 < a i.succ x := fun i x hx =>
    ha i.succ x (by rw [pathList_castSucc_succ]; exact hx)
  have hpbi : ∀ i : Fin m, ∏ x ∈ Li i, b i.castSucc x = 1 := fun i => by
    have := hpb i.castSucc
    rwa [pathList_succ_castSucc] at this
  have hpai : ∀ i : Fin m, ∏ x ∈ Li i, a i.succ x = 1 := fun i => by
    have := hpa i.succ
    rwa [pathList_castSucc_succ] at this
  -- the potentials at the two ends
  have ha0 : ∀ c ∈ Lu, 0 < a 0 c := fun c hc =>
    ha 0 c (by rw [pathList_castSucc_zero]; exact hc)
  have hbl : ∀ d ∈ Lv, 0 < b (Fin.last m) d := fun d hd =>
    hb (Fin.last m) d (by rw [pathList_succ_last]; exact hd)
  have hpa0 : ∏ c ∈ Lu, a 0 c = 1 := by
    have := hpa 0
    rwa [pathList_castSucc_zero] at this
  have hpbl : ∏ d ∈ Lv, b (Fin.last m) d = 1 := by
    have := hpb (Fin.last m)
    rwa [pathList_succ_last] at this
  -- the vertex weights
  set v : Fin m → ℕ → ℝ := fun i x => ω i x * (b i.castSucc x * a i.succ x) with hvdef
  have hba : ∀ i : Fin m, ∀ x ∈ Li i, 0 < b i.castSucc x * a i.succ x := fun i x hx =>
    mul_pos (hbi i x hx) (hai i x hx)
  have hv : ∀ i, ∀ x ∈ Li i, 0 < v i x := fun i x hx => mul_pos (hω i x hx) (hba i x hx)
  have hgm : ∏ i, gmean (Li i) (v i) = ∏ i, gmean (Li i) (ω i) :=
    Finset.prod_congr rfl fun i _ => by
      rw [hvdef]
      dsimp only
      rw [gmean_mul (hω i) (hba i), gmean_mul (hbi i) (hai i), gmean_eq_one (hbi i) (hpbi i),
        gmean_eq_one (hai i) (hpai i), mul_one, mul_one]
  set Γ := ∏ i, gmean (Li i) (ω i) with hΓdef
  set β := lam k (m + 1) / k with hβdef
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hβ : 0 < β := div_pos (lam_pos hk (by omega)) hkpos
  have hΓ : 0 < Γ := Finset.prod_pos fun i _ => gmean_pos _ _
  have hβΓ : 0 < β * Γ := mul_pos hβ hΓ
  -- Egerváry
  obtain ⟨a', b', ha', hb', hpa', hpb', hW'⟩ := exists_potentials hk Lu Lv hLu hLv
    (fun c d => pathY Li v c d / (β * Γ))
    (fun c _ d _ hcd => div_pos (pathY_pos (fun i => by rw [hLi i]; exact hk) hv hcd) hβΓ)
    (fun σ hσ hfix => by
      have h := prod_pathY_ge hk hCL hLu hLi hσ.injOn hfix hv
      rw [hgm] at h
      rw [Finset.prod_div_distrib, Finset.prod_const, hLu]
      exact (one_le_div (pow_pos hβΓ k)).mpr h)
  refine ⟨fun c => a 0 c * a' c, fun d => b (Fin.last m) d * b' d,
    fun c hc => mul_pos (ha0 c hc) (ha' c hc), fun d hd => mul_pos (hbl d hd) (hb' d hd),
    by rw [Finset.prod_mul_distrib, hpa0, hpa', one_mul],
    by rw [Finset.prod_mul_distrib, hpbl, hpb', one_mul], fun c hc d hd hcd => ?_⟩
  have h1 := faceSum_ge hω hE0 (fun j => (hA j).le) ha hb hW hc hd
  have h2 : β * Γ * (a' c * b' d) ≤ pathY Li v c d := by
    have := hW' c hc d hd hcd
    rwa [le_div_iff₀ hβΓ, mul_comm] at this
  have hnn : 0 ≤ (∏ j, A j) * (a 0 c * b (Fin.last m) d) :=
    mul_nonneg (Finset.prod_nonneg fun j _ => (hA j).le) (mul_pos (ha0 c hc) (hbl d hd)).le
  calc β * (∏ j, A j) * Γ * (a 0 c * a' c * (b (Fin.last m) d * b' d))
      = (∏ j, A j) * (a 0 c * b (Fin.last m) d) * (β * Γ * (a' c * b' d)) := by ring
    _ ≤ (∏ j, A j) * (a 0 c * b (Fin.last m) d) * pathY Li v c d :=
        mul_le_mul_of_nonneg_left h2 hnn
    _ ≤ faceSum Li ω E c d := h1

end Outerplanar
