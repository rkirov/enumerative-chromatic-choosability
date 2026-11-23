/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.BareEven

/-!
# The hull class

The class of the profiles of pieces with one square below, as needed for a square over such a
piece (research note `ai_research_notes/OUTERPLANAR_SIX_EVEN_2026-11-23.md`, "Two even faces
below an arbitrary root"). On every matched six-family the six-vector, scaled by three,
dominates a mixture of the constant vector `3` and of the permutations of `(2, 3, 3, 4, 4, 4)`;
every proper pair has at least `2/3` of the constant.

* `vtx t` — for a triple `t = (i, j, k)` of distinct cells, the vertex `4 - 2[z = i] - [z = j]
  - [z = k]`, a permutation of `(2, 3, 3, 4, 4, 4)`. Writing the vertices by triples makes the
  closure under permutations of the cells a reindexing (`HullV.ds`).
* `HullV A x` — `3 x ≥ A · (3 μ₀ + Σ μ_t vtx t)` for a mixture `μ`.
* `HullC S T W A` — `HullV` on every matched six-family, and the floor `2/3`.
* `hullC_square` — a bare square is in the class, by the deficient pair of
  `Outerplanar/BareEven.lean` (`bsq_low`).

Part of the formalization of the six-even-face theorem (proof in the research note above, by a
ChatGPT session; audited and extended by Claude).
-/

namespace Outerplanar

open Finset

/-! ### Vertices and mixtures -/

/-- Triples of cells. -/
abbrev Tr := Fin 6 × Fin 6 × Fin 6

/-- Three distinct cells. -/
def Tr.ok (t : Tr) : Prop := t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

/-- The vertex of a triple: `4`, minus `2` at the first cell and `1` at the other two. -/
def vtx (t : Tr) (z : Fin 6) : ℝ :=
  4 - 2 * (if z = t.1 then 1 else 0) - (if z = t.2.1 then 1 else 0) - (if z = t.2.2 then 1 else 0)

theorem vtx_nonneg (t : Tr) (z : Fin 6) : 0 ≤ vtx t z := by
  unfold vtx
  split_ifs <;> norm_num

/-- `x` dominates `A/3` times a mixture of the constant `3` and of the vertices. -/
def HullV (A : ℝ) (x : Fin 6 → ℝ) : Prop :=
  ∃ (μ₀ : ℝ) (μ : Tr → ℝ), 0 ≤ μ₀ ∧ (∀ t, 0 ≤ μ t) ∧ (∀ t, μ t ≠ 0 → t.ok) ∧
    μ₀ + ∑ t, μ t = 1 ∧ ∀ z, A * (3 * μ₀ + ∑ t, μ t * vtx t z) ≤ 3 * x z

theorem mix_nonneg {μ₀ : ℝ} {μ : Tr → ℝ} (h0 : 0 ≤ μ₀) (hμ : ∀ t, 0 ≤ μ t) (z : Fin 6) :
    0 ≤ 3 * μ₀ + ∑ t, μ t * vtx t z :=
  add_nonneg (by linarith) (Finset.sum_nonneg fun t _ => mul_nonneg (hμ t) (vtx_nonneg t z))

theorem HullV.mono {A : ℝ} {x y : Fin 6 → ℝ} (h : HullV A x) (hle : ∀ z, x z ≤ y z) :
    HullV A y := by
  obtain ⟨μ₀, μ, h0, hμ, hok, h1, hx⟩ := h
  exact ⟨μ₀, μ, h0, hμ, hok, h1, fun z => (hx z).trans (by linarith [hle z])⟩

theorem HullV.of_ge {A : ℝ} {x : Fin 6 → ℝ} (h : ∀ z, A ≤ x z) : HullV A x :=
  ⟨1, fun _ => 0, zero_le_one, fun _ => le_rfl, fun _ h => absurd rfl h, by simp,
    fun z => by simp only [zero_mul, Finset.sum_const_zero, add_zero]; linarith [h z]⟩

theorem HullV.smul {A c : ℝ} {x : Fin 6 → ℝ} (h : HullV A x) (hc : 0 ≤ c) :
    HullV (c * A) fun z => c * x z := by
  obtain ⟨μ₀, μ, h0, hμ, hok, h1, hx⟩ := h
  refine ⟨μ₀, μ, h0, hμ, hok, h1, fun z => ?_⟩
  have := mul_le_mul_of_nonneg_left (hx z) hc
  linarith

theorem HullV.le_const {A A' : ℝ} {x : Fin 6 → ℝ} (h : HullV A x) (hA : A' ≤ A) :
    HullV A' x := by
  obtain ⟨μ₀, μ, h0, hμ, hok, h1, hx⟩ := h
  exact ⟨μ₀, μ, h0, hμ, hok, h1, fun z =>
    (mul_le_mul_of_nonneg_right hA (mix_nonneg h0 hμ z)).trans (hx z)⟩

/-- The triple moved by a permutation of the cells. -/
def Tr.map (σ : Equiv.Perm (Fin 6)) : Equiv.Perm Tr :=
  Equiv.prodCongr σ (Equiv.prodCongr σ σ)

theorem vtx_map (σ : Equiv.Perm (Fin 6)) (t : Tr) (k : Fin 6) :
    vtx (Tr.map σ t) (σ k) = vtx t k := by
  simp only [vtx, Tr.map, Equiv.prodCongr_apply, Prod.map, σ.apply_eq_iff_eq]

theorem Tr.ok_map {σ : Equiv.Perm (Fin 6)} {t : Tr} (h : (Tr.map σ t).ok) : t.ok := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [Tr.map, Equiv.prodCongr_apply, Prod.map] at h1 h2 h3
  exact ⟨fun e => h1 (by rw [e]), fun e => h2 (by rw [e]), fun e => h3 (by rw [e])⟩

/-- **The hull is closed under doubly stochastic mixing** (Birkhoff). -/
theorem HullV.ds {A : ℝ} {x : Fin 6 → ℝ} (h : HullV A x) {D : Fin 6 → Fin 6 → ℝ} (hD : DS D) :
    HullV A fun k => ∑ z, D k z * x z := by
  obtain ⟨μ₀, μ, h0, hμ, hok, h1, hx⟩ := h
  obtain ⟨s, w, hw0, hw1, hsum⟩ := hD.exists_perms
  refine ⟨μ₀, fun t => ∑ σ ∈ s, w σ * μ (Tr.map σ t), h0,
    fun t => Finset.sum_nonneg fun σ hσ => mul_nonneg (hw0 σ hσ) (hμ _), fun t ht => ?_, ?_,
    fun k => ?_⟩
  · obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
    exact Tr.ok_map (hok _ (right_ne_zero_of_mul hσ))
  · rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, Equiv.sum_comp (Tr.map _) μ]
    rw [← Finset.sum_mul, hw1, one_mul, h1]
  · show A * (3 * μ₀ + ∑ t, (∑ σ ∈ s, w σ * μ (Tr.map σ t)) * vtx t k) ≤ 3 * ∑ z, D k z * x z
    rw [hsum k x, Finset.mul_sum]
    -- each permutation: the vertices move with it
    have hσ : ∀ σ ∈ s, w σ * (A * (3 * μ₀ + ∑ t, μ (Tr.map σ t) * vtx t k))
        ≤ w σ * (3 * x (σ k)) := fun σ hσ => by
      refine mul_le_mul_of_nonneg_left ?_ (hw0 σ hσ)
      have e : ∑ t, μ (Tr.map σ t) * vtx t k = ∑ t, μ t * vtx t (σ k) := by
        rw [← Equiv.sum_comp (Tr.map σ) fun t => μ t * vtx t (σ k)]
        exact Finset.sum_congr rfl fun t _ => by rw [vtx_map]
      rw [e]
      exact hx _
    have e2 : A * (3 * μ₀ + ∑ t, (∑ σ ∈ s, w σ * μ (Tr.map σ t)) * vtx t k)
        = ∑ σ ∈ s, w σ * (A * (3 * μ₀ + ∑ t, μ (Tr.map σ t) * vtx t k)) := by
      simp only [Finset.sum_mul, mul_add, Finset.mul_sum]
      rw [Finset.sum_add_distrib, Finset.sum_comm (s := univ)]
      congr 1
      · rw [← Finset.sum_mul, hw1, one_mul]
      · exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun t _ => by ring
    rw [e2]
    calc ∑ σ ∈ s, w σ * (A * (3 * μ₀ + ∑ t, μ (Tr.map σ t) * vtx t k))
        ≤ ∑ σ ∈ s, w σ * (3 * x (σ k)) := Finset.sum_le_sum hσ
      _ = ∑ σ ∈ s, 3 * (w σ * x (σ k)) := Finset.sum_congr rfl fun σ _ => by ring

/-- Renumbering the cells. -/
theorem HullV.comp {A : ℝ} {x : Fin 6 → ℝ} (h : HullV A x) {κ : Fin 6 → Fin 6}
    (hκ : Function.Injective κ) : HullV A fun k => x (κ k) := by
  have := h.ds (pmat_ds hκ)
  refine this.mono fun k => le_of_eq ?_
  simp [pmat]

/-! ### The class -/

/-- **The hull class.** -/
def HullC (S T : Finset ℕ) (W : ℕ → ℕ → ℝ) (A : ℝ) : Prop :=
  (∀ p q : Fin 6 → ℕ, Matched S T p q → (∀ i, p i ≠ q i) → HullV A fun i => W (p i) (q i)) ∧
    Dominant S T W (2 / 3 * A)

section Class

variable {S T : Finset ℕ} {W W' : ℕ → ℕ → ℝ} {A A' : ℝ}

theorem HullC.of_dom (hA : 0 ≤ A) (h : Dominant S T W A) : HullC S T W A :=
  ⟨fun p q hm hpq => HullV.of_ge fun i => h _ (hm.mem i).1 _ (hm.mem i).2 (hpq i),
    fun c hc d hd hcd => le_trans (by linarith) (h c hc d hd hcd)⟩

theorem HullC.mono (h : HullC S T W A) (hle : ∀ c ∈ S, ∀ d ∈ T, c ≠ d → W c d ≤ W' c d) :
    HullC S T W' A :=
  ⟨fun p q hm hpq => (h.1 p q hm hpq).mono fun i =>
      hle _ (hm.mem i).1 _ (hm.mem i).2 (hpq i),
    fun c hc d hd hcd => (h.2 c hc d hd hcd).trans (hle c hc d hd hcd)⟩

theorem HullC.mul_dom (hA : 0 ≤ A) (hA' : 0 ≤ A') (h0 : ∀ c d, 0 ≤ W c d)
    (hD : Dominant S T W' A') (h : HullC S T W A) :
    HullC S T (fun c d => W' c d * W c d) (A' * A) := by
  refine ⟨fun p q hm hpq => ((h.1 p q hm hpq).smul hA').mono fun i => ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right (hD _ (hm.mem i).1 _ (hm.mem i).2 (hpq i)) (h0 _ _)
  · have := Dominant.mul hA' (by positivity) hD h.2
    rwa [show A' * (2 / 3 * A) = 2 / 3 * (A' * A) by ring] at this

theorem HullC.div (h : HullC S T W A) (hA : 0 < A) : HullC S T (fun c d => W c d / A) 1 := by
  refine ⟨fun p q hm hpq => ?_, fun c hc d hd hcd => ?_⟩
  · have := (h.1 p q hm hpq).smul (inv_nonneg.mpr hA.le)
    rw [inv_mul_cancel₀ hA.ne'] at this
    exact this.mono fun i => le_of_eq (by show _ = W (p i) (q i) / A; rw [div_eq_inv_mul])
  · rw [le_div_iff₀ hA]
    have := h.2 c hc d hd hcd
    linarith

theorem HullC.of_div (hA : 0 < A) (h : HullC S T (fun c d => W c d / A) A') :
    HullC S T W (A' * A) := by
  refine ⟨fun p q hm hpq => ?_, fun c hc d hd hcd => ?_⟩
  · have := (h.1 p q hm hpq).smul hA.le
    rw [mul_comm A A'] at this
    exact this.mono fun i => le_of_eq (by field_simp)
  · have := h.2 c hc d hd hcd
    rw [le_div_iff₀ hA] at this
    linarith

/-- The hull class at a root edge from its index form, as `tb_of_idx`. -/
theorem hullC_of_idx {Lu Lv : Finset ℕ} {F : ℕ → ℕ → ℝ} {A : ℝ}
    (h : ∀ α β : Fin 3 → ℕ, Function.Injective α → Function.Injective β → (∀ a, α a ∈ Lu) →
      (∀ b, β b ∈ Lv) → (∀ a b, α a = β b → a = b) →
      HullV A fun r => F (α (offPair r).1) (β (offPair r).2))
    (hfl : Dominant Lu Lv F (2 / 3 * A)) : HullC Lu Lv F A := by
  refine ⟨fun p q hm hpq => ?_, hfl⟩
  obtain ⟨α, β, hα, hβ, hαm, hβm, hab⟩ := hm
  have hal : ∀ a b, α a = β b → a = b := by
    intro a b e
    by_contra hne
    obtain ⟨r, hr1, hr2⟩ := hab a b hne
    exact hpq r (by rw [hr1, hr2, e])
  obtain ⟨κ, hκb, hκ⟩ := matched_reindex hα hβ hab
  have key := h α β hα hβ hαm hβm hal
  obtain ⟨ι, hι⟩ : ∃ ι : Fin 6 → Fin 6, ∀ i, κ (ι i) = i :=
    ⟨fun i => (hκb.2 i).choose, fun i => (hκb.2 i).choose_spec⟩
  have hιinj : Function.Injective ι := fun i i' e => by rw [← hι i, ← hι i', e]
  refine (key.comp hιinj).mono fun i => le_of_eq ?_
  show F (α (offPair (ι i)).1) (β (offPair (ι i)).2) = F (p i) (q i)
  rw [← (hκ (ι i)).1, ← (hκ (ι i)).2, hι]

end Class

/-! ### The bare square -/

theorem offPair_row_mate : ∀ m : Fin 6, ∃ m', m' ≠ m ∧ (offPair m').1 = (offPair m).1 := by
  decide

theorem offPair_col_mate : ∀ m : Fin 6, ∃ m', m' ≠ m ∧ (offPair m').2 = (offPair m).2 := by
  decide

/-- The other cell of the family in the row of a cell. -/
theorem Matched.row_mate {Lu Lw : Finset ℕ} {p q : Fin 6 → ℕ} (h : Matched Lu Lw p q)
    (i : Fin 6) : ∃ j, j ≠ i ∧ p j = p i := by
  obtain ⟨α, β, hα, hβ, -, -, hab⟩ := h
  obtain ⟨κ, hκb, hκ⟩ := matched_reindex hα hβ hab
  obtain ⟨m, rfl⟩ := hκb.2 i
  obtain ⟨m', hne, he⟩ := offPair_row_mate m
  exact ⟨κ m', fun e => hne (hκb.1 e), by rw [(hκ m').1, (hκ m).1, he]⟩

theorem Matched.col_mate {Lu Lw : Finset ℕ} {p q : Fin 6 → ℕ} (h : Matched Lu Lw p q)
    (i : Fin 6) : ∃ j, j ≠ i ∧ q j = q i := by
  obtain ⟨α, β, hα, hβ, -, -, hab⟩ := h
  obtain ⟨κ, hκb, hκ⟩ := matched_reindex hα hβ hab
  obtain ⟨m, rfl⟩ := hκb.2 i
  obtain ⟨m', hne, he⟩ := offPair_col_mate m
  exact ⟨κ m', fun e => hne (hκb.1 e), by rw [(hκ m').2, (hκ m).2, he]⟩

/-- On a matched family the deficient-pair table of a bare square is a vertex. -/
theorem vtx_le_lw {Lu Lw : Finset ℕ} {p q : Fin 6 → ℕ} (hm : Matched Lu Lw p q) {t₀ j k : Fin 6}
    (hj : j ≠ t₀) (hpj : p j = p t₀) (hk : k ≠ t₀) (hqk : q k = q t₀) (z : Fin 6) :
    vtx (t₀, j, k) z ≤ 2 + (if p z ≠ p t₀ then 1 else 0) + (if q z ≠ q t₀ then 1 else 0) := by
  have hqj : q j ≠ q t₀ := fun e => hj (hm.injective hpj e)
  have hpk : p k ≠ p t₀ := fun e => hk (hm.injective e hqk)
  unfold vtx
  by_cases h0 : z = t₀
  · subst h0
    simp [hj.symm, hk.symm]
    norm_num
  by_cases h1 : z = j
  · subst h1
    have hjk : z ≠ k := fun e => hqj (e ▸ hqk)
    simp [h0, hjk, hpj, hqj]
    norm_num
  by_cases h2 : z = k
  · subst h2
    simp [h0, h1, hpk, hqk]
    norm_num
  have hp : p z ≠ p t₀ := fun e =>
    hm.no_three hj.symm (Ne.symm h0) (fun e' => h1 e'.symm) hpj.symm e.symm
  have hq : q z ≠ q t₀ := fun e =>
    hm.symm.no_three hk.symm (Ne.symm h0) (fun e' => h2 e'.symm) hqk.symm e.symm
  simp [h0, h1, h2, hp, hq]
  norm_num

/-- **A bare square is in the hull class.** -/
theorem hullC_square (Lu Lv : Finset ℕ) (Li : Fin 2 → Finset ℕ) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin 3 → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin 3 → ℝ) (hA : ∀ j, 0 ≤ A j)
    (hE : ∀ j, Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    HullC Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 2 * ∏ j, A j) := by
  have hP0 : 0 ≤ ∏ j, A j := Finset.prod_nonneg fun j _ => hA j
  have h3 : faceConst3 2 = 3 := by norm_num [faceConst3]
  rw [h3]
  have hW : ∀ c ∈ Lu, ∀ d ∈ Lv,
      (∏ j, A j) * bsq (Li 0) (Li 1) c d ≤ faceSum Li (fun _ _ => 1) E c d := by
    intro c hc d hd
    have := faceSum_ge_bare Lu Lv Li E hE0 A hA hE hc hd
    rw [faceSum_two Li (fun _ => neP)] at this
    exact this
  refine ⟨fun p q hm hpq => ?_, fun c hc d hd hcd => ?_⟩
  · have hWB : ∀ t, (∏ j, A j) * bsq (Li 0) (Li 1) (p t) (q t)
        ≤ faceSum Li (fun _ _ => 1) E (p t) (q t) := fun t => hW _ (hm.mem t).1 _ (hm.mem t).2
    by_cases hall : ∀ t, 3 ≤ bsq (Li 0) (Li 1) (p t) (q t)
    · refine HullV.of_ge fun t => ?_
      calc 3 * ∏ j, A j = (∏ j, A j) * 3 := mul_comm _ _
        _ ≤ (∏ j, A j) * bsq (Li 0) (Li 1) (p t) (q t) :=
            mul_le_mul_of_nonneg_left (hall t) hP0
        _ ≤ _ := hWB t
    · simp only [not_forall, not_le] at hall
      obtain ⟨t₀, ht₀⟩ := hall
      obtain ⟨j, hj, hpj⟩ := hm.row_mate t₀
      obtain ⟨k, hk, hqk⟩ := hm.col_mate t₀
      have hqj : q j ≠ q t₀ := fun e => hj (hm.injective hpj e)
      have hjk : j ≠ k := fun e => hqj (e ▸ hqk)
      refine ⟨0, fun t => if t = (t₀, j, k) then 1 else 0, le_rfl,
        fun t => by dsimp only; split_ifs <;> norm_num, fun t ht => ?_, by simp, fun z => ?_⟩
      · have : t = (t₀, j, k) := by
          by_contra h
          exact ht (by simp [h])
        subst this
        exact ⟨hj.symm, hk.symm, hjk⟩
      · simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', mem_univ, ite_true,
          mul_zero, zero_add]
        have hlow := bsq_low (hLi 0) (hLi 1) (hpq t₀) ht₀ (hpq z)
        have hv := vtx_le_lw hm hj hpj hk hqk z
        have := hWB z
        nlinarith
  · have h2 := (bsq_ge (hLi 0) (hLi 1) c d).1
    have := hW c hc d hd
    nlinarith

end Outerplanar
