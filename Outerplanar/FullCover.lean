/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Cover
import Cacti.BalancedCore

/-!
# Full covers of a cycle: the balanced case of the capacity lemma

This is the balanced (derangement monodromy) case of the capacity lemma of the outerplanar proof
draft, `ai_research_notes/OUTERPLANAR_PROOF_DRAFT_2026-11-09.md`, sections 2 and 3. A `k`-fold
cover of the cycle on `Fin n` whose matchings are all perfect is, after relabelling every fibre by
`Fin k` along the path `0, 1, …, n - 1`, the cycle twisted by one permutation `π` of `Fin k` on
the closing edge. If no thread closes after one turn, `π` is a derangement, the cover has
`(k - 1) ^ n - (-1) ^ n` colourings, and every colour of every fibre is used by the same number of
them. The inequality `1 + log x ≤ x`, summed over all colourings, then gives `Cover.capGE_full`.

The count is not redone here: the twisted cycle is the cover model `ListColoring.coverSet` of the
cactus development (`Cacti/BalancedCore.lean`), whose fibre counts `card_cover_root` and
`card_cover_vertex`, with the transfer-matrix entries `alpha`, `beta` of
`Cacti/TransferMatrix.lean`, are reused as they stand.

* `card_coverSet_fibre`, `natCast_mul_fibre` — the fibre count for a derangement and its value;
* `Cover.exists_fin_model` — the relabelling of a full cover by `Fin k`;
* `Cover.capGE_full` — the capacity bound.
-/

namespace Outerplanar

open Finset ListColoring

/-- For a derangement, every colour of every vertex of the twisted cycle is used by the same
number of colourings. -/
theorem card_coverSet_fibre {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) (π : Equiv.Perm (Fin k))
    (hπ : ∀ x, π x ≠ x) (i : Fin (m + 1)) (d : Fin k) :
    ((coverSet π m).filter (fun g => g i = d)).card = alpha k m + (k - 2) * beta k m := by
  rw [card_cover_vertex hm, card_cover_root, base_diag_moved hk π]
  exact fun h => hπ d ((Equiv.symm_apply_eq π).mp h).symm

/-- `k` times the fibre count is `(k - 1) ^ n - (-1) ^ n`. -/
theorem natCast_mul_fibre {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    (k : ℝ) * ((alpha k m + (k - 2) * beta k m : ℕ) : ℝ) = lam k (m + 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, k = q + 2 := ⟨k - 2, by omega⟩
  have h1 := alpha_add_beta (k := q + 2) (by omega) m
  have h2 := beta_alternation (k := q + 2) (by omega) m
  have e1 : q + 2 - 1 = q + 1 := by omega
  have e2 : q + 2 - 2 = q := by omega
  rw [e1] at h1
  rw [e2]
  have h1' : (alpha (q + 2) m : ℝ) + ((q : ℝ) + 1) * beta (q + 2) m = ((q : ℝ) + 1) ^ m := by
    exact_mod_cast h1
  have h3 : (alpha (q + 2) m : ℝ) - beta (q + 2) m = (-1) ^ m := by
    rcases Nat.even_or_odd m with he | ho
    · rw [h2.2 he, he.neg_one_pow]; push_cast; ring
    · rw [h2.1 ho, ho.neg_one_pow]; push_cast; ring
  rw [lam]
  push_cast
  linear_combination ((q : ℝ) + 1) * h1' + h3

/-- Adding one in `Fin (m + 1)` below the last element does not wrap. -/
theorem fin_mk_add_one {m j : ℕ} (hj : j + 1 < m + 1) :
    (⟨j, by omega⟩ : Fin (m + 1)) + 1 = ⟨j + 1, hj⟩ := by
  apply Fin.ext
  rw [Fin.val_add_one_of_lt (by rw [Fin.lt_def]; simp; omega)]

namespace Cover

/-- **Relabelling a full cover.** If all fibres have `k` colours and every matching is total,
the fibres can be labelled by `Fin k` so that the matchings along the path `0, …, m` preserve
the label, and the matching on the closing edge `m → 0` is a permutation of the labels. -/
theorem exists_fin_model {k m : ℕ} (P : Cover (m + 1)) (hcard : ∀ i, (P.F i).card = k)
    (hM : P.IsMatching) (hfull : ∀ i, ∀ x ∈ P.F i, ∃ y ∈ P.F (i + 1), P.M i x y) :
    ∃ (σ : Fin (m + 1) → Fin k → ℕ) (π : Equiv.Perm (Fin k)),
      (∀ i x, σ i x ∈ P.F i) ∧ (∀ i, Function.Injective (σ i)) ∧
      (∀ (i : Fin (m + 1)) (x : Fin k), i ≠ Fin.last m → P.M i (σ i x) (σ (i + 1) x)) ∧
      (∀ x, P.M (Fin.last m) (σ (Fin.last m) x) (σ 0 (π x))) := by
  have hex : ∀ (i : Fin (m + 1)) (x : ℕ), ∃ y, x ∈ P.F i → y ∈ P.F (i + 1) ∧ P.M i x y := by
    intro i x
    by_cases hx : x ∈ P.F i
    · obtain ⟨y, hy, hxy⟩ := hfull i x hx
      exact ⟨y, fun _ => ⟨hy, hxy⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose nxt hnxt using hex
  have hnxt_inj : ∀ i, ∀ x ∈ P.F i, ∀ x' ∈ P.F i, nxt i x = nxt i x' → x = x' := by
    intro i x hx x' hx' h
    have h1 := hnxt i x hx
    have h2 := hnxt i x' hx'
    rw [← h] at h2
    exact (hM i).2 x hx x' hx' _ h1.1 h1.2 h2.2
  let e0 : P.F 0 ≃ Fin k := Finset.equivFinOfCardEq (hcard 0)
  let s : ℕ → Fin k → ℕ := fun j => Nat.rec (fun x => ((e0.symm x : P.F 0) : ℕ))
    (fun j f x => if h : j < m + 1 then nxt ⟨j, h⟩ (f x) else f x) j
  have s_zero : ∀ x, s 0 x = ((e0.symm x : P.F 0) : ℕ) := fun x => rfl
  have s_succ : ∀ j (h : j < m + 1) x, s (j + 1) x = nxt ⟨j, h⟩ (s j x) := by
    intro j h x
    show (if h : j < m + 1 then nxt ⟨j, h⟩ (s j x) else s j x) = _
    rw [dite_eq_left h]
  have key : ∀ j (hj : j < m + 1), (∀ x, s j x ∈ P.F ⟨j, hj⟩) ∧ Function.Injective (s j) := by
    intro j
    induction j with
    | zero =>
      intro hj
      refine ⟨fun x => ?_, fun x y hxy => ?_⟩
      · rw [s_zero]
        exact (e0.symm x).2
      · rw [s_zero, s_zero] at hxy
        exact e0.symm.injective (Subtype.ext hxy)
    | succ j ih =>
      intro hj
      obtain ⟨hmem, hinj⟩ := ih (by omega)
      refine ⟨fun x => ?_, fun x y hxy => ?_⟩
      · rw [s_succ j (by omega), ← fin_mk_add_one hj]
        exact (hnxt _ _ (hmem x)).1
      · rw [s_succ j (by omega), s_succ j (by omega)] at hxy
        exact hinj (hnxt_inj _ _ (hmem x) _ (hmem y) hxy)
  let σ : Fin (m + 1) → Fin k → ℕ := fun i => s i.val
  have hσmem : ∀ i x, σ i x ∈ P.F i := fun i x => (key i.val i.isLt).1 x
  have hσinj : ∀ i, Function.Injective (σ i) := fun i => (key i.val i.isLt).2
  have h0 : Fin.last m + 1 = 0 := Fin.last_add_one m
  have hσ0 : ∀ x, σ 0 x = ((e0.symm x : P.F 0) : ℕ) := fun x => by
    show s (0 : Fin (m + 1)).val x = _
    rw [Fin.val_zero, s_zero]
  have hτ : ∀ x, nxt (Fin.last m) (σ (Fin.last m) x) ∈ P.F 0 := by
    intro x
    have := (hnxt (Fin.last m) _ (hσmem (Fin.last m) x)).1
    rwa [h0] at this
  let πf : Fin k → Fin k := fun x => e0 ⟨nxt (Fin.last m) (σ (Fin.last m) x), hτ x⟩
  have hπf : ∀ x, σ 0 (πf x) = nxt (Fin.last m) (σ (Fin.last m) x) := by
    intro x
    rw [hσ0]
    show ((e0.symm (e0 _) : P.F 0) : ℕ) = _
    rw [Equiv.symm_apply_apply]
  have hπinj : Function.Injective πf := by
    intro x y hxy
    have h1 : σ 0 (πf x) = σ 0 (πf y) := by rw [hxy]
    rw [hπf, hπf] at h1
    exact hσinj _ (hnxt_inj _ _ (hσmem _ x) _ (hσmem _ y) h1)
  refine ⟨σ, Equiv.ofBijective πf (Finite.injective_iff_bijective.mp hπinj), hσmem, hσinj,
    fun i x hi => ?_, fun x => ?_⟩
  · have hlt : i.val < m := by
      have := i.isLt
      have : i.val ≠ m := fun h => hi (Fin.ext h)
      omega
    have hv : (i + 1).val = i.val + 1 := Fin.val_add_one_of_lt (by rw [Fin.lt_def]; simpa using hlt)
    show P.M i (s i.val x) (s (i + 1).val x)
    rw [hv, s_succ i.val i.isLt]
    exact (hnxt i _ (hσmem i x)).2
  · show P.M (Fin.last m) (σ (Fin.last m) x) (σ 0 (πf x))
    rw [hπf]
    exact (hnxt _ _ (hσmem _ x)).2

/-- `Cover.capGE_full` on `Fin (m + 1)` with `m ≥ 1`, for `k ≥ 2`. -/
theorem capGE_full_aux {k m : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m) (P : Cover (m + 1))
    (hcard : ∀ i, (P.F i).card = k) (hM : P.IsMatching)
    (hfull : ∀ i, ∀ x ∈ P.F i, ∃ y ∈ P.F (i + 1), P.M i x y)
    (hno : P.NoClosedThread) (b : Fin (m + 1) → ℕ) : P.CapGE Finset.univ b (lam k (m + 1)) := by
  classical
  obtain ⟨σ, π, hσmem, hσinj, hpath, hclose⟩ := P.exists_fin_model hcard hM hfull
  have h0 : Fin.last m + 1 = 0 := Fin.last_add_one m
  -- the monodromy is a derangement
  have hπ : ∀ x, π x ≠ x := by
    intro x hx
    refine hno ⟨fun i => σ i x, fun i => hσmem i x, fun i => ?_⟩
    by_cases hi : i = Fin.last m
    · subst hi
      have := hclose x
      rw [hx] at this
      show P.M (Fin.last m) (σ (Fin.last m) x) (σ (Fin.last m + 1) x)
      rw [h0]
      exact this
    · exact hpath i x hi
  have himg : ∀ i, univ.image (σ i) = P.F i := by
    intro i
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hc
      exact hσmem i x
    · rw [Finset.card_image_of_injective _ (hσinj i), hcard]
      simp
  have hedge : ∀ i, i ≠ Fin.last m → ∀ x y, P.M i (σ i x) (σ (i + 1) y) → x = y := by
    intro i hi x y h
    exact hσinj _ ((hM i).1 _ (hσmem i x) _ (hσmem _ x) _ (hσmem _ y) (hpath i x hi) h)
  have hlast : ∀ x y, P.M (Fin.last m) (σ (Fin.last m) x) (σ 0 y) → π x = y := by
    intro x y h
    have hML := (hM (Fin.last m)).1
    rw [h0] at hML
    exact hσinj _ (hML _ (hσmem _ x) _ (hσmem _ _) _ (hσmem _ y) (hclose x) h)
  -- the colourings of the cover are the colourings of the twisted cycle
  let Φ : (Fin (m + 1) → Fin k) → Fin (m + 1) → ℕ := fun g i => σ i (g i)
  have hΦinj : Function.Injective Φ := fun g g' h => funext fun i => hσinj i (congrFun h i)
  have hcols : P.cols univ b = (coverSet π m).image Φ := by
    ext f
    rw [P.mem_cols, Finset.mem_image]
    constructor
    · rintro ⟨hf', hne'⟩
      have hf := fun i => (hf' i).1 (Finset.mem_univ i)
      have hne := fun i => hne' i (Finset.mem_univ _) (Finset.mem_univ _)
      have hx : ∀ i, ∃ x, σ i x = f i := by
        intro i
        have := hf i
        rw [← himg i, Finset.mem_image] at this
        obtain ⟨x, -, hx⟩ := this
        exact ⟨x, hx⟩
      choose g hg using hx
      refine ⟨g, ?_, funext hg⟩
      simp only [coverSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun e heq => hne e.castSucc ?_, fun heq => hne (Fin.last m) ?_⟩
      · rw [← hg e.castSucc, ← hg (e.castSucc + 1)]
        have := hpath e.castSucc (g e.castSucc) (Fin.castSucc_lt_last e).ne
        rw [Fin.coeSucc_eq_succ] at this ⊢
        rw [← heq]
        exact this
      · rw [h0, ← hg (Fin.last m), ← hg 0, ← heq]
        exact hclose _
    · rintro ⟨g, hg, rfl⟩
      simp only [coverSet, Finset.mem_filter, Finset.mem_univ, true_and] at hg
      refine ⟨fun i => ⟨fun _ => hσmem i _, fun h => absurd (Finset.mem_univ i) h⟩,
        fun i _ _ hMi => ?_⟩
      by_cases hi : i = Fin.last m
      · subst hi
        have h : P.M (Fin.last m) (σ (Fin.last m) (g (Fin.last m)))
            (σ (Fin.last m + 1) (g (Fin.last m + 1))) := hMi
        rw [h0] at h
        exact hg.2 (hlast _ _ h)
      · obtain ⟨e, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
        have h := hedge _ hi _ _ hMi
        rw [Fin.coeSucc_eq_succ] at h
        exact hg.1 e h
  intro w hw
  have hpos : ∀ i x, 0 < w i (σ i x) := fun i x => (hw i (Finset.mem_univ i)).1 _ (hσmem i x)
  have hZ : P.Z univ b w = ∑ g ∈ coverSet π m, ∏ i, w i (σ i (g i)) := by
    rw [Cover.Z, hcols, Finset.sum_image (fun g _ g' _ h => hΦinj h)]
  have hfib : ∀ i d, ((coverSet π m).filter (fun g => g i = d)).card
      = alpha k m + (k - 2) * beta k m := card_coverSet_fibre (by omega) hm π hπ
  -- the logarithms of the weights over a fibre sum to zero
  have hlog : ∀ i, ∑ d : Fin k, Real.log (w i (σ i d)) = 0 := by
    intro i
    rw [← Real.log_prod (fun d _ => (hpos i d).ne')]
    have : ∏ d : Fin k, w i (σ i d) = ∏ c ∈ P.F i, w i c := by
      rw [← himg i, Finset.prod_image (fun x _ y _ h => hσinj i h)]
    rw [this, (hw i (Finset.mem_univ i)).2, Real.log_one]
  -- balance: every colour of every fibre is used equally often
  have hsum : ∑ g ∈ coverSet π m, ∑ i, Real.log (w i (σ i (g i))) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    rw [← Finset.sum_fiberwise (coverSet π m) (fun g => g i)
      (fun g => Real.log (w i (σ i (g i))))]
    have hd : ∀ d : Fin k, ∑ g ∈ coverSet π m with g i = d, Real.log (w i (σ i (g i)))
        = ((alpha k m + (k - 2) * beta k m : ℕ) : ℝ) * Real.log (w i (σ i d)) := by
      intro d
      rw [Finset.sum_congr rfl (fun g hg => by rw [(Finset.mem_filter.mp hg).2]),
        Finset.sum_const, hfib, nsmul_eq_mul]
    rw [Finset.sum_congr rfl (fun d _ => hd d), ← Finset.mul_sum, hlog, mul_zero]
  have hN : ((coverSet π m).card : ℝ) = lam k (m + 1) := by
    rw [← natCast_mul_fibre hk m]
    have : (coverSet π m).card = ∑ d : Fin k, ((coverSet π m).filter (fun g => g 0 = d)).card :=
      Finset.card_eq_sum_card_fiberwise (fun g _ => Finset.mem_univ _)
    rw [this, Finset.sum_congr rfl (fun d _ => hfib 0 d)]
    simp
  rw [hZ, ← hN]
  calc ((coverSet π m).card : ℝ)
      = ∑ g ∈ coverSet π m, (1 + ∑ i, Real.log (w i (σ i (g i)))) := by
        rw [Finset.sum_add_distrib, hsum]
        simp
    _ ≤ ∑ g ∈ coverSet π m, ∏ i, w i (σ i (g i)) := Finset.sum_le_sum fun g _ => by
        rw [← Real.log_prod (fun i _ => (hpos i _).ne')]
        have hp : 0 < ∏ i, w i (σ i (g i)) := Finset.prod_pos (fun i _ => hpos i (g i))
        have := Real.log_le_sub_one_of_pos hp
        linarith

/-- A full cover of the cycle with no one-turn closed thread is balanced, with `lam k n`
colourings; so its capacity is at least `lam k n`. -/
theorem capGE_full {k n : ℕ} [NeZero n] (hn : 2 ≤ n) (P : Cover n)
    (hcard : ∀ i, (P.F i).card = k) (hM : P.IsMatching)
    (hfull : ∀ i, ∀ x ∈ P.F i, ∃ y ∈ P.F (i + 1), P.M i x y)
    (hno : P.NoClosedThread) (b : Fin n → ℕ) : P.CapGE Finset.univ b (lam k n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    · -- no colours at all: no colourings, and `lam 0 n = 0`
      intro w _
      have hempty : P.cols univ b = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro f hf
        have h := ((P.mem_cols.mp hf).1 0).1 (Finset.mem_univ _)
        rw [Finset.card_eq_zero.mp (hcard 0)] at h
        exact absurd h (Finset.notMem_empty _)
      rw [Cover.Z, hempty, Finset.sum_empty]
      simp [lam]
    · -- one colour: the only thread closes
      exfalso
      have hc : ∀ i, ∃ c, P.F i = {c} := fun i => Finset.card_eq_one.mp (hcard i)
      choose c hc using hc
      refine hno ⟨c, fun i => by rw [hc i]; exact Finset.mem_singleton_self _, fun i => ?_⟩
      obtain ⟨y, hy, h⟩ := hfull i (c i) (by rw [hc i]; exact Finset.mem_singleton_self _)
      rw [hc, Finset.mem_singleton] at hy
      rw [← hy]
      exact h
  · exact capGE_full_aux hk (by omega) P hcard hM hfull hno b

end Cover

end Outerplanar
