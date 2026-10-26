/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.K4.Fibre
import GridGen.Four.K4.Cone
import GridGen.Four.K4.Init

/-!
# Height four at `k = 4`: the conditional theorem

**`ecc_of_classify4`**: if the four-bad-pattern classification `Classify4` holds, then
`(pathG 3 □ pathG n).ECCAt 4` for every `n`, i.e. every `4 × (n+1)` grid is `4`-ECC.

The argument is Codex's (OpenAI), `ai_research_notes/cx/h4k4/NOTE.md` and
`ai_research_notes/cx/h4k4b/NOTE.md` (2026-10-25), reviewed in
`ai_research_notes/H4_K4_REVIEW_2026-10-26.md`. The one-column (depth-one) seam inequality is
false at `k = 4`; the telescope is run with lookback depth two (`GridGen/Telescope.lean`):

* **The reference.** GridGen's reference `Φ i s = F i (patCap 4 s)` is, on proper states, the
  class weight `cw (fv i)` of the uniform future `fv i = Hⁱ 1` (`Φ_eq4`); the uniform transfer is
  checked on the `108` uniform states (`cnt_ers_R4`).
* **Seams as seam vectors.** A seam inequality with state vector `N` on column `S` and next lists
  `T` is `0 ≤ ∑_{s ∈ S} N s · ⟪cnt (T ∖ s) − H_{class s}, fv i⟫` (`seam_of`).
* **`DepthOK` at depth two** (`depthOK_two`). The path vector of a state `s₀` two columns back
  turns that sum into `∑_{u ∈ sts X} ⟪dvec (A ∖ u) B, fv i⟫` with `X` the next lists punctured by
  `s₀` (three or four colours), `A`, `B` the following four-lists, which is `depth_two` at the
  weight `fv i ∈ K` (`cone_fv`).
* **`ShortOK`** (`shortOK_two`): the first seam is the one-column seam of four-lists, never bad
  (`not_bad_of_four`); the second is `depth_two` with `X` the unpunctured first column.
* **`Init`** (`init4`): `init_cnt` at `fv n`.

`allSeams_of_lookback` and `total_vec_ge_fw` then give the colouring-count bound.
-/

namespace GridGen.Four.K4

open Finset SimpleGraph ListColoring

/-- The uniform column at `k = 4`. -/
def R4 : Col := (range 4, range 4, range 4, range 4)

/-- **The uniform transfer** at `k = 4`, on the `108` uniform states. -/
theorem cnt_ers_R4 : ∀ t ∈ stsC R4, cnt (ers R4 t) = hrow t := by decide +kernel

/-- The lists of a column of `pathG 3`, as a tuple. -/
def colOf (X : Lists V4) : Col := (X q1, X q2, X q3, X q4)

/-- Sums over the states of a column, over tuples. -/
theorem sum_states4' {β : Type*} [AddCommMonoid β] (X : Lists V4) (f : State V4 → β) :
    ∑ s ∈ states (pathG 3) X, f s = ∑ t ∈ stsC (colOf X), f (ofT t) :=
  sum_states4 X f

/-- Sums over the successors of a state, over the punctured tuples. -/
theorem sum_states4_filter' {β : Type*} [AddCommMonoid β] (X : Lists V4) (s₀ : State V4)
    (f : State V4 → β) :
    ∑ s ∈ (states (pathG 3) X).filter (Compat s₀), f s
      = ∑ t ∈ stsC (ers (colOf X) (toT s₀)), f (ofT t) :=
  sum_states4_filter X s₀ f

theorem colOf_unif : colOf (unif 4) = R4 := rfl

theorem cw_one (t : T4) : cw (1, 1, 1, 1) t = 1 := by
  unfold cw ce; split_ifs <;> simp [dot]

theorem mem_R4_of_ers {s t : T4} (ht : t ∈ stsC (ers R4 s)) : t ∈ stsC R4 := by
  unfold stsC ers R4 at ht
  unfold stsC R4
  rw [mem_sts] at ht ⊢
  obtain ⟨h1, h2, h3, h4, p⟩ := ht
  exact ⟨Finset.mem_of_mem_erase h1, Finset.mem_of_mem_erase h2, Finset.mem_of_mem_erase h3,
    Finset.mem_of_mem_erase h4, p⟩

/-- GridGen's uniform futures at `k = 4` are the class weights of `fv i`. -/
theorem F_eq4 : ∀ i (s : State V4), toT s ∈ stsC R4 →
    (F (pathG 3) 4 i s : ℤ) = cw (fv i) (toT s)
  | 0, s, _ => by rw [F_zero]; simp [fv, cw_one]
  | i + 1, s, hs => by
      rw [F_succ]
      push_cast
      rw [sum_states4_filter', colOf_unif]
      have h : ∀ t ∈ stsC (ers R4 (toT s)), (F (pathG 3) 4 i (ofT t) : ℤ) = cw (fv i) t := by
        intro t ht
        rw [F_eq4 i (ofT t) (by rw [toT_ofT]; exact mem_R4_of_ers ht), toT_ofT]
      rw [Finset.sum_congr rfl h, fv_succ, cw_Hm, ← cnt_ers_R4 _ hs, dot_cnt]

/-- **The reference at `k = 4`**: `Φ i s = cw (fv i) s` on proper states. -/
theorem Φ_eq4 (i : ℕ) {s : State V4} (hs : Proper (toT s)) :
    (Φ (pathG 3) 4 i s : ℤ) = cw (fv i) (toT s) := by
  have hmem : toT (patCap 4 s) ∈ stsC R4 := by
    have hr := rowsIn_patCap (k := 4) le_rfl s
    have hp := proper_patCap (k := 4) le_rfl hs
    unfold stsC R4
    rw [mem_sts]
    exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, hp.1, hp.2.1, hp.2.2⟩
  unfold Φ
  rw [F_eq4 i _ hmem]
  unfold cw
  rw [ce_congr (samePat_patCap le_rfl s)]

/-- The successors of `s` in a column with lists `B`, weighted by the reference. -/
theorem sum_succ4 (B : Lists V4) (s : State V4) (i : ℕ) :
    ∑ t ∈ (states (pathG 3) B).filter (Compat s), (Φ (pathG 3) 4 i t : ℤ)
      = dot (cnt (ers (colOf B) (toT s))) (fv i) := by
  rw [sum_states4_filter', dot_cnt]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Φ_eq4 i (by rw [toT_ofT]; exact proper_of_mem_sts ht), toT_ofT]

/-- The seam defect of a state `s` before a column with lists `T`, at horizon `i`. -/
def dK (i : ℕ) (T : Lists V4) (s : State V4) : ℤ :=
  dot (cnt (ers (colOf T) (toT s)) - hrow (toT s)) (fv i)

/-- **A seam inequality as a sum of defects.** -/
theorem seam_of (S : Finset (State V4)) (N : State V4 → ℕ) (T : Lists V4) (i : ℕ)
    (hS : ∀ s ∈ S, Proper (toT s)) (h : 0 ≤ ∑ s ∈ S, (N s : ℤ) * dK i T s) :
    Seam (pathG 3) (Φ (pathG 3) 4) S N T i := by
  unfold Seam
  rw [sum_step_mul]
  have key : ((∑ s ∈ S, N s * Φ (pathG 3) 4 (i + 1) s : ℕ) : ℤ)
      ≤ ((∑ s ∈ S, N s * ∑ t ∈ (states (pathG 3) T).filter (Compat s),
          Φ (pathG 3) 4 i t : ℕ) : ℤ) := by
    push_cast
    rw [← sub_nonneg, ← Finset.sum_sub_distrib]
    convert h using 1
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Φ_eq4 (i + 1) (hS s hs), sum_succ4, fv_succ, cw_Hm, ← mul_sub, dK, dot_sub]
  exact_mod_cast key

/-- The transfer against an integer function. -/
theorem sum_step_mul_int (S : Finset (State V4)) (N : State V4 → ℕ) (X : Finset (State V4))
    (f : State V4 → ℤ) :
    ∑ t ∈ X, (step S N t : ℤ) * f t
      = ∑ s ∈ S, (N s : ℤ) * ∑ t ∈ X.filter (Compat s), f t := by
  simp only [step, Nat.cast_sum, Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

/-- The defects after a state `u`, summed over its successors: a seam value. -/
theorem inner4 (A T : Lists V4) (u : State V4) (i : ℕ) :
    ∑ s ∈ (states (pathG 3) A).filter (Compat u), dK i T s
      = dot (dvec (ers (colOf A) (toT u)) (colOf T)) (fv i) := by
  rw [sum_states4_filter']
  unfold dvec
  rw [dot_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [dK, toT_ofT]

theorem cards_of {L : Cols V4} (hL : IsKCols 4 L) (j : ℕ) : CardsIn 4 4 (colOf (L j)) := by
  simp only [CardsIn, colOf, hL j q1, hL j q2, hL j q3, hL j q4]
  omega

theorem cards34 {Y : Col} (h : CardsIn 4 4 Y) : CardsIn 3 4 Y := by
  obtain ⟨⟨a1, a1'⟩, ⟨a2, a2'⟩, ⟨a3, a3'⟩, ⟨a4, a4'⟩⟩ := h
  exact ⟨⟨by omega, a1'⟩, ⟨by omega, a2'⟩, ⟨by omega, a3'⟩, ⟨by omega, a4'⟩⟩

theorem proper_of_cols {L : Cols V4} {j : ℕ} {s : State V4} (hs : s ∈ cols (pathG 3) L j) :
    Proper (toT s) :=
  proper_of_mem_sts (mem_states4.mp hs)

/-- **`DepthOK` at depth two**, from the classification. -/
theorem depthOK_two (hC : Classify4) : DepthOK (pathG 3) (Φ (pathG 3) 4) 4 2 := by
  intro L hL j s₀ hs₀ i
  refine seam_of _ _ _ _ (fun s hs => proper_of_cols hs) ?_
  rw [show pathVec (pathG 3) L j s₀ 2
      = step (cols (pathG 3) L (j + 1)) (pathVec (pathG 3) L j s₀ 1) from rfl,
    pathVec_one _ L j hs₀, sum_step_mul_int]
  have e : ∀ u ∈ cols (pathG 3) L (j + 1),
      (((if Compat s₀ u then 1 else 0 : ℕ) : ℤ)
        * ∑ s ∈ (cols (pathG 3) L (j + 2)).filter (Compat u), (dK i (L (j + 2 + 1)) s))
      = if Compat s₀ u then
          ∑ s ∈ (cols (pathG 3) L (j + 2)).filter (Compat u), dK i (L (j + 2 + 1)) s
        else 0 := by
    intro u _; split_ifs <;> simp
  rw [Finset.sum_congr rfl e, ← Finset.sum_filter]
  unfold cols
  rw [sum_states4_filter']
  simp only [inner4, toT_ofT]
  exact depth_two hC (cards_ers (cards_of hL (j + 1)) (toT s₀)) (cards_of hL (j + 2))
    (cards_of hL (j + 2 + 1)) (fun d hd => cone_fv hd i)

/-- **`ShortOK` at depth two**, from the classification. -/
theorem shortOK_two (hC : Classify4) : ShortOK (pathG 3) (Φ (pathG 3) 4) 4 2 := by
  intro L hL j hj i
  refine seam_of _ _ _ _ (fun s hs => proper_of_cols hs) ?_
  interval_cases j
  · simp only [vec_zero, Nat.cast_one, one_mul]
    unfold cols
    rw [sum_states4']
    have e : ∑ t ∈ stsC (colOf (L 0)), dK i (L (0 + 1)) (ofT t)
        = dot (dvec (colOf (L 0)) (colOf (L (0 + 1)))) (fv i) := by
      unfold dvec
      rw [dot_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [dK, toT_ofT]
    rw [e]
    exact cone_fv (hC _ _ (cards34 (cards_of hL 0)) (cards_of hL (0 + 1))
      (not_bad_of_four (cards_of hL 0))) i
  · rw [vec_succ, vec_zero, sum_step_mul_int]
    simp only [Nat.cast_one, one_mul]
    unfold cols
    rw [sum_states4']
    simp only [inner4, toT_ofT]
    exact depth_two hC (cards34 (cards_of hL 0)) (cards_of hL 1) (cards_of hL (1 + 1))
      (fun d hd => cone_fv hd i)

/-- **`Init` at `k = 4`.** -/
theorem init4 : Init (pathG 3) 4 := by
  intro X hX n
  have hL : ∑ s ∈ states (pathG 3) (unif 4), (F (pathG 3) 4 n s : ℤ) = dot (cnt R4) (fv n) := by
    rw [sum_states4', colOf_unif, dot_cnt]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [F_eq4 n _ (by rw [toT_ofT]; exact ht), toT_ofT]
  have hR : ∑ s ∈ states (pathG 3) X, (Φ (pathG 3) 4 n s : ℤ) = dot (cnt (colOf X)) (fv n) := by
    rw [sum_states4', dot_cnt]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Φ_eq4 n (by rw [toT_ofT]; exact proper_of_mem_sts ht), toT_ofT]
  have hX' : CardsIn 4 4 (colOf X) := by
    simp only [CardsIn, colOf, hX q1, hX q2, hX q3, hX q4]
    omega
  have key : ∑ s ∈ states (pathG 3) (unif 4), (F (pathG 3) 4 n s : ℤ)
      ≤ ∑ s ∈ states (pathG 3) X, (Φ (pathG 3) 4 n s : ℤ) := by
    rw [hL, hR, ← sub_nonneg, ← dot_sub]
    have := cone_fv (init_cnt hX') n
    rwa [show cnt R4 = (12, 48, 24, 24) from cnt_range4]
  exact_mod_cast key

/-- **Height four at `k = 4`, conditionally.** If Codex's four-bad-pattern classification holds,
then `P₄ □ P_{n+1}` is `4`-ECC for every `n`. -/
theorem ecc_of_classify4 (hC : Classify4) (n : ℕ) : (pathG 3 □ pathG n).ECCAt 4 := by
  intro M hM
  rw [colConst_eq, col_eq_total_vec]
  have hall := allSeams_of_lookback (pathG 3) (Φ (pathG 3) 4) (depthOK_two hC) (shortOK_two hC)
  have hseams : ∀ j, j < n → Seam (pathG 3) (Φ (pathG 3) 4) (cols (pathG 3) (Lof n M) j)
      (vec (pathG 3) (Lof n M) j) (Lof n M (j + 1)) (n - (j + 1)) :=
    fun j _ => hall _ (Lof_isKCols hM) j _
  have htel := total_vec_ge_fw (pathG 3) (Φ (pathG 3) 4) (Lof n M) n (Φ_zero (pathG 3) 4) hseams
  exact le_trans (init4 _ (fun v => hM _) n) htel

end GridGen.Four.K4
