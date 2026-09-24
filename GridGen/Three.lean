/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.PairC
import GridGen.Explicit

/-!
# Height three: the general-height hypotheses are theorems

For the row graph `pathG 2` — three rows, the grid `P_3 □ P_{n+1}` — the two hypotheses of
`GridGen.Main`, `TwoStep` and `Init`, follow from the height-three development in `Grid3/`:
the pair lemmas `Grid3.pairH_of_five`, `Grid3.pairC_of_five` give the seam inequalities `(H1)`
and `(C1_r)` on every depth-one path vector, `Grid3.seam_le` turns them into the seam
inequality at every horizon for the reference `Grid3.Fpat`, and `Grid3.init_cond` is the
initial condition. This file transports those statements across the identification of
`State (PathV 2)` with `Grid3.State = ℕ × ℕ × ℕ`, and shows that the uniform futures `F` of a
capped pattern are exactly `Fpat`.

So `GeneralHeightConjecture` holds at height three: `conjecture_height_three`. Through
`ecc_of_twoStep` this reproves `ListColoring.ecc_boxProd_pathG_two` inside the general framework
(`ecc_pathG_two_gridGen`).
-/

namespace GridGen

open Finset SimpleGraph ListColoring
open scoped SimpleGraph

/-- The three rows. -/
abbrev V3 := PathV 2

/-! ### States as triples -/

/-- A state of the three-row column as a triple. -/
def toS (s : State V3) : Grid3.State := (s Grid3.rowT, s Grid3.rowM, s Grid3.rowB)

/-- A triple as a state of the three-row column. -/
def ofS (s : Grid3.State) : State V3 := fun x => Grid3.rowColor s x

theorem toS_ofS (s : Grid3.State) : toS (ofS s) = s := by
  obtain ⟨a, b, c⟩ := s
  simp [toS, ofS]

theorem ofS_toS (s : State V3) : ofS (toS s) = s := by
  funext x
  rcases Grid3.row_eq x with rfl | rfl | rfl <;> simp [ofS, toS]

theorem mem_states3 {X : Lists V3} {s : State V3} :
    s ∈ states (pathG 2) X ↔ toS s ∈ Grid3.states (X Grid3.rowT) (X Grid3.rowM) (X Grid3.rowB) := by
  rw [mem_states, Grid3.mem_states]
  constructor
  · rintro ⟨hmem, hprop⟩
    exact ⟨hmem _, hmem _, hmem _, hprop Grid3.adj_rowT_rowM, hprop Grid3.adj_rowM_rowB⟩
  · rintro ⟨h1, h2, h3, h12, h23⟩
    refine ⟨fun v => ?_, fun x y hxy => ?_⟩
    · rcases Grid3.row_eq v with rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
    · rcases Grid3.pathTwo_adj_iff.mp hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h12
      · exact Ne.symm h12
      · exact h23
      · exact Ne.symm h23

theorem compat3 (s t : State V3) : Compat s t ↔ Grid3.Compat (toS s) (toS t) := by
  constructor
  · intro h; exact ⟨h _, h _, h _⟩
  · rintro ⟨h1, h2, h3⟩ v
    rcases Grid3.row_eq v with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3

/-- Sums over the states of a three-row column, as sums over triples. -/
theorem sum_states3 (X : Lists V3) (f : State V3 → ℕ) :
    ∑ s ∈ states (pathG 2) X, f s
      = ∑ s' ∈ Grid3.states (X Grid3.rowT) (X Grid3.rowM) (X Grid3.rowB), f (ofS s') := by
  refine Finset.sum_nbij' toS ofS ?_ ?_ ?_ ?_ ?_
  · intro s hs; exact mem_states3.mp hs
  · intro s' hs'; exact mem_states3.mpr (by rw [toS_ofS]; exact hs')
  · intro s _; exact ofS_toS s
  · intro s' _; exact toS_ofS s'
  · intro s _; rw [ofS_toS]

/-- The same for a filtered sum. -/
theorem sum_states3_filter (X : Lists V3) (P : State V3 → Prop) [DecidablePred P]
    (P' : Grid3.State → Prop) [DecidablePred P'] (hP : ∀ s, P s ↔ P' (toS s))
    (f : State V3 → ℕ) :
    ∑ s ∈ (states (pathG 2) X).filter P, f s
      = ∑ s' ∈ (Grid3.states (X Grid3.rowT) (X Grid3.rowM) (X Grid3.rowB)).filter P',
          f (ofS s') := by
  refine Finset.sum_nbij' toS ofS ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_filter] at hs ⊢
    exact ⟨mem_states3.mp hs.1, (hP s).mp hs.2⟩
  · intro s' hs'
    rw [Finset.mem_filter] at hs' ⊢
    refine ⟨mem_states3.mpr (by rw [toS_ofS]; exact hs'.1), ?_⟩
    rw [hP, toS_ofS]; exact hs'.2
  · intro s _; exact ofS_toS s
  · intro s' _; exact toS_ofS s'
  · intro s _; rw [ofS_toS]

/-- The transfer, as the height-three transfer. -/
theorem step_eq_grid3 (X : Lists V3) (N : State V3 → ℕ) (t' : Grid3.State) :
    step (states (pathG 2) X) N (ofS t')
      = Grid3.step (Grid3.states (X Grid3.rowT) (X Grid3.rowM) (X Grid3.rowB))
          (fun s' => N (ofS s')) t' := by
  unfold step Grid3.step
  exact sum_states3_filter X (fun s => Compat s (ofS t')) (fun s' => Grid3.Compat s' t')
    (fun s => by rw [compat3, toS_ofS]) N

/-! ### Patterns at height three -/

theorem pat_lt_of_lt {V : Type*} [Fintype V] [DecidableEq V] {s : State V} {v w : V}
    (h : s v < s w) : pat s v < pat s w := by
  unfold pat
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨s v, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem s (Finset.mem_univ v), h⟩, ?_⟩
    simp [Finset.mem_filter]
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 h⟩

theorem pat_eq_iff {V : Type*} [Fintype V] [DecidableEq V] {s : State V} {v w : V} :
    pat s v = pat s w ↔ s v = s w := by
  constructor
  · intro h
    rcases lt_trichotomy (s v) (s w) with hlt | heq | hgt
    · exact absurd h (ne_of_lt (pat_lt_of_lt hlt))
    · exact heq
    · exact absurd h (ne_of_gt (pat_lt_of_lt hgt))
  · intro h; unfold pat; rw [h]

theorem image3 (s : State V3) :
    Finset.univ.image s = {s Grid3.rowT, s Grid3.rowM, s Grid3.rowB} := by
  ext c
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨v, rfl⟩
    rcases Grid3.row_eq v with rfl | rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

theorem pat_le_two (s : State V3) (v : V3) : pat s v ≤ 2 := by
  unfold pat
  rw [image3]
  have hv : s v ∈ ({s Grid3.rowT, s Grid3.rowM, s Grid3.rowB} : Finset ℕ) := by
    rcases Grid3.row_eq v with rfl | rfl | rfl <;> simp
  calc (({s Grid3.rowT, s Grid3.rowM, s Grid3.rowB} : Finset ℕ).filter (· < s v)).card
      ≤ (({s Grid3.rowT, s Grid3.rowM, s Grid3.rowB} : Finset ℕ).erase (s v)).card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_filter] at hx
        exact Finset.mem_erase.mpr ⟨ne_of_lt hx.2, hx.1⟩
    _ = ({s Grid3.rowT, s Grid3.rowM, s Grid3.rowB} : Finset ℕ).card - 1 :=
        Finset.card_erase_of_mem hv
    _ ≤ 2 := by have := Finset.card_le_three (a := s Grid3.rowT) (b := s Grid3.rowM) (c := s Grid3.rowB); omega

theorem patCap_eq_pat {k : ℕ} (hk : 3 ≤ k) (s : State V3) (v : V3) : patCap k s v = pat s v := by
  unfold patCap
  exact Nat.min_eq_left (by have := pat_le_two s v; omega)

/-- The capped pattern of a proper three-row state is a uniform state. -/
theorem toS_patCap_mem {k : ℕ} (hk : 3 ≤ k) {X : Lists V3} {s : State V3}
    (hs : s ∈ states (pathG 2) X) :
    toS (patCap k s) ∈ Grid3.states (range k) (range k) (range k) := by
  have hs' := mem_states3.mp hs
  rw [Grid3.mem_states] at hs' ⊢
  obtain ⟨_, _, _, h12, h23⟩ := hs'
  simp only [toS, patCap_eq_pat hk, Finset.mem_range]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := pat_le_two s Grid3.rowT; omega
  · have := pat_le_two s Grid3.rowM; omega
  · have := pat_le_two s Grid3.rowB; omega
  · exact fun h => h12 (pat_eq_iff.mp h)
  · exact fun h => h23 (pat_eq_iff.mp h)

theorem eqInd_patCap {k : ℕ} (hk : 3 ≤ k) (s : State V3) :
    Grid3.eqInd (toS (patCap k s)) = Grid3.eqInd (toS s) := by
  have hiff : Grid3.IsEq (toS (patCap k s)) ↔ Grid3.IsEq (toS s) := by
    unfold Grid3.IsEq toS
    simp only [patCap_eq_pat hk]
    exact pat_eq_iff
  unfold Grid3.eqInd
  by_cases h : Grid3.IsEq (toS s)
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]

/-! ### The uniform futures are `Fpat` -/

theorem unif_apply (k : ℕ) (v : V3) : unif (V := V3) k v = range k := rfl

theorem F_eq_Fpat {k : ℕ} (hk : 2 ≤ k) :
    ∀ i (s' : Grid3.State), s' ∈ Grid3.states (range k) (range k) (range k) →
      F (pathG 2) k i (ofS s') = Grid3.Fpat k i s' := by
  intro i
  induction i with
  | zero => intro s' _; rw [Grid3.Fpat_zero]; rfl
  | succ i ih =>
      intro s' hs'
      rw [F_succ, sum_states3_filter (unif k) (Compat (ofS s')) (Grid3.Compat s')
        (fun t => by rw [compat3, toS_ofS]) (F (pathG 2) k i)]
      simp only [unif_apply]
      rw [Finset.sum_congr rfl (fun t' ht' => ih t' (Finset.mem_filter.mp ht').1),
        Grid3.sum_compat_Fpat, Grid3.succ_uniform hk hs', Grid3.eqSucc_uniform hk hs',
        Grid3.Fpat_succ]

/-- The reference of a proper three-row state is `Fpat` of its triple. -/
theorem Φ_eq_Fpat {k : ℕ} (hk : 3 ≤ k) {X : Lists V3} {s : State V3}
    (hs : s ∈ states (pathG 2) X) (i : ℕ) :
    Φ (pathG 2) k i s = Grid3.Fpat k i (toS s) := by
  unfold Φ
  have hu := toS_patCap_mem hk hs
  rw [← ofS_toS (patCap k s), F_eq_Fpat (by omega) i _ hu]
  unfold Grid3.Fpat
  rw [eqInd_patCap hk]

/-! ### Seams -/

/-- The columns of a three-row chain as a height-three chain. -/
def toCols (L : Cols V3) : Grid3.Cols := fun j => (L j Grid3.rowT, L j Grid3.rowM, L j Grid3.rowB)

theorem isKCols_toCols {k : ℕ} {L : Cols V3} (hL : IsKCols k L) : Grid3.IsKCols k (toCols L) :=
  fun j => ⟨hL j _, hL j _, hL j _⟩

/-- A seam inequality of `Grid3` — `(H1)` and `(C1_r)` on the transported vector — gives the
seam inequality of the general framework at every horizon. -/
theorem seam_of_grid3 {k : ℕ} (hk : 3 ≤ k) (X : Lists V3) (N : State V3 → ℕ) (T : Lists V3)
    (i : ℕ)
    (h1 : Grid3.H1 (Grid3.states (X Grid3.rowT) (X Grid3.rowM) (X Grid3.rowB))
      (fun s' => N (ofS s')) (T Grid3.rowT) (T Grid3.rowM) (T Grid3.rowB) k)
    (hc : Grid3.C1r (Grid3.states (X Grid3.rowT) (X Grid3.rowM) (X Grid3.rowB))
      (fun s' => N (ofS s')) (T Grid3.rowT) (T Grid3.rowM) (T Grid3.rowB) k) :
    Seam (pathG 2) (Φ (pathG 2) k) (states (pathG 2) X) N T i := by
  unfold Seam
  have hl : ∑ s ∈ states (pathG 2) X, N s * Φ (pathG 2) k (i + 1) s
      = ∑ s' ∈ Grid3.states (X Grid3.rowT) (X Grid3.rowM) (X Grid3.rowB),
          N (ofS s') * Grid3.Fpat k (i + 1) s' := by
    rw [sum_states3 X (fun s => N s * Φ (pathG 2) k (i + 1) s)]
    refine Finset.sum_congr rfl fun s' hs' => ?_
    rw [Φ_eq_Fpat hk (mem_states3.mpr (by rw [toS_ofS]; exact hs')) (i + 1), toS_ofS]
  have hr : ∑ t ∈ states (pathG 2) T, step (states (pathG 2) X) N t * Φ (pathG 2) k i t
      = ∑ t' ∈ Grid3.states (T Grid3.rowT) (T Grid3.rowM) (T Grid3.rowB),
          Grid3.step (Grid3.states (X Grid3.rowT) (X Grid3.rowM) (X Grid3.rowB))
            (fun s' => N (ofS s')) t' * Grid3.Fpat k i t' := by
    rw [sum_states3 T (fun t => step (states (pathG 2) X) N t * Φ (pathG 2) k i t)]
    refine Finset.sum_congr rfl fun t' ht' => ?_
    rw [Φ_eq_Fpat hk (mem_states3.mpr (by rw [toS_ofS]; exact ht')) i, toS_ofS, step_eq_grid3]
  rw [hl, hr]
  exact Grid3.seam_le k i _ _ _ _ _ h1 hc

/-- **The two-step hypothesis at height three, for `k ≥ 5`.** -/
theorem depthOK_pathG_two {k : ℕ} (hk : 5 ≤ k) : DepthOK (pathG 2) (Φ (pathG 2) k) k 1 := by
  intro L hL j s₀ hs₀ i
  have hG : Grid3.DepthOK k 1 :=
    Grid3.depthOK_one_of_colOK (Grid3.colOK_of_pairOK (by omega) (Grid3.pairOK_of_five hk))
  have hs₀' : toS s₀ ∈ Grid3.cols (toCols L) j := mem_states3.mp hs₀
  obtain ⟨h1, hc⟩ := hG (toCols L) (isKCols_toCols hL) j (toS s₀) hs₀'
  have hvec : ∀ s' ∈ Grid3.cols (toCols L) (j + 1),
      Grid3.pathVec (toCols L) j (toS s₀) 1 s'
        = (fun s' => pathVec (pathG 2) L j s₀ 1 (ofS s')) s' := by
    intro s' hs'
    rw [Grid3.pathVec_one_compat (toCols L) j hs₀' s' hs', pathVec_one (pathG 2) L j hs₀]
    simp only []
    by_cases hcp : Compat s₀ (ofS s')
    · rw [if_pos hcp, if_pos (by rw [← toS_ofS s']; exact (compat3 _ _).mp hcp)]
    · rw [if_neg hcp, if_neg (fun h => hcp ((compat3 _ _).mpr (by rw [toS_ofS]; exact h)))]
  exact seam_of_grid3 (by omega) (L (j + 1)) _ (L (j + 1 + 1)) i (Grid3.H1_congr hvec h1)
    (Grid3.C1r_congr hvec hc)

/-- **The first seam at height three, for `k ≥ 5`.** -/
theorem shortOK_pathG_two {k : ℕ} (hk : 5 ≤ k) : ShortOK (pathG 2) (Φ (pathG 2) k) k 1 := by
  intro L hL j hj i
  obtain rfl : j = 0 := by omega
  have hG : Grid3.ShortOK k 1 :=
    Grid3.shortOK_one_of_colOK (Grid3.colOK_of_pairOK (by omega) (Grid3.pairOK_of_five hk))
  obtain ⟨h1, hc⟩ := hG (toCols L) (isKCols_toCols hL) 0 (by omega)
  have hvec : ∀ s' ∈ Grid3.cols (toCols L) 0,
      Grid3.vec (toCols L) 0 s' = (fun s' => vec (pathG 2) L 0 (ofS s')) s' := by
    intro s' _; rfl
  exact seam_of_grid3 (by omega) (L 0) _ (L 1) i (Grid3.H1_congr hvec h1) (Grid3.C1r_congr hvec hc)

theorem twoStep_pathG_two {k : ℕ} (hk : 5 ≤ k) : TwoStep (pathG 2) k :=
  ⟨depthOK_pathG_two hk, shortOK_pathG_two hk⟩

/-! ### The initial condition -/

/-- **The initial condition at height three, for `k ≥ 3`.** -/
theorem init_pathG_two {k : ℕ} (hk : 3 ≤ k) : Init (pathG 2) k := by
  intro X hX n
  have hL : ∑ s ∈ states (pathG 2) (unif k), F (pathG 2) k n s
      = Grid3.Fne k n * (k * (k - 1) ^ 2) + Grid3.Dp k n * (k * (k - 1)) := by
    rw [sum_states3]
    simp only [unif_apply]
    rw [Finset.sum_congr rfl (fun s' hs' => F_eq_Fpat (by omega) n s' hs'), Grid3.sum_Fpat,
      Grid3.card_states_uniform, Grid3.card_eq_states_uniform]
  have hR : ∑ s ∈ states (pathG 2) X, Φ (pathG 2) k n s
      = Grid3.Fne k n * (Grid3.states (X Grid3.rowT) (X Grid3.rowM) (X Grid3.rowB)).card
        + Grid3.Dp k n
          * ((Grid3.states (X Grid3.rowT) (X Grid3.rowM) (X Grid3.rowB)).filter Grid3.IsEq).card := by
    rw [sum_states3]
    rw [Finset.sum_congr rfl (fun s' hs' => by
      rw [Φ_eq_Fpat hk (mem_states3.mpr (by rw [toS_ofS]; exact hs')) n, toS_ofS]),
      Grid3.sum_Fpat]
  rw [hL, hR]
  have hst := Grid3.card_states_ge (hX Grid3.rowT) (hX Grid3.rowM) (hX Grid3.rowB)
  have hinit := Grid3.init_cond hk (hX Grid3.rowT) (hX Grid3.rowM) (hX Grid3.rowB)
  have hcd := Grid3.cc_mul_Dp_le k n
  zify at hst hinit hcd ⊢
  nlinarith [mul_le_mul_of_nonneg_left hinit (Int.natCast_nonneg (Grid3.Dp k n)),
    mul_nonneg (sub_nonneg.mpr hcd) (sub_nonneg.mpr hst)]

/-! ### The conjecture at height three -/

/-- **`GeneralHeightConjecture` holds at height three.** Both hypotheses of the general-height
reduction are theorems for the three-row column and every `k ≥ 5`. -/
theorem conjecture_height_three {k : ℕ} (hk : 5 ≤ k) :
    TwoStep (pathG 2) k ∧ Init (pathG 2) k :=
  ⟨twoStep_pathG_two hk, init_pathG_two (by omega)⟩

/-- **The explicit two-step inequality holds at height three.** -/
theorem twoStepExplicit_pathG_two {k : ℕ} (hk : 5 ≤ k) : TwoStepExplicit (pathG 2) k := by
  intro L hL j s₀ hs₀ i
  have h := depthOK_pathG_two hk L hL j s₀ hs₀ i
  unfold Seam at h
  rw [pathVec_one (pathG 2) L j hs₀, sum_step_mul, sum_ind_compat, sum_ind_compat] at h
  exact h

/-- **The explicit first-seam inequality holds at height three.** -/
theorem firstSeamExplicit_pathG_two {k : ℕ} (hk : 5 ≤ k) : FirstSeamExplicit (pathG 2) k := by
  intro L hL i
  have h := shortOK_pathG_two hk L hL 0 (by omega) i
  unfold Seam at h
  rw [vec_zero, sum_step_mul] at h
  simp only [one_mul] at h
  exact h

/-- **`P_3 □ P_{n+1}` is `k`-ECC for `k ≥ 5`, through the general-height framework.** -/
theorem ecc_pathG_two_gridGen {k : ℕ} (hk : 5 ≤ k) (n : ℕ) : (pathG 2 □ pathG n).ECCAt k :=
  ecc_of_twoStep (pathG 2) (twoStep_pathG_two hk) (init_pathG_two (by omega)) n

end GridGen
