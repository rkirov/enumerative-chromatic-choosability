/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.Lookback

/-!
# The column form of the depth-one conditions

At depth one the path vector of a state `s₀` is the indicator of its successors, i.e. of the
states of the *punctured* next column `(T₁ \ a₀, M₁ \ b₀, B₁ \ c₀)`. So `DepthOK k 1` and
`ShortOK k 1` are both instances of one statement about six lists: the two seam inequalities for
the all-ones vector on `states X Y Z`, against a next column `(T, M, B)` of `k`-lists, with
`|X|, |Y|, |Z| ∈ {k-1, k}`. This file makes that reduction and expresses the inequalities as
sums over the middle colour `y ∈ Y` of per-colour terms.
-/

open Finset

namespace Grid3

/-! ### The column inequalities -/

/-- `(H1)` for the all-ones vector on `states X Y Z`, against `(T, M, B)`. -/
def ColH1 (k : ℕ) (X Y Z T M B : Finset ℕ) : Prop :=
  ene k * (states X Y Z).card + ((states X Y Z).filter IsEq).card
    ≤ ∑ s ∈ states X Y Z, succ T M B s

/-- `(C1_r)` for the all-ones vector on `states X Y Z`, against `(T, M, B)`. -/
def ColC1r (k : ℕ) (X Y Z T M B : Finset ℕ) : Prop :=
  cc k * (ene k * (states X Y Z).card + ((states X Y Z).filter IsEq).card)
      + gam k * (states X Y Z).card + del k * ((states X Y Z).filter IsEq).card
    ≤ cc k * ∑ s ∈ states X Y Z, succ T M B s + ∑ s ∈ states X Y Z, eqSucc T M B s

/-- A list of size `k - 1` or `k`. -/
def NearK (k : ℕ) (X : Finset ℕ) : Prop := X.card = k - 1 ∨ X.card = k

/-- **The column condition** at list size `k`: both inequalities for all near-`k` first columns
and all `k`-list next columns. -/
def ColOK (k : ℕ) : Prop :=
  ∀ X Y Z T M B : Finset ℕ, NearK k X → NearK k Y → NearK k Z →
    T.card = k → M.card = k → B.card = k → ColH1 k X Y Z T M B ∧ ColC1r k X Y Z T M B

/-! ### Ones vectors -/

theorem total_ones (S : Finset State) : total S (fun _ => 1) = S.card := by
  simp [total]

theorem eqMass_ones (S : Finset State) : eqMass S (fun _ => 1) = (S.filter IsEq).card := by
  simp [eqMass]

theorem H1_ones_iff (k : ℕ) (X Y Z T M B : Finset ℕ) :
    H1 (states X Y Z) (fun _ => 1) T M B k ↔ ColH1 k X Y Z T M B := by
  unfold H1 ColH1
  rw [total_ones, eqMass_ones, total_step]
  simp

theorem C1r_ones_iff (k : ℕ) (X Y Z T M B : Finset ℕ) :
    C1r (states X Y Z) (fun _ => 1) T M B k ↔ ColC1r k X Y Z T M B := by
  unfold C1r ColC1r
  rw [total_ones, eqMass_ones, total_step, eqMass_step]
  simp

/-- Restricting an indicator vector to a containing state set does not change its total. -/
theorem total_indicator {S S' : Finset State} (hS : S' ⊆ S) :
    total S (fun s => if s ∈ S' then 1 else 0) = total S' (fun _ => 1) := by
  unfold total
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hS]

/-- Restricting an indicator vector to a containing state set does not change its `eq` mass. -/
theorem eqMass_indicator {S S' : Finset State} (hS : S' ⊆ S) :
    eqMass S (fun s => if s ∈ S' then 1 else 0) = eqMass S' (fun _ => 1) := by
  unfold eqMass
  rw [← Finset.sum_filter, Finset.filter_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext s
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hs, heq, hs'⟩
    exact ⟨hs', heq⟩
  · rintro ⟨hs', heq⟩
    exact ⟨hS hs', heq, hs'⟩

/-- Transfer from an indicator inside a containing state set is transfer from that subset. -/
theorem step_indicator {S S' : Finset State} (hS : S' ⊆ S) :
    step S (fun s => if s ∈ S' then 1 else 0) = step S' (fun _ => 1) := by
  funext t
  unfold step
  rw [← Finset.sum_filter, Finset.filter_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext s
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hs, hc, hs'⟩
    exact ⟨hs', hc⟩
  · rintro ⟨hs', hc⟩
    exact ⟨hS hs', hc, hs'⟩

/-- The seam inequalities depend on the vector only through its restriction to the column, so
an indicator of `S'` inside a larger state set `S` behaves exactly as the ones vector on `S'`. -/
theorem H1_indicator_iff {S S' : Finset State} (hS : S' ⊆ S) {T M B : Finset ℕ} {k : ℕ} :
    H1 S (fun s => if s ∈ S' then 1 else 0) T M B k ↔ H1 S' (fun _ => 1) T M B k := by
  unfold H1
  rw [total_indicator hS, eqMass_indicator hS, step_indicator hS]

theorem C1r_indicator_iff {S S' : Finset State} (hS : S' ⊆ S) {T M B : Finset ℕ} {k : ℕ} :
    C1r S (fun s => if s ∈ S' then 1 else 0) T M B k ↔ C1r S' (fun _ => 1) T M B k := by
  unfold C1r
  rw [total_indicator hS, eqMass_indicator hS, step_indicator hS]

theorem H1_of_indicator {S S' : Finset State} (hS : S' ⊆ S) {T M B : Finset ℕ} {k : ℕ}
    (h : H1 S' (fun _ => 1) T M B k) : H1 S (fun s => if s ∈ S' then 1 else 0) T M B k :=
  (H1_indicator_iff hS).2 h

theorem C1r_of_indicator {S S' : Finset State} (hS : S' ⊆ S) {T M B : Finset ℕ} {k : ℕ}
    (h : C1r S' (fun _ => 1) T M B k) : C1r S (fun s => if s ∈ S' then 1 else 0) T M B k :=
  (C1r_indicator_iff hS).2 h

/-! ### Depth one -/

/-- At depth one, a state is reached exactly when it is compatible with the starting state. -/
theorem pathVec_one_compat (L : Cols) (j : ℕ) {s₀ : State} (hs₀ : s₀ ∈ cols L j) :
    ∀ s ∈ cols L (j + 1), pathVec L j s₀ 1 s = if Compat s₀ s then 1 else 0 := by
  intro s _
  rw [pathVec_succ, Nat.add_zero, pathVec_zero]
  unfold step
  rw [Finset.sum_ite_eq' ((cols L j).filter fun s' => Compat s' s) s₀ (fun _ => 1)]
  have hmem : s₀ ∈ (cols L j).filter (fun s' => Compat s' s) ↔ Compat s₀ s := by
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hs₀, h⟩⟩
  by_cases hc : Compat s₀ s
  · rw [if_pos (hmem.mpr hc), if_pos hc]
  · rw [if_neg (fun h => hc (hmem.mp h)), if_neg hc]

/-- The depth-one path vector of `s₀ ∈ cols L j` is the indicator of its successors, which are
the states of the punctured next column. -/
theorem pathVec_one (L : Cols) (j : ℕ) {s₀ : State} (hs₀ : s₀ ∈ cols L j) :
    ∀ s ∈ cols L (j + 1), pathVec L j s₀ 1 s
      = if s ∈ states ((L (j+1)).1.erase s₀.1) ((L (j+1)).2.1.erase s₀.2.1)
          ((L (j+1)).2.2.erase s₀.2.2) then 1 else 0 := by
  intro s hs
  rw [pathVec_one_compat L j hs₀ s hs]
  have h2 : s ∈ states ((L (j+1)).1.erase s₀.1) ((L (j+1)).2.1.erase s₀.2.1)
      ((L (j+1)).2.2.erase s₀.2.2) ↔ Compat s₀ s := by
    rw [← filter_compat_eq_states, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hs, h⟩⟩
  by_cases hc : Compat s₀ s
  · rw [if_pos hc, if_pos (h2.mpr hc)]
  · rw [if_neg hc, if_neg (fun h => hc (h2.mp h))]

theorem nearK_erase {k : ℕ} {X : Finset ℕ} (hX : X.card = k) (a : ℕ) : NearK k (X.erase a) := by
  by_cases h : a ∈ X
  · left; rw [Finset.card_erase_of_mem h, hX]
  · right; rw [Finset.erase_eq_of_notMem h, hX]

theorem nearK_of_card {k : ℕ} {X : Finset ℕ} (hX : X.card = k) : NearK k X := Or.inr hX

/-- The punctured next column sits inside the next column. -/
theorem states_erase_subset (T M B : Finset ℕ) (s₀ : State) :
    states (T.erase s₀.1) (M.erase s₀.2.1) (B.erase s₀.2.2) ⊆ states T M B := by
  intro t ht
  rw [mem_states] at ht ⊢
  exact ⟨(Finset.mem_erase.mp ht.1).2, (Finset.mem_erase.mp ht.2.1).2,
    (Finset.mem_erase.mp ht.2.2.1).2, ht.2.2.2.1, ht.2.2.2.2⟩

/-- **`ColOK` gives depth one.** -/
theorem depthOK_one_of_colOK {k : ℕ} (h : ColOK k) : DepthOK k 1 := by
  intro L hL j s₀ hs₀
  obtain ⟨hT, hM, hB⟩ := hL (j + 1)
  obtain ⟨hT2, hM2, hB2⟩ := hL (j + 1 + 1)
  have hcol := h ((L (j+1)).1.erase s₀.1) ((L (j+1)).2.1.erase s₀.2.1) ((L (j+1)).2.2.erase s₀.2.2)
    (L (j+1+1)).1 (L (j+1+1)).2.1 (L (j+1+1)).2.2 (nearK_erase hT _) (nearK_erase hM _)
    (nearK_erase hB _) hT2 hM2 hB2
  have hsub := states_erase_subset (L (j+1)).1 (L (j+1)).2.1 (L (j+1)).2.2 s₀
  have hcong := pathVec_one L j hs₀
  refine ⟨H1_congr (fun s hs => (hcong s hs).symm) ?_, C1r_congr (fun s hs => (hcong s hs).symm) ?_⟩
  · exact H1_of_indicator hsub ((H1_ones_iff _ _ _ _ _ _ _).mpr hcol.1)
  · exact C1r_of_indicator hsub ((C1r_ones_iff _ _ _ _ _ _ _).mpr hcol.2)

/-- **`ColOK` gives the first seam.** -/
theorem shortOK_one_of_colOK {k : ℕ} (h : ColOK k) : ShortOK k 1 := by
  intro L hL j hj
  have hj0 : j = 0 := by omega
  subst hj0
  obtain ⟨hT, hM, hB⟩ := hL 0
  obtain ⟨hT1, hM1, hB1⟩ := hL 1
  have hcol := h (L 0).1 (L 0).2.1 (L 0).2.2 (L 1).1 (L 1).2.1 (L 1).2.2
    (nearK_of_card hT) (nearK_of_card hM) (nearK_of_card hB) hT1 hM1 hB1
  unfold SeamOK
  rw [vec_zero]
  exact ⟨(H1_ones_iff _ _ _ _ _ _ _).mpr hcol.1, (C1r_ones_iff _ _ _ _ _ _ _).mpr hcol.2⟩

/-- **The theorem, from the column condition.** -/
theorem ecc_of_colOK {k : ℕ} (hk : 3 ≤ k) (h : ColOK k) (n : ℕ) :
    (ListColoring.pathG 2 □ ListColoring.pathG n).ECCAt k :=
  ecc_of_lookback hk (depthOK_one_of_colOK h) (shortOK_one_of_colOK h) n

end Grid3
