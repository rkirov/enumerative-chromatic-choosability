/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.MarkMix

/-!
# The one-mark class

Research note `ai_research_notes/OUTERPLANAR_ELEVEN_AND_CENTRAL_SQUARE_2026-11-23.md`, "Stronger
estimates through three marks": *on a branch with one mark we may use the constant alternative or a
single table `Z` with the following simultaneous bounds: floor `2/3`, bijection product `q`,
four-cell quantity `T ≥ 3/4`, and `AB`; for each matched family its six-vector dominates a convex
combination of the constant vector and permutations of `(2, 3, 3, 4, 4, 4)/3`.* Here `q = 32/27`,
`A = 17/16`, `B` the unit ball.

* `P1 S T Y v` — floor `2/3 v`, `BijGe` with surplus `32/27`, `TB` with `3/4`, the ball with
  constant `v · 17/16`, and the hull class; `cone1`. The class is **`K1 = Mx P1`**: a mixture of the
  constant and such tables (the tables are closed under sums, so a mixture of several is one).
* `p1_lvZ` — the table `lvZ a b` of a deficient bare even face has all five bounds;
  `mx1_even_bare` — **every bare even face is in `K1`**.
* `p1_odd` — **transport through an odd face** with one loaded path edge;
  `mx1_odd` — an odd face with one side in `K1` and greedy other sides is in `K1`.
* `p1_lift`, `p1_swap` — vertex lifts and transposition.

The theorem of the note is due to another AI session of this repository's collaboration; audited
and formalized by Claude.
-/

namespace Outerplanar

open Finset

/-! ### Small facts -/

theorem Dominant.bijGe {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {N : ℝ} (hN : 0 ≤ N)
    (h : Dominant S T W N) : BijGe S T W N 1 := fun α β _ _ hαm hβm hne => by
  rw [one_mul, ← Fin.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ => hN) fun a _ => h _ (hαm a) _ (hβm a) (hne a)

theorem prod_ite_scale {n : ℕ} (j₀ : Fin n) (c : ℝ) (A : Fin n → ℝ) :
    ∏ j, (if j = j₀ then c * A j else A j) = c * ∏ j, A j := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ j₀), ← Finset.mul_prod_erase univ A (mem_univ j₀),
    if_pos rfl, mul_assoc]
  congr 2
  exact Finset.prod_congr rfl fun j hj => if_neg (Finset.ne_of_mem_erase hj)

theorem prod_ite_one {n : ℕ} (j₀ : Fin n) (c : ℝ) :
    ∏ j, (if j = j₀ then c else 1) = c := by
  rw [Finset.prod_ite_eq']
  simp

theorem faceConst3_odd_dd {m : ℕ} (hm : Odd m) (j₀ : Fin (m + 1)) :
    dd j₀ (m - j₀) / faceConst3 m = 1 := by
  rw [dd_face]
  have : ¬ Even m := Nat.not_even_iff_odd.mpr hm
  simp only [this, ↓reduceIte, sub_zero]
  exact div_self (faceConst3_pos m).ne'

/-! ### The class -/

/-- The tables of the one-mark class, with constant `v`. -/
def P1 (S T : Finset ℕ) (Y : ℕ → ℕ → ℝ) (v : ℝ) : Prop :=
  Dominant S T Y (2 / 3 * v) ∧ BijGe S T Y v (32 / 27) ∧ TB S T Y v (3 / 4) ∧
    InBall S T Y (v * (17 / 16)) ∧ HullC S T Y v

theorem cone1 : ConeP P1 where
  zero S T := ⟨fun _ _ _ _ _ => by simp, fun _ _ _ _ _ _ _ => by simp,
    fun _ _ _ _ _ _ _ _ _ _ _ _ => by simp, by rw [zero_mul]; exact InBall.zero fun _ _ => le_rfl,
    HullC.of_dom le_rfl fun _ _ _ _ _ => le_rfl⟩
  add := by
    intro S T Y Y' v v' hv hv' h0 h0' h h'
    refine ⟨?_, h.2.1.add (by norm_num) hv hv' h0 h0' h'.2.1,
      h.2.2.1.add (by norm_num) hv hv' h0 h0' h'.2.2.1, ?_, h.2.2.2.2.add hv hv' h'.2.2.2.2⟩
    · have := h.1.add h'.1
      rwa [show 2 / 3 * v + 2 / 3 * v' = 2 / 3 * (v + v') by ring] at this
    · have := InBall.add (by positivity) (by positivity) h0 h0' h.2.2.2.1 h'.2.2.2.1
      rwa [show v * (17 / 16) + v' * (17 / 16) = (v + v') * (17 / 16) by ring] at this
  smul := by
    intro S T Y v l hl hv h0 h
    refine ⟨?_, h.2.1.smul hl, h.2.2.1.smul hl, ?_, h.2.2.2.2.smul hl hv h0⟩
    · have := h.1.smul hl
      rwa [show l * (2 / 3 * v) = 2 / 3 * (l * v) by ring] at this
    · have := InBall.smul hl (by positivity) h.2.2.2.1
      rwa [show l * (v * (17 / 16)) = l * v * (17 / 16) by ring] at this
  mono := by
    intro S T Y Y' v h0 hle h
    exact ⟨h.1.mono hle, h.2.1.mono h0 hle, h.2.2.1.mono h0 hle, h.2.2.2.1.mono h0 hle,
      h.2.2.2.2.mono hle⟩
  weaken := by
    intro S T Y v v' hv' hle _ h
    exact ⟨h.1.le (by linarith), h.2.1.weaken (by norm_num) hv' hle, h.2.2.1.weaken hv' hle,
      h.2.2.2.1.weaken (by positivity) (by linarith), h.2.2.2.2.weaken hv' hle⟩

theorem P1.nonneg_floor {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} (h : P1 S T Y v) :
    Dominant S T Y (2 / 3 * v) := h.1

theorem p1_swap {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} (h : P1 S T Y v) :
    P1 T S (fun d c => Y c d) v :=
  ⟨h.1.swap, h.2.1.swap, h.2.2.1.swap, h.2.2.2.1.swap, h.2.2.2.2.swap⟩

theorem p1_lift {S T U : Finset ℕ} (hS : S.card = 3) (hT : T.card = 3) (hU : U.card = 3)
    {Y : ℕ → ℕ → ℝ} {v : ℝ} (hv : 0 ≤ v) (h0 : ∀ c d, 0 ≤ Y c d) (h : P1 S T Y v) :
    P1 S U (fun c _ => liftV T Y c) (2 * v) := by
  refine ⟨?_, h.2.1.lift hS hT h0 (by norm_num) hv, lift_tb hT h0 h.2.2.1, ?_,
    lift_hullC hT h0 hv h.2.2.2.2⟩
  · have := lift_dom (U := U) (by positivity) hT h.1
    rwa [show 2 * (2 / 3 * v) = 2 / 3 * (2 * v) by ring] at this
  · have := lift_ball (U := U) hS hT hU h0 (by positivity) h.2.2.2.1
    rwa [show 2 * (v * (17 / 16)) = 2 * v * (17 / 16) by ring] at this

/-! ### The table of a deficient bare even face -/

theorem lvZ_hull (S T : Finset ℕ) (a b : ℕ) : HullC S T (lvZ a b) 1 := by
  refine ⟨fun p q hm hpq => ?_, fun c _ e _ _ => by
    have := (lvZ_bounds a b c e).1; linarith⟩
  by_cases hex : ∃ t₀, p t₀ = a ∧ q t₀ = b
  · obtain ⟨t₀, hpa, hqb⟩ := hex
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
      have hv := vtx_le_lw hm hj hpj hk hqk z
      rw [hpa, hqb] at hv
      have e : 3 * lvZ a b (p z) (q z) = 2 + (if p z ≠ a then 1 else 0) + (if q z ≠ b then 1 else 0) := by
        unfold lvZ
        rw [lv_cast]
        ring
      linarith
  · push Not at hex
    refine HullV.of_ge fun i => ?_
    unfold lvZ
    rw [lv_cast]
    by_cases h1 : p i = a
    · have h2 := hex i h1
      simp [h1, h2]
      norm_num
    · simp only [ne_eq, h1, not_false_eq_true, ite_true]
      split_ifs <;> norm_num

theorem p1_lvZ (S T : Finset ℕ) (a b : ℕ) : P1 S T (lvZ a b) 1 := by
  obtain ⟨-, hD, hB, hT⟩ := zGood_lv S T a b
  refine ⟨by simpa using hD, hB, hT, by simpa using lvZ_ball S T a b, lvZ_hull S T a b⟩

/-! ### Bare even faces -/

/-- The mixture of the constant and `lvZ a b`. -/
theorem mx1_of_low {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {α K : ℝ} (hα : 3 ≤ α) (hK : 0 ≤ K)
    {a b : ℕ} (h : ∀ c ∈ S, ∀ d ∈ T, c ≠ d →
      K * (α - 1 + (if c ≠ a then 1 else 0) + (if d ≠ b then 1 else 0)) ≤ W c d) :
    Mx P1 S T W (α * K) := by
  refine ⟨K * (α - 3), 3 * K, fun c e => 3 * K * lvZ a b c e, by nlinarith, by positivity,
    by nlinarith, fun c e => by unfold lvZ; positivity, ?_, fun c hc d hd hcd => ?_⟩
  · have := cone1.smul (3 * K) (by positivity) zero_le_one (fun c e => by unfold lvZ; positivity)
      (p1_lvZ S T a b)
    rwa [mul_one] at this
  · refine le_trans (le_of_eq ?_) (h c hc d hd hcd)
    simp only [lvZ]
    rw [lv_cast]
    ring

/-- **A bare square is in the one-mark class.** -/
theorem mx1_square (Lu Lv : Finset ℕ) (Li : Fin 2 → Finset ℕ) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin 3 → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin 3 → ℝ) (hA : ∀ j, 0 ≤ A j)
    (hE : ∀ j, Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Mx P1 Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 2 * ∏ j, A j) := by
  have hP0 : 0 ≤ ∏ j, A j := Finset.prod_nonneg fun j _ => hA j
  have h3 : faceConst3 2 = 3 := by norm_num [faceConst3]
  have hW : ∀ c ∈ Lu, ∀ d ∈ Lv,
      (∏ j, A j) * bsq (Li 0) (Li 1) c d ≤ faceSum Li (fun _ _ => 1) E c d := by
    intro c hc d hd
    have := faceSum_ge_bare Lu Lv Li E hE0 A hA hE hc hd
    rw [faceSum_two Li (fun _ => neP)] at this
    exact this
  by_cases hall : ∀ c ∈ Lu, ∀ d ∈ Lv, c ≠ d → 3 ≤ bsq (Li 0) (Li 1) c d
  · refine Mx.of_dom cone1 (by rw [h3]; positivity) fun c hc d hd hcd => ?_
    rw [h3]
    calc 3 * ∏ j, A j = (∏ j, A j) * 3 := mul_comm _ _
      _ ≤ (∏ j, A j) * bsq (Li 0) (Li 1) c d := mul_le_mul_of_nonneg_left (hall c hc d hd hcd) hP0
      _ ≤ _ := hW c hc d hd
  · push Not at hall
    obtain ⟨a, -, b, -, hab, hlt⟩ := hall
    rw [h3]
    refine mx1_of_low (le_refl 3) hP0 (a := a) (b := b) fun c hc d hd hcd => ?_
    have := bsq_low (hLi 0) (hLi 1) hab hlt hcd
    calc (∏ j, A j) * (3 - 1 + (if c ≠ a then 1 else 0) + (if d ≠ b then 1 else 0))
        = (∏ j, A j) * (2 + (if c ≠ a then 1 else 0) + (if d ≠ b then 1 else 0)) := by ring
      _ ≤ (∏ j, A j) * bsq (Li 0) (Li 1) c d := mul_le_mul_of_nonneg_left this hP0
      _ ≤ _ := hW c hc d hd

/-- **A bare even face of length at least six is in the one-mark class.** -/
theorem mx1_even_long {m : ℕ} (hm : Even m) (hm4 : 4 ≤ m) (Lu Lv : Finset ℕ)
    (Li : Fin m → Finset ℕ) (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 ≤ A j)
    (hE : ∀ j, Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Mx P1 Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  have hP0 : 0 ≤ ∏ j, A j := Finset.prod_nonneg fun j _ => hA j
  have hcount : ∀ c ∈ Lu, ∀ d ∈ Lv, (∏ j, A j) * psum (List.ofFn Li ++ [Lv]) (nes (m + 1)) c d
      ≤ faceSum Li (fun _ _ => 1) E c d := fun c hc d hd => by
    have h1 := faceSum_ge_bare Lu Lv Li E hE0 A hA hE hc hd
    have h2 : faceSum Li (fun _ _ => 1) (fun _ => neP) c d
        = psum (List.ofFn Li ++ [Lv]) (nes (m + 1)) c d := by
      rw [faceSum_eq_psum Li Lv _ c d hd, List.ofFn_const]
      rfl
    rwa [h2] at h1
  have hcard : ∀ L ∈ List.ofFn Li, L.card = 3 := fun L hL => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hL
    exact hLi i
  obtain ⟨ψ, hψ, hψm⟩ := exists_enum hLv
  obtain ⟨φ, δs, hφ, hφm, hlen, hle, hkeep⟩ :=
    psum_aligned (List.ofFn Li) Lv ψ hcard hψ hψm Lu hLu
  rw [List.length_ofFn] at hlen hle
  have hodd : Odd δs.length := by
    rw [hlen]; obtain ⟨k, hk⟩ := hm; exact ⟨k, by omega⟩
  have hα : faceConst3 m = (dN (m + 1) : ℝ) := faceConst3_eq_dN m
  have hprop : ∀ i l, φ i ≠ ψ l → (i ≠ l ∨ ∃ δ ∈ δs, δ i = true) := fun i l hne => by
    by_cases hil : i = l
    · subst hil
      right
      by_contra hc
      push Not at hc
      exact hne (hkeep i fun δ hδ => by simpa using hc δ hδ)
    · exact Or.inl hil
  have hα3 : (3 : ℝ) ≤ faceConst3 m := by
    obtain ⟨k, hk⟩ := hm
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk, show k' + 1 + (k' + 1) = 2 * k' + 2 by ring]
    exact faceConst3_even_ge_three k'
  rcases amat_long δs hodd (by omega) with hall | ⟨x, hx⟩
  · refine Mx.of_dom cone1 (by positivity) fun c hc d hd hcd => ?_
    obtain ⟨i, rfl⟩ := enum_surj hLu hφ hφm hc
    obtain ⟨l, rfl⟩ := enum_surj hLv hψ hψm hd
    have h1 : (dN (m + 1) : ℝ) ≤ amat δs i l := by
      have := hall i l (hprop i l hcd)
      rw [hlen] at this
      exact_mod_cast this
    calc faceConst3 m * ∏ j, A j = (∏ j, A j) * dN (m + 1) := by rw [hα, mul_comm]
      _ ≤ (∏ j, A j) * psum (List.ofFn Li ++ [Lv]) (nes (m + 1)) (φ i) (ψ l) :=
          mul_le_mul_of_nonneg_left (h1.trans (hle i l)) hP0
      _ ≤ _ := hcount _ hc _ hd
  · refine mx1_of_low hα3 hP0 (a := φ x) (b := ψ x) fun c hc d hd hcd => ?_
    obtain ⟨i, rfl⟩ := enum_surj hLu hφ hφm hc
    obtain ⟨l, rfl⟩ := enum_surj hLv hψ hψm hd
    have hpar : dN (m + 1) = sN (m + 1) + 1 := by
      have := (sN_dN_parity (m + 1)).2 (by rw [← hlen]; exact hodd)
      exact this
    have h1 := hx i l (hprop i l hcd)
    rw [hlen] at h1
    have e1 : (if φ i ≠ φ x then (1 : ℝ) else 0) = if i ≠ x then 1 else 0 := by
      by_cases h : i = x
      · simp [h]
      · have : φ i ≠ φ x := fun e => h (hφ e)
        simp [h, this]
    have e2 : (if ψ l ≠ ψ x then (1 : ℝ) else 0) = if l ≠ x then 1 else 0 := by
      by_cases h : l = x
      · simp [h]
      · have : ψ l ≠ ψ x := fun e => h (hψ e)
        simp [h, this]
    have h2 : faceConst3 m - 1 + (if i ≠ x then (1 : ℝ) else 0) + (if l ≠ x then 1 else 0)
        ≤ amat δs i l := by
      rw [hα]
      have : ((dN (m + 1) : ℕ) : ℝ) = (sN (m + 1) : ℝ) + 1 := by exact_mod_cast hpar
      rw [this]
      have h1' : ((sN (m + 1) + (if i ≠ x then 1 else 0) + (if l ≠ x then 1 else 0) : ℕ) : ℝ)
          ≤ amat δs i l := by exact_mod_cast h1
      push_cast at h1'
      convert h1' using 2; split_ifs <;> simp
    rw [e1, e2]
    calc (∏ j, A j) * (faceConst3 m - 1 + (if i ≠ x then 1 else 0) + (if l ≠ x then 1 else 0))
        ≤ (∏ j, A j) * psum (List.ofFn Li ++ [Lv]) (nes (m + 1)) (φ i) (ψ l) :=
          mul_le_mul_of_nonneg_left (h2.trans (hle i l)) hP0
      _ ≤ _ := hcount _ hc _ hd

/-- **Every bare even face is in the one-mark class**, with its ordinary constant. -/
theorem mx1_even_bare {m : ℕ} (hm : Even m) (hm2 : 2 ≤ m) (Lu Lv : Finset ℕ)
    (Li : Fin m → Finset ℕ) (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 ≤ A j)
    (hE : ∀ j, Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Mx P1 Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  rcases Nat.lt_or_ge m 4 with h | h
  · obtain rfl : m = 2 := by obtain ⟨k, hk⟩ := hm; omega
    exact mx1_square Lu Lv Li hLi E hE0 A hA hE
  · exact mx1_even_long hm h Lu Lv Li hLu hLv hLi E hE0 A hA hE

/-! ### Faces with one loaded path edge -/

section OneLoaded

variable {m : ℕ} {Lu Lv : Finset ℕ} {Li : Fin m → Finset ℕ} {E : Fin (m + 1) → ℕ → ℕ → ℝ}
  {A : Fin (m + 1) → ℝ} {j₀ : Fin (m + 1)}

/-- The floor through a face with one loaded edge. -/
theorem floor_one (hLi : ∀ j, (Li j).card = 3) (hE0 : ∀ j c d, 0 ≤ E j c d) (hA : ∀ j, 0 < A j)
    {l : ℝ} (hl : 0 ≤ l)
    (hF : Dominant (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) (E j₀) (l * A j₀))
    (hD : ∀ j, j ≠ j₀ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Dominant Lu Lv (faceSum Li (fun _ _ => 1) E) (oddB m * (l * ∏ j, A j)) := by
  have h := dom_face_bare Lu Lv Li hLi E hE0 (fun j => if j = j₀ then l * A j else A j)
    (fun j => by split_ifs <;> [exact mul_nonneg hl (hA j).le; exact (hA j).le]) fun j => by
      by_cases hj : j = j₀
      · subst hj; simpa using hF
      · simpa [hj] using hD j hj
  rwa [prod_ite_scale] at h

/-- The ball through a face with one loaded edge carrying a gain `g`. -/
theorem ball_one (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (hE0 : ∀ j c d, 0 ≤ E j c d) (hA : ∀ j, 0 < A j) {g : ℝ} (hg : 0 < g)
    (hB : InBall (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) (E j₀) (A j₀ * g))
    (hD : ∀ j, j ≠ j₀ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    InBall Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * (∏ j, A j) * g) := by
  have h := ballFaceClosed_of_bare (ballFaceBare_all m) Lu Lv Li hLu hLv hLi j₀ E hE0
    (fun j => if j = j₀ then g * A j else A j)
    (fun j => by split_ifs <;> [exact mul_pos hg (hA j); exact hA j])
    (by simpa [mul_comm] using hB) fun j hj => by simpa [hj] using hD j hj
  rw [prod_ite_scale] at h
  rwa [show faceConst3 m * (g * ∏ j, A j) = faceConst3 m * (∏ j, A j) * g by ring] at h

/-- Bijection surpluses through a face with one loaded edge: at least four sides by matching;
triangles by Hall, with `Q ≤ 2 τ`. -/
theorem bij_one (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (hE0 : ∀ j c d, 0 ≤ E j c d) (hA : ∀ j, 0 < A j) (hm1 : 1 ≤ m) {Q τ l : ℝ} (hQ : 0 < Q)
    (hl : 0 < l) (hQτ : m = 1 → Q ≤ 2 * τ)
    (hF : Dominant (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) (E j₀) (l * A j₀))
    (hB : BijGe (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) (E j₀) (A j₀) Q)
    (hT : TB (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) (E j₀) (A j₀) τ)
    (hD : ∀ j, j ≠ j₀ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    BijGe Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) Q := by
  have hpos : ∀ j, ∀ c ∈ pathList Lu Lv Li j.castSucc, ∀ d ∈ pathList Lu Lv Li j.succ, c ≠ d →
      0 < E j c d := fun j c hc d hd hcd => by
    by_cases hj : j = j₀
    · subst hj; exact lt_of_lt_of_le (mul_pos hl (hA _)) (hF c hc d hd hcd)
    · exact lt_of_lt_of_le (hA j) (hD j hj c hc d hd hcd)
  have hBj : ∀ j, BijGe (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)
      (if j = j₀ then Q else 1) := fun j => by
    by_cases hj : j = j₀
    · subst hj; simpa using hB
    · simpa [hj] using (hD j hj).bijGe (hA j).le
  rcases Nat.lt_or_ge m 2 with h2 | h2
  · obtain rfl : m = 1 := by omega
    have key := bijGe_tri hLu hLv hLi E hE0 A (fun j => if j = j₀ then Q else 1)
      (fun j => if j = j₀ then τ else 1) hA (fun j => by split_ifs <;> norm_num [hQ]) hpos hBj
      (fun j => by
        by_cases hj : j = j₀
        · subst hj; simpa using hT
        · simpa [hj] using (hD j hj).tb (hA j).le)
      (by
        have := hQτ rfl
        fin_cases j₀ <;> simp <;> linarith)
    rw [prod_ite_one] at key
    rwa [faceConst3_one, one_mul]
  · have key := bijGe_face h2 Lu Lv Li hLu hLv hLi E hE0 A (fun j => if j = j₀ then Q else 1) hA
      (fun j => by split_ifs <;> norm_num [hQ]) hpos hBj
    rwa [prod_ite_one] at key

/-- **The one-mark tables pass through odd faces with one loaded edge.** -/
theorem p1_odd (hm : Odd m) (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (hE0 : ∀ j c d, 0 ≤ E j c d) (hA : ∀ j, 0 < A j)
    (hP : P1 (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) (E j₀) (A j₀))
    (hD : ∀ j, j ≠ j₀ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    P1 Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  obtain ⟨hF, hB, hT, hBall, hH⟩ := hP
  have hα : oddB m = faceConst3 m := by
    have := oddB_div_odd hm
    rwa [div_eq_one_iff_eq (faceConst3_pos m).ne'] at this
  refine ⟨?_, ?_, ?_, ?_, hullC_transport m hm Lu Lv Li hLv hLi j₀ E hE0 A hA hH hD⟩
  · have := floor_one hLi hE0 hA (by norm_num) hF hD
    rwa [hα, show faceConst3 m * (2 / 3 * ∏ j, A j) = 2 / 3 * (faceConst3 m * ∏ j, A j) by ring]
      at this
  · exact bij_one hLu hLv hLi hE0 hA hm.pos (by norm_num) (by norm_num : (0 : ℝ) < 2 / 3)
      (fun _ => by norm_num) hF hB hT hD
  · have := tb_transport m Lu Lv Li hLv hLi j₀ E hE0 A hA hT hD
    rwa [faceConst3_odd_dd hm, one_pow, mul_one] at this
  · exact ball_one hLu hLv hLi hE0 hA (by norm_num) hBall hD

end OneLoaded

/-! ### The face rule -/

/-- **An odd face with one side in the one-mark class and greedy other sides.** -/
theorem mx1_odd {m : ℕ} (hm : Odd m) (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ)
    (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3) (j₀ : Fin (m + 1))
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 < A j)
    (hK : Mx P1 (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) (E j₀) (A j₀))
    (hD : ∀ j, j ≠ j₀ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Mx P1 Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  have hE : ∀ j, Mx P1 (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j) :=
    fun j => by
      by_cases hj : j = j₀
      · subst hj; exact hK
      · exact Mx.of_dom cone1 (hA j).le (hD j hj)
  obtain ⟨u, v, Y, hu, hv, huv, hY0, hY, hEY, hDv⟩ :=
    mx_data (Pc := fun _ => P1) (fun _ => cone1) hA hE (fun j => j ≠ j₀) hD
  refine mx_expand cone1 Lu Lv Li E hE0 A hA hu hv huv hY0 hEY fun ρ hρ => ?_
  have h0 : ∀ j, j ≠ j₀ → ρ j = 0 := term_D hDv hρ
  have hG0 := gT_nonneg hu hY0
  have hdom : ∀ j, j ≠ j₀ → Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
      (gT u Y j (ρ j)) (wT u v j (ρ j)) := fun j hj => gT_dom _ _ j (h0 j hj)
  by_cases hr : ρ j₀ = 0
  · refine Mx.of_dom cone1 (mul_pos (faceConst3_pos m) (Finset.prod_pos fun j _ => hρ j)).le
      (domFaceClosed_odd m hm Lu Lv Li hLi _
      (fun j c d => hG0 j (ρ j) c d) _ hρ fun j => ?_)
    by_cases hj : j = j₀
    · subst hj; exact gT_dom _ _ _ hr
    · exact hdom j hj
  · exact Mx.of_P (mul_pos (faceConst3_pos m) (Finset.prod_pos fun j _ => hρ j)).le (faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one)
      (fun j c d => hG0 j (ρ j) c d)) (p1_odd hm hLu hLv hLi (fun j c d => hG0 j (ρ j) c d) hρ
        (gT_P cone1 j₀ hr (hY0 j₀) (hY j₀)) hdom)

end Outerplanar
