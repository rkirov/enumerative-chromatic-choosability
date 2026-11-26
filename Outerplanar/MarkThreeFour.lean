/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.MarkSquare

/-!
# The three- and four-mark classes, and the face rule through four marks

Research note `ai_research_notes/OUTERPLANAR_ELEVEN_AND_CENTRAL_SQUARE_2026-11-23.md`, "Three
marks" and "At most four marks give `B`": *every branch with at most three marks dominates a
mixture of `1` and `AB`*; *each nonconstant alternative of a four-mark branch lies simultaneously in
`B` and `AH`* (`H` the unit matched-six product bound, `A = 17/16`).

* `P4 S T Y v` — the ball with constant `v` and the hexagon bound with `v · 17/16`; `cone4`;
  `p3_p4`. The four-mark class is **`K4 = Mx P4`**; the three-mark class is `BMix = Mx P3`.
* `mx4_odd` — an odd face with all sides in `K4` is in `K4` (ball and hexagon closure of odd faces).
* `p4_cap` — an even face whose path tables have bijection surpluses with product at least `34/27`
  and floors with product at least `8/27` is in `P4`: the cap `(34/27)^191 (16/81)^27 ≥ 1` gives
  the ball, and `34/27 ≥ (17/16)³` the hexagon gain.
* `mx4_even` — an even face whose sides carry at most three marks in all is in `K4` (`2 + 1`,
  `1 + 1 + 1`, one-load closure from three marks).
* **`Kc k`** — the class of a branch with `k ≤ 4` marks (`Kc 0` greedy, then `K1`, `K2`, `BMix`,
  `K4`); `Kc_mono`, `Kc_lift`, `Kc_swap`, `Kc_mul`.
* **`markRule_sound`** — *a face whose path edges carry branches of `τ j` marks is in `Kc k` as
  soon as `k ≤ 4` is at least the number of marks of the face and its sides*;
  `markVertex_sound`, `mark_glue` — products at cut vertices and the glue of two sides.
* `markSys`, **`ecc_three_of_markBuiltW`** — the class system, and the graph theorem for graphs
  built under these rules.

The theorem of the note is due to another AI session of this repository's collaboration; audited
and formalized by Claude.
-/

namespace Outerplanar

open Finset

/-! ### The four-mark class -/

/-- The tables of the four-mark class: the ball with `v`, the hexagon bound with `v · 17/16`. -/
def P4 (S T : Finset ℕ) (Y : ℕ → ℕ → ℝ) (v : ℝ) : Prop :=
  InBall S T Y v ∧ Hex S T Y (v * (17 / 16))

theorem cone4 : ConeP P4 where
  zero S T := ⟨InBall.zero fun _ _ => le_rfl, by
    rw [zero_mul]; exact Dominant.hex (fun _ _ _ _ _ => le_rfl) le_rfl⟩
  add := by
    intro S T Y Y' v v' hv hv' h0 h0' h h'
    refine ⟨InBall.add hv hv' h0 h0' h.1 h'.1, ?_⟩
    have := Hex.add (by positivity) (by positivity) h0 h0' h.2 h'.2
    rwa [show v * (17 / 16) + v' * (17 / 16) = (v + v') * (17 / 16) by ring] at this
  smul := by
    intro S T Y v l hl hv h0 h
    refine ⟨InBall.smul hl hv h.1, ?_⟩
    have := Hex.smul hl (by positivity) h.2
    rwa [show l * (v * (17 / 16)) = l * v * (17 / 16) by ring] at this
  mono := fun h0 hle h => ⟨h.1.mono h0 hle, h.2.mono h0 hle⟩
  weaken := fun hv' hle _ h => ⟨h.1.weaken hv' hle, h.2.weaken (by positivity) (by linarith)⟩

theorem p3_p4 {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} (hv : 0 ≤ v) (h0 : ∀ c d, 0 ≤ Y c d)
    (h : P3 S T Y v) : P4 S T Y v :=
  ⟨h.weaken hv (by linarith), fun _ _ hm hpq => h.hex (by positivity) h0 hm hpq⟩

theorem p4_swap {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} (h : P4 S T Y v) :
    P4 T S (fun d c => Y c d) v := ⟨h.1.swap, h.2.swap'⟩

theorem p4_lift {S T U : Finset ℕ} (hS : S.card = 3) (hT : T.card = 3) (hU : U.card = 3)
    {Y : ℕ → ℕ → ℝ} {v : ℝ} (hv : 0 ≤ v) (h0 : ∀ c d, 0 ≤ Y c d) (h : P4 S T Y v) :
    P4 S U (fun c _ => liftV T Y c) (2 * v) := by
  refine ⟨lift_ball hS hT hU h0 hv h.1, ?_⟩
  have := lift_hex (U := U) hS hT h0 (by positivity) h.2
  rwa [show 2 * (v * (17 / 16)) = 2 * v * (17 / 16) by ring] at this

theorem p44_p4 {S T : Finset ℕ} {Y Y' : ℕ → ℕ → ℝ} {v v' : ℝ} (hv : 0 ≤ v) (hv' : 0 ≤ v')
    (h : P4 S T Y v) (h' : P4 S T Y' v') : P4 S T (fun c d => Y c d * Y' c d) (v * v') := by
  refine ⟨h.1.mul hv hv' h'.1, ?_⟩
  have := h.2.mul (by positivity) (by positivity) h'.2
  exact this.weaken (by positivity) (by nlinarith [mul_nonneg hv hv'])

/-- The four-mark class is in the ball class. -/
theorem Mx.inBall4 {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {N : ℝ} (hN : 0 ≤ N) (h : Mx P4 S T W N) :
    InBall S T W N := by
  obtain ⟨u, v, Y, hu, hv, hNuv, hY0, hY, hW⟩ := h
  have h1 : InBall S T (fun c d => u * (if c ≠ d then 1 else 0)) (u * 1) :=
    InBall.smul hu zero_le_one (inBall_ne S T)
  have h2 := InBall.add (by positivity) hv
    (fun c d => mul_nonneg hu (by split_ifs <;> norm_num)) hY0 h1 hY.1
  refine (h2.mono (fun c d => add_nonneg (mul_nonneg hu (by split_ifs <;> norm_num)) (hY0 c d))
    fun c hc d hd hcd => ?_).weaken hN (by nlinarith)
  simpa [hcd] using hW c hc d hd hcd

/-! ### Odd faces -/

/-- **An odd face with all sides in the four-mark class is in the four-mark class.** -/
theorem mx4_odd {m : ℕ} (hm : Odd m) (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ)
    (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 < A j)
    (hE : ∀ j, Mx P4 (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Mx P4 Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  obtain ⟨u, v, Y, hu, hv, huv, hY0, hY, hEY, -⟩ :=
    mx_data (Pc := fun _ => P4) (fun _ => cone4) hA hE (fun _ => False) fun _ h => h.elim
  refine mx_expand cone4 Lu Lv Li E hE0 A hA hu hv huv hY0 hEY fun ρ hρ => ?_
  have hG0 := gT_nonneg hu hY0
  have hG0' : ∀ j c d, 0 ≤ gT u Y j (ρ j) c d := fun j c d => hG0 j (ρ j) c d
  have hFn := faceSum_nonneg Li (fun _ _ => 1) _ (fun _ _ _ => zero_le_one) hG0'
  have hw := wT_prod_pos hρ
  by_cases hall : ∀ j, ρ j = 0
  · exact Mx.of_dom cone4 hw (domFaceClosed_odd m hm Lu Lv Li hLi _ hG0' _ hρ fun j =>
      gT_dom _ _ j (hall j))
  push Not at hall
  obtain ⟨j₀, hj₀⟩ := hall
  have hP : ∀ j, ρ j ≠ 0 → P4 (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
      (gT u Y j (ρ j)) (wT u v j (ρ j)) := fun j hj => gT_P cone4 j hj (hY0 j) (hY j)
  have hB : ∀ j, InBall (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
      (gT u Y j (ρ j)) (wT u v j (ρ j)) := fun j => by
    by_cases hj : ρ j = 0
    · exact (gT_dom _ _ j hj).inBall (hρ j).le
    · exact (hP j hj).1
  set H : Fin (m + 1) → ℝ := fun j => if j = j₀ then 17 / 16 * wT u v j (ρ j) else wT u v j (ρ j)
    with hH
  have hHpos : ∀ j, 0 < H j := fun j => by
    simp only [hH]; split_ifs
    · exact mul_pos (by norm_num) (hρ j)
    · exact hρ j
  have hX : ∀ j, Hex (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
      (gT u Y j (ρ j)) (H j) := fun j => by
    by_cases h0 : j = j₀
    · subst h0
      have := (hP j hj₀).2
      simpa [hH, mul_comm] using this
    · simp only [hH, h0, ite_false]
      by_cases hj : ρ j = 0
      · exact (gT_dom _ _ j hj).hex (hρ j).le
      · exact (hP j hj).2.weaken (hρ j).le (by linarith [hρ j])
  have hprod : ∏ j, H j = 17 / 16 * ∏ j, wT u v j (ρ j) := prod_ite_scale j₀ _ _
  refine Mx.of_P hw hFn ⟨?_, ?_⟩
  · rcases Nat.lt_or_ge m 3 with h3 | h3
    · obtain rfl : m = 1 := by obtain ⟨k, hk⟩ := hm; omega
      rw [faceConst3_one, one_mul]
      exact ballTriClosed Lu Lv Li hLu hLv hLi _ hG0' _ hρ hB
    · exact ballOddClosed m hm h3 Lu Lv Li hLu hLv hLi _ hG0' _ hρ hB
  · have key : Hex Lu Lv (faceSum Li (fun _ _ => 1) fun j => gT u Y j (ρ j))
        (faceConst3 m * ∏ j, H j) := by
      rcases Nat.lt_or_ge m 3 with h3 | h3
      · obtain rfl : m = 1 := by obtain ⟨k, hk⟩ := hm; omega
        rw [faceConst3_one, one_mul]
        exact hex_tri hLi hG0' (fun j => (hHpos j).le) hX
      · exact hexOddClosed m hm h3 Lu Lv Li hLu hLv hLi _ hG0' _ hHpos hX
    rwa [hprod, show faceConst3 m * (17 / 16 * ∏ j, wT u v j (ρ j))
      = faceConst3 m * (∏ j, wT u v j (ρ j)) * (17 / 16) by ring] at key

/-! ### Even faces -/

/-- **The cap at an even face.** -/
theorem p4_cap {m : ℕ} (hm : Even m) (hm2 : 2 ≤ m) (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ)
    (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A l Q : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 < A j) (hl : ∀ j, 0 < l j) (hQ : ∀ j, 0 < Q j)
    (hF : ∀ j, Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j)
      (l j * A j))
    (hB : ∀ j, BijGe (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j) (Q j))
    (hQ' : 34 / 27 ≤ ∏ j, Q j) (hl' : 8 / 27 ≤ ∏ j, l j) :
    P4 Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  have hαpos := faceConst3_pos m
  have hP0 : 0 < ∏ j, A j := Finset.prod_pos fun j _ => hA j
  set N := faceConst3 m * ∏ j, A j with hN
  have hNpos : 0 < N := mul_pos hαpos hP0
  have hα3 : (3 : ℝ) ≤ faceConst3 m := by
    obtain ⟨k, hk⟩ := hm
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk, show k' + 1 + (k' + 1) = 2 * k' + 2 by ring]
    exact faceConst3_even_ge_three k'
  have hoddB : oddB m = faceConst3 m - 1 := by
    obtain ⟨k, hk⟩ := hm
    rw [hk, ← two_mul, oddB_even]
  -- floor `16/81`
  have hfl : Dominant Lu Lv (faceSum Li (fun _ _ => 1) E) (16 / 81 * N) := by
    have h := dom_face_bare Lu Lv Li hLi E hE0 (fun j => l j * A j)
      (fun j => (mul_pos (hl j) (hA j)).le) hF
    rw [Finset.prod_mul_distrib, hoddB] at h
    refine h.le ?_
    rw [hN]
    have : 0 < ∏ j, l j := Finset.prod_pos fun j _ => hl j
    nlinarith [mul_le_mul_of_nonneg_right hl' hP0.le]
  -- bijections
  have hpos : ∀ j, ∀ c ∈ pathList Lu Lv Li j.castSucc, ∀ d ∈ pathList Lu Lv Li j.succ, c ≠ d →
      0 < E j c d := fun j c hc d hd hcd =>
    lt_of_lt_of_le (mul_pos (hl j) (hA j)) (hF j c hc d hd hcd)
  have hbij := bijGe_face hm2 Lu Lv Li hLu hLv hLi E hE0 A Q hA hQ hpos hB
  refine ⟨cap_ball (l := 16 / 81) (Q := 34 / 27) hNpos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one) hE0) hfl
    (hbij.weakenQ hNpos.le hQ'), ?_⟩
  have := (hbij.weakenQ (Q' := (17 / 16) ^ 3) hNpos.le (le_trans (by norm_num) hQ')).hex
    (by norm_num) hNpos.le (faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one) hE0)
  exact this

/-- The tables of a side with `k` marks, as used at an even face below four marks. -/
def Pk : ℕ → Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop
  | 0 => P1
  | 1 => P1
  | 2 => P2
  | _ => P3

theorem conePk : ∀ k, ConeP (Pk k)
  | 0 => cone1
  | 1 => cone1
  | 2 => cone2
  | _ + 3 => cone3

theorem Pk_p3 : ∀ (k : ℕ) {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ}, Pk k S T Y v → P3 S T Y v
  | 0, _, _, _, _, h => p1_p3 h
  | 1, _, _, _, _, h => p1_p3 h
  | 2, _, _, _, _, h => p2_p3 h
  | _ + 3, _, _, _, _, h => h

/-- The class of a branch with `k` marks: greedy, `K1`, `K2`, `BMix`, `K4`. -/
def Kc : ℕ → Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop
  | 0 => Dominant
  | 1 => Mx P1
  | 2 => Mx P2
  | 3 => Mx P3
  | _ => Mx P4

section Kc

variable {S T U : Finset ℕ} {W W' : ℕ → ℕ → ℝ} {N N' : ℝ}

theorem Kc_succ (hN : 0 ≤ N) : ∀ k, Kc k S T W N → Kc (k + 1) S T W N
  | 0, h => Mx.of_dom cone1 hN h
  | 1, h => Mx.imp (fun hv _ h => p1_p2 hv h) h
  | 2, h => Mx.imp (fun _ _ h => p2_p3 h) h
  | 3, h => Mx.imp (fun hv h0 h => p3_p4 hv h0 h) h
  | _ + 4, h => h

theorem Kc_mono (hN : 0 ≤ N) {a b : ℕ} (hab : a ≤ b) (h : Kc a S T W N) : Kc b S T W N := by
  induction b, hab using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact Kc_succ hN n ih

theorem Kc_mx4 (hN : 0 ≤ N) (k : ℕ) (h : Kc k S T W N) : Mx P4 S T W N :=
  Kc_mono (b := k + 4) hN (Nat.le_add_right k 4) h

theorem Kc_bmix (hN : 0 ≤ N) (k : ℕ) (hk : k ≤ 3) (h : Kc k S T W N) : BMix S T W N := by
  interval_cases k
  · exact (bmix_iff _ _ _ _).mpr (Mx.of_dom cone3 hN h)
  · exact (bmix_iff _ _ _ _).mpr (Mx.imp (P := P1) (P' := P3) (fun _ _ h => p1_p3 h) h)
  · exact (bmix_iff _ _ _ _).mpr (Mx.imp (P := P2) (P' := P3) (fun _ _ h => p2_p3 h) h)
  · exact (bmix_iff _ _ _ _).mpr h

/-- A side with `k ≥ 1` marks, below four, in the mixture class of its tables `Pk k`. -/
theorem Kc_pk (hN : 0 ≤ N) (k : ℕ) (hk : k ≤ 3) (h : Kc k S T W N) :
    Mx (Pk k) S T W N := by
  interval_cases k
  · exact Mx.of_dom cone1 hN h
  · exact h
  · exact h
  · exact h

theorem Kc_swap : ∀ k, Kc k S T W N → Kc k T S (fun d c => W c d) N
  | 0, h => Dominant.swap h
  | 1, h => Mx.swap p1_swap h
  | 2, h => Mx.swap p2_swap h
  | 3, h => Mx.swap (fun h => InBall.swap h) h
  | _ + 4, h => Mx.swap p4_swap h

theorem Kc_lift (hS : S.card = 3) (hT : T.card = 3) (hU : U.card = 3) (hN : 0 ≤ N) :
    ∀ k, Kc k S T W N → Kc k S U (fun c _ => liftV T W c) (2 * N)
  | 0, h => lift_dom hN hT h
  | 1, h => Mx.lift (fun hv h0 h => p1_lift hS hT hU hv h0 h) hT h
  | 2, h => Mx.lift (fun hv h0 h => p2_lift hS hT hU hv h0 h) hT h
  | 3, h => Mx.lift (fun hv h0 h => by
      have := lift_ball (U := U) hS hT hU h0 (by positivity) h
      unfold P3
      rwa [show 2 * (_ * (17 / 16 : ℝ)) = 2 * _ * (17 / 16) by ring] at this) hT h
  | _ + 4, h => Mx.lift (fun hv h0 h => p4_lift hS hT hU hv h0 h) hT h

theorem Kc_mono_table (hle : ∀ c ∈ S, ∀ d ∈ T, c ≠ d → W c d ≤ W' c d) :
    ∀ k, Kc k S T W N → Kc k S T W' N
  | 0, h => Dominant.mono h hle
  | 1, h => Mx.mono h hle
  | 2, h => Mx.mono h hle
  | 3, h => Mx.mono h hle
  | _ + 4, h => Mx.mono h hle

theorem Kc_mul_dom (hN : 0 ≤ N) (hN' : 0 ≤ N') (hW0 : ∀ c d, 0 ≤ W c d)
    (hd : Dominant S T W' N') : ∀ k, Kc k S T W N → Kc k S T (fun c d => W' c d * W c d) (N' * N)
  | 0, h => Dominant.mul hN' hN hd h
  | 1, h => Mx.mul_dom cone1 hN' hW0 hd h
  | 2, h => Mx.mul_dom cone2 hN' hW0 hd h
  | 3, h => Mx.mul_dom cone3 hN' hW0 hd h
  | _ + 4, h => Mx.mul_dom cone4 hN' hW0 hd h

theorem Kc_nonneg_mul {a b : ℕ} (hN : 0 ≤ N) (hN' : 0 ≤ N') (hW0 : ∀ c d, 0 ≤ W c d)
    (hW0' : ∀ c d, 0 ≤ W' c d) (hab : a + b ≤ 4) (h : Kc a S T W N) (h' : Kc b S T W' N') :
    Kc (a + b) S T (fun c d => W c d * W' c d) (N * N') := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [zero_add]
    exact Kc_mul_dom hN' hN hW0' h b h'
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [add_zero]
    have := Kc_mul_dom hN hN' hW0 h' a h
    exact Kc_mono_table (fun c _ d _ _ => le_of_eq (mul_comm _ _)) a
      (by rwa [mul_comm N' N] at this)
  rcases Nat.lt_or_ge (a + b) 3 with h3 | h3
  · obtain ⟨rfl, rfl⟩ : a = 1 ∧ b = 1 := by omega
    exact mx2_mul hN' h h'
  rcases Nat.lt_or_ge (a + b) 4 with h4 | h4
  · have e : a + b = 3 := by omega
    rw [e]
    exact BMix.mul hN' (Kc_bmix hN a (by omega) h) (Kc_bmix hN' b (by omega) h')
  · have e : a + b = 4 := by omega
    rw [e]
    exact Mx.mul cone4 hN' (fun _ _ h => h) (fun _ _ h => h)
      (fun hv hv' _ _ h h' => p44_p4 hv hv' h h') (Kc_mx4 hN a h) (Kc_mx4 hN' b h')

end Kc

/-! ### What the classes give -/

section Give

variable {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {N : ℝ}

/-- Every class is in the ball class with its constant (`B`). -/
theorem Kc_inBall (hN : 0 ≤ N) (k : ℕ) (h : Kc k S T W N) : InBall S T W N :=
  (Kc_mx4 hN k h).inBall4 hN

/-- Every class has the hexagon bound with its constant (`H`). -/
theorem Kc_hex (hN : 0 ≤ N) (h0 : ∀ c d, 0 ≤ W c d) (k : ℕ) (h : Kc k S T W N) : Hex S T W N :=
  fun _ _ hm hpq => (Kc_inBall hN k h).hex hN h0 hm hpq

/-- The two-mark class has bijection products at least `N³`. -/
theorem Mx.bijGe2 (hN : 0 ≤ N) (h : Mx P2 S T W N) : BijGe S T W N 1 := by
  obtain ⟨u, v, Y, hu, hv, hNuv, hY0, hY, hW⟩ := h
  have h1 : BijGe S T (fun c d => if c ≠ d then u else 0) u 1 :=
    Dominant.bijGe hu fun c _ d _ hcd => by simp [hcd]
  have h2 := BijGe.add zero_le_one hu hv (fun c d => by split_ifs <;> simp [hu]) hY0 h1
    (hY.2.1.weakenQ hv (by norm_num))
  refine (h2.mono (fun c d => add_nonneg (by split_ifs <;> simp [hu]) (hY0 c d))
    fun c hc d hd hcd => ?_).weaken zero_le_one hN hNuv
  simpa [hcd] using hW c hc d hd hcd

/-- **Branches with at most two marks have the matching bound** (`M`, the rank-one bound). -/
theorem Kc_hasPot (hS : S.card = 3) (hT : T.card = 3) (hN : 0 < N) (k : ℕ) (hk : k ≤ 2)
    (h : Kc k S T W N) : HasPot S T W N := by
  have h2 : Mx P2 S T W N := Kc_mono hN.le hk h
  have hfl : Dominant S T W (4 / 9 * N) := Mx.floor (by norm_num) (by norm_num) (fun h => h.1) h2
  have hpos : ∀ c ∈ S, ∀ d ∈ T, c ≠ d → 0 < W c d := fun c hc d hd hcd =>
    lt_of_lt_of_le (by positivity) (hfl c hc d hd hcd)
  have := BijGe.hasPot hS hT hN one_pos hpos (h2.bijGe2 hN.le)
  rwa [Real.one_rpow, mul_one] at this

end Give

/-- **An even face whose sides carry at most three marks in all is in the four-mark class.** -/
theorem mx4_even {m : ℕ} (hm : Even m) (hm2 : 2 ≤ m) (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ)
    (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 < A j) (k : Fin (m + 1) → ℕ) (hk : ∑ j, k j ≤ 3)
    (hE : ∀ j, Kc (k j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Mx P4 Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  classical
  have hk1 : ∀ j, k j ≤ 3 := fun j =>
    le_trans (Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (mem_univ j)) hk
  have hE' : ∀ j, Mx (Pk (k j)) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j)
      (A j) := fun j => Kc_pk (hA j).le (k j) (hk1 j) (hE j)
  obtain ⟨u, v, Y, hu, hv, huv, hY0, hY, hEY, hDv⟩ :=
    mx_data (Pc := fun j => Pk (k j)) (fun j => conePk (k j)) hA hE' (fun j => k j = 0)
      fun j hj => by have := hE j; rw [hj] at this; exact this
  refine mx_expand cone4 Lu Lv Li E hE0 A hA hu hv huv hY0 hEY fun ρ hρ => ?_
  have hG0 := gT_nonneg hu hY0
  have hG0' : ∀ j c d, 0 ≤ gT u Y j (ρ j) c d := fun j c d => hG0 j (ρ j) c d
  have hFn := faceSum_nonneg Li (fun _ _ => 1) _ (fun _ _ _ => zero_le_one) hG0'
  have hw := wT_prod_pos hρ
  have hact : ∀ j, ρ j ≠ 0 → k j ≠ 0 := fun j hj hk0 => hj (term_D hDv hρ j hk0)
  have hP : ∀ j, ρ j ≠ 0 → Pk (k j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
      (gT u Y j (ρ j)) (wT u v j (ρ j)) := fun j hj => gT_P (conePk (k j)) j hj (hY0 j) (hY j)
  set s := univ.filter fun j => ρ j ≠ 0 with hs
  rcases Nat.lt_or_ge s.card 1 with h0 | h1
  · -- a bare face
    have hall : ∀ j, ρ j = 0 := fun j => by
      by_contra h
      have : j ∈ s := mem_filter.mpr ⟨mem_univ j, h⟩
      have := card_pos.mpr ⟨j, this⟩
      omega
    exact Mx.imp (fun hv h0 h => p3_p4 hv h0 (p1_p3 h)) (mx1_even_bare hm hm2 Lu Lv Li hLu hLv hLi
      _ hG0' _ (fun j => (hρ j).le) fun j => gT_dom _ _ j (hall j))
  rcases Nat.lt_or_ge s.card 2 with h2 | h2
  · -- one loaded edge
    obtain ⟨j₀, hj₀⟩ := card_eq_one.mp (show s.card = 1 by omega)
    have hρ0 : ∀ j, j ≠ j₀ → ρ j = 0 := fun j hj => by
      by_contra h
      have : j ∈ s := mem_filter.mpr ⟨mem_univ j, h⟩
      rw [hj₀] at this
      exact hj (mem_singleton.mp this)
    have hj₀m : j₀ ∈ s := by rw [hj₀]; exact mem_singleton_self j₀
    have hj₀s : ρ j₀ ≠ 0 := (mem_filter.mp hj₀m).2
    have hb := ball_one hLu hLv hLi hG0' hρ (by norm_num) (Pk_p3 (k j₀) (hP j₀ hj₀s))
      fun j hj => gT_dom _ _ j (hρ0 j hj)
    exact Mx.of_P hw hFn (p3_p4 hw hFn hb)
  · -- at least two loaded edges: all of them one- or two-mark tables
    obtain ⟨j₁, hj₁, j₂, hj₂, hj₁₂⟩ := one_lt_card.mp (show 1 < s.card by omega)
    have hsum2 : ∀ j, ρ j ≠ 0 → k j ≤ 2 := fun j hj => by
      by_contra hc
      push Not at hc
      have hj' : ∃ j', j' ≠ j ∧ ρ j' ≠ 0 := by
        by_cases e : j = j₁
        · exact ⟨j₂, fun h => hj₁₂ (e ▸ h.symm), (mem_filter.mp hj₂).2⟩
        · exact ⟨j₁, fun h => e h.symm, (mem_filter.mp hj₁).2⟩
      obtain ⟨j', hne, hj'0⟩ := hj'
      have := hact j' hj'0
      have hle : k j + k j' ≤ ∑ i, k i := by
        rw [← Finset.sum_pair (f := k) (Ne.symm hne)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.zero_le _
      omega
    set a : ℝ := 1024 / 729 * (16 / 17) with ha
    set b : ℝ := 17 / 16 * (27 / 32) with hb
    set e : Fin (m + 1) → ℕ := fun j => if ρ j = 0 then 0 else k j with he
    have hQk : ∀ j, ρ j ≠ 0 → BijGe (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
        (gT u Y j (ρ j)) (wT u v j (ρ j)) (a * b ^ (k j)) := fun j hj => by
      have hk2 := hsum2 j hj
      have hk0 := hact j hj
      have hPj := hP j hj
      rcases (show k j = 1 ∨ k j = 2 by omega) with h | h
      · rw [h] at hPj ⊢
        have e1 : a * b ^ 1 = 32 / 27 := by rw [ha, hb]; norm_num
        rw [e1]
        exact hPj.2.1
      · rw [h] at hPj ⊢
        have e1 : a * b ^ 2 = 17 / 16 := by rw [ha, hb]; norm_num
        rw [e1]
        exact hPj.2.1
    have hFk : ∀ j, ρ j ≠ 0 → Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
        (gT u Y j (ρ j)) ((2 / 3) ^ (k j) * wT u v j (ρ j)) := fun j hj => by
      have hk2 := hsum2 j hj
      have hk0 := hact j hj
      have hPj := hP j hj
      rcases (show k j = 1 ∨ k j = 2 by omega) with h | h
      · rw [h] at hPj ⊢
        simpa using hPj.1
      · rw [h] at hPj ⊢
        have := hPj.1
        rwa [show (4 / 9 : ℝ) = (2 / 3) ^ 2 by norm_num] at this
    refine Mx.of_P hw hFn (p4_cap hm hm2 Lu Lv Li hLu hLv hLi _ hG0' _
      (fun j => (2 / 3) ^ (e j)) (fun j => (if ρ j = 0 then 1 else a) * b ^ (e j)) hρ
      (fun j => by positivity) (fun j => by
        have : 0 < (if ρ j = 0 then (1 : ℝ) else a) := by split_ifs <;> norm_num [ha]
        positivity)
      (fun j => by
        by_cases hj : ρ j = 0
        · simpa [he, hj] using gT_dom (u := u) (v := v) (Y := Y) (pathList Lu Lv Li j.castSucc)
            (pathList Lu Lv Li j.succ) j hj
        · simpa [he, hj] using hFk j hj)
      (fun j => by
        by_cases hj : ρ j = 0
        · simpa [he, hj] using (gT_dom (u := u) (v := v) (Y := Y) (pathList Lu Lv Li j.castSucc)
            (pathList Lu Lv Li j.succ) j hj).bijGe (hρ j).le
        · simpa [he, hj] using hQk j hj) ?_ ?_)
    · -- the bijection surplus
      have hse : ∑ j, e j ≤ 3 := le_trans (Finset.sum_le_sum fun j _ => by
        simp only [he]; split_ifs <;> omega) hk
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_ite,
        Finset.prod_const_one, one_mul, Finset.prod_const]
      have e1 : (univ.filter fun j => ¬ ρ j = 0) = s := by rw [hs]
      rw [e1]
      have ka : a ^ 2 ≤ a ^ s.card := pow_le_pow_right₀ (by rw [ha]; norm_num) h2
      have kb : b ^ 3 ≤ b ^ (∑ j, e j) :=
        pow_le_pow_of_le_one (by rw [hb]; norm_num) (by rw [hb]; norm_num) hse
      have kab : (34 / 27 : ℝ) = a ^ 2 * b ^ 3 := by rw [ha, hb]; norm_num
      rw [kab]
      exact mul_le_mul ka kb (by positivity) (by positivity)
    · -- the floor
      have hse : ∑ j, e j ≤ 3 := le_trans (Finset.sum_le_sum fun j _ => by
        simp only [he]; split_ifs <;> omega) hk
      rw [Finset.prod_pow_eq_pow_sum]
      calc (8 / 27 : ℝ) = (2 / 3) ^ 3 := by norm_num
        _ ≤ (2 / 3) ^ (∑ j, e j) := pow_le_pow_of_le_one (by norm_num) (by norm_num) hse

/-! ### The face rule through four marks -/

theorem sum_eq_one_iff {n : ℕ} (s : Finset (Fin n)) (τ : Fin n → ℕ) (h : ∑ j ∈ s, τ j = 1) :
    ∃ j₀ ∈ s, τ j₀ = 1 ∧ ∀ j ∈ s, j ≠ j₀ → τ j = 0 := by
  classical
  obtain ⟨j₀, hj₀, hpos⟩ : ∃ j₀ ∈ s, 0 < τ j₀ := by
    by_contra hc
    push Not at hc
    have : ∑ j ∈ s, τ j = 0 := Finset.sum_eq_zero fun j hj => by have := hc j hj; omega
    omega
  have hsplit := Finset.add_sum_erase s τ hj₀
  refine ⟨j₀, hj₀, by omega, fun j hj hne => ?_⟩
  have hrest : ∑ j ∈ s.erase j₀, τ j = 0 := by omega
  exact (Finset.sum_eq_zero_iff.mp hrest) j (mem_erase.mpr ⟨hne, hj⟩)

theorem sum_eq_two_cases {n : ℕ} (τ : Fin n → ℕ) (h : ∑ j, τ j = 2) :
    (∃ j₀, τ j₀ = 2 ∧ ∀ j, j ≠ j₀ → τ j = 0) ∨
      ∃ j₁ j₂, j₁ ≠ j₂ ∧ τ j₁ = 1 ∧ τ j₂ = 1 ∧ ∀ j, j ≠ j₁ → j ≠ j₂ → τ j = 0 := by
  classical
  obtain ⟨j₀, -, hpos⟩ : ∃ j₀ ∈ (univ : Finset (Fin n)), 0 < τ j₀ := by
    by_contra hc
    push Not at hc
    have : ∑ j, τ j = 0 := Finset.sum_eq_zero fun j hj => by have := hc j hj; omega
    omega
  have hsplit := Finset.add_sum_erase univ τ (mem_univ j₀)
  rcases (show τ j₀ = 1 ∨ τ j₀ = 2 by omega) with h1 | h2
  · obtain ⟨j₁, hj₁, h1', hrest⟩ := sum_eq_one_iff (univ.erase j₀) τ (by omega)
    refine Or.inr ⟨j₀, j₁, (Finset.ne_of_mem_erase hj₁).symm, h1, h1', fun j hj0 hj1 => ?_⟩
    exact hrest j (mem_erase.mpr ⟨hj0, mem_univ j⟩) hj1
  · refine Or.inl ⟨j₀, h2, fun j hj => ?_⟩
    have hrest : ∑ j ∈ univ.erase j₀, τ j = 0 := by omega
    exact (Finset.sum_eq_zero_iff.mp hrest) j (mem_erase.mpr ⟨hj, mem_univ j⟩)

/-- **The face rule through four marks**: `k ≤ 4` is at least the number of marks of the face
(one if it is even) and of its sides. -/
def markRule (k m : ℕ) (τ : Fin (m + 1) → ℕ) : Prop :=
  1 ≤ m ∧ (if Even m then 1 else 0) + ∑ j, τ j ≤ k ∧ k ≤ 4

/-- **The face rule is sound.** -/
theorem markRule_sound {k m : ℕ} {τ : Fin (m + 1) → ℕ} (hr : markRule k m τ)
    (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ) (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d)
    (A : Fin (m + 1) → ℝ) (hA : ∀ j, 0 < A j)
    (hE : ∀ j, Kc (τ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Kc k Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  classical
  obtain ⟨hm1, hsum, hk4⟩ := hr
  have hN : 0 ≤ faceConst3 m * ∏ j, A j :=
    (mul_pos (faceConst3_pos m) (Finset.prod_pos fun j _ => hA j)).le
  have hτ : ∀ j, τ j ≤ ∑ i, τ i := fun j =>
    Finset.single_le_sum (f := τ) (fun _ _ => Nat.zero_le _) (mem_univ j)
  have hzero : ∀ j, τ j = 0 →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j) :=
    fun j h => by have := hE j; rw [h] at this; exact this
  have hbm : ∑ j, τ j ≤ 3 → ∀ j,
      BMix (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j) :=
    fun h3 j => Kc_bmix (hA j).le (τ j) ((hτ j).trans h3) (hE j)
  rcases Nat.even_or_odd m with hev | hodd
  · -- even faces
    have hm2 : 2 ≤ m := by obtain ⟨r, hr⟩ := hev; omega
    simp only [hev, ↓reduceIte] at hsum
    rcases Nat.lt_or_ge (∑ j, τ j) 1 with h0 | h1
    · have hall : ∀ j, τ j = 0 := fun j => by have := hτ j; omega
      exact Kc_mono hN (a := 1) (by omega) (mx1_even_bare hev hm2 Lu Lv Li hLu hLv hLi E hE0 A
        (fun j => (hA j).le) fun j => hzero j (hall j))
    rcases Nat.lt_or_ge (∑ j, τ j) 2 with h1' | h2
    · obtain ⟨j₀, -, h1, hrest⟩ := sum_eq_one_iff univ τ (by omega)
      have hK : Mx P1 (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) (E j₀)
          (A j₀) := by have := hE j₀; rw [h1] at this; exact this
      exact Kc_mono hN (a := 2) (by omega) (mx2_even_one Lu Lv Li E A hev hm2 hLu hLv hLi j₀ hE0 hA
        hK fun j hj => hzero j (hrest j (mem_univ j) hj))
    rcases Nat.lt_or_ge (∑ j, τ j) 3 with h2' | h3
    · -- two marks below an even face
      refine Kc_mono hN (a := 3) (by omega) ?_
      rcases Nat.lt_or_ge m 4 with hm4 | hm4
      · obtain rfl : m = 2 := by obtain ⟨r, hr⟩ := hev; omega
        rcases sum_eq_two_cases τ (by omega) with ⟨j₀, h2, hrest⟩ | ⟨j₁, j₂, h12, h1, h2, hrest⟩
        · exact bmix_face hm1 Lu Lv Li hLu hLv hLi E hE0 A hA (fun j => τ j = 0)
            (hbm (by omega)) (fun j hj => hzero j hj) fun _ j j' hj hj' => by
              by_contra hne
              rcases eq_or_ne j j₀ with rfl | h
              · exact hj' (hrest j' (Ne.symm hne))
              · exact hj (hrest j h)
        · exact mx3_square_two Lu Lv Li hLu hLv hLi E hE0 A hA j₁ j₂ h12
            (by have := hE j₁; rw [h1] at this; exact this)
            (by have := hE j₂; rw [h2] at this; exact this)
            fun j hj1 hj2 => hzero j (hrest j hj1 hj2)
      · exact bmix_face hm1 Lu Lv Li hLu hLv hLi E hE0 A hA (fun j => τ j = 0)
          (hbm (by omega)) (fun j hj => hzero j hj) fun hm2' => absurd hm2' (by omega)
    · -- three marks below an even face
      refine Kc_mono hN (a := 4) (by omega) ?_
      exact mx4_even hev hm2 Lu Lv Li hLu hLv hLi E hE0 A hA τ (by omega) hE
  · -- odd faces
    simp only [Nat.not_even_iff_odd.mpr hodd, ↓reduceIte, zero_add] at hsum
    rcases Nat.lt_or_ge (∑ j, τ j) 1 with h0 | h1
    · have hall : ∀ j, τ j = 0 := fun j => by have := hτ j; omega
      exact Kc_mono hN (a := 0) (Nat.zero_le k)
        (domFaceClosed_odd m hodd Lu Lv Li hLi E hE0 A hA fun j => hzero j (hall j))
    rcases Nat.lt_or_ge (∑ j, τ j) 2 with h1' | h2
    · obtain ⟨j₀, -, h1, hrest⟩ := sum_eq_one_iff univ τ (by omega)
      have hK : Mx P1 (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) (E j₀)
          (A j₀) := by have := hE j₀; rw [h1] at this; exact this
      exact Kc_mono hN (a := 1) (by omega) (mx1_odd hodd Lu Lv Li hLu hLv hLi j₀ E hE0 A hA hK
        fun j hj => hzero j (hrest j (mem_univ j) hj))
    rcases Nat.lt_or_ge (∑ j, τ j) 3 with h2' | h3
    · refine Kc_mono hN (a := 2) (by omega) ?_
      rcases sum_eq_two_cases τ (by omega) with ⟨j₀, h2, hrest⟩ | ⟨j₁, j₂, h12, h1, h2, hrest⟩
      · exact mx2_odd_one Lu Lv Li E A hodd hLu hLv hLi j₀ hE0 hA
          (by have := hE j₀; rw [h2] at this; exact this) fun j hj => hzero j (hrest j hj)
      · exact mx2_odd_two Lu Lv Li E A hodd hLu hLv hLi j₁ j₂ h12 hE0 hA
          (by have := hE j₁; rw [h1] at this; exact this)
          (by have := hE j₂; rw [h2] at this; exact this)
          fun j hj1 hj2 => hzero j (hrest j hj1 hj2)
    rcases Nat.lt_or_ge (∑ j, τ j) 4 with h3' | h4
    · refine Kc_mono hN (a := 3) (by omega) ?_
      exact bmix_face hm1 Lu Lv Li hLu hLv hLi E hE0 A hA (fun j => τ j = 0)
        (hbm (by omega)) (fun j hj => hzero j hj) fun hm2' => absurd hm2' (by
          obtain ⟨r, hr⟩ := hodd; omega)
    · refine Kc_mono hN (a := 4) (by omega) ?_
      exact mx4_odd hodd Lu Lv Li hLu hLv hLi E hE0 A hA fun j =>
        Kc_mx4 (hA j).le (τ j) (hE j)

/-! ### Cut vertices, the glue, the class system -/

/-- **The vertex rule**: a branch of `t₁` marks hanging at a corner of a side of `t₀` marks. -/
theorem markVertex_sound {t t₀ t₁ : ℕ} (h : t₀ + t₁ ≤ t ∧ t ≤ 4) (Lv Ly Lw : Finset ℕ)
    (hv : Lv.card = 3) (hy : Ly.card = 3) (hw : Lw.card = 3) (W X X' : ℕ → ℕ → ℝ)
    (hW : ∀ c d, 0 ≤ W c d) (hX : ∀ c d, 0 ≤ X c d) (hX' : ∀ c d, 0 ≤ X' c d) (A A₁ A₂ : ℝ)
    (hA : 0 < A) (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (h₀ : Kc t₀ Lv Ly W A) (h₁ : Kc t₁ Lv Lw X A₁)
    (h₂ : Dominant Lw Lv X' A₂) :
    Kc t Lv Ly (fun c d => W c d * ∑ e ∈ Lw, X c e * X' e c) (A * (2 * A₁ * A₂)) := by
  have hL := Kc_lift (U := Ly) hv hw hy hA₁.le t₁ h₁
  have hL' := Kc_mul_dom (W' := fun _ _ => A₂) (by positivity) hA₂.le
    (fun c _ => liftV_nonneg hX c) (fun _ _ _ _ _ => le_refl _) t₁ hL
  have hB : Kc t₁ Lv Ly (fun c _ => ∑ e ∈ Lw, X c e * X' e c) (A₂ * (2 * A₁)) :=
    Kc_mono_table (fun c hc _ _ _ => branch_ge hX hX' h₂ hc) t₁ hL'
  have hprod := Kc_nonneg_mul hA.le (by positivity) hW
    (fun c _ => Finset.sum_nonneg fun e _ => mul_nonneg (hX _ _) (hX' _ _)) (by omega) h₀ hB
  rw [show A * (2 * A₁ * A₂) = A * (A₂ * (2 * A₁)) by ring]
  exact Kc_mono (by positivity) h.1 hprod

/-- **The glue**: two sides of any classes give the count. -/
theorem mark_glue (t₁ t₂ : ℕ) (S T : Finset ℕ) (W W' : ℕ → ℕ → ℝ) (A A' : ℝ)
    (hS : S.card = 3) (hT : T.card = 3) (h0 : ∀ c d, 0 ≤ W c d) (h0' : ∀ c d, 0 ≤ W' c d)
    (hA : 0 < A) (hA' : 0 < A') (h₁ : Kc t₁ S T W A) (h₂ : Kc t₂ T S W' A') :
    6 * (A * A') ≤ ∑ d ∈ T, ∑ c ∈ S, W' d c * W c d := by
  have b₁ := (Kc_mx4 hA.le t₁ h₁).inBall4 hA.le
  have b₂ := ((Kc_mx4 hA'.le t₂ h₂).inBall4 hA'.le).swap
  have hb := b₁.mul hA.le hA'.le b₂
  have key := hb.sum_ge hS hT (by positivity) fun c d => mul_nonneg (h0 c d) (h0' d c)
  rw [Finset.sum_comm]
  refine key.trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => mul_comm _ _

/-- **The class system of the mark classes.** -/
def markSys : ClassSys where
  Tag := ℕ
  plain := 0
  cls := Kc
  of_dom := fun t _ _ _ _ hA h => Kc_mono hA (Nat.zero_le t) h
  dom_of_plain := fun _ _ _ _ h => h
  mul_dom := fun t _ _ _ _ _ _ hA hA' hW _ hd h => Kc_mul_dom hA hA' hW hd t h

theorem markSys_transposable : markSys.Transposable := fun t _ _ _ _ h => Kc_swap t h

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Every graph built by ears, pendant edges and reorientations under the mark rules is
3-ECC.** -/
theorem ecc_three_of_markBuiltW (G : SimpleGraph V) [DecidableRel G.Adj] {tg : V → V → ℕ}
    (h : TagBuiltW G markSys (fun (k m : ℕ) τ => markRule k m τ) (fun _ _ => True)
      (fun (t t₀ t₁ : ℕ) => t₀ + t₁ ≤ t ∧ t ≤ 4) univ tg) : G.ECCAt 3 :=
  ecc_three_of_tagBuiltW G (R := markSys) (fun _ _ _ hr => markRule_sound hr)
    (fun t₁ t₂ _ => mark_glue t₁ t₂) (fun _ _ _ hr => markVertex_sound hr)
    markSys_transposable h

end Outerplanar
