/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.MarkTerms

/-!
# The face rule through six marks

Research note `ai_research_notes/OUTERPLANAR_THIRTEEN_AND_GAUGE_OBSTRUCTION_2026-11-23.md`, Steps 1
and 2 (another AI session of this repository's collaboration; audited):

* **odd faces** (`term_odd`, `mx56_odd`): a term with a hexagon alternative passes the hexagon bound
  (all other tables are in `H`), every other term passes the ball (all tables are in `B`);
* **Step 1** (`mx5_even`): an even face over at most four marks is in `Kc6 5`. Terms with at most
  three active marks fall to `mx4_even`; one active side gives one-load closure; at length at least
  six the ball design gives `(16/17) A^s ≥ 1`; at a square `[B, M, M]` with the largest side as `B`
  gives `A^{4/3}` (`κq ≥ κA`, `κq² ≥ κA`);
* **Step 2** (`mx6_even`): an even face over at most five marks is in `Kc6 6`. A single five-mark
  side passes its ball part by one-load closure and its hexagon part by the two-distinguished law
  (`sqLawH` at squares, `hexEvenSix` at length at least six), with `A^{4/3}/K = D₆`; several sides
  give the ball at length at least six, and `[B, M, M]` at squares (`κq ≥ D₆` for `(4, 1)`);
* **`markRule6_sound`** — the face rule through six marks.

Formalized by Claude (milestone M3 of `ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`).
-/

namespace Outerplanar

open Finset

/-! ### The data of a face -/

/-- **The alternatives of all sides of a face.** -/
theorem face_data {n : ℕ} (τ : Fin n → ℕ) (L R : Fin n → Finset ℕ) (E : Fin n → ℕ → ℕ → ℝ)
    (A : Fin n → ℝ) (hA : ∀ j, 0 ≤ A j) (hE : ∀ j, Kc6 (τ j) (L j) (R j) (E j) (A j)) :
    ∃ (u v₁ v₂ : Fin n → ℝ) (Y₁ Y₂ : Fin n → ℕ → ℕ → ℝ), (∀ j, 0 ≤ u j) ∧ (∀ j, 0 ≤ v₁ j) ∧
      (∀ j, 0 ≤ v₂ j) ∧ (∀ j, A j ≤ u j + v₁ j + v₂ j) ∧ (∀ j c d, 0 ≤ Y₁ j c d) ∧
      (∀ j c d, 0 ≤ Y₂ j c d) ∧ (∀ j, PP1 (τ j) (L j) (R j) (Y₁ j) (v₁ j)) ∧
      (∀ j, PP2 (τ j) (L j) (R j) (Y₂ j) (v₂ j)) ∧
      ∀ j, ∀ c ∈ L j, ∀ d ∈ R j, c ≠ d → u j + Y₁ j c d + Y₂ j c d ≤ E j c d := by
  choose u v₁ v₂ Y₁ Y₂ h1 h2 h3 h4 h5 h6 h7 h8 h9 using fun j => kc6_data (hA j) (hE j)
  exact ⟨u, v₁, v₂, Y₁, Y₂, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- The marks of a side that are active in a term. -/
def actM {n : ℕ} (τ : Fin n → ℕ) (ρ : Fin n → Fin 3) (j : Fin n) : ℕ := if ρ j = 0 then 0 else τ j

section Act

variable {n : ℕ} {τ : Fin n → ℕ} {ρ : Fin n → Fin 3}

theorem actM_le (j : Fin n) : actM τ ρ j ≤ τ j := by unfold actM; split_ifs <;> omega

theorem actM_le_sum (j : Fin n) : actM τ ρ j ≤ ∑ i, actM τ ρ i :=
  Finset.single_le_sum (f := actM τ ρ) (fun _ _ => Nat.zero_le _) (mem_univ j)

theorem actM_two {j j' : Fin n} (h : j ≠ j') : actM τ ρ j + actM τ ρ j' ≤ ∑ i, actM τ ρ i := by
  rw [← Finset.sum_pair (f := actM τ ρ) h]
  exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.zero_le _

theorem sum_actM_le : ∑ i, actM τ ρ i ≤ ∑ i, τ i := Finset.sum_le_sum fun i _ => actM_le i

theorem actM_act {j : Fin n} (h : ρ j ≠ 0) : actM τ ρ j = τ j := by simp [actM, h]

theorem actM_inact {j : Fin n} (h : ρ j = 0) : actM τ ρ j = 0 := by simp [actM, h]

end Act

theorem fc_prod_nonneg {m : ℕ} {w : Fin (m + 1) → ℝ} (hw : ∀ j, 0 < w j) :
    0 ≤ faceConst3 m * ∏ j, w j :=
  (mul_pos (faceConst3_pos m) (Finset.prod_pos fun j _ => hw j)).le

theorem pt_act_ge {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} {k : ℕ} {r : Fin 3} (hv : 0 < v)
    (hr : r ≠ 0) (h : PT k r S T Y v) : 1 ≤ k := by
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 by fin_cases r <;> simp) with rfl | rfl | rfl
  · exact absurd rfl hr
  · exact pt_one_ge hv h
  · have := pt_two_ge hv h; omega

/-! ### Odd faces -/

section Odd

variable {m : ℕ} {Lu Lv : Finset ℕ} {Li : Fin m → Finset ℕ}

/-- **A term of an odd face.** -/
theorem term_odd (hm : Odd m) (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (G : Fin (m + 1) → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d) (w : Fin (m + 1) → ℝ)
    (hw : ∀ j, 0 < w j) (τ : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j))
    {κ : ℝ} (hκ : 1 ≤ κ)
    (hc2 : ∀ j, ρ j = 2 → Hex (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j * κ)) :
    Alt2 (fun S T Y v => InBall S T Y v) (fun S T Y v => Hex S T Y (v * κ)) Lu Lv
      (faceSum Li (fun _ _ => 1) G) (faceConst3 m * ∏ j, w j) := by
  have hFn := faceSum_nonneg Li (fun _ _ => 1) G (fun _ _ _ => zero_le_one) hG0
  have hN : 0 ≤ faceConst3 m * ∏ j, w j :=
    (mul_pos (faceConst3_pos m) (Finset.prod_pos fun j _ => hw j)).le
  by_cases h2 : ∃ j₀, ρ j₀ = 2
  · obtain ⟨j₀, hj₀⟩ := h2
    set H : Fin (m + 1) → ℝ := fun j => if j = j₀ then κ * w j else w j with hH
    have hHpos : ∀ j, 0 < H j := fun j => by
      simp only [hH]; split_ifs
      · exact mul_pos (by linarith) (hw j)
      · exact hw j
    have hX : ∀ j, Hex (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j) (H j) :=
      fun j => by
        by_cases h0 : j = j₀
        · subst h0
          simpa [hH, mul_comm] using hc2 j hj₀
        · simp only [hH, h0, ite_false]
          exact pt_hex (hw j) (hG0 j) (hpt j)
    have hprod : ∏ j, H j = κ * ∏ j, w j := prod_ite_scale j₀ _ _
    have key : Hex Lu Lv (faceSum Li (fun _ _ => 1) G) (faceConst3 m * ∏ j, H j) := by
      rcases Nat.lt_or_ge m 3 with h3 | h3
      · obtain rfl : m = 1 := by obtain ⟨k, hk⟩ := hm; omega
        rw [faceConst3_one, one_mul]
        exact hex_tri hLi hG0 (fun j => (hHpos j).le) hX
      · exact hexOddClosed m hm h3 Lu Lv Li hLu hLv hLi G hG0 H hHpos hX
    refine Alt2.of_right coneB hN hFn ?_
    rwa [hprod, show faceConst3 m * (κ * ∏ j, w j) = faceConst3 m * (∏ j, w j) * κ by ring]
      at key
  · push Not at h2
    have hB : ∀ j, InBall (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j) (w j) :=
      fun j => pt_ball (hw j) (hG0 j) (h2 j) (hpt j)
    refine Alt2.of_left (coneH (by linarith)) hN hFn ?_
    rcases Nat.lt_or_ge m 3 with h3 | h3
    · obtain rfl : m = 1 := by obtain ⟨k, hk⟩ := hm; omega
      rw [faceConst3_one, one_mul]
      exact ballTriClosed Lu Lv Li hLu hLv hLi G hG0 w hw hB
    · exact ballOddClosed m hm h3 Lu Lv Li hLu hLv hLi G hG0 w hw hB

/-- **An odd face whose sides carry at most `5` marks each is in `Kc6 5`; at most `6`, in
`Kc6 6`.** -/
theorem mx56_odd (hm : Odd m) (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 < A j) (k : ℕ) (hk5 : 5 ≤ k) (hk6 : k ≤ 6) (τ : Fin (m + 1) → ℕ)
    (hτ : ∀ j, τ j ≤ k)
    (hE : ∀ j, Kc6 (τ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Kc6 k Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  obtain ⟨u, v₁, v₂, Y₁, Y₂, hu, hv₁, hv₂, huv, hY₁, hY₂, hP1, hP2, hEY⟩ :=
    face_data τ _ _ E A (fun j => (hA j).le) hE
  have hpt := fun ρ : Fin (m + 1) → Fin 3 => fun j =>
    gT3_pt (u := u) (k := τ j) j (ρ j) (hY₁ j) (hY₂ j) (hP1 j) (hP2 j)
  have hG0 := gT3_nonneg hu hY₁ hY₂
  rcases (show k = 5 ∨ k = 6 by omega) with rfl | rfl
  · refine mx_expand3 cone5 Lu Lv Li E hE0 A hA hu hv₁ hv₂ huv hY₁ hY₂ hEY fun ρ hρ => ?_
    refine Mx.of_P (fc_prod_nonneg hρ) (faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one)
      fun j c d => hG0 j (ρ j) c d) ?_
    refine term_odd hm hLu hLv hLi _ (fun j c d => hG0 j (ρ j) c d) _ hρ τ ρ (hpt ρ) one_le_a5
      fun j hj => ?_
    have h := hpt ρ j
    rw [hj] at h
    have h5 : τ j = 5 := le_antisymm (hτ j) (pt_two_ge (by rw [← hj]; exact hρ j) h)
    rw [h5] at h
    have := pt_hex5 h
    rw [hj]
    exact this
  · refine mx_expand3 cone6 Lu Lv Li E hE0 A hA hu hv₁ hv₂ huv hY₁ hY₂ hEY fun ρ hρ => ?_
    refine Mx.of_P (fc_prod_nonneg hρ) (faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one)
      fun j c d => hG0 j (ρ j) c d) ?_
    exact term_odd hm hLu hLv hLi _ (fun j c d => hG0 j (ρ j) c d) _ hρ τ ρ (hpt ρ) one_le_d6
      fun j hj => by
        have h := hpt ρ j
        rw [hj] at h
        have := pt_hexH (by rw [← hj]; exact hρ j) h
        rw [hj]
        exact this

end Odd

/-! ### Even faces -/

section Even

variable {m : ℕ} {Lu Lv : Finset ℕ} {Li : Fin m → Finset ℕ}

theorem pt_kc6' {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} {k : ℕ} {r : Fin 3} (hv : 0 < v)
    (h0 : ∀ c d, 0 ≤ Y c d) (hk : r = 0 ∨ k ≤ 4) (h : PT k r S T Y v) :
    Kc6 (if r = 0 then 0 else k) S T Y v := by
  rcases hk with rfl | hk
  · exact h.1 rfl
  · exact pt_kc6 hv h0 hk h

theorem act_one {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} {k : ℕ} {r : Fin 3} (hv : 0 < v)
    (hk : k ≤ 4) (hr : r ≠ 0) (h : PT k r S T Y v) : r = 1 ∧ 1 ≤ k := by
  have hr1 : r = 1 := by
    rcases Fin.exists_fin_succ.mp ⟨r, rfl⟩ with h' | ⟨r', rfl⟩
    · exact absurd h' hr
    rcases Fin.exists_fin_succ.mp ⟨r', rfl⟩ with h' | ⟨r'', rfl⟩
    · subst h'; rfl
    · obtain rfl : r'' = 0 := Subsingleton.elim _ _
      exact absurd (pt_two_ge hv h) (by omega)
  subst hr1
  exact ⟨rfl, pt_one_ge hv h⟩

/-- The largest active side of a square carries at least a third of the active marks. -/
theorem actM_max3 (τ : Fin 3 → ℕ) (ρ : Fin 3 → Fin 3) :
    ∃ jB, (∀ j, actM τ ρ j ≤ actM τ ρ jB) ∧ ∑ i, actM τ ρ i ≤ 3 * actM τ ρ jB := by
  obtain ⟨jB, -, hjB⟩ := Finset.exists_max_image univ (actM τ ρ) univ_nonempty
  refine ⟨jB, fun j => hjB j (mem_univ j), ?_⟩
  rw [Fin.sum_univ_three]
  have := hjB 0 (mem_univ _); have := hjB 1 (mem_univ _); have := hjB 2 (mem_univ _)
  omega

/-- **The scales of the light sides of a square**: the bijection scales of the sides other than
`jB` multiply to at least `κA` if one of them is active, and to `κq` if that one is a single. -/
theorem msc_prod (τ : Fin 3 → ℕ) (ρ : Fin 3 → Fin 3) (jB j₁ : Fin 3) (h1 : j₁ ≠ jB)
    (ha : ρ j₁ ≠ 0) :
    κA ≤ ∏ j, (if j = jB then 1 else msc (τ j) (ρ j)) ∧
      (τ j₁ = 1 → κq ≤ ∏ j, (if j = jB then 1 else msc (τ j) (ρ j))) := by
  have hge : ∀ j, 1 ≤ (if j = jB then 1 else msc (τ j) (ρ j)) := fun j => by
    split_ifs
    · exact le_rfl
    · exact msc_ge _ _
  have key : (if j₁ = jB then 1 else msc (τ j₁) (ρ j₁))
      ≤ ∏ j, (if j = jB then 1 else msc (τ j) (ρ j)) := by
    rw [← Finset.mul_prod_erase univ _ (mem_univ j₁)]
    have : 1 ≤ ∏ j ∈ univ.erase j₁, (if j = jB then 1 else msc (τ j) (ρ j)) :=
      Finset.one_le_prod₀ fun j _ => hge j
    have h0 : 0 ≤ (if j₁ = jB then 1 else msc (τ j₁) (ρ j₁)) := le_trans zero_le_one (hge j₁)
    nlinarith
  simp only [h1, ite_false] at key
  exact ⟨(msc_act ha).trans key, fun h => by rw [msc_one ha h] at key; exact key⟩

/-- `[B, M, M]` at a square term: the side `jB` in `B` with scale `b`, the others in `M`. -/
theorem term_sqB (hLv : Lv.card = 3) {Li : Fin 2 → Finset ℕ} (hLi : ∀ j, (Li j).card = 3)
    (G : Fin 3 → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d) (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j)
    (τ : Fin 3 → ℕ) (ρ : Fin 3 → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j))
    (jB : Fin 3) {b : ℝ} (hb : 0 < b)
    (hB : InBall (pathList Lu Lv Li jB.castSucc) (pathList Lu Lv Li jB.succ) (G jB) (w jB * b))
    (hM : ∀ j, j ≠ jB → ρ j = 0 ∨ (ρ j = 1 ∧ τ j ≤ 2)) :
    Hex Lu Lv (faceSum Li (fun _ _ => 1) G)
      (faceConst3 2 * (∏ j, w j) * (b * ∏ j, (if j = jB then 1 else msc (τ j) (ρ j)))) := by
  set N : Fin 3 → ℝ := fun j => w j * (if j = jB then b else msc (τ j) (ρ j)) with hN
  have hNpos : ∀ j, 0 < N j := fun j => by
    simp only [hN]; split_ifs
    · exact mul_pos (hw j) hb
    · exact mul_pos (hw j) (msc_pos _ _)
  have key := sqLawB hLv hLi G hG0 N hNpos jB (by simpa [hN] using hB) fun j hj => by
    simpa [hN, hj] using pt_bij (hw j) (hM j hj) (hpt j)
  have e : ∏ j, N j = (∏ j, w j) * (b * ∏ j, (if j = jB then 1 else msc (τ j) (ρ j))) := by
    rw [hN, Finset.prod_mul_distrib]
    congr 1
    rw [← prod_ite_scale jB b]
    exact Finset.prod_congr rfl fun j _ => by split_ifs <;> simp
  rwa [e, ← mul_assoc] at key

/-- The square case of `term_even4`. -/
theorem term_even4_sq {Li : Fin 2 → Finset ℕ} (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (G : Fin 3 → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d) (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j)
    (τ : Fin 3 → ℕ) (ρ : Fin 3 → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j))
    (hact : ∀ j, ρ j ≠ 0 → ρ j = 1 ∧ 1 ≤ τ j) (h3 : ∀ j, ρ j ≠ 0 → τ j ≤ 3) {j₁ j₂ : Fin 3}
    (h12 : j₁ ≠ j₂) (ha1 : ρ j₁ ≠ 0) (ha2 : ρ j₂ ≠ 0) (ha : ∑ i, actM τ ρ i = 4) :
    P5 Lu Lv (faceSum Li (fun _ _ => 1) G) (faceConst3 2 * ∏ j, w j) := by
  have hFn := faceSum_nonneg Li (fun _ _ => 1) G (fun _ _ _ => zero_le_one) hG0
  have hN : 0 ≤ faceConst3 2 * ∏ j, w j := fc_prod_nonneg hw
  obtain ⟨jB, hmax, h3B⟩ := actM_max3 τ ρ
  have hBact : ρ jB ≠ 0 := fun h => by rw [actM_inact h] at h3B; omega
  have hτB : 2 ≤ τ jB := by rw [actM_act hBact] at h3B; omega
  have hτB3 := h3 jB hBact
  obtain ⟨hρB, -⟩ := hact jB hBact
  have hB := pt_ballA (by omega) hτB3 (hρB ▸ hpt jB)
  obtain ⟨j₁', hj₁', ha₁'⟩ : ∃ j', j' ≠ jB ∧ ρ j' ≠ 0 := by
    by_cases e : jB = j₁
    · exact ⟨j₂, fun h => h12 (e ▸ h.symm), ha2⟩
    · exact ⟨j₁, fun h => e h.symm, ha1⟩
  have hM : ∀ j, j ≠ jB → ρ j = 0 ∨ (ρ j = 1 ∧ τ j ≤ 2) := fun j hj => by
    by_cases hj0 : ρ j = 0
    · exact Or.inl hj0
    · refine Or.inr ⟨(hact j hj0).1, ?_⟩
      have := actM_two (τ := τ) (ρ := ρ) hj
      have := hmax j
      rw [actM_act hj0, actM_act hBact] at *
      omega
  have key := term_sqB hLv hLi G hG0 w hw τ ρ hpt jB (by norm_num) hB hM
  refine pH_p5 hN hFn (key.weaken (by have := a5_pos; positivity) ?_)
  have hp := (msc_prod τ ρ jB j₁' hj₁' ha₁').1
  have hw0 : 0 ≤ faceConst3 2 * ∏ j, w j := hN
  have : a5 ≤ 17 / 16 * ∏ j, (if j = jB then 1 else msc (τ j) (ρ j)) := by
    unfold a5; nlinarith
  exact mul_le_mul_of_nonneg_left this hw0

/-- The square case of `term_even5`. -/
theorem term_even5_sq {Li : Fin 2 → Finset ℕ} (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (G : Fin 3 → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d) (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j)
    (τ : Fin 3 → ℕ) (ρ : Fin 3 → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j))
    (hact : ∀ j, ρ j ≠ 0 → ρ j = 1 ∧ 1 ≤ τ j) (h4 : ∀ j, ρ j ≠ 0 → τ j ≤ 4)
    (hge1 : ∀ j, ρ j ≠ 0 → 1 ≤ τ j) (hother : ∀ j, ρ j ≠ 0 → ∃ j', j' ≠ j ∧ ρ j' ≠ 0)
    (ha : ∑ i, actM τ ρ i = 5) :
    P6 Lu Lv (faceSum Li (fun _ _ => 1) G) (faceConst3 2 * ∏ j, w j) := by
  have hFn := faceSum_nonneg Li (fun _ _ => 1) G (fun _ _ _ => zero_le_one) hG0
  have hN : 0 ≤ faceConst3 2 * ∏ j, w j := fc_prod_nonneg hw
  obtain ⟨jB, hmax, h3B⟩ := actM_max3 τ ρ
  have hBact : ρ jB ≠ 0 := fun h => by rw [actM_inact h] at h3B; omega
  have hτB : 2 ≤ τ jB := by rw [actM_act hBact] at h3B; omega
  have hτB4 := h4 jB hBact
  obtain ⟨hρB, -⟩ := hact jB hBact
  obtain ⟨j₁', hj₁', ha₁'⟩ := hother jB hBact
  have hM : ∀ j, j ≠ jB → ρ j = 0 ∨ (ρ j = 1 ∧ τ j ≤ 2) := fun j hj => by
    by_cases hj0 : ρ j = 0
    · exact Or.inl hj0
    · refine Or.inr ⟨(hact j hj0).1, ?_⟩
      have := actM_two (τ := τ) (ρ := ρ) hj
      have := hmax j
      rw [actM_act hj0, actM_act hBact] at *
      omega
  rcases Nat.lt_or_ge (τ jB) 4 with hB3 | hB4
  · have hB := pt_ballA (by omega) (by omega) (hρB ▸ hpt jB)
    have key := term_sqB hLv hLi G hG0 w hw τ ρ hpt jB (by norm_num) hB hM
    refine pH_p6 hN hFn (key.weaken (by have := d6_pos; positivity) ?_)
    have hp := (msc_prod τ ρ jB j₁' hj₁' ha₁').1
    have : d6 ≤ 17 / 16 * ∏ j, (if j = jB then 1 else msc (τ j) (ρ j)) := by
      have := d6_le_a5; unfold a5 at this; nlinarith
    exact mul_le_mul_of_nonneg_left this hN
  · -- `(4, 1)`
    have hB : InBall (pathList Lu Lv Li jB.castSucc) (pathList Lu Lv Li jB.succ) (G jB)
        (w jB * 1) := by
      rw [mul_one]; exact pt_ball (hw jB) (hG0 jB) (by rw [hρB]; decide) (hpt jB)
    have key := term_sqB hLv hLi G hG0 w hw τ ρ hpt jB one_pos hB hM
    have hτ1 : τ j₁' = 1 := by
      have := actM_two (τ := τ) (ρ := ρ) (Ne.symm hj₁')
      rw [actM_act hBact, actM_act ha₁'] at this
      have := hge1 j₁' ha₁'
      omega
    refine pH_p6 hN hFn (key.weaken (by have := d6_pos; positivity) ?_)
    have hp := (msc_prod τ ρ jB j₁' hj₁' ha₁').2 hτ1
    have : d6 ≤ 1 * ∏ j, (if j = jB then 1 else msc (τ j) (ρ j)) := by
      rw [one_mul]; exact d6_le_κq.trans hp
    exact mul_le_mul_of_nonneg_left this hN

/-- **A term of an even face with four active marks.** -/
theorem term_even4 (hm : Even m) (hm2 : 2 ≤ m) (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (G : Fin (m + 1) → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d)
    (w : Fin (m + 1) → ℝ) (hw : ∀ j, 0 < w j) (τ : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j))
    (hτ : ∀ j, ρ j ≠ 0 → τ j ≤ 4) (ha : ∑ i, actM τ ρ i = 4) :
    P5 Lu Lv (faceSum Li (fun _ _ => 1) G) (faceConst3 m * ∏ j, w j) := by
  have hFn := faceSum_nonneg Li (fun _ _ => 1) G (fun _ _ _ => zero_le_one) hG0
  have hN : 0 ≤ faceConst3 m * ∏ j, w j :=
    (mul_pos (faceConst3_pos m) (Finset.prod_pos fun j _ => hw j)).le
  have hact := fun j (h : ρ j ≠ 0) => act_one (hw j) (hτ j h) h (hpt j)
  by_cases hsingle : ∃ j₁ j₂, j₁ ≠ j₂ ∧ ρ j₁ ≠ 0 ∧ ρ j₂ ≠ 0
  · obtain ⟨j₁, j₂, h12, ha1, ha2⟩ := hsingle
    -- every active side has at most three marks
    have h3 : ∀ j, ρ j ≠ 0 → τ j ≤ 3 := fun j hj => by
      obtain ⟨j', hj', haj'⟩ : ∃ j', j' ≠ j ∧ ρ j' ≠ 0 := by
        by_cases e : j = j₁
        · exact ⟨j₂, fun h => h12 (e ▸ h.symm), ha2⟩
        · exact ⟨j₁, fun h => e h.symm, ha1⟩
      have := actM_two (τ := τ) (ρ := ρ) (Ne.symm hj')
      rw [actM_act hj, actM_act haj'] at this
      have := (hact j' haj').2
      omega
    rcases Nat.lt_or_ge m 4 with hm4 | hm4
    · obtain rfl : m = 2 := by obtain ⟨k, hk⟩ := hm; omega
      exact term_even4_sq hLv hLi G hG0 w hw τ ρ hpt hact h3 h12 ha1 ha2 ha
    · -- length at least six
      set B : Fin (m + 1) → ℝ := fun j => if ρ j = 0 then w j else w j * (17 / 16) with hBdef
      have hBpos : ∀ j, 0 < B j := fun j => by
        simp only [hBdef]; split_ifs
        · exact hw j
        · exact mul_pos (hw j) (by norm_num)
      have hBall : ∀ j, InBall (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
          (B j) := fun j => by
        simp only [hBdef]
        split_ifs with hj
        · exact pt_ball (hw j) (hG0 j) (by rw [hj]; decide) (hpt j)
        · obtain ⟨hρ1, hk1⟩ := hact j hj
          exact pt_ballA hk1 (h3 j hj) (hρ1 ▸ hpt j)
      have key := ballEvenSix m hm hm4 Lu Lv Li hLu hLv hLi G hG0 B hBpos hBall
      refine pB_p5 hN hFn (key.weaken hN ?_)
      have hprod : (17 / 16 : ℝ) ^ 2 * ∏ j, w j ≤ ∏ j, B j := by
        have e : ∏ j, B j = (∏ j, w j) * ∏ j, (if ρ j = 0 then (1 : ℝ) else 17 / 16) := by
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun j _ => by simp only [hBdef]; split_ifs <;> ring
        rw [e]
        have h2 : (17 / 16 : ℝ) ^ 2 ≤ ∏ j, (if ρ j = 0 then (1 : ℝ) else 17 / 16) := by
          rw [← Finset.mul_prod_erase univ _ (mem_univ j₁),
            ← Finset.mul_prod_erase (univ.erase j₁) _ (mem_erase.mpr ⟨Ne.symm h12, mem_univ j₂⟩)]
          simp only [ha1, ha2, ite_false]
          have : 1 ≤ ∏ j ∈ (univ.erase j₁).erase j₂, (if ρ j = 0 then (1 : ℝ) else 17 / 16) :=
            Finset.one_le_prod₀ fun j _ => by split_ifs <;> norm_num
          nlinarith
        have := Finset.prod_pos fun j (_ : j ∈ univ) => hw j
        nlinarith
      have := faceConst3_pos m
      calc faceConst3 m * ∏ j, w j = 16 / 17 * faceConst3 m * ((17 / 16) * ∏ j, w j) := by ring
        _ ≤ 16 / 17 * faceConst3 m * ∏ j, B j := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have := Finset.prod_pos fun j (_ : j ∈ univ) => hw j
            nlinarith
  · -- one active side
    push Not at hsingle
    obtain ⟨j₀, hj₀⟩ : ∃ j₀, ρ j₀ ≠ 0 := by
      by_contra hc
      push Not at hc
      have : ∑ i, actM τ ρ i = 0 := Finset.sum_eq_zero fun i _ => actM_inact (hc i)
      omega
    have hrest : ∀ j, j ≠ j₀ → ρ j = 0 := fun j hj => hsingle j₀ j (Ne.symm hj) hj₀
    obtain ⟨hρ1, -⟩ := hact j₀ hj₀
    have hB := pt_ball (hw j₀) (hG0 j₀) (by rw [hρ1]; decide) (hpt j₀)
    have h := ball_one (j₀ := j₀) hLu hLv hLi hG0 hw one_pos (by rwa [mul_one])
      fun j hj => (hpt j).1 (hrest j hj)
    rw [mul_one] at h
    exact pB_p5 hN hFn h

/-- **Step 1: an even face whose sides carry at most four marks is in `Kc6 5`.** -/
theorem mx5_even (hm : Even m) (hm2 : 2 ≤ m) (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d)
    (A : Fin (m + 1) → ℝ) (hA : ∀ j, 0 < A j) (τ : Fin (m + 1) → ℕ) (hτ : ∑ j, τ j ≤ 4)
    (hE : ∀ j, Kc6 (τ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Mx P5 Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  obtain ⟨u, v₁, v₂, Y₁, Y₂, hu, hv₁, hv₂, huv, hY₁, hY₂, hP1, hP2, hEY⟩ :=
    face_data τ _ _ E A (fun j => (hA j).le) hE
  have hG0 := gT3_nonneg hu hY₁ hY₂
  have hτ4 : ∀ j, τ j ≤ 4 := fun j =>
    (Finset.single_le_sum (f := τ) (fun _ _ => Nat.zero_le _) (mem_univ j)).trans hτ
  refine mx_expand3 cone5 Lu Lv Li E hE0 A hA hu hv₁ hv₂ huv hY₁ hY₂ hEY fun ρ hρ => ?_
  set G := fun j => gT3 u Y₁ Y₂ j (ρ j) with hG
  set w := fun j => wT3 u v₁ v₂ j (ρ j) with hw
  have hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j) := fun j => gT3_pt (k := τ j) j (ρ j) (hY₁ j) (hY₂ j) (hP1 j) (hP2 j)
  have hG0' : ∀ j c d, 0 ≤ G j c d := fun j c d => hG0 j (ρ j) c d
  have hFn := faceSum_nonneg Li (fun _ _ => 1) G (fun _ _ _ => zero_le_one) hG0'
  have ha := (sum_actM_le (τ := τ) (ρ := ρ)).trans hτ
  rcases Nat.lt_or_ge (∑ i, actM τ ρ i) 4 with h3 | h4
  · -- at most three active marks
    have hK : ∀ j, Kc (actM τ ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
        (G j) (w j) := fun j => by
      have := pt_kc6 (hρ j) (hG0' j) (hτ4 j) (hpt j)
      have h4 := hτ4 j
      rw [Kc6_eq (by split_ifs <;> omega)] at this
      exact this
    exact Mx.imp (fun hv h0 h => p4_p5 hv h0 h) (mx4_even hm hm2 Lu Lv Li hLu hLv hLi G hG0' w
      hρ (actM τ ρ) (by omega) hK)
  · exact Mx.of_P (fc_prod_nonneg hρ) hFn (term_even4 hm hm2 hLu hLv hLi G hG0' w hρ τ ρ hpt
      (fun j _ => hτ4 j) (by omega))

/-- **A term of an even face with five active marks.** -/
theorem term_even5 (hm : Even m) (hm2 : 2 ≤ m) (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (G : Fin (m + 1) → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d)
    (w : Fin (m + 1) → ℝ) (hw : ∀ j, 0 < w j) (τ : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j))
    (hτ : ∀ j, ρ j ≠ 0 → τ j ≤ 5) (ha : ∑ i, actM τ ρ i = 5) :
    P6 Lu Lv (faceSum Li (fun _ _ => 1) G) (faceConst3 m * ∏ j, w j) := by
  have hFn := faceSum_nonneg Li (fun _ _ => 1) G (fun _ _ _ => zero_le_one) hG0
  have hN : 0 ≤ faceConst3 m * ∏ j, w j :=
    (mul_pos (faceConst3_pos m) (Finset.prod_pos fun j _ => hw j)).le
  by_cases hsingle : ∃ j₁ j₂, j₁ ≠ j₂ ∧ ρ j₁ ≠ 0 ∧ ρ j₂ ≠ 0
  · obtain ⟨j₁, j₂, h12, ha1, ha2⟩ := hsingle
    have hother : ∀ j, ρ j ≠ 0 → ∃ j', j' ≠ j ∧ ρ j' ≠ 0 := fun j _ => by
      by_cases e : j = j₁
      · exact ⟨j₂, fun h => h12 (e ▸ h.symm), ha2⟩
      · exact ⟨j₁, fun h => e h.symm, ha1⟩
    -- every active side has at most four marks, hence is a first alternative
    have hge1 : ∀ j, ρ j ≠ 0 → 1 ≤ τ j := fun j hj => pt_act_ge (hw j) hj (hpt j)
    have h4 : ∀ j, ρ j ≠ 0 → τ j ≤ 4 := fun j hj => by
      obtain ⟨j', hj', haj'⟩ := hother j hj
      have := actM_two (τ := τ) (ρ := ρ) (Ne.symm hj')
      rw [actM_act hj, actM_act haj'] at this
      have := hge1 j' haj'
      omega
    have hact := fun j (h : ρ j ≠ 0) => act_one (hw j) (h4 j h) h (hpt j)
    rcases Nat.lt_or_ge m 4 with hm4 | hm4
    · obtain rfl : m = 2 := by obtain ⟨k, hk⟩ := hm; omega
      exact term_even5_sq hLv hLi G hG0 w hw τ ρ hpt hact h4 hge1 hother ha
    · -- length at least six: some active side carries at most three marks
      obtain ⟨j₃, hj₃, h3⟩ : ∃ j, ρ j ≠ 0 ∧ τ j ≤ 3 := by
        by_contra hc
        push Not at hc
        have := actM_two (τ := τ) (ρ := ρ) h12
        rw [actM_act ha1, actM_act ha2] at this
        have := hc j₁ ha1
        have := hc j₂ ha2
        omega
      set B : Fin (m + 1) → ℝ := fun j => if j = j₃ then w j * (17 / 16) else w j with hBdef
      have hBpos : ∀ j, 0 < B j := fun j => by
        simp only [hBdef]; split_ifs
        · exact mul_pos (hw j) (by norm_num)
        · exact hw j
      have hBall : ∀ j, InBall (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
          (B j) := fun j => by
        simp only [hBdef]
        split_ifs with hj
        · subst hj
          obtain ⟨hρ1, hk1⟩ := hact j hj₃
          exact pt_ballA hk1 h3 (hρ1 ▸ hpt j)
        · by_cases hj0 : ρ j = 0
          · exact pt_ball (hw j) (hG0 j) (by rw [hj0]; decide) (hpt j)
          · obtain ⟨hρ1, -⟩ := hact j hj0
            exact pt_ball (hw j) (hG0 j) (by rw [hρ1]; decide) (hpt j)
      have key := ballEvenSix m hm hm4 Lu Lv Li hLu hLv hLi G hG0 B hBpos hBall
      refine pB_p6 hN hFn (key.weaken hN (le_of_eq ?_))
      have e : ∏ j, B j = 17 / 16 * ∏ j, w j := by
        rw [← prod_ite_scale j₃ (17 / 16) w]
        exact Finset.prod_congr rfl fun j _ => by simp only [hBdef]; split_ifs <;> ring
      rw [e]
      ring
  · -- one active side, with five marks
    push Not at hsingle
    obtain ⟨j₀, hj₀⟩ : ∃ j₀, ρ j₀ ≠ 0 := by
      by_contra hc
      push Not at hc
      have : ∑ i, actM τ ρ i = 0 := Finset.sum_eq_zero fun i _ => actM_inact (hc i)
      omega
    have hrest : ∀ j, j ≠ j₀ → ρ j = 0 := fun j hj => hsingle j₀ j (Ne.symm hj) hj₀
    have hτ5 : τ j₀ = 5 := by
      have : ∑ i, actM τ ρ i = actM τ ρ j₀ :=
        Finset.sum_eq_single j₀ (fun j _ hj => actM_inact (hrest j hj)) (fun h => (h (mem_univ _)).elim)
      rw [this, actM_act hj₀] at ha
      exact ha
    have hD : ∀ j, j ≠ j₀ → Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
        (G j) (w j) := fun j hj => (hpt j).1 (hrest j hj)
    by_cases h2 : ρ j₀ = 2
    · -- the hexagon part: the two-distinguished law
      have hH : Hex (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) (G j₀)
          (w j₀ * a5) := by
        have h := hpt j₀
        rw [hτ5, h2] at h
        exact pt_hex5 h
      refine pH_p6 hN hFn ?_
      rcases Nat.lt_or_ge m 4 with hm4 | hm4
      · obtain rfl : m = 2 := by obtain ⟨k, hk⟩ := hm; omega
        set N : Fin 3 → ℝ := fun j => if j = j₀ then a5 * w j else w j with hNdef
        have hNpos : ∀ j, 0 < N j := fun j => by
          simp only [hNdef]; split_ifs
          · exact mul_pos a5_pos (hw j)
          · exact hw j
        have key := sqLawH hLv hLi G hG0 N hNpos j₀ (by simpa [hNdef, mul_comm] using hH)
          fun j hj => by simpa [hNdef, hj] using (hD j hj).bijGe (hw j).le
        rw [hNdef, prod_ite_scale] at key
        refine key.weaken (by have := d6_pos; positivity) (le_of_eq ?_)
        unfold d6; ring
      · set N : Fin (m + 1) → ℝ := fun j => if j = j₀ then a5 * w j else w j with hNdef
        have hNpos : ∀ j, 0 < N j := fun j => by
          simp only [hNdef]; split_ifs
          · exact mul_pos a5_pos (hw j)
          · exact hw j
        have key := hexEvenSix m hm hm4 Lu Lv Li hLv hLi G hG0 N hNpos fun j => by
          by_cases hj : j = j₀
          · subst hj; simpa [hNdef, mul_comm] using hH
          · simpa [hNdef, hj] using (hD j hj).hex (hw j).le
        rw [hNdef, prod_ite_scale] at key
        refine key.weaken (by have := d6_pos; positivity) (le_of_eq ?_)
        unfold d6; ring
    · -- the ball part: one-load closure
      have hB := pt_ball (hw j₀) (hG0 j₀) h2 (hpt j₀)
      have h := ball_one (j₀ := j₀) hLu hLv hLi hG0 hw one_pos (by rwa [mul_one]) hD
      rw [mul_one] at h
      exact pB_p6 hN hFn h

/-- **Step 2: an even face whose sides carry at most five marks is in `Kc6 6`.** -/
theorem mx6_even (hm : Even m) (hm2 : 2 ≤ m) (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d)
    (A : Fin (m + 1) → ℝ) (hA : ∀ j, 0 < A j) (τ : Fin (m + 1) → ℕ) (hτ : ∑ j, τ j ≤ 5)
    (hE : ∀ j, Kc6 (τ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Mx P6 Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  obtain ⟨u, v₁, v₂, Y₁, Y₂, hu, hv₁, hv₂, huv, hY₁, hY₂, hP1, hP2, hEY⟩ :=
    face_data τ _ _ E A (fun j => (hA j).le) hE
  have hG0 := gT3_nonneg hu hY₁ hY₂
  have hτ5 : ∀ j, τ j ≤ 5 := fun j =>
    (Finset.single_le_sum (f := τ) (fun _ _ => Nat.zero_le _) (mem_univ j)).trans hτ
  refine mx_expand3 cone6 Lu Lv Li E hE0 A hA hu hv₁ hv₂ huv hY₁ hY₂ hEY fun ρ hρ => ?_
  set G := fun j => gT3 u Y₁ Y₂ j (ρ j) with hG
  set w := fun j => wT3 u v₁ v₂ j (ρ j) with hw
  have hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j) := fun j => gT3_pt (k := τ j) j (ρ j) (hY₁ j) (hY₂ j) (hP1 j) (hP2 j)
  have hG0' : ∀ j c d, 0 ≤ G j c d := fun j c d => hG0 j (ρ j) c d
  have hFn := faceSum_nonneg Li (fun _ _ => 1) G (fun _ _ _ => zero_le_one) hG0'
  have ha := (sum_actM_le (τ := τ) (ρ := ρ)).trans hτ
  rcases Nat.lt_or_ge (∑ i, actM τ ρ i) 5 with h4 | h5
  · -- at most four active marks: Step 1
    have hK : ∀ j, Kc6 (actM τ ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
        (G j) (w j) := fun j => by
      by_cases hj : ρ j = 0
      · have := pt_kc6' (hρ j) (hG0' j) (Or.inl hj) (hpt j)
        rwa [show actM τ ρ j = (if ρ j = 0 then 0 else τ j) from rfl]
      · have hle : τ j ≤ 4 := by
          have := actM_le_sum (τ := τ) (ρ := ρ) j
          rw [actM_act hj] at this
          omega
        exact pt_kc6' (hρ j) (hG0' j) (Or.inr hle) (hpt j)
    exact Mx.imp (fun _ _ h => p5_p6 h) (mx5_even hm hm2 hLu hLv hLi G hG0' w hρ (actM τ ρ)
      (by omega) hK)
  · exact Mx.of_P (fc_prod_nonneg hρ) hFn (term_even5 hm hm2 hLu hLv hLi G hG0' w hρ τ ρ hpt
      (fun j _ => hτ5 j) (by omega))

end Even

/-! ### The face rule -/

/-- **The face rule through six marks**: `k ≤ 6` is at least the number of marks of the face (one
if it is even) and of its sides. -/
def markRule6 (k m : ℕ) (τ : Fin (m + 1) → ℕ) : Prop :=
  1 ≤ m ∧ (if Even m then 1 else 0) + ∑ j, τ j ≤ k ∧ k ≤ 6

/-- **The face rule through six marks is sound.** -/
theorem markRule6_sound {k m : ℕ} {τ : Fin (m + 1) → ℕ} (hr : markRule6 k m τ)
    (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ) (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d)
    (A : Fin (m + 1) → ℝ) (hA : ∀ j, 0 < A j)
    (hE : ∀ j, Kc6 (τ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Kc6 k Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  obtain ⟨hm1, hsum, hk6⟩ := hr
  have hτ : ∀ j, τ j ≤ ∑ i, τ i := fun j =>
    Finset.single_le_sum (f := τ) (fun _ _ => Nat.zero_le _) (mem_univ j)
  rcases Nat.lt_or_ge k 5 with hk4 | hk5
  · rw [Kc6_eq (by omega)]
    refine markRule_sound ⟨hm1, hsum, by omega⟩ Lu Lv Li hLu hLv hLi E hE0 A hA fun j => ?_
    have := hE j
    rwa [Kc6_eq (by have := hτ j; split_ifs at hsum <;> omega)] at this
  rcases Nat.even_or_odd m with hev | hodd
  · have hm2 : 2 ≤ m := by obtain ⟨r, hr⟩ := hev; omega
    simp only [hev, ↓reduceIte] at hsum
    rcases (show k = 5 ∨ k = 6 by omega) with rfl | rfl
    · exact mx5_even hev hm2 hLu hLv hLi E hE0 A hA τ (by omega) hE
    · exact mx6_even hev hm2 hLu hLv hLi E hE0 A hA τ (by omega) hE
  · simp only [Nat.not_even_iff_odd.mpr hodd, ↓reduceIte, zero_add] at hsum
    exact mx56_odd hodd hLu hLv hLi E hE0 A hA k hk5 hk6 τ (fun j => (hτ j).trans hsum) hE

end Outerplanar
