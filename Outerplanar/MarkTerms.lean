/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.MarkFiveSix

/-!
# Terms of the mark classes, and the face laws they feed

The expansion of the classes `Kc6 k` into three alternatives per side: the constant (`r = 0`),
the first table (`r = 1`: the tables of `k ≤ 4` marks, or the ball part of five and six marks) and
the second table (`r = 2`: the hexagon part of five and six marks). A term of a face picks one
alternative per side; its tables have the *pure types* `PT k r`.

* `PP1`, `PP2`, `PT`, `kc6_data` (the alternatives of one class), `gT3`/`wT3` (the term tables and
  constants), `gT3_pt`;
* the capabilities of a pure type: `pt_hex` (`H`), `pt_ball` (`B`), `pt_ballA` (`A B`),
  `pt_hexA` (`A H`), `pt_hexH` (the hexagon parts), `pt_bij` (`M`, with the surpluses `κq`, `κA`),
  `pt_kc6` (back to a class);
* `faceSum_sum3`, **`mx_expand3`** — the multilinear expansion of a face over three alternatives;
* the square laws in path-position form: `sqLawB` (`[B, M, M]` and its two rotations),
  `sqLawH` (`[H, M, M]`, scale `56/59`), `sqLawBBB`, `sqLawHHH`.

Formalized by Claude (milestone M3 of `ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`).
-/

namespace Outerplanar

open Finset

/-! ### Pure types -/

/-- The first alternative of `k` marks. -/
def PP1 : ℕ → Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop
  | 0 => fun _ _ _ v => v = 0
  | 1 => P1
  | 2 => P2
  | 3 => P3
  | 4 => P4
  | _ => fun S T Y v => InBall S T Y v

/-- The second alternative of `k` marks. -/
def PP2 : ℕ → Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop
  | 0 => fun _ _ _ v => v = 0
  | 1 => fun _ _ _ v => v = 0
  | 2 => fun _ _ _ v => v = 0
  | 3 => fun _ _ _ v => v = 0
  | 4 => fun _ _ _ v => v = 0
  | 5 => fun S T Y v => Hex S T Y (v * a5)
  | _ => fun S T Y v => Hex S T Y (v * d6)

/-- **The pure type** `(k, r)` of a term table. -/
def PT (k : ℕ) (r : Fin 3) (S T : Finset ℕ) (Y : ℕ → ℕ → ℝ) (v : ℝ) : Prop :=
  (r = 0 → Dominant S T Y v) ∧ (r = 1 → PP1 k S T Y v) ∧ (r = 2 → PP2 k S T Y v)

section Pure

variable {S T : Finset ℕ} {Y Y' : ℕ → ℕ → ℝ} {v : ℝ} {k : ℕ} {r : Fin 3}

theorem PP1_five (hk : 5 ≤ k) : PP1 k = fun S T Y v => InBall S T Y v := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
  rfl

theorem PP2_six (hk : 6 ≤ k) : PP2 k = fun S T Y v => Hex S T Y (v * d6) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
  rfl

theorem PP2_low (hk : k ≤ 4) : PP2 k S T Y v ↔ v = 0 := by
  interval_cases k <;> rfl

theorem PP1_mono (h0 : ∀ c d, 0 ≤ Y c d) (hle : ∀ c ∈ S, ∀ d ∈ T, c ≠ d → Y c d ≤ Y' c d)
    (h : PP1 k S T Y v) : PP1 k S T Y' v := by
  rcases Nat.lt_or_ge k 5 with hk | hk
  · interval_cases k
    · exact h
    · exact cone1.mono h0 hle h
    · exact cone2.mono h0 hle h
    · exact cone3.mono h0 hle h
    · exact cone4.mono h0 hle h
  · rw [PP1_five hk] at h ⊢
    exact h.mono h0 hle

theorem PP2_mono (h0 : ∀ c d, 0 ≤ Y c d) (hle : ∀ c ∈ S, ∀ d ∈ T, c ≠ d → Y c d ≤ Y' c d)
    (h : PP2 k S T Y v) : PP2 k S T Y' v := by
  rcases Nat.lt_or_ge k 5 with hk | hk
  · exact (PP2_low (by omega)).mpr ((PP2_low (by omega)).mp h)
  rcases Nat.lt_or_ge k 6 with hk' | hk'
  · obtain rfl : k = 5 := by omega
    exact Hex.mono h h0 hle
  · rw [PP2_six hk'] at h ⊢
    exact Hex.mono h h0 hle

/-- **The alternatives of a class.** -/
theorem kc6_data {W : ℕ → ℕ → ℝ} {N : ℝ} (hN : 0 ≤ N) (h : Kc6 k S T W N) :
    ∃ (u v₁ v₂ : ℝ) (Y₁ Y₂ : ℕ → ℕ → ℝ), 0 ≤ u ∧ 0 ≤ v₁ ∧ 0 ≤ v₂ ∧ N ≤ u + v₁ + v₂ ∧
      (∀ c d, 0 ≤ Y₁ c d) ∧ (∀ c d, 0 ≤ Y₂ c d) ∧ PP1 k S T Y₁ v₁ ∧ PP2 k S T Y₂ v₂ ∧
      ∀ c ∈ S, ∀ d ∈ T, c ≠ d → u + Y₁ c d + Y₂ c d ≤ W c d := by
  have hz : ∀ k', k' ≤ 4 → PP2 k' S T (fun _ _ => 0) 0 := fun k' hk' => (PP2_low hk').mpr rfl
  rcases Nat.lt_or_ge k 1 with h0 | h1
  · obtain rfl : k = 0 := by omega
    exact ⟨N, 0, 0, fun _ _ => 0, fun _ _ => 0, hN, le_rfl, le_rfl, by simp, fun _ _ => le_rfl,
      fun _ _ => le_rfl, rfl, rfl, fun c hc d hd hcd => by simpa using h c hc d hd hcd⟩
  have hlow : ∀ (P : Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop),
      (∀ {S' T' : Finset ℕ} {Y' : ℕ → ℕ → ℝ} {v' : ℝ}, P S' T' Y' v' → PP1 k S' T' Y' v') →
      k ≤ 4 → Mx P S T W N → ∃ (u v₁ v₂ : ℝ) (Y₁ Y₂ : ℕ → ℕ → ℝ), 0 ≤ u ∧ 0 ≤ v₁ ∧ 0 ≤ v₂ ∧
        N ≤ u + v₁ + v₂ ∧ (∀ c d, 0 ≤ Y₁ c d) ∧ (∀ c d, 0 ≤ Y₂ c d) ∧ PP1 k S T Y₁ v₁ ∧
        PP2 k S T Y₂ v₂ ∧ ∀ c ∈ S, ∀ d ∈ T, c ≠ d → u + Y₁ c d + Y₂ c d ≤ W c d := by
    intro P hP hk hx
    obtain ⟨u, v, Y, hu, hv, hNuv, hY0, hY, hW⟩ := hx
    exact ⟨u, v, 0, Y, fun _ _ => 0, hu, hv, le_rfl, by linarith, hY0, fun _ _ => le_rfl,
      hP hY, hz k hk, fun c hc d hd hcd => by simpa using hW c hc d hd hcd⟩
  rcases Nat.lt_or_ge k 5 with hk | hk
  · interval_cases k
    · exact hlow P1 (fun h => h) (by norm_num) h
    · exact hlow P2 (fun h => h) (by norm_num) h
    · exact hlow P3 (fun h => h) (by norm_num) h
    · exact hlow P4 (fun h => h) (by norm_num) h
  have halt : ∀ {κ : ℝ}, Mx (Alt2 (fun S T Y v => InBall S T Y v)
        (fun S T Y v => Hex S T Y (v * κ))) S T W N →
      (∀ {S' T' : Finset ℕ} {Y' : ℕ → ℕ → ℝ} {v' : ℝ}, Hex S' T' Y' (v' * κ) →
        PP2 k S' T' Y' v') →
      ∃ (u v₁ v₂ : ℝ) (Y₁ Y₂ : ℕ → ℕ → ℝ), 0 ≤ u ∧ 0 ≤ v₁ ∧ 0 ≤ v₂ ∧
        N ≤ u + v₁ + v₂ ∧ (∀ c d, 0 ≤ Y₁ c d) ∧ (∀ c d, 0 ≤ Y₂ c d) ∧ PP1 k S T Y₁ v₁ ∧
        PP2 k S T Y₂ v₂ ∧ ∀ c ∈ S, ∀ d ∈ T, c ≠ d → u + Y₁ c d + Y₂ c d ≤ W c d := by
    intro κ hx hq
    obtain ⟨u, v, Y, hu, hv, hNuv, hY0, hY, hW⟩ := hx
    obtain ⟨Y₁, Y₂, v₁, v₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hY
    refine ⟨u, v₁, v₂, Y₁, Y₂, hu, h1, h2, by linarith, h4, h5, by rw [PP1_five hk]; exact h7,
      hq h8, fun c hc d hd hcd => ?_⟩
    have := h6 c hc d hd hcd
    have := hW c hc d hd hcd
    linarith
  rcases Nat.lt_or_ge k 6 with hk' | hk'
  · obtain rfl : k = 5 := by omega
    exact halt h fun h => h
  · rw [Kc6_six hk'] at h
    exact halt h fun h => by rw [PP2_six hk']; exact h

/-! ### Capabilities of a pure type -/

theorem pt_hex (hv : 0 < v) (h0 : ∀ c d, 0 ≤ Y c d) (h : PT k r S T Y v) : Hex S T Y v := by
  rcases Fin.exists_fin_succ.mp ⟨r, rfl⟩ with h' | ⟨r', rfl⟩
  · subst h'; exact (h.1 rfl).hex hv.le
  rcases Fin.exists_fin_succ.mp ⟨r', rfl⟩ with h' | ⟨r'', rfl⟩
  · subst h'
    have h1 := h.2.1 rfl
    rcases Nat.lt_or_ge k 5 with hk | hk
    · interval_cases k
      · exact absurd (show v = 0 from h1) hv.ne'
      · exact fun _ _ hm hpq => (h1.2.2.2.1.weaken hv.le (by linarith)).hex hv.le h0 hm hpq
      · exact fun _ _ hm hpq => (h1.2.2.2.weaken hv.le (by linarith)).hex hv.le h0 hm hpq
      · exact fun _ _ hm hpq => (InBall.weaken hv.le (by linarith) h1).hex hv.le h0 hm hpq
      · exact fun _ _ hm hpq => h1.1.hex hv.le h0 hm hpq
    · rw [PP1_five hk] at h1
      exact fun _ _ hm hpq => h1.hex hv.le h0 hm hpq
  · obtain rfl : r'' = 0 := Subsingleton.elim _ _
    have h2 := h.2.2 rfl
    rcases Nat.lt_or_ge k 5 with hk | hk
    · exact absurd ((PP2_low (by omega)).mp h2) hv.ne'
    rcases Nat.lt_or_ge k 6 with hk' | hk'
    · obtain rfl : k = 5 := by omega
      exact h2.weaken hv.le (by nlinarith [one_le_a5])
    · rw [PP2_six hk'] at h2
      exact h2.weaken hv.le (by nlinarith [one_le_d6])

theorem pt_ball (hv : 0 < v) (h0 : ∀ c d, 0 ≤ Y c d) (hr : r ≠ 2) (h : PT k r S T Y v) :
    InBall S T Y v := by
  rcases Fin.exists_fin_succ.mp ⟨r, rfl⟩ with h' | ⟨r', rfl⟩
  · subst h'; exact (h.1 rfl).inBall hv.le
  rcases Fin.exists_fin_succ.mp ⟨r', rfl⟩ with h' | ⟨r'', rfl⟩
  · subst h'
    have h1 := h.2.1 rfl
    rcases Nat.lt_or_ge k 5 with hk | hk
    · interval_cases k
      · exact absurd (show v = 0 from h1) hv.ne'
      · exact h1.2.2.2.1.weaken hv.le (by linarith)
      · exact h1.2.2.2.weaken hv.le (by linarith)
      · exact InBall.weaken hv.le (by linarith) h1
      · exact h1.1
    · rw [PP1_five hk] at h1
      exact h1
  · obtain rfl : r'' = 0 := Subsingleton.elim _ _
    exact absurd rfl hr

theorem pt_ballA (hk1 : 1 ≤ k) (hk3 : k ≤ 3) (h : PT k 1 S T Y v) :
    InBall S T Y (v * (17 / 16)) := by
  have h1 := h.2.1 rfl
  interval_cases k
  · exact h1.2.2.2.1
  · exact h1.2.2.2
  · exact h1

theorem pt_hexA (hv : 0 < v) (h0 : ∀ c d, 0 ≤ Y c d) (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (h : PT k 1 S T Y v) : Hex S T Y (v * (17 / 16)) := by
  rcases Nat.lt_or_ge k 4 with hk | hk
  · exact fun _ _ hm hpq => (pt_ballA hk1 (by omega) h).hex (by positivity) h0 hm hpq
  · obtain rfl : k = 4 := by omega
    exact (h.2.1 rfl).2

theorem pt_two_ge (hv : 0 < v) (h : PT k 2 S T Y v) : 5 ≤ k := by
  by_contra hk
  exact hv.ne' ((PP2_low (by omega)).mp (h.2.2 rfl))

theorem pt_one_ge (hv : 0 < v) (h : PT k 1 S T Y v) : 1 ≤ k := by
  by_contra hk
  obtain rfl : k = 0 := by omega
  exact hv.ne' (h.2.1 rfl)

theorem pt_hex5 (h : PT 5 2 S T Y v) : Hex S T Y (v * a5) := h.2.2 rfl

theorem pt_hexH (hv : 0 < v) (h : PT k 2 S T Y v) : Hex S T Y (v * d6) := by
  have hk := pt_two_ge hv h
  have h2 := h.2.2 rfl
  rcases Nat.lt_or_ge k 6 with hk' | hk'
  · obtain rfl : k = 5 := by omega
    exact h2.weaken (by have := d6_pos; positivity) (mul_le_mul_of_nonneg_left d6_le_a5 hv.le)
  · rw [PP2_six hk'] at h2
    exact h2

/-- The bijection scale of a light pure type. -/
noncomputable def msc (k : ℕ) (r : Fin 3) : ℝ := if r = 0 then 1 else if k = 1 then κq else κA

theorem msc_ge (k : ℕ) (r : Fin 3) : 1 ≤ msc k r := by
  unfold msc; split_ifs
  · exact le_rfl
  · exact one_le_κq
  · exact one_le_κA

theorem msc_pos (k : ℕ) (r : Fin 3) : 0 < msc k r := lt_of_lt_of_le one_pos (msc_ge k r)

theorem msc_act {k : ℕ} {r : Fin 3} (hr : r ≠ 0) : κA ≤ msc k r := by
  unfold msc; simp only [hr, ↓reduceIte]; split_ifs
  · exact κA_le_κq
  · exact le_rfl

theorem msc_one {k : ℕ} {r : Fin 3} (hr : r ≠ 0) (hk : k = 1) : msc k r = κq := by
  unfold msc; simp [hr, hk]

theorem pt_bij (hv : 0 < v) (hl : r = 0 ∨ (r = 1 ∧ k ≤ 2)) (h : PT k r S T Y v) :
    BijGe S T Y (v * msc k r) 1 := by
  rcases hl with rfl | ⟨rfl, hk⟩
  · simpa [msc] using (h.1 rfl).bijGe hv.le
  · have h1 := h.2.1 rfl
    interval_cases k
    · exact absurd (show v = 0 from h1) hv.ne'
    · have := (bijGe_cube (by norm_num : (0 : ℝ) ≤ 32 / 27)).mp h1.2.1
      simpa [msc, κq] using this
    · have := (bijGe_cube (by norm_num : (0 : ℝ) ≤ 17 / 16)).mp h1.2.1
      simpa [msc, κA] using this

/-- A pure type with at most four marks, back in its class. -/
theorem pt_kc6 (hv : 0 < v) (h0 : ∀ c d, 0 ≤ Y c d) (hk : k ≤ 4) (h : PT k r S T Y v) :
    Kc6 (if r = 0 then 0 else k) S T Y v := by
  rcases Fin.exists_fin_succ.mp ⟨r, rfl⟩ with h' | ⟨r', rfl⟩
  · subst h'; exact h.1 rfl
  rcases Fin.exists_fin_succ.mp ⟨r', rfl⟩ with h' | ⟨r'', rfl⟩
  · subst h'
    have h1 := h.2.1 rfl
    simp only [Fin.succ_zero_eq_one, one_ne_zero, ↓reduceIte]
    interval_cases k
    · exact absurd (show v = 0 from h1) hv.ne'
    · exact Mx.of_P hv.le h0 h1
    · exact Mx.of_P hv.le h0 h1
    · exact Mx.of_P hv.le h0 h1
    · exact Mx.of_P hv.le h0 h1
  · obtain rfl : r'' = 0 := Subsingleton.elim _ _
    exact absurd ((PP2_low hk).mp (h.2.2 rfl)) hv.ne'

end Pure

/-! ### Terms -/

section Terms

variable {n : ℕ}

/-- The term tables: on proper pairs the constant, the first or the second table. -/
def gT3 (u : Fin n → ℝ) (Y₁ Y₂ : Fin n → ℕ → ℕ → ℝ) (j : Fin n) (r : Fin 3) : ℕ → ℕ → ℝ :=
  fun c d => if c ≠ d then (if r = 0 then u j else if r = 1 then Y₁ j c d else Y₂ j c d) else 0

/-- The term constants. -/
def wT3 (u v₁ v₂ : Fin n → ℝ) (j : Fin n) (r : Fin 3) : ℝ :=
  if r = 0 then u j else if r = 1 then v₁ j else v₂ j

variable {u v₁ v₂ : Fin n → ℝ} {Y₁ Y₂ : Fin n → ℕ → ℕ → ℝ}

theorem gT3_nonneg (hu : ∀ j, 0 ≤ u j) (hY₁ : ∀ j c d, 0 ≤ Y₁ j c d)
    (hY₂ : ∀ j c d, 0 ≤ Y₂ j c d) (j : Fin n) (r : Fin 3) (c d : ℕ) : 0 ≤ gT3 u Y₁ Y₂ j r c d := by
  unfold gT3; split_ifs
  · exact hu j
  · exact hY₁ j c d
  · exact hY₂ j c d
  · exact le_rfl

theorem wT3_nonneg (hu : ∀ j, 0 ≤ u j) (hv₁ : ∀ j, 0 ≤ v₁ j) (hv₂ : ∀ j, 0 ≤ v₂ j) (j : Fin n)
    (r : Fin 3) : 0 ≤ wT3 u v₁ v₂ j r := by
  unfold wT3; split_ifs
  · exact hu j
  · exact hv₁ j
  · exact hv₂ j

theorem sum_wT3 (j : Fin n) : ∑ r, wT3 u v₁ v₂ j r = u j + v₁ j + v₂ j := by
  simp [wT3, Fin.sum_univ_three, add_assoc]

theorem sum_gT3_le {S T : Finset ℕ} {E : ℕ → ℕ → ℝ} (j : Fin n) (hE0 : ∀ c d, 0 ≤ E c d)
    (hEY : ∀ c ∈ S, ∀ d ∈ T, c ≠ d → u j + Y₁ j c d + Y₂ j c d ≤ E c d) :
    ∀ c ∈ S, ∀ d ∈ T, ∑ r, gT3 u Y₁ Y₂ j r c d ≤ E c d := fun c hc d hd => by
  rw [Fin.sum_univ_three]
  by_cases hcd : c = d
  · simp only [gT3, hcd, ne_eq, not_true_eq_false, ite_false, add_zero]
    exact hE0 _ _
  · simp only [gT3, ne_eq, hcd, not_false_eq_true, ite_true]
    simpa using hEY c hc d hd hcd

/-- **The pure type of a term table.** -/
theorem gT3_pt {k : ℕ} {S T : Finset ℕ} (j : Fin n) (r : Fin 3) (hY₁ : ∀ c d, 0 ≤ Y₁ j c d)
    (hY₂ : ∀ c d, 0 ≤ Y₂ j c d) (h1 : PP1 k S T (Y₁ j) (v₁ j)) (h2 : PP2 k S T (Y₂ j) (v₂ j)) :
    PT k r S T (gT3 u Y₁ Y₂ j r) (wT3 u v₁ v₂ j r) := by
  refine ⟨fun hr => fun c _ d _ hcd => by simp [gT3, wT3, hr, hcd], fun hr => ?_, fun hr => ?_⟩
  · have e : wT3 u v₁ v₂ j r = v₁ j := by simp [wT3, hr]
    rw [e]
    exact PP1_mono hY₁ (fun c _ d _ hcd => by simp [gT3, hr, hcd]) h1
  · have e : wT3 u v₁ v₂ j r = v₂ j := by simp [wT3, hr]
    rw [e]
    exact PP2_mono hY₂ (fun c _ d _ hcd => by simp [gT3, hr, hcd]) h2

end Terms

/-! ### The expansion of a face -/

theorem faceSum_sumF {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (Li : Fin m → Finset ℕ)
    (G : Fin (m + 1) → ι → ℕ → ℕ → ℝ) (c d : ℕ) :
    faceSum Li (fun _ _ => 1) (fun j c d => ∑ r, G j r c d) c d
      = ∑ ρ : Fin (m + 1) → ι, faceSum Li (fun _ _ => 1) (fun j => G j (ρ j)) c d := by
  unfold faceSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- **The multilinear expansion of a face over three alternatives per side.** -/
theorem mx_expand3 {m : ℕ} {P : Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop} (hP : ConeP P)
    (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ) (E : Fin (m + 1) → ℕ → ℕ → ℝ)
    (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ) (hA : ∀ j, 0 < A j)
    {u v₁ v₂ : Fin (m + 1) → ℝ} {Y₁ Y₂ : Fin (m + 1) → ℕ → ℕ → ℝ}
    (hu : ∀ j, 0 ≤ u j) (hv₁ : ∀ j, 0 ≤ v₁ j) (hv₂ : ∀ j, 0 ≤ v₂ j)
    (huv : ∀ j, A j ≤ u j + v₁ j + v₂ j) (hY₁ : ∀ j c d, 0 ≤ Y₁ j c d)
    (hY₂ : ∀ j c d, 0 ≤ Y₂ j c d)
    (hEY : ∀ j, ∀ c ∈ pathList Lu Lv Li j.castSucc, ∀ d ∈ pathList Lu Lv Li j.succ, c ≠ d →
      u j + Y₁ j c d + Y₂ j c d ≤ E j c d)
    (hterm : ∀ ρ : Fin (m + 1) → Fin 3, (∀ j, 0 < wT3 u v₁ v₂ j (ρ j)) →
      Mx P Lu Lv (faceSum Li (fun _ _ => 1) fun j => gT3 u Y₁ Y₂ j (ρ j))
        (faceConst3 m * ∏ j, wT3 u v₁ v₂ j (ρ j))) :
    Mx P Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  classical
  have hG0 := gT3_nonneg hu hY₁ hY₂
  have hw0 := wT3_nonneg hu hv₁ hv₂
  have hle : ∀ c ∈ Lu, ∀ d ∈ Lv, c ≠ d →
      faceSum Li (fun _ _ => 1) (fun j c d => ∑ r, gT3 u Y₁ Y₂ j r c d) c d
        ≤ faceSum Li (fun _ _ => 1) E c d := fun c hc d hd _ =>
    faceSum_le_of_le (fun j c d => Finset.sum_nonneg fun r _ => hG0 j r c d)
      (fun j => sum_gT3_le j (hE0 j) (hEY j)) hc hd
  refine Mx.mono ?_ hle
  have hfun : faceSum Li (fun _ _ => 1) (fun j c d => ∑ r, gT3 u Y₁ Y₂ j r c d)
      = fun c d => ∑ ρ : Fin (m + 1) → Fin 3,
          faceSum Li (fun _ _ => 1) (fun j => gT3 u Y₁ Y₂ j (ρ j)) c d :=
    funext fun c => funext fun d => faceSum_sumF Li (gT3 u Y₁ Y₂) c d
  rw [hfun]
  have hα := faceConst3_pos m
  have hconst : faceConst3 m * ∏ j, A j
      ≤ ∑ ρ : Fin (m + 1) → Fin 3, faceConst3 m * ∏ j, wT3 u v₁ v₂ j (ρ j) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hα.le
    calc ∏ j, A j ≤ ∏ j, (u j + v₁ j + v₂ j) :=
          Finset.prod_le_prod₀ (fun j _ => (hA j).le) fun j _ => huv j
      _ = ∑ ρ : Fin (m + 1) → Fin 3, ∏ j, wT3 u v₁ v₂ j (ρ j) := by
          simp only [← sum_wT3]
          rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Mx.weaken hconst (Mx.finsum hP univ _ _ (fun ρ _ c d => faceSum_nonneg _ _ _
    (fun _ _ _ => zero_le_one) (fun j c d => hG0 j (ρ j) c d) c d) fun ρ _ => ?_)
  by_cases hz : ∃ j, wT3 u v₁ v₂ j (ρ j) = 0
  · obtain ⟨j, hj⟩ := hz
    rw [Finset.prod_eq_zero (mem_univ j) hj, mul_zero]
    exact Mx.zero hP (faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one)
      (fun j c d => hG0 j (ρ j) c d))
  push Not at hz
  exact hterm ρ fun j => lt_of_le_of_ne (hw0 j (ρ j)) (hz j).symm

/-! ### The square laws by path position -/

section Square

variable {Lu Lv : Finset ℕ} {Li : Fin 2 → Finset ℕ}

theorem faceConst3_two : faceConst3 2 = 3 := by norm_num [faceConst3]

/-- **`[B, M, M]` in any position.** -/
theorem sqLawB (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3) (E : Fin 3 → ℕ → ℕ → ℝ)
    (hE0 : ∀ j c d, 0 ≤ E j c d) (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j) (jB : Fin 3)
    (hB : InBall (pathList Lu Lv Li jB.castSucc) (pathList Lu Lv Li jB.succ) (E jB) (N jB))
    (hM : ∀ j, j ≠ jB →
      BijGe (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (N j) 1) :
    Hex Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 2 * ∏ j, N j) := by
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := pathList_two Lu Lv Li
  rw [faceConst3_two, Fin.prod_univ_three]
  obtain rfl | rfl | rfl : jB = 0 ∨ jB = 1 ∨ jB = 2 := by fin_cases jB <;> simp
  · have h0 : InBall Lu (Li 0) (E 0) (N 0) := by rwa [l0, l1] at hB
    have h1 : BijGe (Li 0) (Li 1) (E 1) (N 1) 1 := by
      have := hM 1 (by decide); rwa [l2, l3] at this
    have h2 : BijGe (Li 1) Lv (E 2) (N 2) 1 := by
      have := hM 2 (by decide); rwa [l4, l5] at this
    exact SqMulti.sq_BMM_hex hLv hLi hE0 hN h0 h1 h2
  · have h0 : BijGe Lu (Li 0) (E 0) (N 0) 1 := by
      have := hM 0 (by decide); rwa [l0, l1] at this
    have h1 : InBall (Li 0) (Li 1) (E 1) (N 1) := by rwa [l2, l3] at hB
    have h2 : BijGe (Li 1) Lv (E 2) (N 2) 1 := by
      have := hM 2 (by decide); rwa [l4, l5] at this
    exact SqMulti.sq_MBM_hex hLv hLi hE0 hN h0 h1 h2
  · have h0 : BijGe Lu (Li 0) (E 0) (N 0) 1 := by
      have := hM 0 (by decide); rwa [l0, l1] at this
    have h1 : BijGe (Li 0) (Li 1) (E 1) (N 1) 1 := by
      have := hM 1 (by decide); rwa [l2, l3] at this
    have h2 : InBall (Li 1) Lv (E 2) (N 2) := by rwa [l4, l5] at hB
    exact SqMulti.sq_MMB_hex hLv hLi hE0 hN h0 h1 h2

/-- **`[H, M, M]` in any position**, at the scale `56/59`. -/
theorem sqLawH (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3) (E : Fin 3 → ℕ → ℕ → ℝ)
    (hE0 : ∀ j c d, 0 ≤ E j c d) (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j) (jH : Fin 3)
    (hH : Hex (pathList Lu Lv Li jH.castSucc) (pathList Lu Lv Li jH.succ) (E jH) (N jH))
    (hM : ∀ j, j ≠ jH →
      BijGe (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (N j) 1) :
    Hex Lu Lv (faceSum Li (fun _ _ => 1) E) (56 / 59 * faceConst3 2 * ∏ j, N j) := by
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := pathList_two Lu Lv Li
  rw [faceConst3_two, Fin.prod_univ_three, show (56 / 59 : ℝ) * 3 = 3 * (56 / 59) by ring]
  obtain rfl | rfl | rfl : jH = 0 ∨ jH = 1 ∨ jH = 2 := by fin_cases jH <;> simp
  · have h0 : Hex Lu (Li 0) (E 0) (N 0) := by rwa [l0, l1] at hH
    have h1 : BijGe (Li 0) (Li 1) (E 1) (N 1) 1 := by
      have := hM 1 (by decide); rwa [l2, l3] at this
    have h2 : BijGe (Li 1) Lv (E 2) (N 2) 1 := by
      have := hM 2 (by decide); rwa [l4, l5] at this
    exact SqMulti.sq_HMM_hex hLv hLi hE0 hN h0 h1 h2
  · have h0 : BijGe Lu (Li 0) (E 0) (N 0) 1 := by
      have := hM 0 (by decide); rwa [l0, l1] at this
    have h1 : Hex (Li 0) (Li 1) (E 1) (N 1) := by rwa [l2, l3] at hH
    have h2 : BijGe (Li 1) Lv (E 2) (N 2) 1 := by
      have := hM 2 (by decide); rwa [l4, l5] at this
    exact SqMulti.sq_MHM_hex hLv hLi hE0 hN h0 h1 h2
  · have h0 : BijGe Lu (Li 0) (E 0) (N 0) 1 := by
      have := hM 0 (by decide); rwa [l0, l1] at this
    have h1 : BijGe (Li 0) (Li 1) (E 1) (N 1) 1 := by
      have := hM 1 (by decide); rwa [l2, l3] at this
    have h2 : Hex (Li 1) Lv (E 2) (N 2) := by rwa [l4, l5] at hH
    exact SqMulti.sq_MMH_hex hLv hLi hE0 hN h0 h1 h2

/-- **`[B, B, B]`**, at the scale `(16/17)²`. -/
theorem sqLawBBB (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3) (E : Fin 3 → ℕ → ℕ → ℝ)
    (hE0 : ∀ j c d, 0 ≤ E j c d) (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (hB : ∀ j, InBall (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (N j)) :
    Hex Lu Lv (faceSum Li (fun _ _ => 1) E) ((16 / 17) ^ 2 * faceConst3 2 * ∏ j, N j) := by
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := pathList_two Lu Lv Li
  rw [faceConst3_two, Fin.prod_univ_three, show ((16 / 17 : ℝ)) ^ 2 * 3 = 3 * (16 / 17) ^ 2 by
    ring]
  have h0 : InBall Lu (Li 0) (E 0) (N 0) := by have := hB 0; rwa [l0, l1] at this
  have h1 : InBall (Li 0) (Li 1) (E 1) (N 1) := by have := hB 1; rwa [l2, l3] at this
  have h2 : InBall (Li 1) Lv (E 2) (N 2) := by have := hB 2; rwa [l4, l5] at this
  exact SqMulti.sq_BBB_hex hLv hLi hE0 hN h0 h1 h2

/-- **`[H, H, H]`**, at the scale `(16/17)⁴`. -/
theorem sqLawHHH (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3) (E : Fin 3 → ℕ → ℕ → ℝ)
    (hE0 : ∀ j c d, 0 ≤ E j c d) (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (hH : ∀ j, Hex (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (N j)) :
    Hex Lu Lv (faceSum Li (fun _ _ => 1) E) ((16 / 17) ^ 4 * faceConst3 2 * ∏ j, N j) := by
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := pathList_two Lu Lv Li
  rw [faceConst3_two, Fin.prod_univ_three, show ((16 / 17 : ℝ)) ^ 4 * 3 = 3 * (16 / 17) ^ 4 by
    ring]
  have h0 : Hex Lu (Li 0) (E 0) (N 0) := by have := hH 0; rwa [l0, l1] at this
  have h1 : Hex (Li 0) (Li 1) (E 1) (N 1) := by have := hH 1; rwa [l2, l3] at this
  have h2 : Hex (Li 1) Lv (E 2) (N 2) := by have := hH 2; rwa [l4, l5] at this
  exact SqMulti.sq_HHH_hex hLv hLi hE0 hN h0 h1 h2

end Square

end Outerplanar
