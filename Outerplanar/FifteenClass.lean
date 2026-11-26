/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.MarkFiveSix

/-!
# The mark classes of the fifteen-face theorem, with the floors of Lemma F

Research note `ai_research_notes/OUTERPLANAR_FIFTEEN_EVEN_2026-11-25.md` (with
`ai_research_notes/outerplanar/fivemarks/results.md`): a branch with `k ≤ 7` marks dominates a
mixture of the constant one and of *alternatives*, and every alternative has every proper entry at
least `(2/3)^k` times its constant (**Lemma F**). The alternatives of `k` marks:

* `k = 1, 2`: the tables `P1`, `P2` of `Outerplanar/MarkOne.lean`, `Outerplanar/MarkTwo.lean`
  (they carry the floors `2/3`, `4/9`);
* `k = 3`: `A B` with floor (`Q3f`); `k = 4`: `B ∩ A H` with floor (`Q4f`); `k = 5`: `B` with floor;
* `k = 6`: `B` or `A^{4/3} H`, `k = 7`: `B` or `D₆ H`, with floors (`QBf`, `QHf`).

`PA k` is the first alternative, `PB k` the second (absent below six marks), and
**`Kc15 k`** the class (`Dominant` for no marks). This file has the closure of the classes:
`Kc15_mono`, `Kc15_swap`, `Kc15_lift`, `Kc15_mono_table`, `Kc15_mul_dom`, `Kc15_hex`,
`Kc15_nonneg_mul` (products of branches with at most seven marks in all) and the vertex rule
`markVertex15_sound`. The face rule is in `Outerplanar/FifteenRule.lean`.

Formalized by Claude (milestone M5 of `ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`).
-/

namespace Outerplanar.F15

open Finset Outerplanar

/-! ### Floors -/

/-- The floor of Lemma F. -/
noncomputable def fl (k : ℕ) : ℝ := (2 / 3) ^ k

theorem fl_pos (k : ℕ) : 0 < fl k := by unfold fl; positivity

theorem fl_le_one (k : ℕ) : fl k ≤ 1 := by unfold fl; exact pow_le_one₀ (by norm_num) (by norm_num)

theorem fl_add (a b : ℕ) : fl (a + b) = fl a * fl b := by unfold fl; rw [pow_add]

theorem fl_anti {a b : ℕ} (h : a ≤ b) : fl b ≤ fl a := by
  unfold fl; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h

theorem fl_succ (k : ℕ) : fl (k + 1) = 2 / 3 * fl k := by unfold fl; rw [pow_succ]; ring

/-! ### Cones -/

section Cones

variable {P Q : Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop}

theorem _root_.Outerplanar.ConeP.and (hP : ConeP P) (hQ : ConeP Q) :
    ConeP fun S T Y v => P S T Y v ∧ Q S T Y v where
  zero S T := ⟨hP.zero S T, hQ.zero S T⟩
  add := fun hv hv' h0 h0' h h' => ⟨hP.add hv hv' h0 h0' h.1 h'.1, hQ.add hv hv' h0 h0' h.2 h'.2⟩
  smul := fun l hl hv h0 h => ⟨hP.smul l hl hv h0 h.1, hQ.smul l hl hv h0 h.2⟩
  mono := fun h0 hle h => ⟨hP.mono h0 hle h.1, hQ.mono h0 hle h.2⟩
  weaken := fun hv' hle h0 h => ⟨hP.weaken hv' hle h0 h.1, hQ.weaken hv' hle h0 h.2⟩

theorem coneDom {c : ℝ} (hc : 0 ≤ c) : ConeP fun S T Y v => Dominant S T Y (c * v) where
  zero _ _ := fun _ _ _ _ _ => by simp
  add := by
    intro S T Y Y' v v' _ _ _ _ h h'
    have := Dominant.add h h'
    rwa [show c * v + c * v' = c * (v + v') by ring] at this
  smul := by
    intro S T Y v l hl _ _ h
    have := Dominant.smul hl h
    rwa [show l * (c * v) = c * (l * v) by ring] at this
  mono := fun _ hle h => Dominant.mono h hle
  weaken := fun _ hle _ h => h.le (mul_le_mul_of_nonneg_left hle hc)

theorem coneV0 : ConeP fun (_ _ : Finset ℕ) (_ : ℕ → ℕ → ℝ) (v : ℝ) => v = 0 where
  zero _ _ := rfl
  add := fun _ _ _ _ h h' => by rw [h, h', add_zero]
  smul := fun _ _ _ _ h => by rw [h, mul_zero]
  mono := fun _ _ h => h
  weaken := fun hv' hle _ h => le_antisymm (h ▸ hle) hv'

end Cones

/-! ### The alternatives -/

/-- Three marks: `A B` with floor `(2/3)³`. -/
def Q3f (S T : Finset ℕ) (Y : ℕ → ℕ → ℝ) (v : ℝ) : Prop := P3 S T Y v ∧ Dominant S T Y (fl 3 * v)

/-- Four marks: `B ∩ A H` with floor `(2/3)⁴`. -/
def Q4f (S T : Finset ℕ) (Y : ℕ → ℕ → ℝ) (v : ℝ) : Prop := P4 S T Y v ∧ Dominant S T Y (fl 4 * v)

/-- The ball part with floor `(2/3)^k`. -/
def QBf (k : ℕ) (S T : Finset ℕ) (Y : ℕ → ℕ → ℝ) (v : ℝ) : Prop :=
  InBall S T Y v ∧ Dominant S T Y (fl k * v)

/-- The hexagon part with scale `κ` and floor `(2/3)^k`. -/
def QHf (κ : ℝ) (k : ℕ) (S T : Finset ℕ) (Y : ℕ → ℕ → ℝ) (v : ℝ) : Prop :=
  Hex S T Y (v * κ) ∧ Dominant S T Y (fl k * v)

theorem coneQ3 : ConeP Q3f := Outerplanar.ConeP.and cone3 (coneDom (fl_pos 3).le)

theorem coneQ4 : ConeP Q4f := Outerplanar.ConeP.and cone4 (coneDom (fl_pos 4).le)

theorem coneQB (k : ℕ) : ConeP (QBf k) := Outerplanar.ConeP.and coneB (coneDom (fl_pos k).le)

theorem coneQH {κ : ℝ} (hκ : 0 ≤ κ) (k : ℕ) : ConeP (QHf κ k) :=
  Outerplanar.ConeP.and (coneH hκ) (coneDom (fl_pos k).le)

/-- **The first alternative of `k` marks.** -/
def PA : ℕ → Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop
  | 0 => fun _ _ _ v => v = 0
  | 1 => P1
  | 2 => P2
  | 3 => Q3f
  | 4 => Q4f
  | 5 => QBf 5
  | 6 => QBf 6
  | _ => QBf 7

/-- **The second alternative of `k` marks.** -/
def PB : ℕ → Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop
  | 0 => fun _ _ _ v => v = 0
  | 1 => fun _ _ _ v => v = 0
  | 2 => fun _ _ _ v => v = 0
  | 3 => fun _ _ _ v => v = 0
  | 4 => fun _ _ _ v => v = 0
  | 5 => fun _ _ _ v => v = 0
  | 6 => QHf a5 6
  | _ => QHf d6 7

theorem PA_seven {k : ℕ} (hk : 7 ≤ k) : PA k = QBf 7 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 7 := ⟨k - 7, by omega⟩
  rfl

theorem PB_seven {k : ℕ} (hk : 7 ≤ k) : PB k = QHf d6 7 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 7 := ⟨k - 7, by omega⟩
  rfl

theorem PB_low {k : ℕ} (hk : k ≤ 5) {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} :
    PB k S T Y v ↔ v = 0 := by
  interval_cases k <;> rfl

theorem conePA (k : ℕ) : ConeP (PA k) := by
  rcases Nat.lt_or_ge k 7 with hk | hk
  · interval_cases k
    · exact coneV0
    · exact cone1
    · exact cone2
    · exact coneQ3
    · exact coneQ4
    · exact coneQB 5
    · exact coneQB 6
  · rw [PA_seven hk]; exact coneQB 7

theorem conePB (k : ℕ) : ConeP (PB k) := by
  rcases Nat.lt_or_ge k 6 with hk | hk
  · interval_cases k <;> exact coneV0
  rcases Nat.lt_or_ge k 7 with hk' | hk'
  · obtain rfl : k = 6 := by omega
    exact coneQH a5_pos.le 6
  · rw [PB_seven hk']; exact coneQH d6_pos.le 7

/-! ### Facts of the alternatives -/

theorem _root_.Outerplanar.ConeP.of_zero {P : Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop}
    (hP : ConeP P)
    {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} (h0 : ∀ c d, 0 ≤ Y c d) : P S T Y 0 :=
  hP.mono (fun _ _ => le_rfl) (fun c _ d _ _ => h0 c d) (hP.zero S T)

section Facts

variable {S T U : Finset ℕ} {Y Y' : ℕ → ℕ → ℝ} {v v' : ℝ} {k : ℕ}

theorem PA_floor (hv : 0 ≤ v) (hk : 1 ≤ k) (h : PA k S T Y v) : Dominant S T Y (fl k * v) := by
  rcases Nat.lt_or_ge k 7 with hk7 | hk7
  · interval_cases k
    · exact h.1.le (le_of_eq (by unfold fl; ring))
    · exact h.1.le (le_of_eq (by unfold fl; ring))
    · exact h.2
    · exact h.2
    · exact h.2
    · exact h.2
  · rw [PA_seven hk7] at h
    exact h.2.le (mul_le_mul_of_nonneg_right (fl_anti hk7) hv)

theorem PB_floor (hv : 0 ≤ v) (h0 : ∀ c d, 0 ≤ Y c d) (h : PB k S T Y v) :
    Dominant S T Y (fl k * v) := by
  rcases Nat.lt_or_ge k 6 with hk | hk
  · rw [(PB_low (by omega)).mp h, mul_zero]; exact fun c _ d _ _ => h0 c d
  rcases Nat.lt_or_ge k 7 with hk' | hk'
  · obtain rfl : k = 6 := by omega
    exact h.2
  · rw [PB_seven hk'] at h
    exact h.2.le (mul_le_mul_of_nonneg_right (fl_anti hk') hv)

theorem PA_ball (hv : 0 ≤ v) (hk : 1 ≤ k) (h : PA k S T Y v) : InBall S T Y v := by
  rcases Nat.lt_or_ge k 7 with hk7 | hk7
  · interval_cases k
    · exact h.2.2.2.1.weaken hv (by linarith)
    · exact h.2.2.2.weaken hv (by linarith)
    · exact InBall.weaken hv (by linarith) h.1
    · exact h.1.1
    · exact h.1
    · exact h.1
  · rw [PA_seven hk7] at h; exact h.1

theorem PA_ballA (hk1 : 1 ≤ k) (hk3 : k ≤ 3) (h : PA k S T Y v) :
    InBall S T Y (v * (17 / 16)) := by
  interval_cases k
  · exact h.2.2.2.1
  · exact h.2.2.2
  · exact h.1

theorem PA_hexA (hv : 0 ≤ v) (h0 : ∀ c d, 0 ≤ Y c d) (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (h : PA k S T Y v) : Hex S T Y (v * (17 / 16)) := by
  rcases Nat.lt_or_ge k 4 with hk | hk
  · exact fun _ _ hm hpq => (PA_ballA hk1 (by omega) h).hex (by positivity) h0 hm hpq
  · obtain rfl : k = 4 := by omega
    exact h.1.2

theorem PA_hex (hv : 0 ≤ v) (h0 : ∀ c d, 0 ≤ Y c d) (hk : 1 ≤ k) (h : PA k S T Y v) :
    Hex S T Y v := fun _ _ hm hpq => (PA_ball hv hk h).hex hv h0 hm hpq

theorem PB_hexD (hv : 0 ≤ v) (hk : 6 ≤ k) (h : PB k S T Y v) : Hex S T Y (v * d6) := by
  rcases Nat.lt_or_ge k 7 with hk' | hk'
  · obtain rfl : k = 6 := by omega
    exact h.1.weaken (by have := d6_pos; positivity) (mul_le_mul_of_nonneg_left d6_le_a5 hv)
  · rw [PB_seven hk'] at h; exact h.1

theorem PB_hex (hv : 0 ≤ v) (h0 : ∀ c d, 0 ≤ Y c d) (h : PB k S T Y v) : Hex S T Y v := by
  rcases Nat.lt_or_ge k 6 with hk | hk
  · rw [(PB_low (by omega)).mp h]
    exact Dominant.hex (fun c _ d _ _ => h0 c d) le_rfl
  · exact (PB_hexD hv hk h).weaken hv (by nlinarith [one_le_d6])

theorem PA_succ (hv : 0 ≤ v) (h0 : ∀ c d, 0 ≤ Y c d) (h : PA k S T Y v) : PA (k + 1) S T Y v := by
  rcases Nat.lt_or_ge k 7 with hk7 | hk7
  · interval_cases k
    · show P1 S T Y v
      rw [show v = 0 from h]; exact cone1.of_zero h0
    · exact p1_p2 hv h
    · exact ⟨p2_p3 h, h.1.le (by unfold fl; nlinarith)⟩
    · exact ⟨p3_p4 hv h0 h.1, h.2.le (by unfold fl; nlinarith)⟩
    · exact ⟨h.1.1, h.2.le (by unfold fl; nlinarith)⟩
    · exact ⟨h.1, h.2.le (by unfold fl; nlinarith)⟩
    · exact ⟨h.1, h.2.le (by unfold fl; nlinarith)⟩
  · rw [PA_seven hk7] at h; rw [PA_seven (by omega)]; exact h

theorem PB_succ (hv : 0 ≤ v) (h0 : ∀ c d, 0 ≤ Y c d) (h : PB k S T Y v) : PB (k + 1) S T Y v := by
  rcases Nat.lt_or_ge k 5 with hk | hk
  · exact (PB_low (by omega)).mpr ((PB_low (by omega)).mp h)
  rcases Nat.lt_or_ge k 6 with hk' | hk'
  · obtain rfl : k = 5 := by omega
    show QHf a5 6 S T Y v
    rw [(PB_low le_rfl).mp h]; exact (coneQH a5_pos.le 6).of_zero h0
  rcases Nat.lt_or_ge k 7 with hk'' | hk''
  · obtain rfl : k = 6 := by omega
    exact ⟨h.1.weaken (by have := d6_pos; positivity) (mul_le_mul_of_nonneg_left d6_le_a5 hv),
      h.2.le (by unfold fl; nlinarith)⟩
  · rw [PB_seven hk''] at h; rw [PB_seven (by omega)]; exact h

theorem PA_swap (h : PA k S T Y v) : PA k T S (fun d c => Y c d) v := by
  rcases Nat.lt_or_ge k 7 with hk7 | hk7
  · interval_cases k
    · exact h
    · exact p1_swap h
    · exact p2_swap h
    · exact ⟨InBall.swap h.1, h.2.swap⟩
    · exact ⟨p4_swap h.1, h.2.swap⟩
    · exact ⟨h.1.swap, h.2.swap⟩
    · exact ⟨h.1.swap, h.2.swap⟩
  · rw [PA_seven hk7] at h ⊢; exact ⟨h.1.swap, h.2.swap⟩

theorem PB_swap (h : PB k S T Y v) : PB k T S (fun d c => Y c d) v := by
  rcases Nat.lt_or_ge k 6 with hk | hk
  · exact (PB_low (by omega)).mpr ((PB_low (by omega)).mp h)
  rcases Nat.lt_or_ge k 7 with hk' | hk'
  · obtain rfl : k = 6 := by omega
    exact ⟨h.1.swap', h.2.swap⟩
  · rw [PB_seven hk'] at h ⊢; exact ⟨h.1.swap', h.2.swap⟩

theorem dom_lift {c : ℝ} (hc : 0 ≤ c) (hv : 0 ≤ v) (hT : T.card = 3)
    (h : Dominant S T Y (c * v)) : Dominant S U (fun x _ => liftV T Y x) (c * (2 * v)) := by
  have := lift_dom (U := U) (by positivity) hT h
  rwa [show 2 * (c * v) = c * (2 * v) by ring] at this

theorem PA_lift (hS : S.card = 3) (hT : T.card = 3) (hU : U.card = 3) (hv : 0 ≤ v)
    (h0 : ∀ c d, 0 ≤ Y c d) (h : PA k S T Y v) : PA k S U (fun c _ => liftV T Y c) (2 * v) := by
  have hb : ∀ {κ : ℝ}, 0 ≤ κ → InBall S T Y (v * κ) →
      InBall S U (fun c _ => liftV T Y c) (2 * v * κ) := fun {κ} hκ hB => by
    have := lift_ball (U := U) hS hT hU h0 (by positivity) hB
    rwa [show 2 * (v * κ) = 2 * v * κ by ring] at this
  have hh : ∀ {κ : ℝ}, 0 ≤ κ → Hex S T Y (v * κ) →
      Hex S U (fun c _ => liftV T Y c) (2 * v * κ) := fun {κ} hκ hH => by
    have := lift_hex (U := U) hS hT h0 (by positivity) hH
    rwa [show 2 * (v * κ) = 2 * v * κ by ring] at this
  rcases Nat.lt_or_ge k 7 with hk7 | hk7
  · interval_cases k
    · show 2 * v = 0
      rw [show v = 0 from h, mul_zero]
    · exact p1_lift hS hT hU hv h0 h
    · exact p2_lift hS hT hU hv h0 h
    · exact ⟨hb (by norm_num) h.1, dom_lift (fl_pos _).le hv hT h.2⟩
    · refine ⟨⟨?_, hh (by norm_num) h.1.2⟩, dom_lift (fl_pos _).le hv hT h.2⟩
      simpa using hb zero_le_one (by simpa using h.1.1)
    · exact ⟨by simpa using hb zero_le_one (by simpa using h.1), dom_lift (fl_pos _).le hv hT h.2⟩
    · exact ⟨by simpa using hb zero_le_one (by simpa using h.1), dom_lift (fl_pos _).le hv hT h.2⟩
  · rw [PA_seven hk7] at h ⊢
    exact ⟨by simpa using hb zero_le_one (by simpa using h.1), dom_lift (fl_pos _).le hv hT h.2⟩

theorem PB_lift (hS : S.card = 3) (hT : T.card = 3) (hv : 0 ≤ v)
    (h0 : ∀ c d, 0 ≤ Y c d) (h : PB k S T Y v) : PB k S U (fun c _ => liftV T Y c) (2 * v) := by
  have hh : ∀ {κ : ℝ}, 0 ≤ κ → Hex S T Y (v * κ) →
      Hex S U (fun c _ => liftV T Y c) (2 * v * κ) := fun {κ} hκ hH => by
    have := lift_hex (U := U) hS hT h0 (by positivity) hH
    rwa [show 2 * (v * κ) = 2 * v * κ by ring] at this
  rcases Nat.lt_or_ge k 6 with hk | hk
  · rw [PB_low (by omega)] at h ⊢; rw [h, mul_zero]
  rcases Nat.lt_or_ge k 7 with hk' | hk'
  · obtain rfl : k = 6 := by omega
    exact ⟨hh a5_pos.le h.1, dom_lift (fl_pos _).le hv hT h.2⟩
  · rw [PB_seven hk'] at h ⊢
    exact ⟨hh d6_pos.le h.1, dom_lift (fl_pos _).le hv hT h.2⟩

end Facts

/-! ### Two alternatives -/

section Alt

variable {P Q P' Q' R : Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop}
  {S T U : Finset ℕ} {Y Y' W : ℕ → ℕ → ℝ} {v v' N : ℝ}

theorem alt_swap (hp : ∀ {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ}, P S T Y v →
      P T S (fun d c => Y c d) v)
    (hq : ∀ {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ}, Q S T Y v → Q T S (fun d c => Y c d) v)
    (h : Alt2 P Q S T Y v) : Alt2 P Q T S (fun d c => Y c d) v := by
  obtain ⟨Y₁, Y₂, v₁, v₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨fun d c => Y₁ c d, fun d c => Y₂ c d, v₁, v₂, h1, h2, h3, fun _ _ => h4 _ _,
    fun _ _ => h5 _ _, fun d hd c hc hdc => h6 c hc d hd (Ne.symm hdc), hp h7, hq h8⟩

theorem alt_lift
    (hp : ∀ {Y : ℕ → ℕ → ℝ} {v : ℝ}, 0 ≤ v → (∀ c d, 0 ≤ Y c d) → P S T Y v →
      P S U (fun c _ => liftV T Y c) (2 * v))
    (hq : ∀ {Y : ℕ → ℕ → ℝ} {v : ℝ}, 0 ≤ v → (∀ c d, 0 ≤ Y c d) → Q S T Y v →
      Q S U (fun c _ => liftV T Y c) (2 * v))
    (h : Alt2 P Q S T Y v) : Alt2 P Q S U (fun c _ => liftV T Y c) (2 * v) := by
  obtain ⟨Y₁, Y₂, v₁, v₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨fun c _ => liftV T Y₁ c, fun c _ => liftV T Y₂ c, 2 * v₁, 2 * v₂, by positivity,
    by positivity, by rw [← h3]; ring, fun c _ => liftV_nonneg h4 c, fun c _ => liftV_nonneg h5 c,
    fun c hc d _ _ => ?_, hp h1 h4 h7, hq h2 h5 h8⟩
  rw [← liftV_add]
  exact liftV_mono_proper hc h6

theorem alt_hex
    (hp : ∀ {Y : ℕ → ℕ → ℝ} {v : ℝ}, 0 ≤ v → (∀ c d, 0 ≤ Y c d) → P S T Y v → Hex S T Y v)
    (hq : ∀ {Y : ℕ → ℕ → ℝ} {v : ℝ}, 0 ≤ v → (∀ c d, 0 ≤ Y c d) → Q S T Y v → Hex S T Y v)
    (h0 : ∀ c d, 0 ≤ Y c d) (h : Alt2 P Q S T Y v) : Hex S T Y v := by
  obtain ⟨Y₁, Y₂, v₁, v₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have := Hex.add h1 h2 h4 h5 (hp h1 h4 h7) (hq h2 h5 h8)
  rw [h3] at this
  exact this.mono (fun c d => add_nonneg (h4 c d) (h5 c d)) h6

theorem mx_hex
    (hp : ∀ {Y : ℕ → ℕ → ℝ} {v : ℝ}, 0 ≤ v → (∀ c d, 0 ≤ Y c d) → P S T Y v → Hex S T Y v)
    (hN : 0 ≤ N) (h : Mx P S T W N) : Hex S T W N := by
  obtain ⟨u, v, Y, hu, hv, hNuv, hY0, hY, hW⟩ := h
  have h1 : Hex S T (fun c d => if c ≠ d then u else 0) u :=
    Dominant.hex (fun c _ d _ hcd => by simp [hcd]) hu
  have h2 := Hex.add hu hv (fun c d => by split_ifs <;> simp [hu]) hY0 h1 (hp hv hY0 hY)
  refine (h2.mono (fun c d => add_nonneg (by split_ifs <;> simp [hu]) (hY0 c d))
    fun c hc d hd hcd => ?_).weaken hN hNuv
  simpa [hcd] using hW c hc d hd hcd

/-- Products of two-alternative tables, term by term. -/
theorem alt_mul (hR : ConeP R)
    (h11 : ∀ {X X' : ℕ → ℕ → ℝ} {x x' : ℝ}, 0 ≤ x → 0 ≤ x' → (∀ c d, 0 ≤ X c d) →
      (∀ c d, 0 ≤ X' c d) → P S T X x → P' S T X' x' → R S T (fun c d => X c d * X' c d) (x * x'))
    (h12 : ∀ {X X' : ℕ → ℕ → ℝ} {x x' : ℝ}, 0 ≤ x → 0 ≤ x' → (∀ c d, 0 ≤ X c d) →
      (∀ c d, 0 ≤ X' c d) → P S T X x → Q' S T X' x' → R S T (fun c d => X c d * X' c d) (x * x'))
    (h21 : ∀ {X X' : ℕ → ℕ → ℝ} {x x' : ℝ}, 0 ≤ x → 0 ≤ x' → (∀ c d, 0 ≤ X c d) →
      (∀ c d, 0 ≤ X' c d) → Q S T X x → P' S T X' x' → R S T (fun c d => X c d * X' c d) (x * x'))
    (h22 : ∀ {X X' : ℕ → ℕ → ℝ} {x x' : ℝ}, 0 ≤ x → 0 ≤ x' → (∀ c d, 0 ≤ X c d) →
      (∀ c d, 0 ≤ X' c d) → Q S T X x → Q' S T X' x' → R S T (fun c d => X c d * X' c d) (x * x'))
    (h0 : ∀ c d, 0 ≤ Y c d) (h0' : ∀ c d, 0 ≤ Y' c d)
    (h : Alt2 P Q S T Y v) (h' : Alt2 P' Q' S T Y' v') :
    R S T (fun c d => Y c d * Y' c d) (v * v') := by
  obtain ⟨Y₁, Y₂, v₁, v₂, a1, a2, a3, a4, a5', a6, a7, a8⟩ := h
  obtain ⟨Z₁, Z₂, w₁, w₂, b1, b2, b3, b4, b5, b6, b7, b8⟩ := h'
  have e11 := h11 a1 b1 a4 b4 a7 b7
  have e12 := h12 a1 b2 a4 b5 a7 b8
  have e21 := h21 a2 b1 a5' b4 a8 b7
  have e22 := h22 a2 b2 a5' b5 a8 b8
  have n11 : ∀ c d, 0 ≤ Y₁ c d * Z₁ c d := fun c d => mul_nonneg (a4 c d) (b4 c d)
  have n12 : ∀ c d, 0 ≤ Y₁ c d * Z₂ c d := fun c d => mul_nonneg (a4 c d) (b5 c d)
  have n21 : ∀ c d, 0 ≤ Y₂ c d * Z₁ c d := fun c d => mul_nonneg (a5' c d) (b4 c d)
  have n22 : ∀ c d, 0 ≤ Y₂ c d * Z₂ c d := fun c d => mul_nonneg (a5' c d) (b5 c d)
  have s1 := hR.add (by positivity) (by positivity) n11 n12 e11 e12
  have s2 := hR.add (by positivity) (by positivity) n21 n22 e21 e22
  have s3 := hR.add (by positivity) (by positivity) (fun c d => add_nonneg (n11 c d) (n12 c d))
    (fun c d => add_nonneg (n21 c d) (n22 c d)) s1 s2
  have ev : v * v' = v₁ * w₁ + v₁ * w₂ + (v₂ * w₁ + v₂ * w₂) := by rw [← a3, ← b3]; ring
  rw [ev]
  refine hR.mono (fun c d => add_nonneg (add_nonneg (n11 c d) (n12 c d))
    (add_nonneg (n21 c d) (n22 c d))) (fun c hc d hd hcd => ?_) s3
  have q1 := a6 c hc d hd hcd
  have q2 := b6 c hc d hd hcd
  have := a4 c d; have := a5' c d; have := b4 c d; have := b5 c d
  calc Y₁ c d * Z₁ c d + Y₁ c d * Z₂ c d + (Y₂ c d * Z₁ c d + Y₂ c d * Z₂ c d)
      = (Y₁ c d + Y₂ c d) * (Z₁ c d + Z₂ c d) := by ring
    _ ≤ Y c d * Y' c d := mul_le_mul q1 q2 (by positivity) (h0 c d)

end Alt

/-! ### The classes -/

/-- The two alternatives of `k` marks. -/
def AP (k : ℕ) : Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop := Alt2 (PA k) (PB k)

theorem coneAP (k : ℕ) : ConeP (AP k) := coneAlt2 (conePA k) (conePB k)

/-- **The class of a branch with `k` marks.** -/
def Kc15 : ℕ → Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop
  | 0 => Dominant
  | k + 1 => Mx (AP (k + 1))

section Kc15

variable {S T U : Finset ℕ} {W W' : ℕ → ℕ → ℝ} {N N' : ℝ} {k : ℕ}

theorem Kc15_pos (hk : 1 ≤ k) : Kc15 k = Mx (AP k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl

theorem AP_succ {Y : ℕ → ℕ → ℝ} {v : ℝ} (hv : 0 ≤ v) (h0 : ∀ c d, 0 ≤ Y c d) (h : AP k S T Y v) :
    AP (k + 1) S T Y v :=
  Alt2.imp (fun hv h0 h => PA_succ hv h0 h) (fun hv h0 h => PB_succ hv h0 h) h

theorem AP_mono {Y : ℕ → ℕ → ℝ} {v : ℝ} (hv : 0 ≤ v) (h0 : ∀ c d, 0 ≤ Y c d) {a b : ℕ}
    (hab : a ≤ b) (h : AP a S T Y v) : AP b S T Y v := by
  induction b, hab using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact AP_succ hv h0 ih

theorem Kc15_succ (hN : 0 ≤ N) (h : Kc15 k S T W N) : Kc15 (k + 1) S T W N := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Mx.of_dom (coneAP 1) hN h
  · rw [Kc15_pos hk] at h
    rw [Kc15_pos (by omega)]
    exact Mx.imp (fun hv h0 h => AP_succ hv h0 h) h

theorem Kc15_mono (hN : 0 ≤ N) {a b : ℕ} (hab : a ≤ b) (h : Kc15 a S T W N) :
    Kc15 b S T W N := by
  induction b, hab using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact Kc15_succ hN ih

theorem Kc15_of_dom (hN : 0 ≤ N) (h : Dominant S T W N) : Kc15 k S T W N :=
  Kc15_mono (a := 0) hN (Nat.zero_le k) h

theorem Kc15_swap (h : Kc15 k S T W N) : Kc15 k T S (fun d c => W c d) N := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Dominant.swap h
  · rw [Kc15_pos hk] at h ⊢
    exact Mx.swap (fun h => alt_swap (fun h => PA_swap h) (fun h => PB_swap h) h) h

theorem Kc15_lift (hS : S.card = 3) (hT : T.card = 3) (hU : U.card = 3) (hN : 0 ≤ N)
    (h : Kc15 k S T W N) : Kc15 k S U (fun c _ => liftV T W c) (2 * N) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact lift_dom hN hT h
  · rw [Kc15_pos hk] at h ⊢
    exact Mx.lift (fun _ _ h => alt_lift (fun hv h0 h => PA_lift hS hT hU hv h0 h)
      (fun hv h0 h => PB_lift hS hT hv h0 h) h) hT h

theorem Kc15_mono_table (hle : ∀ c ∈ S, ∀ d ∈ T, c ≠ d → W c d ≤ W' c d)
    (h : Kc15 k S T W N) : Kc15 k S T W' N := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Dominant.mono h hle
  · rw [Kc15_pos hk] at h ⊢
    exact Mx.mono h hle

theorem Kc15_mul_dom (hN : 0 ≤ N) (hN' : 0 ≤ N') (hW0 : ∀ c d, 0 ≤ W c d)
    (hd : Dominant S T W' N') (h : Kc15 k S T W N) :
    Kc15 k S T (fun c d => W' c d * W c d) (N' * N) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Dominant.mul hN' hN hd h
  · rw [Kc15_pos hk] at h ⊢
    exact Mx.mul_dom (coneAP k) hN' hW0 hd h

theorem AP_hex {Y : ℕ → ℕ → ℝ} {v : ℝ} (hv : 0 ≤ v) (h0 : ∀ c d, 0 ≤ Y c d) (hk : 1 ≤ k)
    (h : AP k S T Y v) : Hex S T Y v :=
  alt_hex (fun hv h0 h => PA_hex hv h0 hk h) (fun hv h0 h => PB_hex hv h0 h) h0 h

/-- **Every class has the hexagon bound** with its constant. -/
theorem Kc15_hex (hN : 0 ≤ N) (h0 : ∀ c d, 0 ≤ W c d) (h : Kc15 k S T W N) : Hex S T W N := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Dominant.hex h hN
  · rw [Kc15_pos hk] at h
    exact mx_hex (fun hv h0 h => AP_hex hv h0 hk h) hN h

/-- Below three marks the classes are those of `Outerplanar/MarkThreeFour.lean`. -/
theorem Kc15_of_kc (hk : k ≤ 2) (h : Kc k S T W N) : Kc15 k S T W N := by
  interval_cases k
  · exact h
  · exact Mx.imp (fun hv h0 h => Alt2.of_left coneV0 hv h0 h) h
  · exact Mx.imp (fun hv h0 h => Alt2.of_left coneV0 hv h0 h) h

theorem alt_left {P : Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop} (hP : ConeP P)
    {Y : ℕ → ℕ → ℝ} {v : ℝ}
    (h : Alt2 P (fun (_ _ : Finset ℕ) (_ : ℕ → ℕ → ℝ) (v : ℝ) => v = 0) S T Y v) : P S T Y v := by
  obtain ⟨Y₁, Y₂, v₁, v₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  rw [← h3, show v₂ = 0 from h8, add_zero]
  exact hP.mono h4 (fun c hc d hd hcd => le_trans (le_add_of_nonneg_right (h5 c d))
    (h6 c hc d hd hcd)) h7

theorem kc_of_Kc15 (hk : k ≤ 2) (h : Kc15 k S T W N) : Kc k S T W N := by
  interval_cases k
  · exact h
  · exact Mx.imp (fun _ _ h => alt_left cone1 h) h
  · exact Mx.imp (fun _ _ h => alt_left cone2 h) h

/-! ### Products -/

theorem PA_mul {a b : ℕ} {X X' : ℕ → ℕ → ℝ} {x x' : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b ≤ 7)
    (hx : 0 ≤ x) (hx' : 0 ≤ x') (h0 : ∀ c d, 0 ≤ X c d) (h0' : ∀ c d, 0 ≤ X' c d)
    (h : PA a S T X x) (h' : PA b S T X' x') :
    PA (a + b) S T (fun c d => X c d * X' c d) (x * x') := by
  have hfl : Dominant S T (fun c d => X c d * X' c d) (fl (a + b) * (x * x')) := by
    have := Dominant.mul (by have := fl_pos a; positivity) (by have := fl_pos b; positivity)
      (PA_floor hx ha h) (PA_floor hx' hb h')
    rwa [show fl a * x * (fl b * x') = fl (a + b) * (x * x') by rw [fl_add]; ring] at this
  have hB : InBall S T (fun c d => X c d * X' c d) (x * x') :=
    (PA_ball hx ha h).mul hx hx' (PA_ball hx' hb h')
  have hAA : a ≤ 3 → b ≤ 3 → InBall S T (fun c d => X c d * X' c d) (x * x' * (17 / 16)) :=
    fun ha3 hb3 => by
      have := (PA_ballA ha ha3 h).mul (by positivity) (by positivity) (PA_ballA hb hb3 h')
      exact this.weaken (by positivity) (by nlinarith [mul_nonneg hx hx'])
  have hX0 : ∀ c d, 0 ≤ X c d * X' c d := fun c d => mul_nonneg (h0 c d) (h0' c d)
  rcases Nat.lt_or_ge (a + b) 3 with h2 | h3
  · obtain ⟨rfl, rfl⟩ : a = 1 ∧ b = 1 := by omega
    exact p11_p2 hx hx' h0 h0' h h'
  rcases Nat.lt_or_ge (a + b) 4 with h3' | h4
  · have e : a + b = 3 := by omega
    rw [e] at hfl ⊢
    exact ⟨hAA (by omega) (by omega), hfl⟩
  rcases Nat.lt_or_ge (a + b) 5 with h4' | h5
  · have e : a + b = 4 := by omega
    rw [e] at hfl ⊢
    refine ⟨⟨hB, fun _ _ hm hpq => (hAA (by omega) (by omega)).hex (by positivity) hX0 hm hpq⟩,
      hfl⟩
  have e : ∀ n, 5 ≤ n → n ≤ 7 → Dominant S T (fun c d => X c d * X' c d) (fl n * (x * x')) →
      PA n S T (fun c d => X c d * X' c d) (x * x') := fun n h5 h7 hf => by
    rcases (show n = 5 ∨ n = 6 ∨ n = 7 by omega) with rfl | rfl | rfl
    · exact ⟨hB, hf⟩
    · exact ⟨hB, hf⟩
    · exact ⟨hB, hf⟩
  exact e _ h5 hab hfl

/-- One term of a product of two alternatives. -/
theorem AP_mul_part {a b : ℕ} {X X' : ℕ → ℕ → ℝ} {x x' : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : a + b ≤ 7) (hx : 0 ≤ x) (hx' : 0 ≤ x') (h0 : ∀ c d, 0 ≤ X c d)
    (h0' : ∀ c d, 0 ≤ X' c d) (h : PA a S T X x ∨ PB a S T X x)
    (h' : PA b S T X' x' ∨ PB b S T X' x') :
    AP (a + b) S T (fun c d => X c d * X' c d) (x * x') := by
  have hX0 : ∀ c d, 0 ≤ X c d * X' c d := fun c d => mul_nonneg (h0 c d) (h0' c d)
  have hz : x = 0 ∨ x' = 0 → AP (a + b) S T (fun c d => X c d * X' c d) (x * x') := by
    rintro (e | e) <;> rw [e] <;> simp only [zero_mul, mul_zero] <;> exact (coneAP _).of_zero hX0
  rcases h with h | h <;> rcases h' with h' | h'
  · exact Alt2.of_left (conePB _) (by positivity) hX0 (PA_mul ha hb hab hx hx' h0 h0' h h')
  · rcases Nat.lt_or_ge b 6 with hb6 | hb6
    · exact hz (Or.inr ((PB_low (by omega)).mp h'))
    obtain ⟨rfl, rfl⟩ : a = 1 ∧ b = 6 := by omega
    refine Alt2.of_right (conePA _) (by positivity) hX0 ⟨?_, ?_⟩
    · have h1 : Hex S T X (x * (17 / 16)) :=
        fun _ _ hm hpq => h.2.2.2.1.hex (by positivity) h0 hm hpq
      have := h1.mul (by positivity) (by have := a5_pos; positivity) h'.1
      refine this.weaken (by have := d6_pos; positivity) ?_
      have := d6_le_a5; have := a5_pos; have := d6_pos
      nlinarith [mul_nonneg hx hx']
    · have := Dominant.mul (by positivity) (by have := fl_pos 6; positivity) h.1 h'.2
      refine this.le (le_of_eq ?_)
      unfold fl; ring
  · rcases Nat.lt_or_ge a 6 with ha6 | ha6
    · exact hz (Or.inl ((PB_low (by omega)).mp h))
    obtain ⟨rfl, rfl⟩ : a = 6 ∧ b = 1 := by omega
    refine Alt2.of_right (conePA _) (by positivity) hX0 ⟨?_, ?_⟩
    · have h1 : Hex S T X' (x' * (17 / 16)) :=
        fun _ _ hm hpq => h'.2.2.2.1.hex (by positivity) h0' hm hpq
      have := h.1.mul (by have := a5_pos; positivity) (by positivity) h1
      refine this.weaken (by have := d6_pos; positivity) ?_
      have := d6_le_a5; have := a5_pos; have := d6_pos
      nlinarith [mul_nonneg hx hx']
    · have := Dominant.mul (by have := fl_pos 6; positivity) (by positivity) h.2 h'.1
      refine this.le (le_of_eq ?_)
      unfold fl; ring
  · rcases Nat.lt_or_ge a 6 with ha6 | ha6
    · exact hz (Or.inl ((PB_low (by omega)).mp h))
    · exact hz (Or.inr ((PB_low (by omega)).mp h'))

/-- **Products of two classes**, the marks adding up to at most seven. -/
theorem Kc15_nonneg_mul {a b : ℕ} (hN : 0 ≤ N) (hN' : 0 ≤ N') (hW0 : ∀ c d, 0 ≤ W c d)
    (hW0' : ∀ c d, 0 ≤ W' c d) (hab : a + b ≤ 7) (h : Kc15 a S T W N) (h' : Kc15 b S T W' N') :
    Kc15 (a + b) S T (fun c d => W c d * W' c d) (N * N') := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [zero_add]
    exact Kc15_mul_dom hN' hN hW0' h h'
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [add_zero]
    have := Kc15_mul_dom hN hN' hW0 h' h
    exact Kc15_mono_table (fun c _ d _ _ => le_of_eq (mul_comm _ _))
      (by rwa [mul_comm N' N] at this)
  rw [Kc15_pos ha] at h
  rw [Kc15_pos hb] at h'
  rw [Kc15_pos (by omega)]
  refine Mx.mul (coneAP _) hN' (fun hv h0 h => AP_mono hv h0 (by omega) h)
    (fun hv h0 h => AP_mono hv h0 (by omega) h) (fun hv hv' h0 h0' h h' => ?_) h h'
  refine alt_mul (coneAP _) ?_ ?_ ?_ ?_ h0 h0' h h'
  · exact fun hx hx' h0 h0' h h' => AP_mul_part ha hb hab hx hx' h0 h0' (Or.inl h) (Or.inl h')
  · exact fun hx hx' h0 h0' h h' => AP_mul_part ha hb hab hx hx' h0 h0' (Or.inl h) (Or.inr h')
  · exact fun hx hx' h0 h0' h h' => AP_mul_part ha hb hab hx hx' h0 h0' (Or.inr h) (Or.inl h')
  · exact fun hx hx' h0 h0' h h' => AP_mul_part ha hb hab hx hx' h0 h0' (Or.inr h) (Or.inr h')

end Kc15

/-! ### The vertex rule -/

/-- **The vertex rule**: a branch of `t₁` marks hanging at a corner of a side of `t₀` marks. -/
theorem markVertex15_sound {t t₀ t₁ : ℕ} (h : t₀ + t₁ ≤ t ∧ t ≤ 7) (Lv Ly Lw : Finset ℕ)
    (hv : Lv.card = 3) (hy : Ly.card = 3) (hw : Lw.card = 3) (W X X' : ℕ → ℕ → ℝ)
    (hW : ∀ c d, 0 ≤ W c d) (hX : ∀ c d, 0 ≤ X c d) (hX' : ∀ c d, 0 ≤ X' c d) (A A₁ A₂ : ℝ)
    (hA : 0 < A) (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (h₀ : Kc15 t₀ Lv Ly W A)
    (h₁ : Kc15 t₁ Lv Lw X A₁) (h₂ : Dominant Lw Lv X' A₂) :
    Kc15 t Lv Ly (fun c d => W c d * ∑ e ∈ Lw, X c e * X' e c) (A * (2 * A₁ * A₂)) := by
  have hL := Kc15_lift (U := Ly) hv hw hy hA₁.le h₁
  have hL' := Kc15_mul_dom (W' := fun _ _ => A₂) (by positivity) hA₂.le
    (fun c _ => liftV_nonneg hX c) (fun _ _ _ _ _ => le_refl _) hL
  have hB : Kc15 t₁ Lv Ly (fun c _ => ∑ e ∈ Lw, X c e * X' e c) (A₂ * (2 * A₁)) :=
    Kc15_mono_table (fun c hc _ _ _ => branch_ge hX hX' h₂ hc) hL'
  have hprod := Kc15_nonneg_mul hA.le (by positivity) hW
    (fun c _ => Finset.sum_nonneg fun e _ => mul_nonneg (hX _ _) (hX' _ _)) (by omega) h₀ hB
  rw [show A * (2 * A₁ * A₂) = A * (A₂ * (2 * A₁)) by ring]
  exact Kc15_mono (by positivity) h.1 hprod

end Outerplanar.F15
