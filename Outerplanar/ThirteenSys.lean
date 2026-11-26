/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.ThirteenCentroid

/-!
# The class system of the thirteen-face theorem

Tags (`T13`): `small k` — a branch with `k ≤ 6` marks, class `Kc6 k`; `top j` — the *dual* of
`Kc6 j`: the tables whose glue with every table of `j` marks on the other side of the edge gives
the count (`TopCls`); `triv` — every table.

* `rule13` — the face rule: `markRule6` for small tags; for `top j`, a face whose sides carry small
  tags, at most twelve marks with the root side's `j` around an even face (the centroid,
  `centroid_close`); nothing to show for `triv`.
* `glue13` — two small tags (both in `H`), or `top j` against `small j` (by the definition of `top`).
* `vrule13` — the vertex rule: small from small (`markVertex6_sound`), `top j` from `top j'` and a
  small branch of `j' - j` marks (the vertex rule of the root side, transposed), `top` from two
  small tags (a cut vertex closes: everything is in `H`), `top j` from the plain tag and `top j`.
* **`ecc_three_of_thirteenBuiltW`** — graphs built under these rules are 3-ECC.

Formalized by Claude (milestone M3 of `ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`); the
dual tag is how the face-level centroid closing of the research note
`ai_research_notes/OUTERPLANAR_THIRTEEN_AND_GAUGE_OBSTRUCTION_2026-11-23.md` (Step 3) fits the
edge glue of `Outerplanar/TagBuiltW.lean`.
-/

namespace Outerplanar

open Finset

/-- The tags. -/
inductive T13
  | small (k : ℕ)
  | top (j : ℕ)
  | triv

/-- **The dual class**: the glue with every table of `Kc6 j` on the other side gives the count. -/
def TopCls (j : ℕ) (S T : Finset ℕ) (W : ℕ → ℕ → ℝ) (A : ℝ) : Prop :=
  S.card = 3 → T.card = 3 → ∀ (W' : ℕ → ℕ → ℝ) (A' : ℝ), (∀ c d, 0 ≤ W' c d) → 0 < A' →
    Kc6 j T S W' A' → 6 * (A * A') ≤ ∑ d ∈ T, ∑ c ∈ S, (if c ≠ d then W' d c * W c d else 0)

/-- The classes. -/
def cls13 : T13 → Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop
  | .small k => Kc6 k
  | .top j => TopCls j
  | .triv => fun _ _ _ _ => True

section Top

variable {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {A : ℝ}

/-- The proper sum of a table of a class is at least six times its constant. -/
theorem kc6_sum (hS : S.card = 3) (hT : T.card = 3) {k : ℕ} {W' : ℕ → ℕ → ℝ} {A' : ℝ}
    (hW'0 : ∀ c d, 0 ≤ W' c d) (hA' : 0 < A') (h : Kc6 k T S W' A') :
    6 * A' ≤ ∑ d ∈ T, ∑ c ∈ S, (if c ≠ d then W' d c else 0) := by
  have hH := Kc6_hex hA'.le hW'0 k h
  have hm : Hex T S (fun d c => if c ≠ d then W' d c else 0) A' :=
    hH.mono hW'0 fun d _ c _ hdc => by simp [Ne.symm hdc]
  exact hm.sum_ge hT hS hA' fun d c => by split_ifs <;> simp [hW'0]

theorem topCls_of_dom {j : ℕ} (hA : 0 ≤ A) (h : Dominant S T W A) : TopCls j S T W A := by
  intro hS hT W' A' hW'0 hA' hW'
  have key := kc6_sum hS hT hW'0 hA' hW'
  calc 6 * (A * A') = A * (6 * A') := by ring
    _ ≤ A * ∑ d ∈ T, ∑ c ∈ S, (if c ≠ d then W' d c else 0) := mul_le_mul_of_nonneg_left key hA
    _ = ∑ d ∈ T, ∑ c ∈ S, A * (if c ≠ d then W' d c else 0) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun d _ => by rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun d hd => Finset.sum_le_sum fun c hc => by
        split_ifs with hcd
        · rw [mul_comm]; exact mul_le_mul_of_nonneg_left (h c hc d hd hcd) (hW'0 _ _)
        · simp

theorem topCls_mul_dom {j : ℕ} {W' : ℕ → ℕ → ℝ} {A' : ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (hW : ∀ c d, 0 ≤ W c d) (hd : Dominant S T W' A') (h : TopCls j S T W A) :
    TopCls j S T (fun c d => W' c d * W c d) (A' * A) := by
  intro hS hT W'' A'' hW''0 hA'' hW''
  have key := h hS hT W'' A'' hW''0 hA'' hW''
  calc 6 * (A' * A * A'') = A' * (6 * (A * A'')) := by ring
    _ ≤ A' * ∑ d ∈ T, ∑ c ∈ S, (if c ≠ d then W'' d c * W c d else 0) :=
        mul_le_mul_of_nonneg_left key hA'
    _ = ∑ d ∈ T, ∑ c ∈ S, A' * (if c ≠ d then W'' d c * W c d else 0) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun d _ => by rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun d hd' => Finset.sum_le_sum fun c hc => by
        split_ifs with hcd
        · calc A' * (W'' d c * W c d) ≤ W' c d * (W'' d c * W c d) :=
              mul_le_mul_of_nonneg_right (hd c hc d hd' hcd) (mul_nonneg (hW''0 d c) (hW c d))
            _ = W'' d c * (W' c d * W c d) := by ring
        · simp

theorem topCls_swap {j : ℕ} (h : TopCls j S T W A) : TopCls j T S (fun d c => W c d) A := by
  intro hT hS W' A' hW'0 hA' hW'
  have key := h hS hT (fun d c => W' c d) A' (fun d c => hW'0 c d) hA' (Kc6_swap j hW')
  refine key.trans (le_of_eq ?_)
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => by
    simp only [ne_comm]

end Top

/-- **The class system.** -/
def sys13 : ClassSys where
  Tag := T13
  plain := .small 0
  cls := cls13
  of_dom := fun t S T W A hA h => by
    cases t with
    | small k => exact Kc6_mono hA (Nat.zero_le k) h
    | top j => exact topCls_of_dom hA h
    | triv => trivial
  dom_of_plain := fun _ _ _ _ h => h
  mul_dom := fun t S T W W' A A' hA hA' hW _ hd h => by
    cases t with
    | small k => exact Kc6_mul_dom hA hA' hW hd k h
    | top j => exact topCls_mul_dom hA hA' hW hd h
    | triv => trivial

theorem sys13_transposable : sys13.Transposable := fun t S T W A h => by
  cases t with
  | small k => exact Kc6_swap k h
  | top j => exact topCls_swap h
  | triv => trivial

/-! ### The face rule -/

/-- **The face rule.** -/
def rule13 (t : T13) (m : ℕ) (τ : Fin (m + 1) → T13) : Prop :=
  (∃ (k : ℕ) (f : Fin (m + 1) → ℕ), t = .small k ∧ (∀ i, τ i = .small (f i)) ∧ markRule6 k m f) ∨
  (∃ (j : ℕ) (f : Fin (m + 1) → ℕ), t = .top j ∧ (∀ i, τ i = .small (f i)) ∧ 1 ≤ m ∧
    (Even m → j + ∑ i, f i ≤ 12)) ∨
  t = .triv

theorem rule13_sound {t : T13} {m : ℕ} {τ : Fin (m + 1) → T13} (hr : rule13 t m τ) :
    sys13.RuleSound t m τ := by
  intro Lu Lv Li hLu hLv hLi E hE0 A hA hE
  rcases hr with ⟨k, f, rfl, hf, hk⟩ | ⟨j, f, rfl, hf, hm1, hsum⟩ | rfl
  · exact markRule6_sound hk Lu Lv Li hLu hLv hLi E hE0 A hA fun i => by
      have := hE i; rw [hf i] at this; exact this
  · intro _ _ W' A' hW'0 hA' hW'
    have key := centroid_close hm1 Lu Lv Li hLu hLv hLi E hE0 A hA f
      (fun i => by have := hE i; rw [hf i] at this; exact this) j W' hW'0 A' hA' hW' hsum
    exact key
  · trivial

/-! ### The glue -/

/-- **The glue.** -/
def glue13 (t₁ t₂ : T13) : Prop :=
  (∃ a b, t₁ = .small a ∧ t₂ = .small b) ∨ (∃ j, t₁ = .top j ∧ t₂ = .small j) ∨
    (∃ j, t₁ = .small j ∧ t₂ = .top j)

theorem glue13_sound {t₁ t₂ : T13} (hg : glue13 t₁ t₂) : sys13.GlueSound t₁ t₂ := by
  intro S T W W' A A' hS hT h0 h0' hA hA' h₁ h₂
  rcases hg with ⟨a, b, rfl, rfl⟩ | ⟨j, rfl, rfl⟩ | ⟨j, rfl, rfl⟩
  · have b₁ := Kc6_hex hA.le h0 a h₁
    have b₂ := (Kc6_hex hA'.le h0' b h₂).swap'
    have key := Hex.glue hS hT b₁ b₂ hA hA' h0 fun c d => h0' d c
    rw [Finset.sum_comm]
    refine key.trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => mul_comm _ _
  · have key := h₁ hS hT W' A' h0' hA' h₂
    refine key.trans (Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun c _ => ?_)
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (h0' _ _) (h0 _ _)
  · have key := h₂ hT hS W A h0 hA h₁
    rw [mul_comm A A']
    refine key.trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun c _ => ?_
    split_ifs
    · rw [mul_comm]
    · exact mul_nonneg (h0' _ _) (h0 _ _)

/-! ### The vertex rule -/

/-- **The vertex rule.** -/
def vrule13 (t t₀ t₁ : T13) : Prop :=
  (∃ k a b, t = .small k ∧ t₀ = .small a ∧ t₁ = .small b ∧ a + b ≤ k ∧ k ≤ 6) ∨ t = .triv ∨
  (∃ j j' b, t = .top j ∧ t₀ = .top j' ∧ t₁ = .small b ∧ j + b ≤ j' ∧ j' ≤ 6) ∨
  (∃ j a b, t = .top j ∧ t₀ = .small a ∧ t₁ = .small b) ∨
  (∃ j, t = .top j ∧ t₀ = .small 0 ∧ t₁ = .top j ∧ j ≤ 6)

theorem vrule13_sound {t t₀ t₁ : T13} (hv : vrule13 t t₀ t₁) : sys13.VertexSound t t₀ t₁ := by
  intro Lv Ly Lw hv' hy hw W X X' hW hX hX' A A₁ A₂ hA hA₁ hA₂ h₀ h₁ h₂
  have h₂' : Dominant Lw Lv X' A₂ := h₂
  set φ : ℕ → ℝ := fun c => ∑ e ∈ Lw, X c e * X' e c with hφ
  have hφ0 : ∀ c, 0 ≤ φ c := fun c => Finset.sum_nonneg fun e _ => mul_nonneg (hX _ _) (hX' _ _)
  rcases hv with ⟨k, a, b, rfl, rfl, rfl, hab, hk⟩ | rfl | ⟨j, j', b, rfl, rfl, rfl, hjb, hj'⟩ |
    ⟨j, a, b, rfl, rfl, rfl⟩ | ⟨j, rfl, rfl, rfl, hj6⟩
  · exact markVertex6_sound ⟨hab, hk⟩ Lv Ly Lw hv' hy hw W X X' hW hX hX' A A₁ A₂ hA hA₁ hA₂
      h₀ h₁ h₂'
  · trivial
  · -- `top` through a small branch: the vertex rule on the root side
    intro _ _ W'' A'' hW''0 hA'' hW''
    have hZ := markVertex6_sound (t := j') (t₀ := j) (t₁ := b) ⟨hjb, hj'⟩ Lv Ly Lw hv' hy hw
      (fun c d => W'' d c) X X' (fun c d => hW''0 d c) hX hX' A'' A₁ A₂ hA'' hA₁ hA₂
      (Kc6_swap j hW'') h₁ h₂'
    have hZ' := Kc6_swap j' hZ
    have key := (h₀ : TopCls j' Lv Ly W A) hv' hy (fun d c => W'' d c * φ c) (A'' * (2 * A₁ * A₂))
      (fun d c => mul_nonneg (hW''0 d c) (hφ0 c)) (by positivity) hZ'
    calc 6 * (A * (2 * A₁ * A₂) * A'') = 6 * (A * (A'' * (2 * A₁ * A₂))) := by ring
      _ ≤ _ := key
      _ = _ := Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => by
          split_ifs <;> ring
  · -- two small sides at a cut vertex: everything is in `H`
    intro _ _ W'' A'' hW''0 hA'' hW''
    have hH₀ := Kc6_hex hA.le hW a h₀
    have hL := Kc6_hex (by positivity) (fun c _ => liftV_nonneg hX c) b
      (Kc6_lift (U := Ly) hv' hw hy hA₁.le b h₁)
    have hU : Hex Lv Ly (fun c d => W c d * φ c) (A * (2 * A₁ * A₂)) := by
      have hprod := hH₀.mul hA.le (by positivity) (hL.mul (by positivity) hA₂.le
        (Dominant.hex (S := Lv) (T := Ly) (W := fun _ _ => A₂) (fun _ _ _ _ _ => le_rfl)
          hA₂.le))
      refine (hprod.mono (fun c d => mul_nonneg (hW c d)
        (mul_nonneg (liftV_nonneg hX c) hA₂.le)) fun c hc d _ _ => ?_).weaken
        (by positivity) (le_of_eq (by ring))
      have hb := branch_ge hX hX' h₂' hc
      calc W c d * (liftV Lw X c * A₂) = W c d * (A₂ * liftV Lw X c) := by ring
        _ ≤ W c d * φ c := mul_le_mul_of_nonneg_left (by simpa [hφ] using hb) (hW c d)
    have hR : Hex Lv Ly (fun c d => if c ≠ d then W'' d c else 0) A'' :=
      (Kc6_hex hA''.le hW''0 j hW'').swap'.mono (fun c d => hW''0 d c)
        fun c _ d _ hcd => by simp [hcd]
    have key := Hex.glue hv' hy hU hR (by positivity) hA'' (fun c d => mul_nonneg (hW c d) (hφ0 c))
      fun c d => by split_ifs <;> simp [hW''0]
    refine key.trans (le_of_eq ?_)
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => by
      split_ifs <;> ring
  · -- the plain side and a `top` branch
    intro _ _ W'' A'' hW''0 hA'' hW''
    have hD : Dominant Lv Ly W A := h₀
    set ψ : ℕ → ℝ := fun c => ∑ d ∈ Ly, W'' d c * (if d ≠ c then 1 else 0) with hψ
    have hψ0 : ∀ c, 0 ≤ ψ c := fun c => Finset.sum_nonneg fun d _ =>
      mul_nonneg (hW''0 d c) (by split_ifs <;> norm_num)
    -- the table `X' ψ` of the branch side is in `Kc6 j`
    have hZ := markVertex6_sound (t := j) (t₀ := 0) (t₁ := j) ⟨by omega, hj6⟩ Lv Lw Ly hv' hw hy
      (fun c e => X' e c) (fun c d => W'' d c) (fun d c => if d ≠ c then 1 else 0)
      (fun c e => hX' e c) (fun c d => hW''0 d c) (fun d c => by split_ifs <;> norm_num)
      A₂ A'' 1 hA₂ hA'' one_pos h₂'.swap (Kc6_swap j hW'')
      (fun d _ c _ hdc => by simp [hdc])
    have hZ' := Kc6_swap j hZ
    have key := (h₁ : TopCls j Lv Lw X A₁) hv' hw (fun e c => X' e c * ψ c) (A₂ * (2 * A'' * 1))
      (fun e c => mul_nonneg (hX' e c) (hψ0 c)) (by positivity) hZ'
    -- the sum against `W''` is at least `A` times that against `ψ`
    have h1 : A * ∑ c ∈ Lv, φ c * ψ c
        ≤ ∑ d ∈ Ly, ∑ c ∈ Lv, (if c ≠ d then W'' d c * (W c d * φ c) else 0) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_le_sum fun c hc => ?_
      simp only [hψ]
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun d hd => ?_
      by_cases hcd : c = d
      · subst hcd; simp
      · have hdc : d ≠ c := Ne.symm hcd
        simp only [hcd, hdc, ne_eq, not_false_eq_true, ite_true, ite_false, mul_one]
        have h3 := hD c hc d hd hcd
        have h4 := hW''0 d c
        have h5 := hφ0 c
        calc A * (φ c * W'' d c) = (φ c * W'' d c) * A := by ring
          _ ≤ (φ c * W'' d c) * W c d := mul_le_mul_of_nonneg_left h3 (mul_nonneg h5 h4)
          _ = W'' d c * (W c d * φ c) := by ring
    have h2 : ∑ e ∈ Lw, ∑ c ∈ Lv, (if c ≠ e then X' e c * ψ c * X c e else 0)
        ≤ ∑ c ∈ Lv, φ c * ψ c := by
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun c _ => ?_
      rw [hφ, Finset.sum_mul]
      refine Finset.sum_le_sum fun e _ => ?_
      split_ifs
      · exact le_of_eq (by ring)
      · exact mul_nonneg (mul_nonneg (hX _ _) (hX' _ _)) (hψ0 c)
    calc 6 * (A * (2 * A₁ * A₂) * A'') = A * (6 * (A₁ * (A₂ * (2 * A'' * 1)))) := by ring
      _ ≤ A * ∑ c ∈ Lv, φ c * ψ c := mul_le_mul_of_nonneg_left (key.trans h2) hA.le
      _ ≤ _ := h1

/-! ### The theorem for built graphs -/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Every graph built by ears, pendant edges and reorientations under the thirteen-face rules
is 3-ECC.** -/
theorem ecc_three_of_thirteenBuiltW (G : SimpleGraph V) [DecidableRel G.Adj] {tg : V → V → T13}
    (h : TagBuiltW G sys13 rule13 glue13 vrule13 univ tg) : G.ECCAt 3 :=
  ecc_three_of_tagBuiltW G (R := sys13) (fun _ _ _ hr => rule13_sound hr)
    (fun _ _ hg => glue13_sound hg) (fun _ _ _ hv => vrule13_sound hv) sys13_transposable h

end Outerplanar
