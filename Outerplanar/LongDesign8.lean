/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.OddBall

/-!
# Even faces of length at least eight with every path edge loaded

An even face of length `L = m + 2 ≥ 8` maps the ball class on *all* its path edges to the ball class
on its root edge, at the price of the factor `16/17` (**`ballEvenLong`**): with constants `A_j` on the
path edges, the root edge gets `(16/17) · faceConst3 m · ∏ A_j`. Unlike odd faces (`ballOddClosed`),
even faces do not preserve the full constant: their closed cells have one walk fewer than the
constant `dN n` (n = m + 1 steps).

The proof works in index form, as for odd faces (`Outerplanar/Walks.lean`). Split the path into a
first part of `j` steps and a second of `k` steps. In every cell choose the midpoint uniformly among
the three indices, and the two half-walks uniformly given their ends. In product form, with
`S = s_j d_j s_k d_k`, the walk through the midpoint `z` gets the exponent `S / cnt` for each half.

* `cell_hub` — AM–GM over the midpoint (`amgm3`) and over each half (`pw_ub`):
  `(27 s_j d_j² s_k d_k²)^S · Γ ≤ pw^(3S)`.
* `cells_bal` — for every bijection `σ`, the six cells `(a, σ b)`, `a ≠ b`, use every pair of
  different indices at every step equally often (`Og_eq`, `Dg_eq`):
  `∏ Γ = up (3S)`. The design does not depend on `σ`.
* `mid_assembly` — the assembly of `sel_assembly` with a real constant. The weight that moves to
  an arbitrary cell is charged to the children by `OffBall.minmax`, which needs the constant to
  be at most the walk count of every cell. For an odd number of steps that count is `s_n = d_n - 1`.
* `long_numbers` — `n = 2r + 1`, `r ≥ 3`, `j = r`, `k = r + 1`, `N = (16/17) d_n`:
  `N³ ≤ 27 s_j d_j² s_k d_k²` (with `x = 2^r`, a degree-six polynomial inequality for `x ≥ 8`) and
  `N ≤ s_n`.

This is the long-face lemma of the research note
`ai_research_notes/OUTERPLANAR_BRANCHING_SQUARES_2026-11-23.md` ("A balanced walk law", lengths
`L ≥ 8`; another AI session of this repository's collaboration). The paper charges the moved weight
through total variation and entropy; here it is charged crudely, which costs nothing at these lengths
(`ai_research_notes/T4b_M1_longface.md`). Formalized by Claude.
-/

namespace Outerplanar

open Finset

/-! ### Assembly with a real constant -/

/-- **Assembly for a design in product form**: `sel_assembly` with the constant `N` and the
exponent `e` separated. -/
theorem mid_assembly {e : ℕ} (he : 0 < e) {N : ℝ} (hN : 0 ≤ N) {p Γ : Fin 6 → ℝ}
    {pmv AP Uα U100 mnp mxp : ℝ}
    (hp : ∀ k, 0 ≤ p k) (hΓ : ∀ k, 0 ≤ Γ k) (hub : ∀ k, N ^ e * Γ k ≤ p k ^ e)
    (hbal : ∏ k, Γ k = Uα) (hΓle : ∀ k, Γ k ≤ mxp ^ e) (hmv : N * mnp ≤ pmv)
    (hchild : AP ^ 600 * mxp ^ 9 ≤ U100 * mnp ^ 9) (hU : Uα ^ 100 = U100 ^ e)
    (hmxp : 0 < mxp) (hmnp : 0 ≤ mnp) (hAP : 0 ≤ AP) (j : Fin 6) :
    (N * AP) ^ 600 ≤ (∏ k ∈ univ.erase j, p k) ^ 100 * p j ^ 91 * pmv ^ 9 := by
  set G' := ∏ k ∈ univ.erase j, Γ k with hG'
  have hG'0 : 0 ≤ G' := prod_nonneg fun k _ => hΓ k
  have hsplit : Γ j * G' = Uα := by
    rw [← hbal]
    exact Finset.mul_prod_erase univ Γ (mem_univ j)
  have hpmv : 0 ≤ pmv := (mul_nonneg hN hmnp).trans hmv
  have h1 : AP ^ (600 * e) * mxp ^ (9 * e)
      ≤ G' ^ 100 * Γ j ^ 91 * mnp ^ (9 * e) * mxp ^ (9 * e) :=
    calc AP ^ (600 * e) * mxp ^ (9 * e) = (AP ^ 600 * mxp ^ 9) ^ e := by
          rw [mul_pow, ← pow_mul, ← pow_mul]
      _ ≤ (U100 * mnp ^ 9) ^ e :=
          pow_le_pow_left₀ (mul_nonneg (pow_nonneg hAP _) (pow_nonneg hmxp.le _)) hchild e
      _ = Uα ^ 100 * mnp ^ (9 * e) := by rw [mul_pow, ← hU, ← pow_mul]
      _ = G' ^ 100 * Γ j ^ 91 * mnp ^ (9 * e) * Γ j ^ 9 := by rw [← hsplit]; ring
      _ ≤ G' ^ 100 * Γ j ^ 91 * mnp ^ (9 * e) * mxp ^ (9 * e) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg (pow_nonneg hG'0 _)
            (pow_nonneg (hΓ j) _)) (pow_nonneg hmnp _))
          calc Γ j ^ 9 ≤ (mxp ^ e) ^ 9 := pow_le_pow_left₀ (hΓ j) (hΓle j) 9
            _ = mxp ^ (9 * e) := by rw [← pow_mul, mul_comm]
  have h2 : AP ^ (600 * e) ≤ G' ^ 100 * Γ j ^ 91 * mnp ^ (9 * e) :=
    le_of_mul_le_mul_right h1 (pow_pos hmxp _)
  have h3 : N ^ (5 * e) * G' ≤ (∏ k ∈ univ.erase j, p k) ^ e := by
    rw [← Finset.prod_pow]
    have hc : (univ.erase j : Finset (Fin 6)).card = 5 := by
      rw [Finset.card_erase_of_mem (mem_univ j), Finset.card_univ, Fintype.card_fin]
    calc N ^ (5 * e) * G' = ∏ k ∈ univ.erase j, N ^ e * Γ k := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, hc, ← pow_mul, mul_comm e 5]
      _ ≤ _ := Finset.prod_le_prod₀ (fun k _ => mul_nonneg (pow_nonneg hN _) (hΓ k))
          fun k _ => hub k
  have h4 : (N * mnp) ^ e ≤ pmv ^ e := pow_le_pow_left₀ (mul_nonneg hN hmnp) hmv e
  have hX : ((N * AP) ^ 600) ^ e
      ≤ ((∏ k ∈ univ.erase j, p k) ^ 100 * p j ^ 91 * pmv ^ 9) ^ e :=
    calc ((N * AP) ^ 600) ^ e = N ^ (600 * e) * AP ^ (600 * e) := by
          rw [← pow_mul, mul_pow]
      _ ≤ N ^ (600 * e) * (G' ^ 100 * Γ j ^ 91 * mnp ^ (9 * e)) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hN _)
      _ = (N ^ (5 * e) * G') ^ 100 * (N ^ e * Γ j) ^ 91 * ((N * mnp) ^ e) ^ 9 := by
          ring
      _ ≤ ((∏ k ∈ univ.erase j, p k) ^ e) ^ 100 * (p j ^ e) ^ 91 * (pmv ^ e) ^ 9 := by
          refine mul_le_mul (mul_le_mul (pow_le_pow_left₀ (mul_nonneg (pow_nonneg hN _) hG'0)
            h3 _) (pow_le_pow_left₀ (mul_nonneg (pow_nonneg hN _) (hΓ j)) (hub j) _)
            (pow_nonneg (mul_nonneg (pow_nonneg hN _) (hΓ j)) _)
            (pow_nonneg (pow_nonneg (prod_nonneg fun k _ => hp k) _) _))
            (pow_le_pow_left₀ (pow_nonneg (mul_nonneg hN hmnp) _) h4 _)
            (pow_nonneg (pow_nonneg (mul_nonneg hN hmnp) _) _)
            (mul_nonneg (pow_nonneg (pow_nonneg (prod_nonneg fun k _ => hp k) _) _)
              (pow_nonneg (pow_nonneg (hp j) _) _))
      _ = _ := by ring
  exact le_of_pow_le_pow_left₀ he.ne' (mul_nonneg (mul_nonneg (pow_nonneg
    (prod_nonneg fun k _ => hp k) _) (pow_nonneg (hp j) _)) (pow_nonneg hpmv _)) hX

/-! ### The design -/

/-- A power of AM–GM over the walks of a cell. -/
theorem pw_ub_pow (Ms : List (Fin 3 → Fin 3 → ℝ)) (hM : ∀ M ∈ Ms, ∀ a b, 0 ≤ M a b)
    (a b : Fin 3) {S : ℕ} (hS : cnt Ms.length a b ∣ S) :
    ((cnt Ms.length a b : ℕ) : ℝ) ^ S * wgp Ms a b ^ (S / cnt Ms.length a b) ≤ pw Ms a b ^ S := by
  obtain ⟨q, hq⟩ := hS
  rcases Nat.eq_zero_or_pos (cnt Ms.length a b) with h0 | hpos
  · rw [h0, zero_mul] at hq
    subst hq
    simp
  · have hdiv : S / cnt Ms.length a b = q := by rw [hq]; exact Nat.mul_div_cancel_left q hpos
    rw [hdiv, hq, pow_mul, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (wgp_nonneg Ms hM a b)) (pw_ub Ms hM a b) q

/-- The product over the walks of the cell `(a, b)` of a path `L₁ ++ L₂`, the midpoint between the
two parts chosen uniformly: a walk through `z` has the exponent `S / cnt` in each part. -/
noncomputable def midΓ (L₁ L₂ : List (Fin 3 → Fin 3 → ℝ)) (S : ℕ) (a b : Fin 3) : ℝ :=
  ∏ z : Fin 3, wgp L₁ a z ^ (S / cnt L₁.length a z) * wgp L₂ z b ^ (S / cnt L₂.length z b)

theorem midΓ_nonneg (L₁ L₂ : List (Fin 3 → Fin 3 → ℝ)) (h₁ : ∀ M ∈ L₁, ∀ a b, 0 ≤ M a b)
    (h₂ : ∀ M ∈ L₂, ∀ a b, 0 ≤ M a b) (S : ℕ) (a b : Fin 3) : 0 ≤ midΓ L₁ L₂ S a b :=
  prod_nonneg fun _ _ => mul_nonneg (pow_nonneg (wgp_nonneg L₁ h₁ _ _) _)
    (pow_nonneg (wgp_nonneg L₂ h₂ _ _) _)

theorem prod_cnt_left (h : ℕ) (a : Fin 3) :
    ∏ z : Fin 3, (cnt h a z : ℝ) = (sN h : ℝ) * (dN h : ℝ) ^ 2 := by
  fin_cases a <;> simp [Fin.prod_univ_three, cnt] <;> ring

theorem prod_cnt_right (h : ℕ) (b : Fin 3) :
    ∏ z : Fin 3, (cnt h z b : ℝ) = (sN h : ℝ) * (dN h : ℝ) ^ 2 := by
  fin_cases b <;> simp [Fin.prod_univ_three, cnt] <;> ring

/-- **AM–GM in one cell**: over the midpoint and over each part. -/
theorem cell_hub (L₁ L₂ : List (Fin 3 → Fin 3 → ℝ)) (h₁ : ∀ M ∈ L₁, ∀ a b, 0 ≤ M a b)
    (h₂ : ∀ M ∈ L₂, ∀ a b, 0 ≤ M a b) (S : ℕ) (hd₁ : ∀ a z, cnt L₁.length a z ∣ S)
    (hd₂ : ∀ z b, cnt L₂.length z b ∣ S) (a b : Fin 3) :
    (27 * ((sN L₁.length : ℝ) * (dN L₁.length : ℝ) ^ 2)
        * ((sN L₂.length : ℝ) * (dN L₂.length : ℝ) ^ 2)) ^ S * midΓ L₁ L₂ S a b
      ≤ pw (L₁ ++ L₂) a b ^ (3 * S) := by
  have hp₁ := pw_nonneg L₁ h₁
  have hp₂ := pw_nonneg L₂ h₂
  have h3 : 27 * ∏ z : Fin 3, (pw L₁ a z * pw L₂ z b) ≤ pw (L₁ ++ L₂) a b ^ 3 := by
    rw [pw_append, Fin.prod_univ_three]
    exact amgm3 (mul_nonneg (hp₁ _ _) (hp₂ _ _)) (mul_nonneg (hp₁ _ _) (hp₂ _ _))
      (mul_nonneg (hp₁ _ _) (hp₂ _ _))
  have hw0 : ∀ z : Fin 3, 0 ≤ wgp L₁ a z ^ (S / cnt L₁.length a z)
      * wgp L₂ z b ^ (S / cnt L₂.length z b) := fun z =>
    mul_nonneg (pow_nonneg (wgp_nonneg L₁ h₁ _ _) _) (pow_nonneg (wgp_nonneg L₂ h₂ _ _) _)
  have hz : ∀ z : Fin 3, (((cnt L₁.length a z : ℕ) : ℝ) * (cnt L₂.length z b : ℕ)) ^ S
      * (wgp L₁ a z ^ (S / cnt L₁.length a z) * wgp L₂ z b ^ (S / cnt L₂.length z b))
      ≤ (pw L₁ a z * pw L₂ z b) ^ S := fun z => by
    have k1 := pw_ub_pow L₁ h₁ a z (hd₁ a z)
    have k2 := pw_ub_pow L₂ h₂ z b (hd₂ z b)
    calc _ = (((cnt L₁.length a z : ℕ) : ℝ) ^ S * wgp L₁ a z ^ (S / cnt L₁.length a z))
          * (((cnt L₂.length z b : ℕ) : ℝ) ^ S * wgp L₂ z b ^ (S / cnt L₂.length z b)) := by
            ring
      _ ≤ pw L₁ a z ^ S * pw L₂ z b ^ S :=
          mul_le_mul k1 k2 (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
            (pow_nonneg (wgp_nonneg L₂ h₂ _ _) _)) (pow_nonneg (hp₁ _ _) _)
      _ = _ := by rw [mul_pow]
  have hprod : ∏ z : Fin 3, ((((cnt L₁.length a z : ℕ) : ℝ) * (cnt L₂.length z b : ℕ)) ^ S
      * (wgp L₁ a z ^ (S / cnt L₁.length a z) * wgp L₂ z b ^ (S / cnt L₂.length z b)))
      ≤ ∏ z : Fin 3, (pw L₁ a z * pw L₂ z b) ^ S :=
    Finset.prod_le_prod₀ (fun z _ => mul_nonneg (pow_nonneg (by positivity) _) (hw0 z))
      fun z _ => hz z
  have hcnt : ∏ z : Fin 3, (((cnt L₁.length a z : ℕ) : ℝ) * (cnt L₂.length z b : ℕ))
      = ((sN L₁.length : ℝ) * (dN L₁.length : ℝ) ^ 2)
        * ((sN L₂.length : ℝ) * (dN L₂.length : ℝ) ^ 2) := by
    rw [Finset.prod_mul_distrib, prod_cnt_left, prod_cnt_right]
  have hP0 : 0 ≤ ∏ z : Fin 3, (pw L₁ a z * pw L₂ z b) :=
    prod_nonneg fun z _ => mul_nonneg (hp₁ _ _) (hp₂ _ _)
  calc (27 * ((sN L₁.length : ℝ) * (dN L₁.length : ℝ) ^ 2)
        * ((sN L₂.length : ℝ) * (dN L₂.length : ℝ) ^ 2)) ^ S * midΓ L₁ L₂ S a b
      = 27 ^ S * ∏ z : Fin 3, ((((cnt L₁.length a z : ℕ) : ℝ) * (cnt L₂.length z b : ℕ)) ^ S
          * (wgp L₁ a z ^ (S / cnt L₁.length a z) * wgp L₂ z b ^ (S / cnt L₂.length z b))) := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow, hcnt, midΓ]
        ring
    _ ≤ 27 ^ S * ∏ z : Fin 3, (pw L₁ a z * pw L₂ z b) ^ S :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = (27 * ∏ z : Fin 3, (pw L₁ a z * pw L₂ z b)) ^ S := by rw [Finset.prod_pow, mul_pow]
    _ ≤ (pw (L₁ ++ L₂) a b ^ 3) ^ S := pow_le_pow_left₀ (by positivity) h3 S
    _ = _ := by rw [← pow_mul]

/-! ### Balance -/

theorem prod_offPair_fst (f : Fin 3 → ℝ) : ∏ k : Fin 6, f (offPair k).1 = (∏ a, f a) ^ 2 := by
  simp [Fin.prod_univ_six, Fin.prod_univ_three, offPair]
  ring

theorem prod_offPair_snd (f : Fin 3 → ℝ) : ∏ k : Fin 6, f (offPair k).2 = (∏ a, f a) ^ 2 := by
  simp [Fin.prod_univ_six, Fin.prod_univ_three, offPair]
  ring

theorem mul_div_half {d S : ℕ} (h : 2 * d ∣ S) : d * (S / (2 * d)) = S / 2 := by
  obtain ⟨t, rfl⟩ := h
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · rw [Nat.mul_div_cancel_left t (by omega), mul_assoc, Nat.mul_div_cancel_left _ (by omega)]

/-- **The nine cells of one part**, each with exponent `S / cnt`, use every pair of different
indices at every step `S + S / 2` times. -/
theorem prod_half (L : List (Fin 3 → Fin 3 → ℝ)) (hL : L ≠ []) (S : ℕ) (hd : dN L.length ∣ S)
    (hs : sN L.length ∣ S) :
    ∏ a : Fin 3, ∏ z : Fin 3, wgp L a z ^ (S / cnt L.length a z) = up L S * up L (S / 2) := by
  obtain ⟨M, Ms, rfl⟩ := List.exists_cons_of_ne_nil hL
  have e1 : ∏ a : Fin 3, ∏ z : Fin 3, wgp (M :: Ms) a z ^ (S / cnt (M :: Ms).length a z)
      = Og (M :: Ms) ^ (S / dN (M :: Ms).length) * Dg (M :: Ms) ^ (S / sN (M :: Ms).length) := by
    simp only [Og, Dg, Fin.prod_univ_three, Fin.prod_univ_six, offPair, cnt, mul_pow]
    simp
    ring
  have hs' : 2 * dN Ms.length ∣ S := by
    have : sN (M :: Ms).length = 2 * dN Ms.length := sN_succ Ms.length
    rwa [this] at hs
  rw [e1, Og_eq, Dg_eq, ← up_mul, ← up_mul, Nat.mul_div_cancel' hd,
    show sN (M :: Ms).length = 2 * dN Ms.length from sN_succ Ms.length, mul_div_half hs']

theorem up_three (L : List (Fin 3 → Fin 3 → ℝ)) {S : ℕ} (hS : 2 ∣ S) :
    (up L S * up L (S / 2)) ^ 2 = up L (3 * S) := by
  rw [mul_pow, ← up_mul, ← up_mul, Nat.div_mul_cancel hS, ← up_add]
  congr 1
  ring

/-- **Balance**: for every bijection `σ`, the six cells `(a, σ b)`, `a ≠ b`, use every pair of
different indices at every step `3 S` times. -/
theorem cells_bal (L₁ L₂ : List (Fin 3 → Fin 3 → ℝ)) (h₁ : L₁ ≠ []) (h₂ : L₂ ≠ []) (S : ℕ)
    (hd₁ : dN L₁.length ∣ S) (hs₁ : sN L₁.length ∣ S) (hd₂ : dN L₂.length ∣ S)
    (hs₂ : sN L₂.length ∣ S) (hS2 : 2 ∣ S) {σ : Fin 3 → Fin 3} (hσ : Function.Injective σ) :
    ∏ k : Fin 6, midΓ L₁ L₂ S (offPair k).1 (σ (offPair k).2) = up (L₁ ++ L₂) (3 * S) := by
  set F : Fin 3 → ℝ := fun a => ∏ z : Fin 3, wgp L₁ a z ^ (S / cnt L₁.length a z) with hF
  set G : Fin 3 → ℝ := fun b => ∏ z : Fin 3, wgp L₂ z b ^ (S / cnt L₂.length z b) with hG
  have hsplit : ∀ a b, midΓ L₁ L₂ S a b = F a * G b := fun a b => by
    rw [midΓ, Finset.prod_mul_distrib]
  simp only [hsplit]
  rw [Finset.prod_mul_distrib, prod_offPair_fst F, prod_offPair_snd (fun b => G (σ b)),
    Function.Bijective.prod_comp (Finite.injective_iff_bijective.mp hσ) G]
  have hG' : ∏ b, G b = up L₂ S * up L₂ (S / 2) := by
    rw [hG, Finset.prod_comm]
    exact prod_half L₂ h₂ S hd₂ hs₂
  rw [hF, prod_half L₁ h₁ S hd₁ hs₁, hG', up_three L₁ hS2, up_three L₂ hS2, up_append]

theorem mxP_append (L₁ L₂ : List (Fin 3 → Fin 3 → ℝ)) : mxP (L₁ ++ L₂) = mxP L₁ * mxP L₂ := by
  simp [mxP]

theorem wgp_pow_le (Ms : List (Fin 3 → Fin 3 → ℝ)) (hM : ∀ M ∈ Ms, ∀ a b, 0 ≤ M a b)
    (a b : Fin 3) {S : ℕ} (hS : cnt Ms.length a b ∣ S) :
    wgp Ms a b ^ (S / cnt Ms.length a b) ≤ mxP Ms ^ S := by
  calc wgp Ms a b ^ (S / cnt Ms.length a b)
      ≤ (mxP Ms ^ cnt Ms.length a b) ^ (S / cnt Ms.length a b) :=
        pow_le_pow_left₀ (wgp_nonneg Ms hM a b) (wgp_le Ms hM a b) _
    _ = mxP Ms ^ S := by rw [← pow_mul, Nat.mul_div_cancel' hS]

/-- A cell weighs at most the product of the largest entries. -/
theorem midΓ_le (L₁ L₂ : List (Fin 3 → Fin 3 → ℝ)) (h₁ : ∀ M ∈ L₁, ∀ a b, 0 ≤ M a b)
    (h₂ : ∀ M ∈ L₂, ∀ a b, 0 ≤ M a b) (S : ℕ) (hd₁ : ∀ a z, cnt L₁.length a z ∣ S)
    (hd₂ : ∀ z b, cnt L₂.length z b ∣ S) (a b : Fin 3) :
    midΓ L₁ L₂ S a b ≤ mxP (L₁ ++ L₂) ^ (3 * S) := by
  have hx₁ := mxP_nonneg L₁ h₁
  have hx₂ := mxP_nonneg L₂ h₂
  calc midΓ L₁ L₂ S a b ≤ ∏ _z : Fin 3, (mxP L₁ ^ S * mxP L₂ ^ S) :=
        Finset.prod_le_prod₀ (fun z _ => mul_nonneg (pow_nonneg (wgp_nonneg L₁ h₁ _ _) _)
          (pow_nonneg (wgp_nonneg L₂ h₂ _ _) _)) fun z _ =>
          mul_le_mul (wgp_pow_le L₁ h₁ a z (hd₁ a z)) (wgp_pow_le L₂ h₂ z b (hd₂ z b))
            (pow_nonneg (wgp_nonneg L₂ h₂ _ _) _) (pow_nonneg hx₁ _)
    _ = mxP (L₁ ++ L₂) ^ (3 * S) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mxP_append, ← mul_pow,
          ← pow_mul, mul_comm S 3]

/-! ### The ball inequalities of a path through a uniform midpoint -/

theorem sN_pos_two (h : ℕ) (hh : 2 ≤ h) : 0 < sN h := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 + 1 := ⟨h - 2, by omega⟩
  rw [sN_succ]
  have := dN_pos k
  omega

theorem dN_pos_one (h : ℕ) (hh : 1 ≤ h) : 0 < dN h := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  exact dN_pos k

theorem two_dvd_sN (h : ℕ) (hh : 1 ≤ h) : 2 ∣ sN h := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  rw [sN_succ]
  exact dvd_mul_right 2 _

/-- **The ball inequalities of a path `L₁ ++ L₂` with a uniform midpoint**, for every bijection
`σ`, weight being moved to any cell, with any constant `N` whose cube is at most the effective
count `27 s_j d_j² s_k d_k²` and which is at most every walk count. -/
theorem walks_ball_mid' (L₁ L₂ : List (Fin 3 → Fin 3 → ℝ)) (As : List ℝ) (hl₁ : 2 ≤ L₁.length)
    (hl₂ : 2 ≤ L₂.length) (hM : ∀ M ∈ L₁ ++ L₂, ∀ a b, 0 ≤ M a b) (hA : ∀ A ∈ As, 0 < A)
    (hball : List.Forall₂ OffBall (L₁ ++ L₂) As) {N : ℝ} (hN : 0 ≤ N)
    (hN3 : N ^ 3 ≤ 27 * ((sN L₁.length : ℝ) * (dN L₁.length : ℝ) ^ 2)
        * ((sN L₂.length : ℝ) * (dN L₂.length : ℝ) ^ 2))
    (hNc : ∀ c d, N ≤ cnt (L₁ ++ L₂).length c d) (σ : Fin 3 → Fin 3)
    (hσ : Function.Injective σ) (j : Fin 6) (c d : Fin 3) :
    (N * As.prod) ^ 600
      ≤ (∏ k ∈ univ.erase j, pw (L₁ ++ L₂) (offPair k).1 (σ (offPair k).2)) ^ 100
        * pw (L₁ ++ L₂) (offPair j).1 (σ (offPair j).2) ^ 91 * pw (L₁ ++ L₂) c d ^ 9 := by
  have h₁ : ∀ M ∈ L₁, ∀ a b, 0 ≤ M a b := fun M hM' => hM M (List.mem_append_left _ hM')
  have h₂ : ∀ M ∈ L₂, ∀ a b, 0 ≤ M a b := fun M hM' => hM M (List.mem_append_right _ hM')
  set s₁ := sN L₁.length
  set d₁ := dN L₁.length
  set s₂ := sN L₂.length
  set d₂ := dN L₂.length
  set S := s₁ * d₁ * s₂ * d₂ with hS
  have dvs₁ : s₁ ∣ S := ((dvd_mul_right s₁ d₁).mul_right s₂).mul_right d₂
  have dvd₁ : d₁ ∣ S := ((dvd_mul_left d₁ s₁).mul_right s₂).mul_right d₂
  have dvs₂ : s₂ ∣ S := (dvd_mul_left s₂ (s₁ * d₁)).mul_right d₂
  have dvd₂ : d₂ ∣ S := dvd_mul_left d₂ _
  have hc₁ : ∀ a z, cnt L₁.length a z ∣ S := fun a z => by
    unfold cnt; split_ifs
    · exact dvs₁
    · exact dvd₁
  have hc₂ : ∀ z b, cnt L₂.length z b ∣ S := fun z b => by
    unfold cnt; split_ifs
    · exact dvs₂
    · exact dvd₂
  have hS2 : 2 ∣ S := (((two_dvd_sN _ (by omega)).mul_right d₁).mul_right s₂).mul_right d₂
  have hSpos : 0 < S := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (sN_pos_two _ hl₁)
    (dN_pos_one _ (by omega))) (sN_pos_two _ hl₂)) (dN_pos_one _ (by omega))
  have hne₁ : L₁ ≠ [] := fun h => by rw [h] at hl₁; simp at hl₁
  have hne₂ : L₂ ≠ [] := fun h => by rw [h] at hl₂; simp at hl₂
  obtain ⟨hchild, hmxp⟩ := offBall_prod (L₁ ++ L₂) As hM hA hball
  have hp := pw_nonneg (L₁ ++ L₂) hM
  refine mid_assembly (e := 3 * S) (by omega) hN
    (p := fun k => pw (L₁ ++ L₂) (offPair k).1 (σ (offPair k).2))
    (Γ := fun k => midΓ L₁ L₂ S (offPair k).1 (σ (offPair k).2))
    (Uα := up (L₁ ++ L₂) (3 * S)) (U100 := up (L₁ ++ L₂) 100) (mnp := mnP (L₁ ++ L₂))
    (mxp := mxP (L₁ ++ L₂)) (fun k => hp _ _) (fun k => midΓ_nonneg L₁ L₂ h₁ h₂ S _ _)
    (fun k => ?_) (cells_bal L₁ L₂ hne₁ hne₂ S dvd₁ dvs₁ dvd₂ dvs₂ hS2 hσ)
    (fun k => midΓ_le L₁ L₂ h₁ h₂ S hc₁ hc₂ _ _) ?_ hchild ?_ hmxp (mnP_nonneg _ hM)
    (List.prod_nonneg fun A hA' => (hA A hA').le) j
  · have key := cell_hub L₁ L₂ h₁ h₂ S hc₁ hc₂ (offPair k).1 (σ (offPair k).2)
    refine le_trans ?_ key
    refine mul_le_mul_of_nonneg_right ?_ (midΓ_nonneg L₁ L₂ h₁ h₂ S _ _)
    rw [pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg hN 3) hN3 S
  · exact (mul_le_mul_of_nonneg_right (hNc c d) (mnP_nonneg _ hM)).trans (pw_ge _ hM c d)
  · rw [← up_mul, ← up_mul, mul_comm]

/-- **The ball inequalities of a path with a uniform midpoint after `h` steps.** -/
theorem walks_ball_mid (Ms : List (Fin 3 → Fin 3 → ℝ)) (As : List ℝ) (h : ℕ) (hh : 2 ≤ h)
    (hlen : h + 2 ≤ Ms.length) (hM : ∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) (hA : ∀ A ∈ As, 0 < A)
    (hball : List.Forall₂ OffBall Ms As) {N : ℝ} (hN : 0 ≤ N)
    (hN3 : N ^ 3 ≤ 27 * ((sN h : ℝ) * (dN h : ℝ) ^ 2)
        * ((sN (Ms.length - h) : ℝ) * (dN (Ms.length - h) : ℝ) ^ 2))
    (hNc : ∀ c d, N ≤ cnt Ms.length c d) (σ : Fin 3 → Fin 3) (hσ : Function.Injective σ)
    (j : Fin 6) (c d : Fin 3) :
    (N * As.prod) ^ 600
      ≤ (∏ k ∈ univ.erase j, pw Ms (offPair k).1 (σ (offPair k).2)) ^ 100
        * pw Ms (offPair j).1 (σ (offPair j).2) ^ 91 * pw Ms c d ^ 9 := by
  have e : Ms.take h ++ Ms.drop h = Ms := List.take_append_drop h Ms
  have hl₁ : (Ms.take h).length = h := by simp; omega
  have hl₂ : (Ms.drop h).length = Ms.length - h := by simp
  have key := walks_ball_mid' (Ms.take h) (Ms.drop h) As (by omega) (by omega)
    (by rw [e]; exact hM) hA (by rw [e]; exact hball) hN (by rw [hl₁, hl₂]; exact hN3)
    (by rw [e]; exact hNc) σ hσ j c d
  rwa [e] at key

/-! ### The numbers -/

/-- The polynomial inequality behind `long_numbers`, for both signs. -/
theorem long_poly (x : ℝ) (hx : 8 ≤ x) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    (16 / 17 * ((2 * x ^ 2 + 1) / 3)) ^ 3
      ≤ 27 * ((x + 2 * ε) / 3 * ((x - ε) / 3) ^ 2) * ((2 * x - 2 * ε) / 3 * ((2 * x + ε) / 3) ^ 2) := by
  obtain ⟨y, hy, rfl⟩ : ∃ y, 0 ≤ y ∧ x = y + 8 := ⟨x - 8, by linarith, by ring⟩
  rcases hε with rfl | rfl
  · have e : 27 * ((y + 8 + 2 * 1) / 3 * ((y + 8 - 1) / 3) ^ 2)
          * ((2 * (y + 8) - 2 * 1) / 3 * ((2 * (y + 8) + 1) / 3) ^ 2)
        - (16 / 17 * ((2 * (y + 8) ^ 2 + 1) / 3)) ^ 3
        = (947380876 + 896710266 * y + 327814338 * y ^ 2 + 60708078 * y ^ 3 + 6078018 * y ^ 4
          + 313728 * y ^ 5 + 6536 * y ^ 6) / 132651 := by ring
    have : 0 ≤ (947380876 + 896710266 * y + 327814338 * y ^ 2 + 60708078 * y ^ 3
        + 6078018 * y ^ 4 + 313728 * y ^ 5 + 6536 * y ^ 6) / 132651 := by positivity
    linarith
  · have e : 27 * ((y + 8 + 2 * -1) / 3 * ((y + 8 - -1) / 3) ^ 2)
          * ((2 * (y + 8) - 2 * -1) / 3 * ((2 * (y + 8) + -1) / 3) ^ 2)
        - (16 / 17 * ((2 * (y + 8) ^ 2 + 1) / 3)) ^ 3
        = (877419756 + 870356934 * y + 324512802 * y ^ 2 + 60570514 * y ^ 3 + 6078018 * y ^ 4
          + 313728 * y ^ 5 + 6536 * y ^ 6) / 132651 := by ring
    have : 0 ≤ (877419756 + 870356934 * y + 324512802 * y ^ 2 + 60570514 * y ^ 3
        + 6078018 * y ^ 4 + 313728 * y ^ 5 + 6536 * y ^ 6) / 132651 := by positivity
    linarith

/-- The walk counts in terms of `x = 2 ^ r`. -/
theorem counts_closed (r : ℕ) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ (sN r : ℝ) = ((2 : ℝ) ^ r + 2 * ε) / 3 ∧
      (dN r : ℝ) = ((2 : ℝ) ^ r - ε) / 3 ∧ (sN (r + 1) : ℝ) = (2 * (2 : ℝ) ^ r - 2 * ε) / 3 ∧
      (dN (r + 1) : ℝ) = (2 * (2 : ℝ) ^ r + ε) / 3 := by
  have t0 : ((2 ^ r : ℕ) : ℝ) = 2 * dN r + sN r := by exact_mod_cast two_pow_eq r
  have t1 : ((2 ^ (r + 1) : ℕ) : ℝ) = 2 * dN (r + 1) + sN (r + 1) := by
    exact_mod_cast two_pow_eq (r + 1)
  push_cast at t0 t1
  rw [pow_succ] at t1
  rcases Nat.even_or_odd r with he | ho
  · have p0 : (sN r : ℝ) = dN r + 1 := by exact_mod_cast (sN_dN_parity r).1 he
    have p1 : (dN (r + 1) : ℝ) = sN (r + 1) + 1 := by
      exact_mod_cast (sN_dN_parity (r + 1)).2 (Even.add_one he)
    refine ⟨1, Or.inl rfl, ?_, ?_, ?_, ?_⟩ <;> linarith
  · have p0 : (dN r : ℝ) = sN r + 1 := by exact_mod_cast (sN_dN_parity r).2 ho
    have p1 : (sN (r + 1) : ℝ) = dN (r + 1) + 1 := by
      exact_mod_cast (sN_dN_parity (r + 1)).1 (Odd.add_one ho)
    refine ⟨-1, Or.inr rfl, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- **The numbers of the long face**: `n = 2 r + 1` steps, `r ≥ 3`, split after `r` steps,
`N = (16/17) d_n`. -/
theorem long_numbers (r : ℕ) (hr : 3 ≤ r) :
    (16 / 17 * (dN (2 * r + 1) : ℝ)) ^ 3
        ≤ 27 * ((sN r : ℝ) * (dN r : ℝ) ^ 2) * ((sN (r + 1) : ℝ) * (dN (r + 1) : ℝ) ^ 2) ∧
      ∀ c d : Fin 3, 16 / 17 * (dN (2 * r + 1) : ℝ) ≤ cnt (2 * r + 1) c d := by
  have hx : (8 : ℝ) ≤ 2 ^ r := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hr
  have tn : ((2 ^ (2 * r + 1) : ℕ) : ℝ) = 2 * dN (2 * r + 1) + sN (2 * r + 1) := by
    exact_mod_cast two_pow_eq (2 * r + 1)
  have pn : (dN (2 * r + 1) : ℝ) = sN (2 * r + 1) + 1 := by
    exact_mod_cast (sN_dN_parity (2 * r + 1)).2 ⟨r, rfl⟩
  push_cast at tn
  have e2 : (2 : ℝ) ^ (2 * r + 1) = 2 * ((2 : ℝ) ^ r) ^ 2 := by ring
  rw [e2] at tn
  have hdn : (dN (2 * r + 1) : ℝ) = (2 * ((2 : ℝ) ^ r) ^ 2 + 1) / 3 := by linarith
  obtain ⟨ε, hε, h1, h2, h3, h4⟩ := counts_closed r
  refine ⟨?_, fun c d => ?_⟩
  · rw [hdn, h1, h2, h3, h4]
    exact long_poly _ hx ε hε
  · have hc : (sN (2 * r + 1) : ℝ) ≤ cnt (2 * r + 1) c d := by
      unfold cnt
      split_ifs
      · exact le_rfl
      · linarith
    have h17 : (17 : ℝ) ≤ dN (2 * r + 1) := by
      rw [hdn]; nlinarith
    linarith

/-! ### The face -/

/-- **An even face of length at least eight maps the ball class on all its path edges to the ball
class on its root edge**, with the factor `16/17`. -/
theorem ballEvenLong (m : ℕ) (hev : Even m) (h6 : 6 ≤ m) (Lu Lv : Finset ℕ)
    (Li : Fin m → Finset ℕ) (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 < A j)
    (hE : ∀ j, InBall (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    InBall Lu Lv (faceSum Li (fun _ _ => 1) E) (16 / 17 * faceConst3 m * ∏ j, A j) := by
  refine inBall_of_idx hLu hLv fun α β hα hβ hαm hβm _ => ⟨id, Function.bijective_id, ?_⟩
  intro j c d _
  set Vs := List.ofFn Li ++ [Lv] with hVs
  have hVcard : ∀ L ∈ Vs, L.card = 3 := by
    intro L hL
    rcases List.mem_append.mp hL with h | h
    · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp h
      exact hLi i
    · rw [List.mem_singleton.mp h]
      exact hLv
  have hEs0 : ∀ E' ∈ List.ofFn E, ∀ c d, 0 ≤ E' c d := by
    intro E' hE' c d
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hE'
    exact hE0 i c d
  have hAs : ∀ A' ∈ List.ofFn A, 0 < A' := by
    intro A' hA'
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hA'
    exact hA i
  obtain ⟨ζs, hζs, hOff, hMnn⟩ := frames Vs (List.ofFn E) (List.ofFn A) Lu α hα hαm hVcard hEs0
    (chain_of_fin Lu Lv Li E A hE)
  have hlenV : Vs.length = m + 1 := by simp [hVs]
  have hlenE : (List.ofFn E).length = m + 1 := List.length_ofFn
  have hlenζ : ζs.length = m + 1 := by rw [hζs.length_eq, hlenV]
  set Ms := mkMs α ζs (List.ofFn E) with hMs
  have hlenM : Ms.length = m + 1 := by
    rw [hMs, mkMs_length _ _ _ (by rw [hlenζ, hlenE]), hlenE]
  have hend : Function.Injective (ζs.getLastD α) ∧ ∀ a, (ζs.getLastD α) a ∈ Lv := by
    have h := forall₂_getLastD (P := fun ζ L => Function.Injective ζ ∧ ∀ a, ζ a ∈ L) ζs Vs α Lu
      hζs ⟨hα, hαm⟩
    have e : Vs.getLastD Lu = Lv := by
      rw [hVs, getLastD_append]
      rfl
    rwa [e] at h
  have himg : ∀ b, ∃ x, (ζs.getLastD α) x = β b := fun b => by
    have hb : β b ∈ univ.image (ζs.getLastD α) := by
      rw [image_enum hLv hend.1 hend.2]
      exact hβm b
    obtain ⟨x, -, hx⟩ := mem_image.mp hb
    exact ⟨x, hx⟩
  choose σ hσ using himg
  have hσinj : Function.Injective σ := fun b b' e => hβ (by rw [← hσ b, ← hσ b', e])
  obtain ⟨r, hr⟩ := hev
  have hr3 : 3 ≤ r := by omega
  have hlen' : Ms.length = 2 * r + 1 := by rw [hlenM]; omega
  obtain ⟨hnum, hcnt⟩ := long_numbers r hr3
  have key := walks_ball_mid Ms (List.ofFn A) r (by omega) (by omega) hMnn hAs hOff
    (N := 16 / 17 * (dN (2 * r + 1) : ℝ)) (by positivity)
    (by rw [hlen', show 2 * r + 1 - r = r + 1 by omega]; exact hnum)
    (by rw [hlen']; exact hcnt) σ hσinj j c (σ d)
  have hp := pw_nonneg Ms hMnn
  have hcell : ∀ a b : Fin 3, pw Ms a (σ b) ≤ faceSum Li (fun _ _ => 1) E (α a) (β b) :=
    fun a b => by
      rw [faceSum_eq_psum Li Lv E (α a) (β b) (hβm b), ← hσ b]
      exact pw_le_psum Vs (List.ofFn E) ζs α (by rw [hlenE, hlenV]) hζs hEs0 a (σ b)
  show (16 / 17 * faceConst3 m * ∏ j, A j) ^ 600
    ≤ (∏ k ∈ univ.erase j, faceSum Li (fun _ _ => 1) E (α (offPair k).1) (β (offPair k).2)) ^ 100
      * faceSum Li (fun _ _ => 1) E (α (offPair j).1) (β (offPair j).2) ^ 91
      * faceSum Li (fun _ _ => 1) E (α c) (β d) ^ 9
  calc (16 / 17 * faceConst3 m * ∏ j, A j) ^ 600
      = (16 / 17 * (dN (2 * r + 1) : ℝ) * (List.ofFn A).prod) ^ 600 := by
        rw [faceConst3_eq_dN, List.prod_ofFn, show dN (m + 1) = dN (2 * r + 1) by
          congr 1; omega]
    _ ≤ (∏ k ∈ univ.erase j, pw Ms (offPair k).1 (σ (offPair k).2)) ^ 100
        * pw Ms (offPair j).1 (σ (offPair j).2) ^ 91 * pw Ms c (σ d) ^ 9 := key
    _ ≤ _ := by
        refine mul_le_mul (mul_le_mul (pow_le_pow_left₀ (prod_nonneg fun k _ => hp _ _)
          (Finset.prod_le_prod₀ (fun k _ => hp _ _) fun k _ => hcell _ _) _)
          (pow_le_pow_left₀ (hp _ _) (hcell _ _) _) (pow_nonneg (hp _ _) _)
          (pow_nonneg (prod_nonneg fun k _ => (hp _ _).trans (hcell _ _)) _))
          (pow_le_pow_left₀ (hp _ _) (hcell _ _) _) (pow_nonneg (hp _ _) _)
          (mul_nonneg (pow_nonneg (prod_nonneg fun k _ => (hp _ _).trans (hcell _ _)) _)
            (pow_nonneg ((hp _ _).trans (hcell _ _)) _))

end Outerplanar

/-- info: 'Outerplanar.ballEvenLong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Outerplanar.ballEvenLong
