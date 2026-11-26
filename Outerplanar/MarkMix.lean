/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.LongFaceGain
import Outerplanar.SevenSwap

/-!
# Mixture classes for the mark classes

The mark classes of the thirteen-even-face theorem (research note
`ai_research_notes/OUTERPLANAR_ELEVEN_AND_CENTRAL_SQUARE_2026-11-23.md`, "Stronger estimates through
three marks", "Four and five marks"; plan `ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`, §1.2)
all have the shape of the mixture class `BMix` of `Outerplanar/Mix.lean`: a profile dominates
`u + Y` on proper pairs, where `Y` has some property `P` with a constant `v` and `u + v ≥ N`. The
properties used are conjunctions of floors, bijection products, four-cell bounds, the ball, the
hexagon bound and the hull, and each of these is closed under sums (weighted geometric means are
superadditive), scaling, increase and smaller constants.

* `pow_superadd`, `BijGe.add`, `TB.add`, `Hex.add`, `HullV.add`, `HullC.add`, and the scalings and
  monotonicity of the same classes; `BijGe.lift`, `BijGe.hex`.
* `ConeP P` — the closure properties; `Mx P S T W N` — the mixture class of `P`.
* `Mx.of_dom`, `Mx.of_P`, `Mx.mono`, `Mx.weaken`, `Mx.add`, `Mx.finsum`, `Mx.mul_dom`, `Mx.imp`,
  `Mx.swap`, `Mx.lift`, `Mx.mul` — closure of the mixture class.
* **`mx_expand`** — the multilinear expansion of a face: if every term of the expansion of the
  children's mixtures (each path edge either its constant or its table) is in `Mx P`, so is the
  face.
* `bijGe_face`, `bijGe_tri` — bijection surpluses through faces of length at least four (the
  matching theorem) and through triangles (Hall, with the four-cell bounds paying a failure).
* `hull_pair` — two distinct cells of a matched family in the hull class have product at least
  `2/3` of the squared constant.

The theorems of the notes are due to another AI session of this repository's collaboration; audited
and formalized by Claude.
-/

namespace Outerplanar

open Finset

/-! ### Superadditivity -/

/-- A root of a nonnegative number. -/
theorem exists_root {K : ℝ} (hK : 0 ≤ K) {e : ℕ} (he : 0 < e) : ∃ κ : ℝ, 0 ≤ κ ∧ κ ^ e = K :=
  ⟨K ^ ((1 : ℝ) / e), Real.rpow_nonneg hK _, by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK, one_div_mul_cancel (by exact_mod_cast he.ne'),
      Real.rpow_one]⟩

/-- **The bound `K N^e ≤ ∏ x^n` is superadditive in `(N, x)`.** -/
theorem pow_superadd {ι : Type*} (s : Finset ι) (x y : ι → ℝ) (n : ι → ℕ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hy : ∀ i ∈ s, 0 ≤ y i) {K N N' : ℝ} (hK : 0 ≤ K) (hN : 0 ≤ N)
    (hN' : 0 ≤ N') (hn : 0 < ∑ i ∈ s, n i) (h1 : K * N ^ (∑ i ∈ s, n i) ≤ ∏ i ∈ s, x i ^ n i)
    (h2 : K * N' ^ (∑ i ∈ s, n i) ≤ ∏ i ∈ s, y i ^ n i) :
    K * (N + N') ^ (∑ i ∈ s, n i) ≤ ∏ i ∈ s, (x i + y i) ^ n i := by
  obtain ⟨κ, hκ, hκe⟩ := exists_root hK hn
  have e1 : ∀ M : ℝ, K * M ^ (∑ i ∈ s, n i) = (κ * M) ^ (∑ i ∈ s, n i) := fun M => by
    rw [mul_pow, hκe]
  rw [e1] at h1 h2 ⊢
  rw [mul_add]
  exact gm_superadd s x y n hx hy (mul_nonneg hκ hN) (mul_nonneg hκ hN') hn h1 h2

section Closure

variable {S T U : Finset ℕ} {W W' : ℕ → ℕ → ℝ} {N N' Q τ : ℝ}

theorem BijGe.add (hQ : 0 ≤ Q) (hN : 0 ≤ N) (hN' : 0 ≤ N') (h0 : ∀ c d, 0 ≤ W c d)
    (h0' : ∀ c d, 0 ≤ W' c d) (h : BijGe S T W N Q) (h' : BijGe S T W' N' Q) :
    BijGe S T (fun c d => W c d + W' c d) (N + N') Q := fun α β hα hβ hαm hβm hne => by
  have key := pow_superadd univ (fun a => W (α a) (β a)) (fun a => W' (α a) (β a)) (fun _ => 1)
    (fun _ _ => h0 _ _) (fun _ _ => h0' _ _) hQ hN hN' (by simp)
    (by simpa using h α β hα hβ hαm hβm hne) (by simpa using h' α β hα hβ hαm hβm hne)
  simpa using key

theorem BijGe.smul {l : ℝ} (hl : 0 ≤ l) (h : BijGe S T W N Q) :
    BijGe S T (fun c d => l * W c d) (l * N) Q := fun α β hα hβ hαm hβm hne => by
  have := h α β hα hβ hαm hβm hne
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc Q * (l * N) ^ 3 = l ^ 3 * (Q * N ^ 3) := by ring
    _ ≤ l ^ 3 * ∏ a, W (α a) (β a) := mul_le_mul_of_nonneg_left this (by positivity)

theorem BijGe.mono (h : BijGe S T W N Q) (h0 : ∀ c d, 0 ≤ W c d)
    (hle : ∀ c ∈ S, ∀ d ∈ T, c ≠ d → W c d ≤ W' c d) : BijGe S T W' N Q :=
  fun α β hα hβ hαm hβm hne => (h α β hα hβ hαm hβm hne).trans
    (Finset.prod_le_prod₀ (fun a _ => h0 _ _) fun a _ => hle _ (hαm a) _ (hβm a) (hne a))

theorem BijGe.weaken (hQ : 0 ≤ Q) (hN' : 0 ≤ N') (hle : N' ≤ N) (h : BijGe S T W N Q) :
    BijGe S T W N' Q := fun α β hα hβ hαm hβm hne =>
  le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hN' hle 3) hQ) (h α β hα hβ hαm hβm hne)

theorem BijGe.weakenQ {Q' : ℝ} (hN : 0 ≤ N) (hle : Q' ≤ Q) (h : BijGe S T W N Q) :
    BijGe S T W N Q' := fun α β hα hβ hαm hβm hne =>
  le_trans (mul_le_mul_of_nonneg_right hle (pow_nonneg hN 3)) (h α β hα hβ hαm hβm hne)

theorem BijGe.mul {Q' : ℝ} (hQ : 0 ≤ Q) (hN : 0 ≤ N) (hQ' : 0 ≤ Q') (hN' : 0 ≤ N')
    (h : BijGe S T W N Q) (h' : BijGe S T W' N' Q') :
    BijGe S T (fun c d => W c d * W' c d) (N * N') (Q * Q') := fun α β hα hβ hαm hβm hne => by
  have h1 := h α β hα hβ hαm hβm hne
  have h2 := h' α β hα hβ hαm hβm hne
  rw [Finset.prod_mul_distrib]
  calc Q * Q' * (N * N') ^ 3 = (Q * N ^ 3) * (Q' * N' ^ 3) := by ring
    _ ≤ _ := mul_le_mul h1 h2 (by positivity) ((by positivity : (0 : ℝ) ≤ Q * N ^ 3).trans h1)

theorem BijGe.lift (hS : S.card = 3) (hT : T.card = 3) (hX : ∀ c d, 0 ≤ W c d) (hQ : 0 ≤ Q)
    (hN : 0 ≤ N) (h : BijGe S T W N Q) : BijGe S U (fun c _ => liftV T W c) (2 * N) Q := by
  have hp := lift_prod hS hT hX (K := Q * N ^ 3) (by positivity) fun p q hm hpq => by
    obtain ⟨α, β, hα, hβ, hαm, hβm, h1, h2, e⟩ := hm.prod_two hpq W
    rw [e, sq]
    have k1 := h α (fun a => β (a + 1)) hα (fun a b e' => add_right_cancel (hβ e')) hαm
      (fun a => hβm _) h1
    have k2 := h α (fun a => β (a + 2)) hα (fun a b e' => add_right_cancel (hβ e')) hαm
      (fun a => hβm _) h2
    exact mul_le_mul k1 k2 (by positivity) (Finset.prod_nonneg fun _ _ => hX _ _)
  intro α β hα _ hαm _ _
  rw [prod_enum hS hα hαm (fun c => liftV T W c)]
  calc Q * (2 * N) ^ 3 = 8 * (Q * N ^ 3) := by ring
    _ ≤ _ := hp

/-- A bijection surplus `κ³` gives the hexagon bound with `κ`. -/
theorem BijGe.hex {κ : ℝ} (hκ : 0 ≤ κ) (hN : 0 ≤ N) (h0 : ∀ c d, 0 ≤ W c d)
    (h : BijGe S T W N (κ ^ 3)) : Hex S T W (N * κ) := fun p q hm hpq => by
  obtain ⟨α, β, hα, hβ, hαm, hβm, h1, h2, e⟩ := hm.prod_two hpq W
  rw [e]
  have k1 := h α (fun a => β (a + 1)) hα (fun a b e' => add_right_cancel (hβ e')) hαm
    (fun a => hβm _) h1
  have k2 := h α (fun a => β (a + 2)) hα (fun a b e' => add_right_cancel (hβ e')) hαm
    (fun a => hβm _) h2
  calc (N * κ) ^ 6 = (κ ^ 3 * N ^ 3) * (κ ^ 3 * N ^ 3) := by ring
    _ ≤ _ := mul_le_mul k1 k2 (by positivity) (Finset.prod_nonneg fun _ _ => h0 _ _)

theorem TB.add (hτ : 0 ≤ τ) (hN : 0 ≤ N) (hN' : 0 ≤ N') (h0 : ∀ c d, 0 ≤ W c d)
    (h0' : ∀ c d, 0 ≤ W' c d) (h : TB S T W N τ) (h' : TB S T W' N' τ) :
    TB S T (fun c d => W c d + W' c d) (N + N') τ := by
  intro p q hm hpq i j k l hij hik hil hjk hjl hkl
  set x : Fin 4 → ℝ := ![W (p i) (q i), W (p j) (q j), W (p k) (q k), W (p l) (q l)] with hx
  set y : Fin 4 → ℝ := ![W' (p i) (q i), W' (p j) (q j), W' (p k) (q k), W' (p l) (q l)] with hy
  set n : Fin 4 → ℕ := ![2, 2, 1, 1] with hn
  have hsum : ∑ z, n z = 6 := by simp [hn, Fin.sum_univ_four]
  have hpx : ∀ M : ℝ, M ^ 6 * τ ^ 2 = τ ^ 2 * M ^ 6 := fun M => mul_comm _ _
  have key := pow_superadd univ x y n (fun z _ => by fin_cases z <;> simp [hx, h0])
    (fun z _ => by fin_cases z <;> simp [hy, h0']) (sq_nonneg τ) hN hN' (by rw [hsum]; norm_num)
    (by
      rw [hsum]
      have := h p q hm hpq i j k l hij hik hil hjk hjl hkl
      simpa [hx, hn, Fin.prod_univ_four, mul_assoc] using this)
    (by
      rw [hsum]
      have := h' p q hm hpq i j k l hij hik hil hjk hjl hkl
      simpa [hy, hn, Fin.prod_univ_four, mul_assoc] using this)
  rw [hsum] at key
  simpa [hx, hy, hn, Fin.prod_univ_four, mul_assoc] using key

theorem TB.smul {l : ℝ} (hl : 0 ≤ l) (h : TB S T W N τ) :
    TB S T (fun c d => l * W c d) (l * N) τ := by
  have hd : TB S T (fun _ _ => l) l 1 := Dominant.tb (fun _ _ _ _ _ => le_refl l) hl
  have := hd.mul h
  rwa [one_mul] at this

theorem TB.weaken (hN' : 0 ≤ N') (hle : N' ≤ N) (h : TB S T W N τ) : TB S T W N' τ := by
  intro p q hm hpq i j k l hij hik hil hjk hjl hkl
  refine le_trans ?_ (h p q hm hpq i j k l hij hik hil hjk hjl hkl)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hN' hle 6) (sq_nonneg τ)

theorem Hex.add (hN : 0 ≤ N) (hN' : 0 ≤ N') (h0 : ∀ c d, 0 ≤ W c d) (h0' : ∀ c d, 0 ≤ W' c d)
    (h : Hex S T W N) (h' : Hex S T W' N') : Hex S T (fun c d => W c d + W' c d) (N + N') :=
  fun p q hm hpq => by
    have key := pow_superadd univ (fun i => W (p i) (q i)) (fun i => W' (p i) (q i))
      (fun _ => 1) (fun _ _ => h0 _ _) (fun _ _ => h0' _ _) zero_le_one hN hN' (by simp)
      (by simpa using h p q hm hpq) (by simpa using h' p q hm hpq)
    simpa using key

theorem Hex.smul {l : ℝ} (hl : 0 ≤ l) (hN : 0 ≤ N) (h : Hex S T W N) :
    Hex S T (fun c d => l * W c d) (l * N) :=
  (Dominant.hex (fun _ _ _ _ _ => le_refl l) hl : Hex S T (fun _ _ => l) l).mul hl hN h

theorem Hex.weaken (hN' : 0 ≤ N') (hle : N' ≤ N) (h : Hex S T W N) : Hex S T W N' :=
  fun p q hm hpq => le_trans (pow_le_pow_left₀ hN' hle 6) (h p q hm hpq)

theorem Hex.swap' (h : Hex S T W N) : Hex T S (fun d c => W c d) N :=
  fun p q hm hpq => h q p hm.symm fun i => (hpq i).symm

theorem Dominant.add (h : Dominant S T W N) (h' : Dominant S T W' N') :
    Dominant S T (fun c d => W c d + W' c d) (N + N') := fun c hc d hd hcd =>
  add_le_add (h c hc d hd hcd) (h' c hc d hd hcd)

theorem Dominant.smul {l : ℝ} (hl : 0 ≤ l) (h : Dominant S T W N) :
    Dominant S T (fun c d => l * W c d) (l * N) := fun c hc d hd hcd =>
  mul_le_mul_of_nonneg_left (h c hc d hd hcd) hl

theorem Dominant.mono (h : Dominant S T W N) (hle : ∀ c ∈ S, ∀ d ∈ T, c ≠ d → W c d ≤ W' c d) :
    Dominant S T W' N := fun c hc d hd hcd => (h c hc d hd hcd).trans (hle c hc d hd hcd)

theorem HullV.add {A A' : ℝ} {x x' : Fin 6 → ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A') (h : HullV A x)
    (h' : HullV A' x') : HullV (A + A') fun z => x z + x' z := by
  obtain ⟨μ₀, μ, h0, hμ, hok, h1, hx⟩ := h
  obtain ⟨μ₀', μ', h0', hμ', hok', h1', hx'⟩ := h'
  rcases (add_nonneg hA hA').eq_or_lt with hz | hpos
  · have hA0 : A = 0 := by linarith
    have hA0' : A' = 0 := by linarith
    refine HullV.of_ge fun z => ?_
    have a1 := hx z
    have a2 := hx' z
    rw [hA0, zero_mul] at a1
    rw [hA0', zero_mul] at a2
    rw [← hz]
    linarith
  set s := A + A' with hs
  refine ⟨(A * μ₀ + A' * μ₀') / s, fun t => (A * μ t + A' * μ' t) / s, by positivity,
    fun t => by have := hμ t; have := hμ' t; positivity, fun t ht => ?_, ?_, fun z => ?_⟩
  · by_cases h1 : μ t = 0
    · by_cases h2 : μ' t = 0
      · exact absurd (by simp [h1, h2]) ht
      · exact hok' t h2
    · exact hok t h1
  · rw [← Finset.sum_div, ← add_div, div_eq_one_iff_eq hpos.ne', Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    have e1 : ∑ t, μ t = 1 - μ₀ := by linarith
    have e2 : ∑ t, μ' t = 1 - μ₀' := by linarith
    rw [e1, e2]
    ring
  · have e : s * (3 * ((A * μ₀ + A' * μ₀') / s) + ∑ t, (A * μ t + A' * μ' t) / s * vtx t z)
        = A * (3 * μ₀ + ∑ t, μ t * vtx t z) + A' * (3 * μ₀' + ∑ t, μ' t * vtx t z) := by
      have : ∑ t, (A * μ t + A' * μ' t) / s * vtx t z
          = (A * ∑ t, μ t * vtx t z + A' * ∑ t, μ' t * vtx t z) / s := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
        exact Finset.sum_congr rfl fun t _ => by ring
      rw [this]
      field_simp
      ring
    rw [e]
    linarith [hx z, hx' z]

theorem HullC.add {A A' : ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A') (h : HullC S T W A)
    (h' : HullC S T W' A') : HullC S T (fun c d => W c d + W' c d) (A + A') := by
  refine ⟨fun p q hm hpq => HullV.add hA hA' (h.1 p q hm hpq) (h'.1 p q hm hpq), ?_⟩
  have := h.2.add h'.2
  rwa [show 2 / 3 * A + 2 / 3 * A' = 2 / 3 * (A + A') by ring] at this

theorem HullC.smul {A l : ℝ} (hl : 0 ≤ l) (hA : 0 ≤ A) (h0 : ∀ c d, 0 ≤ W c d)
    (h : HullC S T W A) : HullC S T (fun c d => l * W c d) (l * A) :=
  HullC.mul_dom (W' := fun _ _ => l) hA hl h0 (fun _ _ _ _ _ => le_refl l) h

theorem HullC.weaken {A A' : ℝ} (hA' : 0 ≤ A') (hle : A' ≤ A) (h : HullC S T W A) :
    HullC S T W A' :=
  ⟨fun p q hm hpq => (h.1 p q hm hpq).le_const hle, fun c hc d hd hcd =>
    le_trans (by linarith) (h.2 c hc d hd hcd)⟩

/-- **Two distinct cells of a matched family in the hull class have product at least `2/3` of
the squared constant.** The geometric mean of two coordinates is concave, so the minimum over the
hull is at a vertex: `3 · 3` at the constant, at least `2 · 3` at the others. -/
theorem hullV_pair {A : ℝ} {x : Fin 6 → ℝ} (hA : 0 ≤ A) (h : HullV A x) {i j : Fin 6}
    (hij : i ≠ j) : 2 / 3 * A ^ 2 ≤ x i * x j := by
  obtain ⟨μ₀, μ, h0, hμ, hok, h1, hx⟩ := h
  -- the mixture as a sum over `Option Tr`
  set ω : Option Tr → ℝ := fun o => o.elim μ₀ μ with hω
  set val : Option Tr → Fin 6 → ℝ := fun o z => o.elim 3 (fun t => vtx t z) with hval
  have hω0 : ∀ o, 0 ≤ ω o := fun o => by cases o <;> simp [hω, h0, hμ]
  have hω1 : ∑ o, ω o = 1 := by rw [Fintype.sum_option]; exact h1
  have hval0 : ∀ o z, 0 ≤ val o z := fun o z => by
    cases o
    · simp [hval]
    · exact vtx_nonneg _ _
  have hmix : ∀ z, ∑ o, ω o * val o z = 3 * μ₀ + ∑ t, μ t * vtx t z := fun z => by
    rw [Fintype.sum_option]
    simp [hω, hval, mul_comm]
  -- each vertex has pair product at least six
  have hv : ∀ o, ω o ≠ 0 → 6 ≤ val o i * val o j := fun o ho => by
    cases o with
    | none =>
      show (6 : ℝ) ≤ 3 * 3
      norm_num
    | some t =>
      obtain ⟨t1, t2, t3⟩ := t
      have htok := hok (t1, t2, t3) ho
      obtain ⟨h12, h13, h23⟩ := htok
      have hge3 : ∀ z, z ≠ t1 → 3 ≤ vtx (t1, t2, t3) z := fun z hz => by
        unfold vtx
        dsimp only
        rw [if_neg hz]
        by_cases a2 : z = t2 <;> by_cases a3 : z = t3 <;>
          simp only [a2, a3, h23, Ne.symm h23, ite_true, ite_false] <;> first
            | norm_num
            | exact absurd (a2.symm.trans a3) h23
      have hge2 : ∀ z, 2 ≤ vtx (t1, t2, t3) z := fun z => by
        by_cases hz : z = t1
        · subst hz
          unfold vtx
          dsimp only
          rw [if_pos rfl, if_neg h12, if_neg h13]
          norm_num
        · linarith [hge3 z hz]
      show 6 ≤ vtx (t1, t2, t3) i * vtx (t1, t2, t3) j
      by_cases hi : i = t1
      · have := hge3 j (fun e => hij (hi.trans e.symm))
        nlinarith [hge2 i]
      · have := hge3 i hi
        nlinarith [hge2 j]
  -- weighted AM–GM on each coordinate
  have hgm : ∀ z, ∏ o, val o z ^ ω o ≤ ∑ o, ω o * val o z := fun z =>
    Real.geom_mean_le_arith_mean_weighted univ ω (fun o => val o z) (fun o _ => hω0 o) hω1
      (fun o _ => hval0 o z)
  have hprod : (6 : ℝ) ≤ (∏ o, val o i ^ ω o) * ∏ o, val o j ^ ω o := by
    rw [← Finset.prod_mul_distrib]
    calc (6 : ℝ) = (6 : ℝ) ^ (∑ o, ω o) := by rw [hω1, Real.rpow_one]
      _ = ∏ o, (6 : ℝ) ^ ω o := Real.rpow_sum_of_nonneg (by norm_num) fun o _ => hω0 o
      _ ≤ ∏ o, (val o i * val o j) ^ ω o := Finset.prod_le_prod₀
          (fun o _ => Real.rpow_nonneg (by norm_num) _) fun o _ => by
            by_cases ho : ω o = 0
            · rw [ho, Real.rpow_zero, Real.rpow_zero]
            · exact Real.rpow_le_rpow (by norm_num) (hv o ho) (hω0 o)
      _ = ∏ o, val o i ^ ω o * val o j ^ ω o := Finset.prod_congr rfl fun o _ =>
          Real.mul_rpow (hval0 o i) (hval0 o j)
  have hg0 : ∀ z, 0 ≤ ∏ o, val o z ^ ω o := fun z =>
    Finset.prod_nonneg fun o _ => Real.rpow_nonneg (hval0 o z) _
  have ki := (mul_le_mul_of_nonneg_left ((hgm i).trans (le_of_eq (hmix i))) hA).trans (hx i)
  have kj := (mul_le_mul_of_nonneg_left ((hgm j).trans (le_of_eq (hmix j))) hA).trans (hx j)
  have := mul_le_mul ki kj (mul_nonneg hA (hg0 j)) (by linarith [mul_nonneg hA (hg0 i)])
  nlinarith [mul_nonneg hA hA]

theorem hull_pair {A : ℝ} (hA : 0 ≤ A) (h : HullC S T W A) {p q : Fin 6 → ℕ}
    (hm : Matched S T p q) (hpq : ∀ i, p i ≠ q i) {i j : Fin 6} (hij : i ≠ j) :
    2 / 3 * A ^ 2 ≤ W (p i) (q i) * W (p j) (q j) :=
  hullV_pair hA (h.1 p q hm hpq) hij

end Closure

/-! ### The mixture class of a property -/

/-- The closure properties of a property `P S T Y v` of tables `Y` with constants `v`. -/
structure ConeP (P : Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop) : Prop where
  zero : ∀ S T, P S T (fun _ _ => 0) 0
  add : ∀ {S T : Finset ℕ} {Y Y' : ℕ → ℕ → ℝ} {v v' : ℝ}, 0 ≤ v → 0 ≤ v' →
    (∀ c d, 0 ≤ Y c d) → (∀ c d, 0 ≤ Y' c d) → P S T Y v → P S T Y' v' →
    P S T (fun c d => Y c d + Y' c d) (v + v')
  smul : ∀ {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} (l : ℝ), 0 ≤ l → 0 ≤ v →
    (∀ c d, 0 ≤ Y c d) → P S T Y v → P S T (fun c d => l * Y c d) (l * v)
  mono : ∀ {S T : Finset ℕ} {Y Y' : ℕ → ℕ → ℝ} {v : ℝ}, (∀ c d, 0 ≤ Y c d) →
    (∀ c ∈ S, ∀ d ∈ T, c ≠ d → Y c d ≤ Y' c d) → P S T Y v → P S T Y' v
  weaken : ∀ {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v v' : ℝ}, 0 ≤ v' → v' ≤ v →
    (∀ c d, 0 ≤ Y c d) → P S T Y v → P S T Y v'

/-- **The mixture class of `P`**: `W` dominates `u + Y` on proper pairs, with `u + v ≥ N` and `Y`
of property `P` with constant `v`. -/
def Mx (P : Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop) (S T : Finset ℕ)
    (W : ℕ → ℕ → ℝ) (N : ℝ) : Prop :=
  ∃ (u v : ℝ) (Y : ℕ → ℕ → ℝ), 0 ≤ u ∧ 0 ≤ v ∧ N ≤ u + v ∧ (∀ c d, 0 ≤ Y c d) ∧
    P S T Y v ∧ ∀ c ∈ S, ∀ d ∈ T, c ≠ d → u + Y c d ≤ W c d

section Mx

variable {P P' P'' : Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop}
  {S T U : Finset ℕ} {W W' : ℕ → ℕ → ℝ} {N N' : ℝ}

theorem Mx.of_dom (hP : ConeP P) (hN : 0 ≤ N) (h : Dominant S T W N) : Mx P S T W N :=
  ⟨N, 0, fun _ _ => 0, hN, le_refl 0, by simp, fun _ _ => le_refl 0, hP.zero S T,
    fun c hc d hd hcd => by simpa using h c hc d hd hcd⟩

theorem Mx.of_P (hN : 0 ≤ N) (h0 : ∀ c d, 0 ≤ W c d) (h : P S T W N) : Mx P S T W N :=
  ⟨0, N, W, le_refl 0, hN, by simp, h0, h, fun c _ d _ _ => by simp⟩

theorem Mx.zero (hP : ConeP P) (h0 : ∀ c d, 0 ≤ W c d) : Mx P S T W 0 :=
  Mx.of_dom hP (le_refl 0) fun c _ d _ _ => h0 c d

theorem Mx.mono (h : Mx P S T W N) (hle : ∀ c ∈ S, ∀ d ∈ T, c ≠ d → W c d ≤ W' c d) :
    Mx P S T W' N := by
  obtain ⟨u, v, Y, hu, hv, hN, hY0, hY, hW⟩ := h
  exact ⟨u, v, Y, hu, hv, hN, hY0, hY, fun c hc d hd hcd =>
    (hW c hc d hd hcd).trans (hle c hc d hd hcd)⟩

theorem Mx.weaken (hle : N' ≤ N) (h : Mx P S T W N) : Mx P S T W N' := by
  obtain ⟨u, v, Y, hu, hv, hN, hY0, hY, hW⟩ := h
  exact ⟨u, v, Y, hu, hv, hle.trans hN, hY0, hY, hW⟩

theorem Mx.dom (h : Mx P S T W N) : Dominant S T W 0 → Dominant S T W 0 := id

theorem Mx.add (hP : ConeP P) (h : Mx P S T W N) (h' : Mx P S T W' N') :
    Mx P S T (fun c d => W c d + W' c d) (N + N') := by
  obtain ⟨u, v, Y, hu, hv, hNuv, hY0, hY, hW⟩ := h
  obtain ⟨u', v', Y', hu', hv', hNuv', hY0', hY', hW'⟩ := h'
  refine ⟨u + u', v + v', fun c d => Y c d + Y' c d, by positivity, by positivity, by linarith,
    fun c d => add_nonneg (hY0 c d) (hY0' c d), hP.add hv hv' hY0 hY0' hY hY',
    fun c hc d hd hcd => ?_⟩
  have h1 := hW c hc d hd hcd
  have h2 := hW' c hc d hd hcd
  show u + u' + (Y c d + Y' c d) ≤ W c d + W' c d
  linarith

theorem Mx.finsum (hP : ConeP P) {ι : Type*} (s : Finset ι) (W : ι → ℕ → ℕ → ℝ) (N : ι → ℝ)
    (h0 : ∀ i ∈ s, ∀ c d, 0 ≤ W i c d) (h : ∀ i ∈ s, Mx P S T (W i) (N i)) :
    Mx P S T (fun c d => ∑ i ∈ s, W i c d) (∑ i ∈ s, N i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Mx.zero hP fun _ _ => le_refl 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact Mx.add hP (h a (mem_insert_self a s))
      (ih (fun i hi => h0 i (mem_insert_of_mem hi)) fun i hi => h i (mem_insert_of_mem hi))

theorem Mx.mul_dom (hP : ConeP P) (hN' : 0 ≤ N') (hW0 : ∀ c d, 0 ≤ W c d)
    (hd : Dominant S T W' N') (h : Mx P S T W N) :
    Mx P S T (fun c d => W' c d * W c d) (N' * N) := by
  obtain ⟨u, v, Y, hu, hv, hN, hY0, hY, hW⟩ := h
  refine ⟨N' * u, N' * v, fun c d => N' * Y c d, mul_nonneg hN' hu, mul_nonneg hN' hv,
    by nlinarith, fun c d => mul_nonneg hN' (hY0 c d), hP.smul N' hN' hv hY0 hY,
    fun c hc d hd' hcd => ?_⟩
  have h1 := hW c hc d hd' hcd
  have h2 := hd c hc d hd' hcd
  calc N' * u + N' * Y c d = N' * (u + Y c d) := by ring
    _ ≤ N' * W c d := mul_le_mul_of_nonneg_left h1 hN'
    _ ≤ W' c d * W c d := mul_le_mul_of_nonneg_right h2 (hW0 c d)

theorem Mx.imp (himp : ∀ {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ}, 0 ≤ v →
      (∀ c d, 0 ≤ Y c d) → P S T Y v → P' S T Y v) (h : Mx P S T W N) : Mx P' S T W N := by
  obtain ⟨u, v, Y, hu, hv, hN, hY0, hY, hW⟩ := h
  exact ⟨u, v, Y, hu, hv, hN, hY0, himp hv hY0 hY, hW⟩

theorem Mx.swap (hsw : ∀ {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ}, P S T Y v →
      P T S (fun d c => Y c d) v) (h : Mx P S T W N) : Mx P T S (fun d c => W c d) N := by
  obtain ⟨u, v, Y, hu, hv, hN, hY0, hY, hW⟩ := h
  exact ⟨u, v, fun d c => Y c d, hu, hv, hN, fun _ _ => hY0 _ _, hsw hY,
    fun d hd c hc hdc => hW c hc d hd (Ne.symm hdc)⟩

/-- **A vertex lift keeps the mixture class**, with the constant doubled. -/
theorem Mx.lift (hl : ∀ {Y : ℕ → ℕ → ℝ} {v : ℝ}, 0 ≤ v → (∀ c d, 0 ≤ Y c d) → P S T Y v →
      P S U (fun c _ => liftV T Y c) (2 * v)) (hT : T.card = 3) (h : Mx P S T W N) :
    Mx P S U (fun c _ => liftV T W c) (2 * N) := by
  obtain ⟨u, v, Y, hu, hv, hN, hY0, hY, hW⟩ := h
  refine ⟨2 * u, 2 * v, fun c _ => liftV T Y c, by positivity, by positivity, by linarith,
    fun c _ => liftV_nonneg hY0 c, hl hv hY0 hY, fun c hc d _ _ => ?_⟩
  have hle : ∑ e ∈ T, (if c ≠ e then u + Y c e else 0) ≤ liftV T W c :=
    Finset.sum_le_sum fun e he => by
      split_ifs with hce
      · exact hW c hc e he hce
      · exact le_refl 0
  have hn := card_filter_ne hT c
  have hsum : ∑ e ∈ T, (if c ≠ e then u + Y c e else 0)
      = ((T.filter fun e => c ≠ e).card : ℝ) * u + liftV T Y c := by
    unfold liftV
    rw [← Finset.sum_filter, ← Finset.sum_filter, ← nsmul_eq_mul, ← Finset.sum_const,
      ← Finset.sum_add_distrib]
  have hn' : (2 : ℝ) ≤ (T.filter fun e => c ≠ e).card := by exact_mod_cast hn
  show 2 * u + liftV T Y c ≤ liftV T W c
  nlinarith

/-- **Products.** `P · P'` lands in `P''`, and so do `P` and `P'`. -/
theorem Mx.mul (hP'' : ConeP P'') (hN' : 0 ≤ N')
    (h1 : ∀ {Y : ℕ → ℕ → ℝ} {v : ℝ}, 0 ≤ v → (∀ c d, 0 ≤ Y c d) → P S T Y v → P'' S T Y v)
    (h2 : ∀ {Y : ℕ → ℕ → ℝ} {v : ℝ}, 0 ≤ v → (∀ c d, 0 ≤ Y c d) → P' S T Y v → P'' S T Y v)
    (h12 : ∀ {Y Y' : ℕ → ℕ → ℝ} {v v' : ℝ}, 0 ≤ v → 0 ≤ v' → (∀ c d, 0 ≤ Y c d) →
      (∀ c d, 0 ≤ Y' c d) → P S T Y v → P' S T Y' v' →
      P'' S T (fun c d => Y c d * Y' c d) (v * v'))
    (h : Mx P S T W N) (h' : Mx P' S T W' N') :
    Mx P'' S T (fun c d => W c d * W' c d) (N * N') := by
  obtain ⟨u, v, Y, hu, hv, hNuv, hY0, hY, hW⟩ := h
  obtain ⟨u', v', Y', hu', hv', hNuv', hY0', hY', hW'⟩ := h'
  have a1 := hP''.smul u hu hv' hY0' (h2 hv' hY0' hY')
  have a2 := hP''.smul u' hu' hv hY0 (h1 hv hY0 hY)
  have a3 := h12 hv hv' hY0 hY0' hY hY'
  have a12 := hP''.add (by positivity) (by positivity) (fun c d => mul_nonneg hu (hY0' c d))
    (fun c d => mul_nonneg hu' (hY0 c d)) a1 a2
  have a123 := hP''.add (by positivity) (by positivity)
    (fun c d => add_nonneg (mul_nonneg hu (hY0' c d)) (mul_nonneg hu' (hY0 c d)))
    (fun c d => mul_nonneg (hY0 c d) (hY0' c d)) a12 a3
  refine ⟨u * u', u * v' + u' * v + v * v',
    fun c d => u * Y' c d + u' * Y c d + Y c d * Y' c d, mul_nonneg hu hu', by positivity,
    ?_, fun c d => by have := hY0 c d; have := hY0' c d; positivity, a123, ?_⟩
  · calc N * N' ≤ (u + v) * (u' + v') := mul_le_mul hNuv hNuv' hN' (by linarith)
      _ = _ := by ring
  · intro c hc d hd hcd
    have e1 := hW c hc d hd hcd
    have e2 := hW' c hc d hd hcd
    have hy := hY0 c d
    have hy' := hY0' c d
    calc u * u' + (u * Y' c d + u' * Y c d + Y c d * Y' c d) = (u + Y c d) * (u' + Y' c d) := by
          ring
      _ ≤ W c d * W' c d := mul_le_mul e1 e2 (by positivity) (by linarith)

/-- The mixture class gives the floor of the constant part plus that of the tables. -/
theorem Mx.floor {l : ℝ} (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (hfl : ∀ {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ}, P S T Y v → Dominant S T Y (l * v))
    (h : Mx P S T W N) : Dominant S T W (l * N) := by
  obtain ⟨u, v, Y, hu, hv, hN, hY0, hY, hW⟩ := h
  intro c hc d hd hcd
  have h1 := hfl hY c hc d hd hcd
  have h2 := hW c hc d hd hcd
  nlinarith

end Mx

/-! ### The expansion of a face -/

/-- The term tables: the constant `u j` (on proper pairs) or the table `Y j`. -/
def gT {m : ℕ} (u : Fin (m + 1) → ℝ) (Y : Fin (m + 1) → ℕ → ℕ → ℝ) (j : Fin (m + 1)) (r : Fin 2) :
    ℕ → ℕ → ℝ := fun c d => if c ≠ d then (if r = 0 then u j else Y j c d) else 0

/-- The term constants. -/
def wT {m : ℕ} (u v : Fin (m + 1) → ℝ) (j : Fin (m + 1)) (r : Fin 2) : ℝ :=
  if r = 0 then u j else v j

section Expand

variable {m : ℕ} {u v : Fin (m + 1) → ℝ} {Y : Fin (m + 1) → ℕ → ℕ → ℝ}

theorem gT_nonneg (hu : ∀ j, 0 ≤ u j) (hY0 : ∀ j c d, 0 ≤ Y j c d) (j : Fin (m + 1)) (r : Fin 2)
    (c d : ℕ) : 0 ≤ gT u Y j r c d := by
  unfold gT
  split_ifs
  · exact hu j
  · exact hY0 j c d
  · exact le_refl 0

theorem gT_dom (S T : Finset ℕ) (j : Fin (m + 1)) {r : Fin 2} (hr : r = 0) :
    Dominant S T (gT u Y j r) (wT u v j r) := fun c _ d _ hcd => by
  simp [gT, wT, hr, hcd]

theorem gT_P {P : Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop} (hP : ConeP P)
    {S T : Finset ℕ} (j : Fin (m + 1)) {r : Fin 2} (hr : r ≠ 0) (hY0 : ∀ c d, 0 ≤ Y j c d)
    (h : P S T (Y j) (v j)) : P S T (gT u Y j r) (wT u v j r) := by
  have e : wT u v j r = v j := by simp [wT, hr]
  rw [e]
  exact hP.mono hY0 (fun c _ d _ hcd => by simp [gT, hr, hcd]) h

theorem fin2_ne_zero {r : Fin 2} (h : r ≠ 0) : r = 1 := by
  rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with h' | h'
  · exact absurd h' h
  · exact h'

/-- **The multilinear expansion of a face.** Each path edge `j` dominates `u j + Y j` with
`A j ≤ u j + v j`; if every term (each edge either the constant `u j` or the table `Y j`) with
positive constants is in `Mx P`, so is the face, with the ordinary constant. -/
theorem mx_expand {P : Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop} (hP : ConeP P)
    (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ) (E : Fin (m + 1) → ℕ → ℕ → ℝ)
    (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ) (hA : ∀ j, 0 < A j)
    (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j) (huv : ∀ j, A j ≤ u j + v j)
    (hY0 : ∀ j c d, 0 ≤ Y j c d)
    (hEY : ∀ j, ∀ c ∈ pathList Lu Lv Li j.castSucc, ∀ d ∈ pathList Lu Lv Li j.succ, c ≠ d →
      u j + Y j c d ≤ E j c d)
    (hterm : ∀ ρ : Fin (m + 1) → Fin 2, (∀ j, 0 < wT u v j (ρ j)) →
      Mx P Lu Lv (faceSum Li (fun _ _ => 1) fun j => gT u Y j (ρ j))
        (faceConst3 m * ∏ j, wT u v j (ρ j))) :
    Mx P Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  classical
  have hG0 := gT_nonneg hu hY0
  have hw0 : ∀ j r, 0 ≤ wT u v j r := fun j r => by
    unfold wT
    split_ifs
    · exact hu j
    · exact hv j
  have hle : ∀ c ∈ Lu, ∀ d ∈ Lv, c ≠ d →
      faceSum Li (fun _ _ => 1) (fun j c d => ∑ r, gT u Y j r c d) c d
        ≤ faceSum Li (fun _ _ => 1) E c d := fun c hc d hd _ => by
    refine faceSum_le_of_le (fun j c d => Finset.sum_nonneg fun r _ => hG0 j r c d)
      (fun j c hc d hd => ?_) hc hd
    rw [Fin.sum_univ_two]
    by_cases hcd : c = d
    · simp only [gT, hcd, ne_eq, not_true_eq_false, ite_false, add_zero]
      exact hE0 _ _ _
    · simp only [gT, ne_eq, hcd, not_false_eq_true, ite_true, one_ne_zero, ite_false]
      exact hEY j c hc d hd hcd
  refine Mx.mono ?_ hle
  have hfun : faceSum Li (fun _ _ => 1) (fun j c d => ∑ r, gT u Y j r c d)
      = fun c d => ∑ ρ : Fin (m + 1) → Fin 2,
          faceSum Li (fun _ _ => 1) (fun j => gT u Y j (ρ j)) c d :=
    funext fun c => funext fun d => faceSum_sum2 Li (gT u Y) c d
  rw [hfun]
  have hα := faceConst3_pos m
  have hconst : faceConst3 m * ∏ j, A j
      ≤ ∑ ρ : Fin (m + 1) → Fin 2, faceConst3 m * ∏ j, wT u v j (ρ j) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hα.le
    have e : ∀ j, u j + v j = ∑ r, wT u v j r := fun j => by
      simp only [wT, Fin.sum_univ_two, ite_true, one_ne_zero, ite_false]
    calc ∏ j, A j ≤ ∏ j, (u j + v j) :=
          Finset.prod_le_prod₀ (fun j _ => (hA j).le) fun j _ => huv j
      _ = ∑ ρ : Fin (m + 1) → Fin 2, ∏ j, wT u v j (ρ j) := by
          simp only [e]
          rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Mx.weaken hconst (Mx.finsum hP univ _ _ (fun ρ _ c d => faceSum_nonneg _ _ _
    (fun _ _ _ => zero_le_one) (fun j c d => hG0 j (ρ j) c d) c d) fun ρ _ => ?_)
  by_cases hz : ∃ j, wT u v j (ρ j) = 0
  · obtain ⟨j, hj⟩ := hz
    rw [Finset.prod_eq_zero (mem_univ j) hj, mul_zero]
    exact Mx.zero hP (faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one)
      (fun j c d => hG0 j (ρ j) c d))
  push Not at hz
  exact hterm ρ fun j => lt_of_le_of_ne (hw0 j (ρ j)) (hz j).symm

/-- The data of children in mixture classes; children in `D` are greedy and get `v = 0`. -/
theorem mx_data {Pc : Fin (m + 1) → Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop}
    (hPc : ∀ j, ConeP (Pc j)) {Lu Lv : Finset ℕ} {Li : Fin m → Finset ℕ}
    {E : Fin (m + 1) → ℕ → ℕ → ℝ} {A : Fin (m + 1) → ℝ} (hA : ∀ j, 0 < A j)
    (hE : ∀ j, Mx (Pc j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j))
    (D : Fin (m + 1) → Prop)
    (hD : ∀ j, D j → Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    ∃ (u v : Fin (m + 1) → ℝ) (Y : Fin (m + 1) → ℕ → ℕ → ℝ), (∀ j, 0 ≤ u j) ∧ (∀ j, 0 ≤ v j) ∧
      (∀ j, A j ≤ u j + v j) ∧ (∀ j c d, 0 ≤ Y j c d) ∧
      (∀ j, Pc j (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (Y j) (v j)) ∧
      (∀ j, ∀ c ∈ pathList Lu Lv Li j.castSucc, ∀ d ∈ pathList Lu Lv Li j.succ, c ≠ d →
        u j + Y j c d ≤ E j c d) ∧ (∀ j, D j → v j = 0) := by
  classical
  have hrep : ∀ j, ∃ (u v : ℝ) (Y : ℕ → ℕ → ℝ), 0 ≤ u ∧ 0 ≤ v ∧ A j ≤ u + v ∧
      (∀ c d, 0 ≤ Y c d) ∧
      Pc j (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) Y v ∧
      (∀ c ∈ pathList Lu Lv Li j.castSucc, ∀ d ∈ pathList Lu Lv Li j.succ, c ≠ d →
        u + Y c d ≤ E j c d) ∧ (D j → v = 0) := fun j => by
    by_cases hDj : D j
    · exact ⟨A j, 0, fun _ _ => 0, (hA j).le, le_refl 0, by simp, fun _ _ => le_refl 0,
        (hPc j).zero _ _, fun c hc d hd hcd => by simpa using hD j hDj c hc d hd hcd,
        fun _ => rfl⟩
    · obtain ⟨u, v, Y, h1, h2, h3, h4, h5, h6⟩ := hE j
      exact ⟨u, v, Y, h1, h2, h3, h4, h5, h6, fun h => absurd h hDj⟩
  choose u v Y hu hv huv hY0 hY hEY hDv using hrep
  exact ⟨u, v, Y, hu, hv, huv, hY0, hY, hEY, hDv⟩

/-- In a term with positive constants, children in `D` are constant. -/
theorem term_D {D : Fin (m + 1) → Prop} (hDv : ∀ j, D j → v j = 0) {ρ : Fin (m + 1) → Fin 2}
    (hρ : ∀ j, 0 < wT u v j (ρ j)) (j : Fin (m + 1)) (hj : D j) : ρ j = 0 := by
  by_contra h
  have := hρ j
  rw [wT, ite_eq_right h, hDv j hj] at this
  exact lt_irrefl 0 this

end Expand

/-! ### Bijection surpluses through faces -/

theorem pathList_card {m : ℕ} {Lu Lv : Finset ℕ} {Li : Fin m → Finset ℕ} (hLu : Lu.card = 3)
    (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3) (i : Fin (m + 2)) :
    (pathList Lu Lv Li i).card = 3 := by
  refine Fin.cases hLu (fun i => ?_) i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simpa [pathList] using hLv
  · simpa [pathList] using hLi i

/-- Cube roots: `BijGe` with surplus `Q` is `BijGe` with constant `N Q^{1/3}` and surplus one. -/
theorem bijGe_cube {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {N Q : ℝ} (hQ : 0 ≤ Q) :
    BijGe S T W N Q ↔ BijGe S T W (N * Q ^ ((1 : ℝ) / 3)) 1 := by
  have hc : (Q ^ ((1 : ℝ) / 3)) ^ 3 = Q := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ]
    norm_num
  constructor
  · intro h α β hα hβ hαm hβm hne
    have := h α β hα hβ hαm hβm hne
    calc 1 * (N * Q ^ ((1 : ℝ) / 3)) ^ 3 = (Q ^ ((1 : ℝ) / 3)) ^ 3 * N ^ 3 := by ring
      _ = Q * N ^ 3 := by rw [hc]
      _ ≤ _ := this
  · intro h
    have := BijGe.of_one h
    rwa [hc] at this

/-- **The matching theorem with surpluses**: at a face of length at least four the bijection
surpluses of the path edges multiply. -/
theorem bijGe_face {m : ℕ} (hm : 2 ≤ m) (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ)
    (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A Q : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 < A j) (hQ : ∀ j, 0 < Q j)
    (hpos : ∀ j, ∀ c ∈ pathList Lu Lv Li j.castSucc, ∀ d ∈ pathList Lu Lv Li j.succ, c ≠ d →
      0 < E j c d)
    (hE : ∀ j, BijGe (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j) (Q j)) :
    BijGe Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) (∏ j, Q j) := by
  have hcard := pathList_card hLu hLv hLi
  have hP : ∀ j, HasPot (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j)
      (A j * Q j ^ ((1 : ℝ) / 3)) := fun j =>
    BijGe.hasPot (hcard _) (hcard _) (hA j) (hQ j) (hpos j) (hE j)
  have h := hasPot_face3 hm Lu Lv Li hLu hLv hLi E hE0 _
    (fun j => mul_pos (hA j) (Real.rpow_pos_of_pos (hQ j) _)) hP
  have hb := HasPot.bijGe hLu hLv (by
    exact mul_nonneg (faceConst3_pos m).le (Finset.prod_nonneg fun j _ =>
      mul_nonneg (hA j).le (Real.rpow_nonneg (hQ j).le _))) h
  rw [bijGe_cube (Finset.prod_nonneg fun j _ => (hQ j).le)]
  have e : faceConst3 m * ∏ j, (A j * Q j ^ ((1 : ℝ) / 3))
      = faceConst3 m * (∏ j, A j) * (∏ j, Q j) ^ ((1 : ℝ) / 3) := by
    rw [Finset.prod_mul_distrib, Real.finsetProd_rpow _ _ fun j _ => (hQ j).le]
    ring
  rwa [e] at hb

/-- **Hall with surpluses**: at a triangle the bijection surpluses multiply when the four-cell
bounds pay for a failure of Hall's condition, `Q₀ Q₁ ≤ 2 τ₀ τ₁`. -/
theorem bijGe_tri {Lu Lv : Finset ℕ} {Li : Fin 1 → Finset ℕ} (hLu : Lu.card = 3)
    (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3) (E : Fin 2 → ℕ → ℕ → ℝ)
    (hE0 : ∀ j c d, 0 ≤ E j c d) (A Q τ : Fin 2 → ℝ) (hA : ∀ j, 0 < A j) (hQ : ∀ j, 0 < Q j)
    (hpos : ∀ j, ∀ c ∈ pathList Lu Lv Li j.castSucc, ∀ d ∈ pathList Lu Lv Li j.succ, c ≠ d →
      0 < E j c d)
    (hE : ∀ j, BijGe (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j) (Q j))
    (hT : ∀ j, TB (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j) (τ j))
    (h2 : Q 0 * Q 1 ≤ 2 * (τ 0 * τ 1)) :
    BijGe Lu Lv (faceSum Li (fun _ _ => 1) E) (∏ j, A j) (∏ j, Q j) := by
  have hcard := pathList_card (m := 1) hLu hLv hLi
  set κ : Fin 2 → ℝ := fun j => Q j ^ ((1 : ℝ) / 3) with hκ
  have hκ0 : ∀ j, 0 < κ j := fun j => Real.rpow_pos_of_pos (hQ j) _
  have hκ3 : ∀ j, κ j ^ 3 = Q j := fun j => by
    rw [hκ]
    dsimp only
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hQ j).le]
    norm_num
  have hP : ∀ j : Fin 2, HasPot (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j)
      (A j * κ j) := fun j =>
    BijGe.hasPot (hcard _) (hcard _) (hA j) (hQ j) (hpos j) (hE j)
  have hT' : ∀ j : Fin 2, TB (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j)
      (A j * κ j) (τ j / Q j) := fun j => by
    intro p q hm hpq i i' k l h1 h2' h3 h4 h5 h6
    have := hT j p q hm hpq i i' k l h1 h2' h3 h4 h5 h6
    have e : (τ j / Q j) ^ 2 * (A j * κ j) ^ 6 = τ j ^ 2 * A j ^ 6 := by
      have : κ j ^ 6 = Q j ^ 2 := by rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, hκ3]
      rw [mul_pow, this]
      field_simp [(hQ j).ne']
    rw [e]
    exact this
  have h2' : 1 ≤ 2 * (τ 0 / Q 0 * (τ 1 / Q 1)) := by
    rw [div_mul_div_comm, ← mul_div_assoc, le_div_iff₀ (mul_pos (hQ 0) (hQ 1))]
    linarith
  have h := hasPot_tri hLu hLv hLi hE0 (fun j => mul_pos (hA j) (hκ0 j)) hP hT' h2'
  have hb := HasPot.bijGe hLu hLv (Finset.prod_nonneg fun j _ =>
    (mul_pos (hA j) (hκ0 j)).le) h
  rw [Fin.prod_univ_two] at hb ⊢
  rw [Fin.prod_univ_two]
  intro α β hα hβ hαm hβm hne
  have := hb α β hα hβ hαm hβm hne
  calc Q 0 * Q 1 * (A 0 * A 1) ^ 3 = 1 * (A 0 * κ 0 * (A 1 * κ 1)) ^ 3 := by
        rw [← hκ3 0, ← hκ3 1]; ring
    _ ≤ _ := this

end Outerplanar
