/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.BareEven
import Outerplanar.BallAdd
import Outerplanar.LongFace
import Outerplanar.Egervary

/-!
# A gain from a single even face

The class of the pieces with a single even face, in the form needed when an even face has
several such children (research note `ai_research_notes/OUTERPLANAR_SEVEN_AND_CUTS_2026-11-23.md`,
"A gain from a single even face" and "An even face with any number of single marks").

* `BijGe S T W N Q` — every proper bijection between the lists has product at least `Q N³`.
  `HasPot.bijGe` and `BijGe.hasPot` (Egerváry) translate to and from the rank-one bound.
* `ZGood S T Z` — floor `2/3`, bijection products at least `q = 32/27`, four-cell bound `3/4`.
* `Gain1 S T W A` — `W` dominates `A` times a mixture of the constant one and a `ZGood` table.
* `cap_ball` — a floor `l` and a bijection surplus `Q` with `Q¹⁹¹ l²⁷ ≥ 1` give the ball class:
  cap every entry at `Q/l²`; the six-family product stays at least `Q²` and the spread is at most
  `Q/l³`.
* **`ball_even_gain`** — an even face whose path edges all carry `Gain1` is in the ball class
  with its full ordinary constant: expand the mixtures multilinearly; the all-constant term is
  the bare face, every other term has surplus `q^s` and floor `(2/3)^(s+1)`, and
  `(32/27)^191 (2/3)^54 ≥ 1`.

The theorem of the note is due to another AI session of this repository's collaboration (the
seven-face note); audited and formalized by Claude.
-/

namespace Outerplanar

open Finset

/-! ### Bijection products -/

/-- Every proper bijection between the lists has product at least `Q N³`. -/
def BijGe (S T : Finset ℕ) (W : ℕ → ℕ → ℝ) (N Q : ℝ) : Prop :=
  ∀ α β : Fin 3 → ℕ, Function.Injective α → Function.Injective β → (∀ a, α a ∈ S) →
    (∀ a, β a ∈ T) → (∀ a, α a ≠ β a) → Q * N ^ 3 ≤ ∏ a, W (α a) (β a)

/-- An enumeration of a three-set. -/
theorem prod_enum {S : Finset ℕ} (hS : S.card = 3) {α : Fin 3 → ℕ} (hα : Function.Injective α)
    (hm : ∀ a, α a ∈ S) (f : ℕ → ℝ) : ∏ a, f (α a) = ∏ c ∈ S, f c := by
  have himg : univ.image α = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hc
      exact hm a
    · rw [Finset.card_image_of_injective _ hα, hS, Finset.card_univ, Fintype.card_fin]
  rw [← himg, Finset.prod_image fun a _ b _ h => hα h]

theorem HasPot.bijGe {S T : Finset ℕ} (hS : S.card = 3) (hT : T.card = 3) {W : ℕ → ℕ → ℝ}
    {N : ℝ} (hN : 0 ≤ N) (h : HasPot S T W N) : BijGe S T W N 1 := by
  obtain ⟨a, b, ha, hb, hpa, hpb, hW⟩ := h
  intro α β hα hβ hαm hβm hne
  calc 1 * N ^ 3 = ∏ x : Fin 3, (N * (a (α x) * b (β x))) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, prod_enum hS hα hαm a,
          prod_enum hT hβ hβm b, hpa, hpb, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
        ring
    _ ≤ _ := Finset.prod_le_prod₀
        (fun x _ => mul_nonneg hN (mul_pos (ha _ (hαm x)) (hb _ (hβm x))).le)
        fun x _ => hW _ (hαm x) _ (hβm x) (hne x)

/-- The cube root. -/
theorem rpow_third_cube {Q : ℝ} (hQ : 0 ≤ Q) : (Q ^ ((1 : ℝ) / 3)) ^ 3 = Q := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hQ]
  norm_num

/-- **Egerváry**: a bijection surplus gives a rank-one bound with the cube root of the
surplus. -/
theorem BijGe.hasPot {S T : Finset ℕ} (hS : S.card = 3) (hT : T.card = 3) {W : ℕ → ℕ → ℝ}
    {N Q : ℝ} (hN : 0 < N) (hQ : 0 < Q) (hpos : ∀ c ∈ S, ∀ d ∈ T, c ≠ d → 0 < W c d)
    (h : BijGe S T W N Q) : HasPot S T W (N * Q ^ ((1 : ℝ) / 3)) := by
  set κ := Q ^ ((1 : ℝ) / 3) with hκ
  have hκpos : 0 < κ := Real.rpow_pos_of_pos hQ _
  have hκ3 : κ ^ 3 = Q := rpow_third_cube hQ.le
  have hM : 0 < N * κ := mul_pos hN hκpos
  have hB' : ∀ σ : ℕ → ℕ, Set.BijOn σ S T → (∀ c ∈ S, σ c ≠ c) →
      1 ≤ ∏ c ∈ S, W c (σ c) / (N * κ) := by
    intro σ hσ hne
    let α : Fin 3 → ℕ := fun x => (S.equivFin.symm (Fin.cast hS.symm x) : ℕ)
    have hα : Function.Injective α := fun x y hxy => by
      have := S.equivFin.symm.injective (Subtype.ext hxy)
      exact Fin.cast_injective _ this
    have hαm : ∀ x, α x ∈ S := fun x => (S.equivFin.symm _).2
    have hβ : Function.Injective fun x => σ (α x) := fun x y hxy =>
      hα (hσ.injOn (hαm x) (hαm y) hxy)
    have key := h α (fun x => σ (α x)) hα hβ hαm (fun x => hσ.mapsTo (hαm x))
      fun x => (hne _ (hαm x)).symm
    rw [← prod_enum hS hα hαm (fun c => W c (σ c) / (N * κ)), Finset.prod_div_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, le_div_iff₀ (pow_pos hM 3)]
    calc 1 * (N * κ) ^ 3 = Q * N ^ 3 := by rw [mul_pow, hκ3]; ring
      _ ≤ _ := key
  obtain ⟨a, b, ha, hb, hpa, hpb, hW⟩ := exists_potentials (le_refl 3) S T hS hT
    (fun c d => W c d / (N * κ)) (fun c hc d hd hcd => div_pos (hpos c hc d hd hcd) hM) hB'
  refine ⟨a, b, ha, hb, hpa, hpb, fun c hc d hd hcd => ?_⟩
  have := hW c hc d hd hcd
  rw [le_div_iff₀ hM] at this
  linarith

/-- A rescaled bijection bound. -/
theorem BijGe.of_one {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {N K : ℝ} (h : BijGe S T W (N * K) 1) :
    BijGe S T W N (K ^ 3) := fun α β hα hβ hαm hβm hne => by
  have := h α β hα hβ hαm hβm hne
  calc K ^ 3 * N ^ 3 = 1 * (N * K) ^ 3 := by ring
    _ ≤ _ := this

/-! ### Capping -/

/-- The six cells of a matched family are two proper bijections. -/
theorem Matched.prod_two {S T : Finset ℕ} {p q : Fin 6 → ℕ} (hm : Matched S T p q)
    (hpq : ∀ i, p i ≠ q i) (W : ℕ → ℕ → ℝ) :
    ∃ α β : Fin 3 → ℕ, Function.Injective α ∧ Function.Injective β ∧ (∀ a, α a ∈ S) ∧
      (∀ b, β b ∈ T) ∧ (∀ a, α a ≠ β (a + 1)) ∧ (∀ a, α a ≠ β (a + 2)) ∧
      ∏ i, W (p i) (q i) = (∏ a, W (α a) (β (a + 1))) * ∏ a, W (α a) (β (a + 2)) := by
  obtain ⟨α, β, hα, hβ, hαm, hβm, hab⟩ := hm
  obtain ⟨κ, hκb, hκ⟩ := matched_reindex hα hβ hab
  have hne : ∀ a b, a ≠ b → α a ≠ β b := fun a b h => by
    obtain ⟨i, hp, hq⟩ := hab a b h
    rw [← hp, ← hq]
    exact hpq i
  refine ⟨α, β, hα, hβ, hαm, hβm, fun a => hne _ _ (add_one_ne a),
    fun a => hne _ _ (add_two_ne a), ?_⟩
  rw [← Fintype.prod_bijective κ hκb (fun j => W (p (κ j)) (q (κ j))) _ fun _ => rfl]
  simp only [hκ, Fin.prod_univ_six, Fin.prod_univ_three, offPair]
  simp only [Matrix.cons_val]
  simp only [show ((0 : Fin 3) + 1) = 1 from rfl, show ((1 : Fin 3) + 1) = 2 from rfl,
    show ((2 : Fin 3) + 1) = 0 from rfl, show ((0 : Fin 3) + 2) = 2 from rfl,
    show ((1 : Fin 3) + 2) = 0 from rfl, show ((2 : Fin 3) + 2) = 1 from rfl]
  ring

/-- A floor `l` and a bijection surplus `Q` with `Q¹⁹¹ l²⁷ ≥ 1` give the ball class. -/
theorem cap_ball {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {N l Q : ℝ} (hN : 0 < N) (hl : 0 < l)
    (hl1 : l ≤ 1) (hQ1 : 1 ≤ Q) (hlQ : 1 ≤ Q ^ 191 * l ^ 27) (h0 : ∀ c d, 0 ≤ W c d)
    (hdom : Dominant S T W (l * N)) (hB : BijGe S T W N Q) : InBall S T W N := by
  set C : ℝ := Q * N / l ^ 2 with hC
  have hCpos : 0 < C := div_pos (mul_pos (by linarith) hN) (pow_pos hl 2)
  set W' : ℕ → ℕ → ℝ := fun c d => min (W c d) C with hW'
  have hW'0 : ∀ c d, 0 ≤ W' c d := fun c d => le_min (h0 c d) hCpos.le
  have hlC : l * N ≤ C := by
    rw [hC, le_div_iff₀ (pow_pos hl 2)]
    have h3 : l ^ 3 ≤ Q := (pow_le_one₀ hl.le hl1).trans hQ1
    nlinarith [pow_pos hl 3]
  have hfl : ∀ c ∈ S, ∀ d ∈ T, c ≠ d → l * N ≤ W' c d := fun c hc d hd hcd =>
    le_min (hdom c hc d hd hcd) hlC
  have hcap : ∀ c d, W' c d ≤ C := fun c d => min_le_right _ _
  -- bijections of the capped table
  have hbij : ∀ α β : Fin 3 → ℕ, Function.Injective α → Function.Injective β →
      (∀ a, α a ∈ S) → (∀ a, β a ∈ T) → (∀ a, α a ≠ β a) →
      Q * N ^ 3 ≤ ∏ a, W' (α a) (β a) := by
    intro α β hα hβ hαm hβm hne
    by_cases hall : ∀ a, W (α a) (β a) ≤ C
    · have e : ∀ a, W' (α a) (β a) = W (α a) (β a) := fun a => min_eq_left (hall a)
      simp only [e]
      exact hB α β hα hβ hαm hβm hne
    · push Not at hall
      obtain ⟨a₀, ha₀⟩ := hall
      have e0 : W' (α a₀) (β a₀) = C := min_eq_right ha₀.le
      rw [← Finset.mul_prod_erase univ _ (mem_univ a₀), e0]
      have h2 : (l * N) ^ 2 ≤ ∏ a ∈ univ.erase a₀, W' (α a) (β a) := by
        calc (l * N) ^ 2 = ∏ _a ∈ univ.erase a₀, l * N := by
              rw [Finset.prod_const, Finset.card_erase_of_mem (mem_univ _)]
              simp
          _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => (mul_pos hl hN).le)
              fun a _ => hfl _ (hαm a) _ (hβm a) (hne a)
      calc Q * N ^ 3 = C * (l * N) ^ 2 := by
            rw [hC]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 hCpos.le
  refine (show InBall S T W' N from ?_).mono hW'0 fun c _ d _ _ => min_le_left _ _
  intro p q hm hpq j c hc d hd hcd
  obtain ⟨α, β, hα, hβ, hαm, hβm, h1, h2, hprod⟩ := hm.prod_two hpq W'
  have hb1 := hbij α (fun a => β (a + 1)) hα (fun x y h => add_right_cancel (hβ h)) hαm
    (fun a => hβm _) h1
  have hb2 := hbij α (fun a => β (a + 2)) hα (fun x y h => add_right_cancel (hβ h)) hαm
    (fun a => hβm _) h2
  set X := ∏ k ∈ univ.erase j, W' (p k) (q k) with hX
  set y := W' (p j) (q j)
  set z := W' c d
  have hX0 : 0 ≤ X := Finset.prod_nonneg fun k _ => hW'0 _ _
  have hy0 : 0 ≤ y := hW'0 _ _
  have hyC : y ≤ C := hcap _ _
  have hz : l * N ≤ z := hfl c hc d hd hcd
  have hXy : (Q * N ^ 3) * (Q * N ^ 3) ≤ X * y := by
    have e : X * y = ∏ i, W' (p i) (q i) := by
      rw [hX, mul_comm]
      exact Finset.mul_prod_erase univ (fun k => W' (p k) (q k)) (mem_univ j)
    rw [e, hprod]
    exact mul_le_mul hb1 hb2 (by nlinarith [pow_pos hN 3]) (by
      exact Finset.prod_nonneg fun a _ => hW'0 _ _)
  -- the main inequality, multiplied by `C ^ 9`
  have hC9 : 0 < C ^ 9 := pow_pos hCpos 9
  have step1 : ((Q * N ^ 3) * (Q * N ^ 3)) ^ 100 * (l * N) ^ 9
      ≤ X ^ 100 * y ^ 91 * z ^ 9 * C ^ 9 := by
    have a1 : ((Q * N ^ 3) * (Q * N ^ 3)) ^ 100 ≤ (X * y) ^ 100 :=
      pow_le_pow_left₀ (by positivity) hXy _
    have a2 : (X * y) ^ 100 ≤ X ^ 100 * y ^ 91 * C ^ 9 := by
      rw [mul_pow, show y ^ 100 = y ^ 91 * y ^ 9 by ring, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy0 hyC 9)
        (mul_nonneg (pow_nonneg hX0 _) (pow_nonneg hy0 _))
    have a3 : (l * N) ^ 9 ≤ z ^ 9 := pow_le_pow_left₀ (mul_pos hl hN).le hz 9
    calc ((Q * N ^ 3) * (Q * N ^ 3)) ^ 100 * (l * N) ^ 9
        ≤ (X ^ 100 * y ^ 91 * C ^ 9) * z ^ 9 :=
          mul_le_mul (a1.trans a2) a3 (by positivity) (by positivity)
      _ = X ^ 100 * y ^ 91 * z ^ 9 * C ^ 9 := by ring
  have step2 : N ^ 600 * C ^ 9 ≤ ((Q * N ^ 3) * (Q * N ^ 3)) ^ 100 * (l * N) ^ 9 := by
    have e : ((Q * N ^ 3) * (Q * N ^ 3)) ^ 100 * (l * N) ^ 9
        = (N ^ 600 * C ^ 9) * (Q ^ 191 * l ^ 27) := by
      rw [hC]; field_simp
    rw [e]
    exact le_mul_of_one_le_right (by positivity) hlQ
  exact le_of_mul_le_mul_right (step2.trans step1) hC9

/-! ### Sums and the face map -/

theorem InBall.zero {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} (h0 : ∀ c d, 0 ≤ W c d) :
    InBall S T W 0 := fun p q _ _ j c _ d _ _ => by
  rw [zero_pow (by norm_num)]
  exact mul_nonneg (mul_nonneg (pow_nonneg (Finset.prod_nonneg fun k _ => h0 _ _) _)
    (pow_nonneg (h0 _ _) _)) (pow_nonneg (h0 _ _) _)

theorem InBall.finsum {ι : Type*} (s : Finset ι) {S T : Finset ℕ} (W : ι → ℕ → ℕ → ℝ)
    (A : ι → ℝ) (hA : ∀ i ∈ s, 0 ≤ A i) (h0 : ∀ i ∈ s, ∀ c d, 0 ≤ W i c d)
    (h : ∀ i ∈ s, InBall S T (W i) (A i)) :
    InBall S T (fun c d => ∑ i ∈ s, W i c d) (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact InBall.zero fun _ _ => le_refl 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    refine InBall.add (hA a (mem_insert_self a s))
      (Finset.sum_nonneg fun i hi => hA i (mem_insert_of_mem hi))
      (h0 a (mem_insert_self a s)) (fun c d => Finset.sum_nonneg fun i hi =>
        h0 i (mem_insert_of_mem hi) c d) (h a (mem_insert_self a s))
      (ih (fun i hi => hA i (mem_insert_of_mem hi)) (fun i hi => h0 i (mem_insert_of_mem hi))
        fun i hi => h i (mem_insert_of_mem hi))

/-- The face map is monotone in the path profiles. -/
theorem faceSum_le_of_le {m : ℕ} {Lu Lv : Finset ℕ} {Li : Fin m → Finset ℕ}
    {E F : Fin (m + 1) → ℕ → ℕ → ℝ} (hF0 : ∀ j c d, 0 ≤ F j c d)
    (hle : ∀ j, ∀ c ∈ pathList Lu Lv Li j.castSucc, ∀ d ∈ pathList Lu Lv Li j.succ,
      F j c d ≤ E j c d)
    {c d : ℕ} (hc : c ∈ Lu) (hd : d ∈ Lv) :
    faceSum Li (fun _ _ => 1) F c d ≤ faceSum Li (fun _ _ => 1) E c d := by
  unfold faceSum
  refine Finset.sum_le_sum fun g hg => ?_
  have hmem : ∀ i : Fin (m + 2), pathCol c d g i ∈ pathList Lu Lv Li i := fun i =>
    pathCol_mem hc hd (fun j => Fintype.mem_piFinset.mp hg j) i
  refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun _ _ => zero_le_one)
  exact Finset.prod_le_prod₀ (fun j _ => hF0 _ _ _) fun j _ => hle j _ (hmem _) _ (hmem _)

/-- The face map is multilinear: two terms on every path edge. -/
theorem faceSum_sum2 {m : ℕ} (Li : Fin m → Finset ℕ) (G : Fin (m + 1) → Fin 2 → ℕ → ℕ → ℝ)
    (c d : ℕ) :
    faceSum Li (fun _ _ => 1) (fun j c d => ∑ r, G j r c d) c d
      = ∑ ρ : Fin (m + 1) → Fin 2, faceSum Li (fun _ _ => 1) (fun j => G j (ρ j)) c d := by
  unfold faceSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-! ### The gain class -/

/-- The table of a piece with one even face, after the constant alternative is split off:
floor `2/3`, bijection surplus `32/27`, four-cell bound `3/4`. -/
def ZGood (S T : Finset ℕ) (Z : ℕ → ℕ → ℝ) : Prop :=
  (∀ c d, 0 ≤ Z c d) ∧ Dominant S T Z (2 / 3) ∧ BijGe S T Z 1 (32 / 27) ∧ TB S T Z 1 (3 / 4)

/-- `W` dominates `A` times a mixture of the constant one and a `ZGood` table. -/
def Gain1 (S T : Finset ℕ) (W : ℕ → ℕ → ℝ) (A : ℝ) : Prop :=
  ∃ (t : ℝ) (Z : ℕ → ℕ → ℝ), 0 ≤ t ∧ t ≤ 1 ∧ ZGood S T Z ∧
    ∀ c ∈ S, ∀ d ∈ T, c ≠ d → A * ((1 - t) + t * Z c d) ≤ W c d

theorem zGood_const (S T : Finset ℕ) : ZGood S T (fun _ _ => 4 / 3) := by
  refine ⟨fun _ _ => by norm_num, fun _ _ _ _ _ => by norm_num, fun α β _ _ _ _ _ => ?_,
    fun p q _ _ i j k l _ _ _ _ _ _ => by norm_num⟩
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

/-- Greedy pieces are in the gain class. -/
theorem Dominant.gain1 {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {A : ℝ} (h : Dominant S T W A) :
    Gain1 S T W A :=
  ⟨0, fun _ _ => 4 / 3, le_refl 0, zero_le_one, zGood_const S T,
    fun c hc d hd hcd => by simpa using h c hc d hd hcd⟩

theorem faceConst3_even_ge_three : ∀ k : ℕ, 3 ≤ faceConst3 (2 * k + 2)
  | 0 => by norm_num [faceConst3]
  | (k + 1) => by
    have e : 2 * (k + 1) + 2 = (2 * k + 2) + 2 := by ring
    rw [e, faceConst3_add_two]
    have := faceConst3_even_ge_three k
    have : (0 : ℝ) ≤ 2 ^ (2 * k + 2 + 1) := by positivity
    linarith

/-- The numbers of the capping step. -/
theorem gain_numbers (s : ℕ) (hs : 1 ≤ s) :
    1 ≤ ((32 / 27 : ℝ) ^ s) ^ 191 * ((2 / 3 : ℝ) ^ (s + 1)) ^ 27 := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have h1 : (1 : ℝ) ≤ (32 / 27) ^ 191 * (2 / 3) ^ 27 := by norm_num
  have h2 : (1 : ℝ) ≤ (32 / 27) ^ 191 * (2 / 3) ^ 54 := by norm_num
  have e : ∀ a b : ℝ, (a ^ (k + 1)) ^ 191 * (b ^ (k + 1 + 1)) ^ 27
      = (a ^ 191 * b ^ 27) ^ k * (a ^ 191 * b ^ 54) := fun a b => by ring
  rw [e]
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ h1) h2

/-- **An even face with any number of singly marked children is in the ball class**, with its
full ordinary constant. -/
theorem ball_even_gain {m : ℕ} (hm : Even m) (hm2 : 2 ≤ m) (Lu Lv : Finset ℕ)
    (Li : Fin m → Finset ℕ) (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 < A j)
    (hE : ∀ j, Gain1 (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    InBall Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  choose t Z ht0 ht1 hZ hEZ using hE
  -- the two terms on each path edge
  set w : Fin (m + 1) → Fin 2 → ℝ := fun j r => if r = 0 then A j * (1 - t j) else A j * t j
    with hw
  set U : Fin (m + 1) → Fin 2 → ℕ → ℕ → ℝ :=
    fun j r c d => if c ≠ d then (if r = 0 then 1 else Z j c d) else 0 with hU
  set G : Fin (m + 1) → Fin 2 → ℕ → ℕ → ℝ := fun j r c d => w j r * U j r c d with hG
  have hw0 : ∀ j r, 0 ≤ w j r := fun j r => by
    simp only [hw]
    split_ifs
    · exact mul_nonneg (hA j).le (by linarith [ht1 j])
    · exact mul_nonneg (hA j).le (ht0 j)
  have hU0 : ∀ j r c d, 0 ≤ U j r c d := fun j r c d => by
    simp only [hU]
    split_ifs
    · exact zero_le_one
    · exact (hZ j).1 c d
    · exact le_refl 0
  have hG0 : ∀ j r c d, 0 ≤ G j r c d := fun j r c d => mul_nonneg (hw0 j r) (hU0 j r c d)
  have hα3 : 3 ≤ faceConst3 m := by
    obtain ⟨k, hk⟩ := hm
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk, show k' + 1 + (k' + 1) = 2 * k' + 2 by ring]
    exact faceConst3_even_ge_three k'
  have hαpos : 0 < faceConst3 m := by linarith
  -- reduce to the expanded face sum
  have hle : ∀ c ∈ Lu, ∀ d ∈ Lv, c ≠ d →
      faceSum Li (fun _ _ => 1) (fun j c d => ∑ r, G j r c d) c d
        ≤ faceSum Li (fun _ _ => 1) E c d := fun c hc d hd _ => by
    refine faceSum_le_of_le (fun j c d => Finset.sum_nonneg fun r _ => hG0 j r c d)
      (fun j c hc d hd => ?_) hc hd
    rw [Fin.sum_univ_two]
    by_cases hcd : c = d
    · simp only [hG, hU, hcd, ne_eq, not_true_eq_false, ite_false, mul_zero, add_zero]
      exact hE0 _ _ _
    · simp only [hG, hU, hw, ne_eq, hcd, not_false_eq_true, ite_true,
        ite_false, one_ne_zero]
      have := hEZ j c hc d hd hcd
      linarith
  refine InBall.mono ?_ (faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one)
    (fun j c d => Finset.sum_nonneg fun r _ => hG0 j r c d)) hle
  have hfun : faceSum Li (fun _ _ => 1) (fun j c d => ∑ r, G j r c d)
      = fun c d => ∑ ρ : Fin (m + 1) → Fin 2,
          faceSum Li (fun _ _ => 1) (fun j => G j (ρ j)) c d :=
    funext fun c => funext fun d => faceSum_sum2 Li G c d
  have hconst : faceConst3 m * ∏ j, A j
      = ∑ ρ : Fin (m + 1) → Fin 2, faceConst3 m * ∏ j, w j (ρ j) := by
    rw [← Finset.mul_sum]
    congr 1
    have : ∀ j, A j = ∑ r, w j r := fun j => by
      simp only [hw, Fin.sum_univ_two, ite_true,
        ite_false, one_ne_zero]
      ring
    simp only [this]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [hfun, hconst]
  refine InBall.finsum univ _ _ (fun ρ _ => mul_nonneg hαpos.le
    (Finset.prod_nonneg fun j _ => hw0 j (ρ j)))
    (fun ρ _ c d => faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one)
      (fun j c d => hG0 j (ρ j) c d) c d) fun ρ _ => ?_
  -- one term
  by_cases hz : ∃ j, w j (ρ j) = 0
  · obtain ⟨j, hj⟩ := hz
    rw [Finset.prod_eq_zero (mem_univ j) hj, mul_zero]
    exact InBall.zero fun c d => faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one)
      (fun j c d => hG0 j (ρ j) c d) c d
  push Not at hz
  have hwpos : ∀ j, 0 < w j (ρ j) := fun j => lt_of_le_of_ne (hw0 j (ρ j)) (hz j).symm
  -- the floors and the bijection surpluses of the terms
  have hdomj : ∀ j, Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
      (G j (ρ j)) (w j (ρ j) * (2 / 3) ^ (ρ j).val) := fun j c hc d hd hcd => by
    simp only [hG, hU, ne_eq, hcd, not_false_eq_true, ite_true]
    refine mul_le_mul_of_nonneg_left ?_ (hw0 j (ρ j))
    rcases Fin.exists_fin_two.mp ⟨ρ j, rfl⟩ with h | h <;> rw [h]
    · simp
    · simpa using (hZ j).2.1 c hc d hd hcd
  by_cases hρ : ∀ j, ρ j = 0
  · -- the bare face
    have hb := ballFaceClosed_of_bare (ballFaceBare_all m) Lu Lv Li hLu hLv hLi 0
      (fun j => G j (ρ j)) (fun j c d => hG0 j (ρ j) c d) (fun j => w j (ρ j)) hwpos
      (Dominant.inBall (hw0 0 (ρ 0)) (by simpa [hρ 0] using hdomj 0))
      (fun j _ => by simpa [hρ j] using hdomj j)
    exact hb
  push Not at hρ
  obtain ⟨j₁, hj₁⟩ := hρ
  set s : ℕ := ∑ j, (ρ j).val with hs
  have hs1 : 1 ≤ s := by
    have : 1 ≤ (ρ j₁).val := by
      rcases Fin.exists_fin_two.mp ⟨ρ j₁, rfl⟩ with h | h
      · exact absurd h hj₁
      · rw [h]; decide
    exact this.trans (Finset.single_le_sum (f := fun j => (ρ j).val) (fun j _ => Nat.zero_le _)
      (mem_univ j₁))
  set N : ℝ := faceConst3 m * ∏ j, w j (ρ j) with hN
  have hNpos : 0 < N := mul_pos hαpos (Finset.prod_pos fun j _ => hwpos j)
  -- floor
  have hfloor : Dominant Lu Lv (faceSum Li (fun _ _ => 1) (fun j => G j (ρ j)))
      ((2 / 3) ^ (s + 1) * N) := by
    have h := dom_face_even hm Lu Lv Li hLi (fun j => G j (ρ j)) (fun j c d => hG0 j (ρ j) c d)
      _ (fun j => mul_nonneg (hw0 j (ρ j)) (by positivity)) hdomj
    refine fun c hc d hd hcd => le_trans ?_ (h c hc d hd hcd)
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← hs, hN, pow_succ]
    have hP : 0 ≤ ∏ j, w j (ρ j) := Finset.prod_nonneg fun j _ => hw0 j (ρ j)
    have h23 : (0 : ℝ) ≤ (2 / 3) ^ s := by positivity
    nlinarith [mul_nonneg hP h23]
  -- bijection surplus
  have hbij : ∀ j, BijGe (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
      (G j (ρ j)) (w j (ρ j)) ((32 / 27) ^ (ρ j).val) := fun j α β hα hβ hαm hβm hne => by
    simp only [hG, hU, ne_eq, hne, not_false_eq_true, ite_true, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rcases Fin.exists_fin_two.mp ⟨ρ j, rfl⟩ with h | h <;> rw [h]
    · simp
    · have := (hZ j).2.2.1 α β hα hβ hαm hβm hne
      have hw1 := hwpos j
      rw [h] at hw1
      simp only [Fin.isValue, Fin.val_one, pow_one, one_ne_zero, ite_false]
      rw [one_pow, mul_one] at this
      nlinarith [mul_le_mul_of_nonneg_left this (pow_pos hw1 3).le]
  have hcard : ∀ i : Fin (m + 2), (pathList Lu Lv Li i).card = 3 := fun i => by
    refine Fin.cases hLu (fun i => ?_) i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa [pathList] using hLv
    · simpa [pathList] using hLi i
  have hpot : ∀ j, HasPot (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
      (G j (ρ j)) (w j (ρ j) * ((32 / 27) ^ (ρ j).val) ^ ((1 : ℝ) / 3)) := fun j =>
    (hbij j).hasPot (hcard _) (hcard _) (hwpos j) (by positivity) fun c hc d hd hcd =>
      lt_of_lt_of_le (mul_pos (hwpos j) (by positivity)) (hdomj j c hc d hd hcd)
  have hface := hasPot_face3 hm2 Lu Lv Li hLu hLv hLi (fun j => G j (ρ j))
    (fun j c d => hG0 j (ρ j) c d) _ (fun j => mul_pos (hwpos j) (by positivity)) hpot
  rw [Finset.prod_mul_distrib, ← mul_assoc] at hface
  have hB := (hface.bijGe hLu hLv (mul_pos hNpos (Finset.prod_pos fun j _ => by
    positivity)).le).of_one
  have hQ : (∏ j, ((32 / 27 : ℝ) ^ (ρ j).val) ^ ((1 : ℝ) / 3)) ^ 3 = (32 / 27) ^ s := by
    rw [← Finset.prod_pow]
    simp only [fun j => rpow_third_cube (show (0 : ℝ) ≤ (32 / 27) ^ (ρ j).val by positivity)]
    rw [Finset.prod_pow_eq_pow_sum]
  rw [hQ] at hB
  exact cap_ball hNpos (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
    (one_le_pow₀ (by norm_num)) (gain_numbers s hs1)
    (fun c d => faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one)
      (fun j c d => hG0 j (ρ j) c d) c d) hfloor hB

end Outerplanar
