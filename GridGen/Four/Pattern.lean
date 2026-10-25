/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Fibre

/-!
# Height four: the pattern term

The weighted successor count `G w A` is the plain count times the average pattern weight over the
proper columns of `A`. When the weights lie in `[ρ, 1]`, two list systems `A` and `U` whose
columns mostly coincide have close averages:
`avg_A g - avg_U g ≥ -(1-ρ)·max(|Ω∖Ω'|/|Ω|, |Ω'∖Ω|/|Ω'|)` (`avg_sub_ge`), and a column of
`Ω ∖ Ω'` has a row whose colour lies in `A_i ∖ U_i`, which by the fibre bound happens for at most a
`|A_i ∖ U_i|/(k-3)` share of the columns (`card_sdiff_le`).
-/

namespace GridGen.Four

open Finset GridGen.Lookback

/-- Lists of at least three colours have a proper column. -/
theorem sts_nonempty {A₁ A₂ A₃ A₄ : Finset ℕ} (h₁ : 3 ≤ A₁.card) (h₂ : 3 ≤ A₂.card)
    (h₃ : 3 ≤ A₃.card) (h₄ : 3 ≤ A₄.card) : (sts A₁ A₂ A₃ A₄).Nonempty := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < A₁.card)
  obtain ⟨b, hb⟩ := Finset.card_pos.mp
    (by have := Finset.pred_card_le_card_erase (s := A₂) (a := a); omega : 0 < (A₂.erase a).card)
  obtain ⟨c, hc⟩ := Finset.card_pos.mp
    (by have := Finset.pred_card_le_card_erase (s := A₃) (a := b); omega : 0 < (A₃.erase b).card)
  obtain ⟨d, hd⟩ := Finset.card_pos.mp
    (by have := Finset.pred_card_le_card_erase (s := A₄) (a := c); omega : 0 < (A₄.erase c).card)
  rw [Finset.mem_erase] at hb hc hd
  exact ⟨(a, b, c, d), mem_sts.mpr ⟨ha, hb.2, hc.2, hd.2, Ne.symm hb.1, Ne.symm hc.1, Ne.symm hd.1⟩⟩

/-- **Averages over overlapping sets.** With `a = |Ω|`, `b = |Ω'|`, `c = |Ω ∩ Ω'|`, `S` the weight
on the overlap and `X`, `Y` the weights on the two differences, all weights in `[ρ, 1]`:
`(S + X)/a - (S + Y)/b ≥ -(1-ρ)·max((a-c)/a, (b-c)/b)`. -/
theorem avg_sub_ge {a b c S X Y ρ : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hca : c ≤ a)
    (hcb : c ≤ b) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hS0 : ρ * c ≤ S) (hS1 : S ≤ c)
    (hX0 : ρ * (a - c) ≤ X) (hY1 : Y ≤ b - c) :
    -((1 - ρ) * max ((a - c) / a) ((b - c) / b)) ≤ (S + X) / a - (S + Y) / b := by
  have hm1 : (a - c) / a ≤ max ((a - c) / a) ((b - c) / b) := le_max_left _ _
  have hm2 : (b - c) / b ≤ max ((a - c) / a) ((b - c) / b) := le_max_right _ _
  have h1ρ : 0 ≤ 1 - ρ := by linarith
  rcases le_or_gt a b with hab | hab
  · -- the overlap weighs more on the `a` side: worst case `S = ρc`
    have key : -((1 - ρ) * ((b - c) / b)) ≤ (S + X) / a - (S + Y) / b := by
      rw [div_sub_div _ _ ha.ne' hb.ne', le_div_iff₀ (by positivity)]
      have : -((1 - ρ) * ((b - c) / b)) * (a * b) = -((1 - ρ) * (b - c) * a) := by
        field_simp
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_left hab (by linarith : 0 ≤ S - ρ * c),
        mul_nonneg ha.le (by linarith : 0 ≤ X - ρ * (a - c)),
        mul_nonneg hb.le (by linarith : 0 ≤ X - ρ * (a - c)),
        mul_nonneg ha.le (by linarith : 0 ≤ b - c - Y)]
    have := mul_le_mul_of_nonneg_left hm2 h1ρ
    linarith
  · -- worst case `S = c`
    have key : -((1 - ρ) * ((a - c) / a)) ≤ (S + X) / a - (S + Y) / b := by
      rw [div_sub_div _ _ ha.ne' hb.ne', le_div_iff₀ (by positivity)]
      have : -((1 - ρ) * ((a - c) / a)) * (a * b) = -((1 - ρ) * (a - c) * b) := by
        field_simp
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_left hab.le (by linarith : 0 ≤ c - S),
        mul_nonneg hb.le (by linarith : 0 ≤ X - ρ * (a - c)),
        mul_nonneg ha.le (by linarith : 0 ≤ b - c - Y)]
    have := mul_le_mul_of_nonneg_left hm1 h1ρ
    linarith

section Diff

variable {k : ℕ} {A₁ A₂ A₃ A₄ : Finset ℕ}

/-- The share of columns with a prescribed colour in a prescribed row, unweighted. -/
theorem card_row_le (hA₁ : k - 1 ≤ A₁.card) (hA₂ : k - 1 ≤ A₂.card) (hA₃ : k - 1 ≤ A₃.card)
    (hA₄ : k - 1 ≤ A₄.card) (c : ℕ) :
    ((k - 3 : ℕ) : ℝ) * ((sts A₁ A₂ A₃ A₄).filter (fun t => r1 t = c)).card ≤ (sts A₁ A₂ A₃ A₄).card ∧
    ((k - 3 : ℕ) : ℝ) * ((sts A₁ A₂ A₃ A₄).filter (fun t => r2 t = c)).card ≤ (sts A₁ A₂ A₃ A₄).card ∧
    ((k - 3 : ℕ) : ℝ) * ((sts A₁ A₂ A₃ A₄).filter (fun t => r3 t = c)).card ≤ (sts A₁ A₂ A₃ A₄).card ∧
    ((k - 3 : ℕ) : ℝ) * ((sts A₁ A₂ A₃ A₄).filter (fun t => r4 t = c)).card ≤ (sts A₁ A₂ A₃ A₄).card := by
  have hw : ∀ t : T4, (0 : ℝ) ≤ 1 := fun _ => zero_le_one
  have hR : ∀ t ∈ sts A₁ A₂ A₃ A₄, ∀ t' ∈ sts A₁ A₂ A₃ A₄, (1 : ℝ) ≤ 1 * 1 := fun _ _ _ _ => by norm_num
  have e : ∀ P : T4 → Prop, ∀ [DecidablePred P],
      (∑ t ∈ (sts A₁ A₂ A₃ A₄).filter P, (1 : ℝ)) = ((sts A₁ A₂ A₃ A₄).filter P).card := by
    intro P _; simp
  have e' : (∑ t ∈ sts A₁ A₂ A₃ A₄, (1 : ℝ)) = (sts A₁ A₂ A₃ A₄).card := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := fibre_sts1 (fun _ => (1 : ℝ)) (fun _ => zero_le_one) (fun t => r1 t = c) hA₁ hA₂ hA₃ hA₄
      zero_le_one hR (fun _ => c) (fun _ _ => rfl) (fun _ h => h)
    rwa [e, e', one_mul] at this
  · have := fibre_sts2 (fun _ => (1 : ℝ)) (fun _ => zero_le_one) (fun t => r2 t = c) hA₁ hA₂ hA₃ hA₄
      zero_le_one hR (fun _ => c) (fun _ _ => rfl) (fun _ h => h)
    rwa [e, e', one_mul] at this
  · have := fibre_sts3 (fun _ => (1 : ℝ)) (fun _ => zero_le_one) (fun t => r3 t = c) hA₁ hA₂ hA₃ hA₄
      zero_le_one hR (fun _ => c) (fun _ _ => rfl) (fun _ h => h)
    rwa [e, e', one_mul] at this
  · have := fibre_sts4 (fun _ => (1 : ℝ)) (fun _ => zero_le_one) (fun t => r4 t = c) hA₁ hA₂ hA₃ hA₄
      zero_le_one hR (fun _ => c) (fun _ _ => rfl) (fun _ h => h)
    rwa [e, e', one_mul] at this

/-- Columns whose row-`i` colour lies in a set `D`: at most `|D|/(k-3)` of them. -/
theorem card_row_mem_le {Ω : Finset T4} (get : T4 → ℕ) (D : Finset ℕ)
    (hrow : ∀ c, ((k - 3 : ℕ) : ℝ) * (Ω.filter (fun t => get t = c)).card ≤ Ω.card) :
    ((k - 3 : ℕ) : ℝ) * (Ω.filter (fun t => get t ∈ D)).card ≤ D.card * Ω.card := by
  have hsub : Ω.filter (fun t => get t ∈ D) ⊆ D.biUnion (fun c => Ω.filter (fun t => get t = c)) := by
    intro t ht
    obtain ⟨htΩ, htD⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_biUnion.mpr ⟨get t, htD, Finset.mem_filter.mpr ⟨htΩ, rfl⟩⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hk0 : (0 : ℝ) ≤ ((k - 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  calc ((k - 3 : ℕ) : ℝ) * (Ω.filter (fun t => get t ∈ D)).card
      ≤ ((k - 3 : ℕ) : ℝ) * ∑ c ∈ D, ((Ω.filter (fun t => get t = c)).card : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hk0; exact_mod_cast hcard
    _ = ∑ c ∈ D, ((k - 3 : ℕ) : ℝ) * (Ω.filter (fun t => get t = c)).card := by rw [Finset.mul_sum]
    _ ≤ ∑ _c ∈ D, (Ω.card : ℝ) := Finset.sum_le_sum fun c _ => hrow c
    _ = D.card * Ω.card := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Columns lost when the lists change.** -/
theorem card_sdiff_le (hA₁ : k - 1 ≤ A₁.card) (hA₂ : k - 1 ≤ A₂.card) (hA₃ : k - 1 ≤ A₃.card)
    (hA₄ : k - 1 ≤ A₄.card) (U₁ U₂ U₃ U₄ : Finset ℕ) :
    ((k - 3 : ℕ) : ℝ) * (sts A₁ A₂ A₃ A₄ \ sts U₁ U₂ U₃ U₄).card
      ≤ ((A₁ \ U₁).card + (A₂ \ U₂).card + (A₃ \ U₃).card + (A₄ \ U₄).card)
        * (sts A₁ A₂ A₃ A₄).card := by
  set Ω := sts A₁ A₂ A₃ A₄
  obtain ⟨h1, h2, h3, h4⟩ := And.intro (fun c => (card_row_le hA₁ hA₂ hA₃ hA₄ c).1)
    (And.intro (fun c => (card_row_le hA₁ hA₂ hA₃ hA₄ c).2.1)
      (And.intro (fun c => (card_row_le hA₁ hA₂ hA₃ hA₄ c).2.2.1)
        (fun c => (card_row_le hA₁ hA₂ hA₃ hA₄ c).2.2.2)))
  have hsub : Ω \ sts U₁ U₂ U₃ U₄ ⊆
      ((Ω.filter (fun t => r1 t ∈ A₁ \ U₁)) ∪ (Ω.filter (fun t => r2 t ∈ A₂ \ U₂)))
        ∪ ((Ω.filter (fun t => r3 t ∈ A₃ \ U₃)) ∪ (Ω.filter (fun t => r4 t ∈ A₄ \ U₄))) := by
    intro t ht
    obtain ⟨htΩ, htU⟩ := Finset.mem_sdiff.mp ht
    have hm := mem_sts.mp htΩ
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    by_contra hno
    push Not at hno
    apply htU
    rw [mem_sts]
    exact ⟨hno.1.1 htΩ hm.1, hno.1.2 htΩ hm.2.1, hno.2.1 htΩ hm.2.2.1, hno.2.2 htΩ hm.2.2.2.1,
      hm.2.2.2.2⟩
  have hc := Finset.card_le_card hsub
  have hu := (Finset.card_union_le
      ((Ω.filter (fun t => r1 t ∈ A₁ \ U₁)) ∪ (Ω.filter (fun t => r2 t ∈ A₂ \ U₂)))
      ((Ω.filter (fun t => r3 t ∈ A₃ \ U₃)) ∪ (Ω.filter (fun t => r4 t ∈ A₄ \ U₄)))).trans
    (add_le_add (Finset.card_union_le _ _) (Finset.card_union_le _ _))
  have hk0 : (0 : ℝ) ≤ ((k - 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  have b1 := card_row_mem_le r1 (A₁ \ U₁) h1
  have b2 := card_row_mem_le r2 (A₂ \ U₂) h2
  have b3 := card_row_mem_le r3 (A₃ \ U₃) h3
  have b4 := card_row_mem_le r4 (A₄ \ U₄) h4
  have hcr : ((Ω \ sts U₁ U₂ U₃ U₄).card : ℝ) ≤
      (Ω.filter (fun t => r1 t ∈ A₁ \ U₁)).card + (Ω.filter (fun t => r2 t ∈ A₂ \ U₂)).card
        + ((Ω.filter (fun t => r3 t ∈ A₃ \ U₃)).card + (Ω.filter (fun t => r4 t ∈ A₄ \ U₄)).card) := by
    exact_mod_cast hc.trans hu
  nlinarith [mul_le_mul_of_nonneg_left hcr hk0]

/-- **The pattern term.** For lists of at least `k - 1 ≥ 3` colours and pattern weights in
`[ρ, 1]` (`0 < ρ`), the log ratio of the average weights is at least
`-(1-ρ)/ρ · max(Σ|Aᵢ∖Uᵢ|, Σ|Uᵢ∖Aᵢ|)/(k-3)`. -/
theorem pattern_log_ge {U₁ U₂ U₃ U₄ : Finset ℕ} (hk : 4 ≤ k)
    (hA₁ : k - 1 ≤ A₁.card) (hA₂ : k - 1 ≤ A₂.card) (hA₃ : k - 1 ≤ A₃.card)
    (hA₄ : k - 1 ≤ A₄.card) (hU₁ : k - 1 ≤ U₁.card) (hU₂ : k - 1 ≤ U₂.card)
    (hU₃ : k - 1 ≤ U₃.card) (hU₄ : k - 1 ≤ U₄.card)
    (w : Wt) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hg : ∀ t, ρ ≤ gw w t ∧ gw w t ≤ 1) :
    -((1 - ρ) / ρ * (max ((A₁ \ U₁).card + (A₂ \ U₂).card + (A₃ \ U₃).card + (A₄ \ U₄).card : ℝ)
          ((U₁ \ A₁).card + (U₂ \ A₂).card + (U₃ \ A₃).card + (U₄ \ A₄).card)
        / ((k - 3 : ℕ) : ℝ)))
      ≤ Real.log ((G w A₁ A₂ A₃ A₄ / (sts A₁ A₂ A₃ A₄).card)
          / (G w U₁ U₂ U₃ U₄ / (sts U₁ U₂ U₃ U₄).card)) := by
  classical
  set Ω := sts A₁ A₂ A₃ A₄ with hΩ
  set Ω' := sts U₁ U₂ U₃ U₄ with hΩ'
  have hk3 : (0 : ℝ) < ((k - 3 : ℕ) : ℝ) := by
    have : 0 < k - 3 := by omega
    exact_mod_cast this
  have ha : (0 : ℝ) < Ω.card := by
    exact_mod_cast (sts_nonempty (by omega) (by omega) (by omega) (by omega)).card_pos
  have hb : (0 : ℝ) < Ω'.card := by
    exact_mod_cast (sts_nonempty (by omega) (by omega) (by omega) (by omega)).card_pos
  -- split the two sums over the overlap and the differences
  have hsA : G w A₁ A₂ A₃ A₄ = ∑ t ∈ Ω ∩ Ω', gw w t + ∑ t ∈ Ω \ Ω', gw w t := by
    rw [G, ← hΩ, ← Finset.sum_union (Finset.disjoint_sdiff_inter Ω Ω').symm,
      Finset.union_comm, Finset.sdiff_union_inter]
  have hsU : G w U₁ U₂ U₃ U₄ = ∑ t ∈ Ω ∩ Ω', gw w t + ∑ t ∈ Ω' \ Ω, gw w t := by
    rw [G, ← hΩ', Finset.inter_comm, ← Finset.sum_union (Finset.disjoint_sdiff_inter Ω' Ω).symm,
      Finset.union_comm, Finset.sdiff_union_inter]
  have hcA : (Ω.card : ℝ) = (Ω ∩ Ω').card + (Ω \ Ω').card := by
    rw [← Finset.card_inter_add_card_sdiff Ω Ω']; push_cast; ring
  have hcU : (Ω'.card : ℝ) = (Ω ∩ Ω').card + (Ω' \ Ω).card := by
    rw [← Finset.card_inter_add_card_sdiff Ω' Ω, Finset.inter_comm]; push_cast; ring
  have hsum_bounds : ∀ S : Finset T4, ρ * S.card ≤ ∑ t ∈ S, gw w t ∧ ∑ t ∈ S, gw w t ≤ S.card := by
    intro S
    constructor
    · have := Finset.card_nsmul_le_sum S (gw w) ρ (fun t _ => (hg t).1)
      simpa [nsmul_eq_mul, mul_comm] using this
    · have := Finset.sum_le_card_nsmul S (gw w) 1 (fun t _ => (hg t).2)
      simpa using this
  obtain ⟨hS0, hS1⟩ := hsum_bounds (Ω ∩ Ω')
  obtain ⟨hX0, -⟩ := hsum_bounds (Ω \ Ω')
  obtain ⟨-, hY1⟩ := hsum_bounds (Ω' \ Ω)
  have havg := avg_sub_ge (a := Ω.card) (b := Ω'.card) (c := (Ω ∩ Ω').card)
    (S := ∑ t ∈ Ω ∩ Ω', gw w t) (X := ∑ t ∈ Ω \ Ω', gw w t) (Y := ∑ t ∈ Ω' \ Ω, gw w t)
    ha hb (Nat.cast_nonneg _) (by rw [hcA]; linarith [(Nat.cast_nonneg _ : (0:ℝ) ≤ (Ω \ Ω').card)])
    (by rw [hcU]; linarith [(Nat.cast_nonneg _ : (0:ℝ) ≤ (Ω' \ Ω).card)]) hρ0.le hρ1 hS0 hS1
    (by rw [hcA]; have : ρ * ((Ω ∩ Ω').card + (Ω \ Ω').card - (Ω ∩ Ω').card : ℝ)
          = ρ * (Ω \ Ω').card := by ring
        linarith)
    (by rw [hcU]; linarith)
  -- the differences are small
  have hdA := card_sdiff_le hA₁ hA₂ hA₃ hA₄ U₁ U₂ U₃ U₄
  have hdU := card_sdiff_le hU₁ hU₂ hU₃ hU₄ A₁ A₂ A₃ A₄
  set DA : ℝ := (A₁ \ U₁).card + (A₂ \ U₂).card + (A₃ \ U₃).card + (A₄ \ U₄).card
  set DU : ℝ := (U₁ \ A₁).card + (U₂ \ A₂).card + (U₃ \ A₃).card + (U₄ \ A₄).card
  have h1 : ((Ω.card : ℝ) - (Ω ∩ Ω').card) / Ω.card ≤ max DA DU / ((k - 3 : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ ha hk3]
    have : (Ω.card : ℝ) - (Ω ∩ Ω').card = (Ω \ Ω').card := by rw [hcA]; ring
    rw [this]
    nlinarith [le_max_left DA DU, ha.le]
  have h2 : ((Ω'.card : ℝ) - (Ω ∩ Ω').card) / Ω'.card ≤ max DA DU / ((k - 3 : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ hb hk3]
    have : (Ω'.card : ℝ) - (Ω ∩ Ω').card = (Ω' \ Ω).card := by rw [hcU]; ring
    rw [this]
    nlinarith [le_max_right DA DU, hb.le]
  have hmax : max (((Ω.card : ℝ) - (Ω ∩ Ω').card) / Ω.card) (((Ω'.card : ℝ) - (Ω ∩ Ω').card) / Ω'.card)
      ≤ max DA DU / ((k - 3 : ℕ) : ℝ) := max_le h1 h2
  rw [← hsA, ← hsU] at havg
  -- the averages are at least `ρ`
  set EB := G w A₁ A₂ A₃ A₄ / Ω.card
  set EU := G w U₁ U₂ U₃ U₄ / Ω'.card
  have hEB : ρ ≤ EB := by
    rw [le_div_iff₀ ha, G]; exact (hsum_bounds Ω).1 |>.trans_eq' (by ring)
  have hEU : ρ ≤ EU := by
    rw [le_div_iff₀ hb, G]; exact (hsum_bounds Ω').1 |>.trans_eq' (by ring)
  have hdiff : -((1 - ρ) * (max DA DU / ((k - 3 : ℕ) : ℝ))) ≤ EB - EU := by
    have := mul_le_mul_of_nonneg_left hmax (by linarith : 0 ≤ 1 - ρ)
    linarith
  -- convert to a log bound
  have hlog : 1 - EU / EB ≤ Real.log (EB / EU) := by
    have := Real.one_sub_inv_le_log_of_pos (div_pos (hρ0.trans_le hEB) (hρ0.trans_le hEU))
    rwa [inv_div] at this
  have hconv : -((1 - ρ) / ρ * (max DA DU / ((k - 3 : ℕ) : ℝ))) ≤ 1 - EU / EB := by
    have hEBp : 0 < EB := hρ0.trans_le hEB
    rw [show 1 - EU / EB = (EB - EU) / EB by field_simp]
    have hM : 0 ≤ (1 - ρ) * (max DA DU / ((k - 3 : ℕ) : ℝ)) := by
      apply mul_nonneg (by linarith); apply div_nonneg _ hk3.le
      exact le_max_of_le_left (by positivity)
    rcases le_or_gt 0 (EB - EU) with hpos | hneg
    · have : 0 ≤ (EB - EU) / EB := div_nonneg hpos hEBp.le
      have : 0 ≤ (1 - ρ) / ρ * (max DA DU / ((k - 3 : ℕ) : ℝ)) := by
        rw [div_mul_eq_mul_div]; exact div_nonneg hM hρ0.le
      linarith
    · rw [le_div_iff₀ hEBp, neg_mul, div_mul_eq_mul_div, div_mul_eq_mul_div]
      have : (1 - ρ) * (max DA DU / ((k - 3 : ℕ) : ℝ)) * EB / ρ
          ≥ (1 - ρ) * (max DA DU / ((k - 3 : ℕ) : ℝ)) := by
        rw [ge_iff_le, le_div_iff₀ hρ0]; exact mul_le_mul_of_nonneg_left hEB hM
      nlinarith
  exact hconv.trans hlog

end Diff

end GridGen.Four
