/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.WitnessCount

/-!
# The witness law for `k ≥ 4`

This is Step 4 of the outerplanar proof draft
(`ai_research_notes/OUTERPLANAR_PROOF_DRAFT_2026-11-09.md`), a result of this repository's 2026-11
AI research collaboration, not from the literature.

`witness_of_four_le`: for `k ≥ 4` and `n ≥ 3` there is a law on the sets `J` of vertices of the
cycle, supported on sets without two consecutive elements of the path `0, …, n - 1`, with all
marginals `1 / k`, whose entropy relative to `gW (k - 1) ((k - 2) ^ n - (-1) ^ n)` is at least
`log ((k - 1) ^ n - (-1) ^ n)`.

The law is that of the zero set of a uniformly random colouring of the twisted full cover
(`twist`, see `Outerplanar/WitnessCount.lean`). With `q = k - 1`, `r = k - 2`, `h J` the number
of colourings with zero set `J` and `g = gW`:

* the marginals are `1 / k` because adding a constant to all colours permutes the colourings;
* `h J ≤ c_J * g J` with `c_J = 1` if `0, n - 1 ∈ J`, `r / q` if exactly one of them is in `J`,
  `1 + 1 / (q r)` if neither is and `J ≠ ∅` (`class_bound`), and `h ∅`, `g ∅` are known exactly;
* `log (g / h) ≥ 1 - h / g`, so the relative entropy is at least `log λ + (1 / λ) ∑ h J (1 - c_J)`,
  and the sum is an explicit expression in the class masses, which are given by the transfer
  count. It is nonnegative for all `k ≥ 4`, `n ≥ 3` (`final_ineq`); no case needs a separate
  numerical check.
-/

namespace Outerplanar

open Finset

section Real

variable {n : ℕ} [NeZero n] {r : ℕ}

theorem twist_card_real {j : ℕ} (hn : n = j + 1) :
    (#(twist n r) : ℝ) = ((r : ℝ) + 1) * ((r : ℝ) + 1) ^ j + (-1) ^ j := by
  rw [card_twist hn]
  obtain ⟨ha, hb⟩ := wab_closed r j
  push_cast
  linear_combination ha + (r : ℝ) * hb

theorem twist_both_real {j : ℕ} (hn : n = j + 1) :
    ((r : ℝ) + 2) * (#{f ∈ twist n r | f 0 = 0 ∧ f (-1) = 0} : ℝ) =
      ((r : ℝ) + 1) ^ j + (-1) ^ j * ((r : ℝ) + 1) := by
  rw [card_twist_both hn]
  exact (wab_closed r j).1

theorem twist_nozero_real {j : ℕ} (hn : n = j + 1) (s : ℕ) :
    ((s : ℝ) + 2) * (#{f ∈ twist n (s + 1) | ∀ i, f i ≠ 0} : ℝ) =
      ((s : ℝ) + 2) * (((s : ℝ) + 1) * ((s : ℝ) + 1) ^ j + (-1) ^ j) +
        ((s : ℝ) + 1) ^ j - (-1) ^ j := by
  rw [card_twist_nozero hn s]
  obtain ⟨ha, hb⟩ := wab_closed s j
  push_cast
  linear_combination ((s : ℝ) + 2) * ha + ((s : ℝ) + 2) * (s : ℝ) * hb + hb

/-- The inequality between the class masses to which the witness inequality reduces. -/
theorem final_ineq {R q K X Y σ lam a h0 g0 : ℝ} (hq : q = R + 1) (hK : K = R + 2) (hR : 2 ≤ R)
    (hσ : σ = 1 ∨ σ = -1) (hX : q ≤ X) (hY : 2 ≤ Y) (hlam : lam = q * X + σ)
    (ha : K * a = X + σ * q) (hg : g0 = R * Y + σ) (hh : q * h0 = q * g0 + Y - σ) :
    0 ≤ -1 / (q * R) * lam + 1 / R * (lam / K) + 1 / R * (lam / K) +
      (1 / (q * R) - 2 / R) * a + (1 / (q * R) - (h0 - g0) / g0) * h0 := by
  have hR0 : 0 < R := by linarith
  have hq0 : 0 < q := by linarith
  have hK0 : 0 < K := by linarith
  have hg0 : 0 < g0 := by
    rcases hσ with h | h <;> rw [hg, h] <;> nlinarith
  have ha' : a = (X + σ * q) / K := by rw [eq_div_iff hK0.ne']; linarith
  have hh' : h0 = g0 + (Y - σ) / q := by
    rw [← sub_eq_iff_eq_add', eq_div_iff hq0.ne']; linarith
  have hcoef : 1 / (q * R) - (h0 - g0) / g0 = σ / (R * g0) := by
    rw [hh', add_sub_cancel_left]
    field_simp
    rw [hg, hq]; ring
  have key : -1 / (q * R) * lam + 1 / R * (lam / K) + 1 / R * (lam / K) +
      (1 / (q * R) - 2 / R) * a + (1 / (q * R) - (h0 - g0) / g0) * h0 =
      ((q ^ 2 - 3 * q + 1) * X - σ * (2 * q ^ 2 - 2 * q + 1)) / (q * R * K) +
        σ * (h0 / (R * g0)) := by
    rw [hcoef, ha', hlam, hK, hq]
    field_simp
    ring
  rw [key]
  have hpoly : 1 ≤ q ^ 2 - 3 * q + 1 := by nlinarith
  rcases hσ with h | h
  · rw [h]
    have h1 : 1 / R ≤ h0 / (R * g0) := by
      rw [div_le_div_iff₀ hR0 (by positivity)]
      have : g0 ≤ h0 := by
        rw [hh']
        have : 0 ≤ (Y - σ) / q := div_nonneg (by rw [h]; linarith) hq0.le
        linarith
      nlinarith
    have h2 : ((q ^ 2 - 3 * q + 1) * X - 1 * (2 * q ^ 2 - 2 * q + 1)) / (q * R * K) + 1 / R =
        (q ^ 2 - 3 * q + 1) * (X - 1) / (q * R * K) := by
      rw [hK, hq]; field_simp; ring
    have h3 : 0 ≤ (q ^ 2 - 3 * q + 1) * (X - 1) / (q * R * K) :=
      div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
    linarith
  · rw [h]
    have h1 : h0 / (R * g0) ≤ K / (q * R) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : q * h0 ≤ K * g0 := by rw [hh, hK, hq, hg, h]; nlinarith
      nlinarith
    have h2 : ((q ^ 2 - 3 * q + 1) * X - -1 * (2 * q ^ 2 - 2 * q + 1)) / (q * R * K) -
        K / (q * R) = ((q ^ 2 - 3 * q + 1) * X + q ^ 2 - 4 * q) / (q * R * K) := by
      rw [hK, hq]; field_simp; ring
    have h3 : 0 ≤ ((q ^ 2 - 3 * q + 1) * X + q ^ 2 - 4 * q) / (q * R * K) :=
      div_nonneg (by nlinarith) (by positivity)
    linarith

end Real

section Assembly

variable {n : ℕ} [NeZero n] {r : ℕ}

/-- The set of vertices coloured `0`. -/
def zset (f : Fin n → Fin (r + 2)) : Finset (Fin n) := univ.filter fun i => f i = 0

omit [NeZero n] in
theorem mem_zset {f : Fin n → Fin (r + 2)} {i : Fin n} : i ∈ zset f ↔ f i = 0 := by
  simp [zset]

/-- The number of colourings of the twisted cover whose zero set is `J`. -/
def hcount (n r : ℕ) [NeZero n] (J : Finset (Fin n)) : ℕ := #{f ∈ twist n r | zset f = J}

theorem sum_hcount (Q : Finset (Fin n) → Prop) [DecidablePred Q] :
    ∑ J with Q J, hcount n r J = #{f ∈ twist n r | Q (zset f)} := by
  rw [Finset.card_eq_sum_card_fiberwise (f := zset) (t := univ.filter Q)
    (fun f hf => mem_coe.2 (mem_filter.2 ⟨mem_univ _, (mem_filter.1 (mem_coe.1 hf)).2⟩))]
  refine Finset.sum_congr rfl fun J hJ => ?_
  rw [hcount]
  congr 1
  ext f
  simp only [mem_filter]
  constructor
  · rintro ⟨hf, rfl⟩; exact ⟨⟨hf, (mem_filter.1 hJ).2⟩, rfl⟩
  · rintro ⟨⟨hf, _⟩, h⟩; exact ⟨hf, h⟩

theorem sum_hcount_univ : ∑ J, hcount n r J = #(twist n r) := by
  have := sum_hcount (n := n) (r := r) (fun _ => True)
  simpa using this

theorem sum_hcount_mem (i : Fin n) :
    ∑ J with i ∈ J, hcount n r J = #{f ∈ twist n r | f i = 0} := by
  rw [sum_hcount (fun J => i ∈ J)]
  simp only [mem_zset]

theorem sum_hcount_both :
    ∑ J with (0 ∈ J ∧ -1 ∈ J), hcount n r J = #{f ∈ twist n r | f 0 = 0 ∧ f (-1) = 0} := by
  rw [sum_hcount (fun J => 0 ∈ J ∧ -1 ∈ J)]
  simp only [mem_zset]

theorem hcount_empty : hcount n r ∅ = #{f ∈ twist n r | ∀ i, f i ≠ 0} := by
  rw [hcount]
  refine congrArg card (Finset.filter_congr fun f _ => ?_)
  rw [zset, Finset.filter_eq_empty_iff]
  simp

theorem hcount_le_part (J : Finset (Fin n)) : hcount n r J ≤ #(part n r Jᶜ) := by
  refine Finset.card_le_card fun f hf => ?_
  rw [mem_filter, mem_twist] at hf
  obtain ⟨⟨hp, hc⟩, rfl⟩ := hf
  rw [mem_part]
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi _ _ => hp i hi, hc⟩
  · rw [mem_compl, not_not] at hi; exact mem_zset.1 hi
  · rw [mem_compl] at hi; exact fun h => hi (mem_zset.2 h)

theorem good_of_hcount_pos {J : Finset (Fin n)} (h : 0 < hcount n r J) : Good (-1) J := by
  obtain ⟨f, hf⟩ := Finset.card_pos.1 h
  rw [mem_filter, mem_twist] at hf
  obtain ⟨⟨hp, -⟩, rfl⟩ := hf
  intro i hi hiJ hiJ'
  exact hp i hi ((mem_zset.1 hiJ).trans (mem_zset.1 hiJ').symm)

omit [NeZero n] in
theorem sum_mul_ind (h : Finset (Fin n) → ℝ) (A : ℝ) (P : Finset (Fin n) → Prop)
    [DecidablePred P] :
    ∑ J, h J * (A * if P J then 1 else 0) = A * ∑ J with P J, h J := by
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  split_ifs <;> ring

theorem arcW_pos (hr : 1 ≤ r) (J : Finset (Fin n)) : 0 < arcW (r + 1) J := by
  refine Finset.prod_pos fun i _ => ?_
  have : (1 : ℝ) ≤ r := by exact_mod_cast hr
  split_ifs
  · positivity
  · push_cast; linarith

/-- The comparison of the number of colourings with zero set `J` with `arcW`, in the form used
by the entropy bound; `b` is the class constant. -/
theorem class_bound (hn : 3 ≤ n) (hr : 1 ≤ r) {J : Finset (Fin n)} (hJ : J ≠ ∅) :
    (-1 / (((r : ℝ) + 1) * r) + 1 / (r : ℝ) * (if (0 : Fin n) ∈ J then 1 else 0) +
      1 / (r : ℝ) * (if (-1 : Fin n) ∈ J then 1 else 0) +
      (1 / (((r : ℝ) + 1) * r) - 2 / r) * (if (0 : Fin n) ∈ J ∧ (-1 : Fin n) ∈ J then 1 else 0)) ≤
      1 - (hcount n r J : ℝ) / arcW (r + 1) J := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hw := arcW_pos hr J
  have hle : (hcount n r J : ℝ) ≤ #(part n r Jᶜ) := by exact_mod_cast hcount_le_part J
  have hh0 : (0 : ℝ) ≤ hcount n r J := Nat.cast_nonneg _
  by_cases h0 : (0 : Fin n) ∈ J
  · by_cases h1 : (-1 : Fin n) ∈ J
    · have hb : (#(part n r Jᶜ) : ℝ) ≤ arcW (r + 1) J := by
        rw [← phi_compl_eq (Or.inl h0)]; exact_mod_cast peel_both h0 h1
      have : (hcount n r J : ℝ) / arcW (r + 1) J ≤ 1 := (div_le_one hw).2 (hle.trans hb)
      simp only [h0, h1, and_self, ite_true]
      have e : -1 / (((r : ℝ) + 1) * r) + 1 / (r : ℝ) * 1 + 1 / (r : ℝ) * 1 +
          (1 / (((r : ℝ) + 1) * r) - 2 / r) * 1 = 0 := by field_simp; ring
      rw [e]; linarith
    · have hb : (#(part n r Jᶜ) : ℝ) * ((r : ℝ) + 1) ≤ r * arcW (r + 1) J := by
        rw [← phi_compl_eq (Or.inl h0)]; exact_mod_cast peel_last (by omega) h0 h1
      have : (hcount n r J : ℝ) / arcW (r + 1) J ≤ r / ((r : ℝ) + 1) := by
        rw [div_le_div_iff₀ hw (by positivity)]; nlinarith
      simp only [h0, h1, and_false, ite_true, ite_false]
      have e : -1 / (((r : ℝ) + 1) * r) + 1 / (r : ℝ) * 1 + 1 / (r : ℝ) * 0 +
          (1 / (((r : ℝ) + 1) * r) - 2 / r) * 0 = 1 - r / ((r : ℝ) + 1) := by field_simp; ring
      rw [e]; linarith
  · by_cases h1 : (-1 : Fin n) ∈ J
    · have hb : (#(part n r Jᶜ) : ℝ) * ((r : ℝ) + 1) ≤ r * arcW (r + 1) J := by
        rw [← phi_compl_eq (Or.inr h1)]; exact_mod_cast peel_zero (by omega) h0 h1
      have : (hcount n r J : ℝ) / arcW (r + 1) J ≤ r / ((r : ℝ) + 1) := by
        rw [div_le_div_iff₀ hw (by positivity)]; nlinarith
      simp only [h0, h1, false_and, ite_true, ite_false]
      have e : -1 / (((r : ℝ) + 1) * r) + 1 / (r : ℝ) * 0 + 1 / (r : ℝ) * 1 +
          (1 / (((r : ℝ) + 1) * r) - 2 / r) * 0 = 1 - r / ((r : ℝ) + 1) := by field_simp; ring
      rw [e]; linarith
    · obtain ⟨j, hj⟩ := nonempty_iff_ne_empty.2 hJ
      have hb1 : (#(part n r Jᶜ) : ℝ) * (((r : ℝ) + 1) * ((r : ℝ) + 1)) ≤
          ((r : ℝ) * ((r : ℝ) + 1) + 1) * phi r Jᶜ := by
        exact_mod_cast peel_none hn h0 h1 hj
      have hb2 := phi_compl_mul (r := r) h0 h1
      have hb : (#(part n r Jᶜ) : ℝ) * (((r : ℝ) + 1) * r) ≤
          ((r : ℝ) * ((r : ℝ) + 1) + 1) * arcW (r + 1) J := by
        have h3 : (#(part n r Jᶜ) : ℝ) * (((r : ℝ) + 1) * ((r : ℝ) + 1)) * r ≤
            ((r : ℝ) * ((r : ℝ) + 1) + 1) * (arcW (r + 1) J * ((r : ℝ) + 1)) := by
          have h5 := mul_le_mul_of_nonneg_right hb1 hr0.le
          rw [← hb2]
          linarith
        have h4 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
        refine le_of_mul_le_mul_right ?_ h4
        linarith
      have : (hcount n r J : ℝ) / arcW (r + 1) J ≤
          ((r : ℝ) * ((r : ℝ) + 1) + 1) / (((r : ℝ) + 1) * r) := by
        rw [div_le_div_iff₀ hw (by positivity)]
        have := mul_le_mul_of_nonneg_right hle (by positivity : (0 : ℝ) ≤ ((r : ℝ) + 1) * r)
        linarith
      simp only [h0, h1, and_self, ite_false]
      have e : -1 / (((r : ℝ) + 1) * r) + 1 / (r : ℝ) * 0 + 1 / (r : ℝ) * 0 +
          (1 / (((r : ℝ) + 1) * r) - 2 / r) * 0 =
          1 - ((r : ℝ) * ((r : ℝ) + 1) + 1) / (((r : ℝ) + 1) * r) := by field_simp; ring
      rw [e]; linarith

end Assembly

section Main

variable {n : ℕ} [NeZero n] {r : ℕ}

theorem twist_nozero_real' {j : ℕ} (hn : n = j + 1) (hr : 1 ≤ r) :
    ((r : ℝ) + 1) * (#{f ∈ twist n r | ∀ i, f i ≠ 0} : ℝ) =
      ((r : ℝ) + 1) * ((r : ℝ) * (r : ℝ) ^ j + (-1) ^ j) + (r : ℝ) ^ j - (-1) ^ j := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have h := twist_nozero_real (n := n) hn s
  have e : ((s + 1 : ℕ) : ℝ) = (s : ℝ) + 1 := by push_cast; ring
  have e2 : (s : ℝ) + 1 + 1 = (s : ℝ) + 2 := by ring
  rw [e, e2]
  exact h

theorem witness_core (j : ℕ) (hr : 2 ≤ r) (hn : n = j + 1) (hj : 2 ≤ j) :
    ∃ p : Finset (Fin n) → ℝ, (∀ J, 0 ≤ p J) ∧
      (∀ J, 0 < p J → Good (-1) J ∧ 0 < gW (r + 1) ((r : ℝ) ^ n - (-1) ^ n) J) ∧
      ∑ J, p J = 1 ∧ (∀ i, ∑ J with i ∈ J, p J = 1 / ((r : ℝ) + 2)) ∧
      Real.log (((r : ℝ) + 1) ^ n - (-1) ^ n) ≤
        ∑ J, p J * Real.log (gW (r + 1) ((r : ℝ) ^ n - (-1) ^ n) J / p J) := by
  have hn3 : 3 ≤ n := by omega
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hσ := neg_one_pow_eq_or ℝ j
  obtain ⟨lam, hlamdef⟩ : ∃ lam : ℝ, lam = ((r : ℝ) + 1) ^ n - (-1) ^ n := ⟨_, rfl⟩
  obtain ⟨g0, hg0def⟩ : ∃ g0 : ℝ, g0 = (r : ℝ) ^ n - (-1) ^ n := ⟨_, rfl⟩
  rw [← hlamdef, ← hg0def]
  have hlam : lam = ((r : ℝ) + 1) * ((r : ℝ) + 1) ^ j + (-1) ^ j := by
    rw [hlamdef, hn, pow_succ, pow_succ]; ring
  have hg0 : g0 = (r : ℝ) * (r : ℝ) ^ j + (-1) ^ j := by
    rw [hg0def, hn, pow_succ, pow_succ]; ring
  have hX : (r : ℝ) + 1 ≤ ((r : ℝ) + 1) ^ j :=
    le_self_pow₀ (by linarith) (by omega)
  have hY : (2 : ℝ) ≤ (r : ℝ) ^ j := hr'.trans (le_self_pow₀ (by linarith) (by omega))
  have hlam0 : 0 < lam := by
    rcases hσ with h | h <;> rw [hlam, h] <;> nlinarith
  have hg00 : 0 < g0 := by
    rcases hσ with h | h <;> rw [hg0, h] <;> nlinarith
  have hD : (#(twist n r) : ℝ) = lam := by rw [twist_card_real hn, hlam]
  have S_all : ∑ J, (hcount n r J : ℝ) = lam := by
    rw [← Nat.cast_sum, sum_hcount_univ, hD]
  have S_i : ∀ i : Fin n, ∑ J with i ∈ J, (hcount n r J : ℝ) = lam / ((r : ℝ) + 2) := by
    intro i
    rw [← Nat.cast_sum, sum_hcount_mem, eq_div_iff (by positivity), ← hD, ← card_twist_fiber i]
    push_cast; ring
  have S_b : ((r : ℝ) + 2) * ∑ J with ((0 : Fin n) ∈ J ∧ (-1 : Fin n) ∈ J), (hcount n r J : ℝ) =
      ((r : ℝ) + 1) ^ j + (-1) ^ j * ((r : ℝ) + 1) := by
    rw [← Nat.cast_sum, sum_hcount_both]; exact twist_both_real hn
  have S_0 : ((r : ℝ) + 1) * (hcount n r ∅ : ℝ) =
      ((r : ℝ) + 1) * g0 + (r : ℝ) ^ j - (-1) ^ j := by
    rw [hcount_empty, hg0]; exact twist_nozero_real' hn (by omega)
  have S_e : ∑ J with J = (∅ : Finset (Fin n)), (hcount n r J : ℝ) = hcount n r ∅ := by
    rw [Finset.sum_filter, Finset.sum_ite_eq']; simp
  have hgW : ∀ J : Finset (Fin n), 0 < gW (r + 1) g0 J := by
    intro J
    unfold gW
    split_ifs
    · exact hg00
    · exact arcW_pos (by omega) J
  -- the class constants
  obtain ⟨b, hb⟩ : ∃ b : Finset (Fin n) → ℝ, b = fun J =>
      -1 / (((r : ℝ) + 1) * r) + 1 / (r : ℝ) * (if (0 : Fin n) ∈ J then 1 else 0) +
        1 / (r : ℝ) * (if (-1 : Fin n) ∈ J then 1 else 0) +
        (1 / (((r : ℝ) + 1) * r) - 2 / r) * (if (0 : Fin n) ∈ J ∧ (-1 : Fin n) ∈ J then 1 else 0) +
        (1 / (((r : ℝ) + 1) * r) - ((hcount n r ∅ : ℝ) - g0) / g0) * (if J = ∅ then 1 else 0) :=
    ⟨_, rfl⟩
  have hT := final_ineq (R := r) (q := (r : ℝ) + 1) (K := (r : ℝ) + 2) rfl rfl hr' hσ hX hY hlam
    S_b hg0 S_0
  have hsum : ∑ J, (hcount n r J : ℝ) * b J =
      -1 / (((r : ℝ) + 1) * r) * lam + 1 / (r : ℝ) * (lam / ((r : ℝ) + 2)) +
        1 / (r : ℝ) * (lam / ((r : ℝ) + 2)) + (1 / (((r : ℝ) + 1) * r) - 2 / r) *
          ∑ J with ((0 : Fin n) ∈ J ∧ (-1 : Fin n) ∈ J), (hcount n r J : ℝ) +
        (1 / (((r : ℝ) + 1) * r) - ((hcount n r ∅ : ℝ) - g0) / g0) * (hcount n r ∅ : ℝ) := by
    simp only [hb, mul_add, sum_add_distrib, sum_mul_ind, ← Finset.sum_mul, S_all, S_i, S_e]
    ring
  have hbJ : ∀ J : Finset (Fin n), b J ≤ 1 - (hcount n r J : ℝ) / gW (r + 1) g0 J := by
    intro J
    by_cases hJ : J = ∅
    · subst hJ
      simp only [hb, gW, notMem_empty, ite_false, ite_true, false_and, mul_zero, add_zero, mul_one]
      refine le_of_eq ?_
      field_simp
      ring
    · have := class_bound (r := r) hn3 (by omega) hJ
      simp only [hb, gW, ite_eq_right hJ, mul_zero, add_zero]
      exact this
  obtain ⟨p, hp⟩ : ∃ p : Finset (Fin n) → ℝ, p = fun J => (hcount n r J : ℝ) / lam := ⟨_, rfl⟩
  have hp0 : ∀ J, 0 ≤ p J := fun J => by
    rw [hp]; exact div_nonneg (Nat.cast_nonneg _) hlam0.le
  have hterm : ∀ J, p J * (Real.log lam + b J) ≤ p J * Real.log (gW (r + 1) g0 J / p J) := by
    intro J
    by_cases hz : hcount n r J = 0
    · have : p J = 0 := by rw [hp]; simp only [hz, Nat.cast_zero, zero_div]
      rw [this, zero_mul, zero_mul]
    · have hpos : (0 : ℝ) < hcount n r J := Nat.cast_pos.2 (Nat.pos_of_ne_zero hz)
      have hgp := div_pos (hgW J) hpos
      have e : gW (r + 1) g0 J / p J = lam * (gW (r + 1) g0 J / (hcount n r J : ℝ)) := by
        rw [hp]; field_simp
      rw [e, Real.log_mul hlam0.ne' hgp.ne']
      have h1 := Real.one_sub_inv_le_log_of_pos hgp
      rw [inv_div] at h1
      exact mul_le_mul_of_nonneg_left (by linarith [hbJ J]) (hp0 J)
  refine ⟨p, hp0, ?_, ?_, ?_, ?_⟩
  · intro J hJ
    refine ⟨good_of_hcount_pos (r := r) (Nat.pos_of_ne_zero fun hz => ?_), hgW J⟩
    rw [hp] at hJ
    simp only [hz, Nat.cast_zero, zero_div, lt_self_iff_false] at hJ
  · rw [hp, ← Finset.sum_div, S_all, div_self hlam0.ne']
  · intro i
    rw [hp, ← Finset.sum_div, S_i]
    field_simp
  · have e : ∀ J, p J * (Real.log lam + b J) =
        ((hcount n r J : ℝ) * Real.log lam + (hcount n r J : ℝ) * b J) / lam := fun J => by
      rw [hp]; ring
    have hfinal : Real.log lam ≤ ∑ J, p J * (Real.log lam + b J) := by
      rw [Finset.sum_congr rfl (fun J _ => e J), ← Finset.sum_div, sum_add_distrib,
        ← Finset.sum_mul, S_all, hsum, le_div_iff₀ hlam0]
      linarith
    exact hfinal.trans (Finset.sum_le_sum fun J _ => hterm J)

end Main

/-- The witness law of Step 4: the law of the set of vertices coloured `0` in a uniformly random
colouring of the full cover with a shift twist. -/
theorem witness_of_four_le {k n : ℕ} [NeZero n] (hk : 4 ≤ k) (hn : 3 ≤ n) :
    Witness (n := n) k (-1) (((k : ℝ) - 2) ^ n - (-1) ^ n) (lam k n) := by
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 2 := ⟨k - 2, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have e1 : ((r + 2 : ℕ) : ℝ) - 2 = r := by push_cast; ring
  have e2 : ((r + 2 : ℕ) : ℝ) - 1 = (r : ℝ) + 1 := by push_cast; ring
  have e3 : ((r + 2 : ℕ) : ℝ) = (r : ℝ) + 2 := by push_cast; ring
  rw [lam, e1, e2]
  unfold Witness
  rw [e3]
  exact witness_core j (by omega) hj (by omega)

end Outerplanar
