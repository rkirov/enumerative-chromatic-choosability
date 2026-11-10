/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Defs

/-!
# Witness laws: rotation, and the digon

* `Witness.rotate` — a witness law for the exceptional edge `n - 1 → 0` gives one for any edge;
* `witness_two` — the witness law on the cycle of length two (Step 2 of the proof draft).
-/

namespace Outerplanar

open Finset

section Rotate

variable {n : ℕ} [NeZero n]

/-- Translation of subsets of the cycle. -/
def shift (s : Fin n) : Finset (Fin n) ≃ Finset (Fin n) := Equiv.finsetCongr (Equiv.addRight s)

theorem mem_shift {s i : Fin n} {J : Finset (Fin n)} : i ∈ shift s J ↔ i - s ∈ J := by
  simp only [shift, Equiv.finsetCongr_apply, Finset.mem_map_equiv]
  rw [show (Equiv.addRight s).symm i = i - s from by simp [sub_eq_add_neg]]

theorem shift_eq_empty {s : Fin n} {J : Finset (Fin n)} : shift s J = ∅ ↔ J = ∅ := by
  simp [shift]

theorem arcW_shift (m : ℕ) (s : Fin n) (J : Finset (Fin n)) : arcW m (shift s J) = arcW m J := by
  unfold arcW
  symm
  refine Finset.prod_bij (fun i _ => i + s) (fun i hi => ?_) (fun i _ j _ h => add_right_cancel h)
    (fun j hj => ⟨j - s, ?_, by simp⟩) (fun i hi => ?_)
  · simpa [mem_shift] using hi
  · simpa [mem_shift] using hj
  · have : i + s - 1 - s = i - 1 := by abel
    simp [mem_shift, this]

theorem gW_shift (m : ℕ) (g0 : ℝ) (s : Fin n) (J : Finset (Fin n)) :
    gW m g0 (shift s J) = gW m g0 J := by
  unfold gW
  rw [arcW_shift]
  by_cases h : J = ∅
  · simp [h, shift_eq_empty]
  · simp [h, shift_eq_empty]

open Classical in
/-- A witness law can be rotated to any exceptional edge. -/
theorem Witness.rotate {k : ℕ} {g0 C : ℝ} (h : Witness (n := n) k (-1) g0 C) (e : Fin n) :
    Witness k e g0 C := by
  obtain ⟨p, hp0, hpgood, hpsum, hpmarg, hpent⟩ := h
  set s : Fin n := e + 1 with hs
  refine ⟨fun J => p ((shift s).symm J), fun J => hp0 _, fun J hJ => ?_, ?_, fun i => ?_, ?_⟩
  · obtain ⟨J', rfl⟩ := (shift s).surjective J
    have hJ' : 0 < p J' := by simpa using hJ
    obtain ⟨hg, hpos⟩ := hpgood _ hJ'
    rw [gW_shift]
    refine ⟨fun i hie hi hi1 => ?_, hpos⟩
    rw [mem_shift] at hi hi1
    refine hg (i - s) (fun h => hie ?_) hi ?_
    · have : i = -1 + s := by rw [← h]; abel
      rw [this, hs]; abel
    · have : i - s + 1 = i + 1 - s := by abel
      rwa [this]
  · rw [← hpsum]
    exact Equiv.sum_comp (shift s).symm p
  · rw [← hpmarg (i - s), Finset.sum_filter, Finset.sum_filter,
      ← Equiv.sum_comp (shift s) fun J => if i ∈ J then p ((shift s).symm J) else 0]
    exact Finset.sum_congr rfl fun J _ => by simp [mem_shift]
  · refine hpent.trans (le_of_eq ?_)
    rw [← Equiv.sum_comp (shift s)
      fun J => p ((shift s).symm J) * Real.log (gW (k - 1) g0 J / p ((shift s).symm J))]
    exact Finset.sum_congr rfl fun J _ => by simp [gW_shift]

end Rotate

/-! ### The digon -/

/-- `(t / (t - 1)) ^ t ≤ ((t + 1) / t) ^ (t + 2)` for `t ≥ 2`, by Bernoulli's inequality. -/
theorem digon_pow {t : ℕ} (ht : 2 ≤ t) :
    ((t : ℝ) / (t - 1)) ^ t ≤ (((t : ℝ) + 1) / t) ^ (t + 2) := by
  have ht' : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have h1 : (0 : ℝ) < (t : ℝ) - 1 := by linarith
  have h0 : (0 : ℝ) < t := by linarith
  -- Bernoulli: `1 - 1 / t ≤ (1 - 1 / t ^ 2) ^ t`
  have hb : 1 + (t : ℝ) * (-(1 / (t : ℝ) ^ 2)) ≤ (1 + -(1 / (t : ℝ) ^ 2)) ^ t :=
    one_add_mul_le_pow (by
      have : 1 / (t : ℝ) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith
      linarith) t
  have hb' : ((t : ℝ) - 1) / t ≤ (((t : ℝ) ^ 2 - 1) / (t : ℝ) ^ 2) ^ t := by
    have e1 : 1 + (t : ℝ) * (-(1 / (t : ℝ) ^ 2)) = ((t : ℝ) - 1) / t := by field_simp; ring
    have e2 : 1 + -(1 / (t : ℝ) ^ 2) = ((t : ℝ) ^ 2 - 1) / (t : ℝ) ^ 2 := by field_simp; ring
    rwa [e1, e2] at hb
  -- `t ^ 2 / (t + 1) ^ 2 ≤ (t - 1) / t`
  have hc : (t : ℝ) ^ 2 / ((t : ℝ) + 1) ^ 2 ≤ ((t : ℝ) - 1) / t := by
    rw [div_le_div_iff₀ (by positivity) h0]
    nlinarith
  have hd := hc.trans hb'
  -- rearrange
  have key : ((t : ℝ) / (t - 1)) ^ t * ((t : ℝ) ^ 2 / ((t : ℝ) + 1) ^ 2)
      ≤ ((t : ℝ) / (t - 1)) ^ t * (((t : ℝ) ^ 2 - 1) / (t : ℝ) ^ 2) ^ t :=
    mul_le_mul_of_nonneg_left hd (by positivity)
  have e3 : ((t : ℝ) / (t - 1)) ^ t * (((t : ℝ) ^ 2 - 1) / (t : ℝ) ^ 2) ^ t
      = (((t : ℝ) + 1) / t) ^ t := by
    rw [← mul_pow]
    congr 1
    field_simp
    ring
  rw [e3] at key
  have e4 : (((t : ℝ) + 1) / t) ^ (t + 2) = (((t : ℝ) + 1) / t) ^ t * (((t : ℝ) + 1) ^ 2 / (t : ℝ) ^ 2) := by
    rw [pow_add, div_pow ((t : ℝ) + 1) (t : ℝ) 2]
  rw [e4]
  have hpos : (0 : ℝ) < ((t : ℝ) + 1) ^ 2 / (t : ℝ) ^ 2 := by positivity
  calc ((t : ℝ) / (t - 1)) ^ t
      = ((t : ℝ) / (t - 1)) ^ t * ((t : ℝ) ^ 2 / ((t : ℝ) + 1) ^ 2)
        * (((t : ℝ) + 1) ^ 2 / (t : ℝ) ^ 2) := by field_simp
    _ ≤ (((t : ℝ) + 1) / t) ^ t * (((t : ℝ) + 1) ^ 2 / (t : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right key hpos.le

/-- **The witness law on the digon** (Step 2 of the proof draft): the removed colour sits on
vertex `0`, on vertex `1`, or nowhere. -/
theorem witness_two {k : ℕ} (hk : 4 ≤ k) :
    Witness (n := 2) k 1 (((k : ℝ) - 2) ^ 2 - 1) (lam k 2) := by
  have hk' : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have huniv : (univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have hc0 : ({0} : Finset (Fin 2))ᶜ = {1} := by decide
  have hc1 : ({1} : Finset (Fin 2))ᶜ = {0} := by decide
  have hg0 : gW (n := 2) (k - 1) (((k : ℝ) - 2) ^ 2 - 1) ∅ = ((k : ℝ) - 2) ^ 2 - 1 := by
    simp [gW]
  have hgA : gW (n := 2) (k - 1) (((k : ℝ) - 2) ^ 2 - 1) {0} = (k : ℝ) - 1 := by
    have : ({0} : Finset (Fin 2)) ≠ ∅ := by decide
    simp [gW, this, arcW, hc0, hk1]
  have hgB : gW (n := 2) (k - 1) (((k : ℝ) - 2) ^ 2 - 1) {1} = (k : ℝ) - 1 := by
    have : ({1} : Finset (Fin 2)) ≠ ∅ := by decide
    have h01 : (0 : Fin 2) - 1 = 1 := by decide
    simp [gW, this, arcW, hc1, hk1, h01]
  have hg0pos : (0 : ℝ) < ((k : ℝ) - 2) ^ 2 - 1 := by nlinarith
  let p : Finset (Fin 2) → ℝ := fun J =>
    if J = ∅ then 1 - 2 / (k : ℝ) else if J = {0} ∨ J = {1} then 1 / (k : ℝ) else 0
  have hp0 : p ∅ = 1 - 2 / (k : ℝ) := by simp [p]
  have hpA : p {0} = 1 / (k : ℝ) := by
    have : ({0} : Finset (Fin 2)) ≠ ∅ := by decide
    simp [p, this]
  have hpB : p {1} = 1 / (k : ℝ) := by
    have h1 : ({1} : Finset (Fin 2)) ≠ ∅ := by decide
    simp [p, h1]
  have hpC : p {0, 1} = 0 := by
    have h1 : ({0, 1} : Finset (Fin 2)) ≠ ∅ := by decide
    have h2 : ({0, 1} : Finset (Fin 2)) ≠ {0} := by decide
    have h3 : ({0, 1} : Finset (Fin 2)) ≠ {1} := by decide
    simp [p, h1, h2, h3]
  have hsum4 : ∀ F : Finset (Fin 2) → ℝ, ∑ J, F J = F ∅ + F {0} + F {1} + F {0, 1} := by
    intro F
    rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  have hpos0 : (0 : ℝ) < 1 - 2 / (k : ℝ) := by
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  refine ⟨p, fun J => ?_, fun J hJ => ?_, ?_, fun i => ?_, ?_⟩
  · simp only [p]
    split_ifs
    exacts [hpos0.le, by positivity, le_rfl]
  · simp only [p] at hJ
    split_ifs at hJ with h1 h2
    · subst h1
      exact ⟨fun i _ hi => absurd hi (by simp), by rw [hg0]; exact hg0pos⟩
    · rcases h2 with rfl | rfl
      · refine ⟨fun i hi hi' => ?_, by rw [hgA]; linarith⟩
        fin_cases i <;> simp_all
      · refine ⟨fun i hi hi' => ?_, by rw [hgB]; linarith⟩
        fin_cases i <;> simp_all
    · exact absurd hJ (lt_irrefl _)
  · rw [hsum4, hp0, hpA, hpB, hpC]
    ring
  · rw [Finset.sum_filter, hsum4]
    fin_cases i <;> simp [hpA, hpB, hpC]
  · rw [hsum4, hp0, hpA, hpB, hpC, hg0, hgA, hgB, zero_mul, add_zero]
    have hlam : lam k 2 = (k : ℝ) * ((k : ℝ) - 2) := by simp [lam]; ring
    rw [hlam]
    -- the inequality between the logarithms
    obtain ⟨t, rfl⟩ : ∃ t, k = t + 2 := ⟨k - 2, by omega⟩
    have ht : 2 ≤ t := by omega
    have ht' : (2 : ℝ) ≤ t := by exact_mod_cast ht
    push_cast at *
    have hd := Real.log_le_log (pow_pos (div_pos (by linarith) (by linarith)) _) (digon_pow ht)
    rw [Real.log_pow, Real.log_pow, Real.log_div (by linarith) (by linarith),
      Real.log_div (by linarith) (by linarith)] at hd
    push_cast at hd
    set a := Real.log ((t : ℝ) + 1) with ha
    set b := Real.log (t : ℝ) with hb
    set c := Real.log ((t : ℝ) - 1) with hc
    set d := Real.log ((t : ℝ) + 2) with hd'
    have e1 : Real.log (((t : ℝ) + 2) * ((t : ℝ) + 2 - 2)) = d + b := by
      rw [Real.log_mul (by linarith) (by linarith), show (t : ℝ) + 2 - 2 = t by ring]
    have e2 : Real.log ((((t : ℝ) + 2 - 2) ^ 2 - 1) / (1 - 2 / ((t : ℝ) + 2)))
        = a + c + d - b := by
      have : (((t : ℝ) + 2 - 2) ^ 2 - 1) / (1 - 2 / ((t : ℝ) + 2))
          = ((t : ℝ) + 1) * ((t : ℝ) - 1) * ((t : ℝ) + 2) / t := by
        have ht0 : (t : ℝ) ≠ 0 := by linarith
        have ht2 : (t : ℝ) + 2 ≠ 0 := by linarith
        rw [show (t : ℝ) + 2 - 2 = t by ring, show 1 - 2 / ((t : ℝ) + 2) = t / ((t : ℝ) + 2) by
          field_simp; ring]
        field_simp
        ring
      rw [this, Real.log_div (by nlinarith) (by linarith),
        Real.log_mul (by nlinarith) (by linarith), Real.log_mul (by linarith) (by linarith)]
    have e3 : Real.log (((t : ℝ) + 2 - 1) / (1 / ((t : ℝ) + 2))) = a + d := by
      have : ((t : ℝ) + 2 - 1) / (1 / ((t : ℝ) + 2)) = ((t : ℝ) + 1) * ((t : ℝ) + 2) := by
        field_simp
        ring
      rw [this, Real.log_mul (by linarith) (by linarith)]
    rw [e1, e2, e3]
    have hT : (0 : ℝ) < (t : ℝ) + 2 := by linarith
    have : (1 - 2 / ((t : ℝ) + 2)) * (a + c + d - b) + 1 / ((t : ℝ) + 2) * (a + d)
        + 1 / ((t : ℝ) + 2) * (a + d) - (d + b)
        = (((t : ℝ) + 2) * (a - b) - (t : ℝ) * (b - c)) / ((t : ℝ) + 2) := by
      field_simp
      ring
    have h2 : 0 ≤ (((t : ℝ) + 2) * (a - b) - (t : ℝ) * (b - c)) / ((t : ℝ) + 2) :=
      div_nonneg (by linarith) hT.le
    linarith

end Outerplanar
