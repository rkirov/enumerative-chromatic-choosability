import Grid3.Three.Entropy
import Grid3.Three.Cert.Parry

/-!
# A common entropy interface for numerical and symbolic seams

The assembly needs a lower bound on conditional Shannon entropy, not a strict certificate of
one particular format. This file converts both numerical certificate formats and the exact
Parry seam to that common interface. The final two lemmas assemble a finite chain directly
from its column laws and row-entropy bounds, allowing arbitrary mixtures of seam formats.

This is a proved interface, not the missing canonicalization of actual list assignments.
-/

open Finset Real

namespace Grid3.Three

variable {S : Type*} [Fintype S]

/-- Read a single stochastic kernel's entropy from the length-zero Markov marginal. -/
theorem seamterm_zero_eq (law : S → ℝ) (K : S → S → ℝ)
    (hK : ∀ c, ∑ s, K c s = 1) :
    seamterm law (fun _ => K) 0 = ∑ c, law c * rowH K c := by
  classical
  rw [seamterm_marginal law (fun _ => K) (fun _ => hK)]
  simp only [lastMarg_zero]

/-- A collision certificate gives a local bound without assuming a whole Markov chain. -/
theorem row_entropy_of_collision (law : S → ℝ) (K : S → S → ℝ)
    (hlaw : ∀ c, 0 ≤ law c) (hsum : ∑ c, law c = 1)
    (hK : ∀ c s, 0 ≤ K c s) (hKn : ∀ c, ∑ s, K c s = 1)
    (r : ℝ) (hr : 0 < r)
    (hc : (∑ c, ∑ s, law c * K c s ^ 2) * r < 1) :
    Real.log r ≤ ∑ c, law c * rowH K c := by
  classical
  have h := seamterm_ge_log_collision r hr law (fun _ => K) (fun _ => hK)
    (fun _ => hKn) 0 law hlaw hsum (lastMarg_zero law (fun _ => K)) hc
  rwa [seamterm_zero_eq law K hKn] at h

/-- The fourth-root fallback gives exactly the same local interface. -/
theorem row_entropy_of_fourth (law : S → ℝ) (K : S → S → ℝ)
    (hlaw : ∀ c, 0 ≤ law c) (hsum : ∑ c, law c = 1)
    (hK : ∀ c s, 0 ≤ K c s) (hKn : ∀ c, ∑ s, K c s = 1)
    (r : ℝ) (hr : 0 < r) (w : S → S → ℝ) (hw : ∀ c s, 0 ≤ w c s)
    (he : ∀ c s, law c * K c s ≤ w c s ^ 4 * law c)
    (hc : (∑ c, ∑ s, law c * K c s * w c s) ^ 4 * r < 1) :
    Real.log r ≤ ∑ c, law c * rowH K c := by
  classical
  have h := seamterm_ge_log r hr law (fun _ => K) (fun _ => hK) (fun _ => hKn)
    0 law hlaw hsum (lastMarg_zero law (fun _ => K)) w hw he hc
  rwa [seamterm_zero_eq law K hKn] at h

namespace Cert

theorem rhoR_eq_rho : rhoR = Grid3.Three.rho := rfl

/-- Consume the disjunctive numerical certificate; normalization is an explicit obligation. -/
theorem EntropyCert.row_entropy {law : Fin SB → ℝ} {K : Fin SB → Fin SB → ℝ}
    (h : EntropyCert law K) (hlaw : ∀ c, 0 ≤ law c) (hsum : ∑ c, law c = 1)
    (hK : ∀ c s, 0 ≤ K c s) (hKn : ∀ c, ∑ s, K c s = 1) :
    Real.log rhoR ≤ ∑ c, law c * rowH K c := by
  rcases h with hc | ⟨w, hw, he, hc⟩
  · exact row_entropy_of_collision law K hlaw hsum hK hKn rhoR rhoR_pos hc
  · exact row_entropy_of_fourth law K hlaw hsum hK hKn rhoR rhoR_pos w hw he hc

theorem SeamOK.row_entropy {mL mR : ℕ} {pL pR : List ℕ}
    {K : Fin SB → Fin SB → ℝ} (h : SeamOK mL pL mR pR K)
    (hsum : ∑ c, lawR mL pL c = 1) :
    Real.log Grid3.Three.rho ≤ ∑ c, lawR mL pL c * rowH K c :=
  h.entropy.row_entropy (lawR_nonneg mL pL) hsum h.nonneg h.rowsum

/-- A uniform source's stronger collision certificate supplies the root-deficit bonus. -/
theorem SeamOK.row_entropy_bonus {mL mR : ℕ} {pL pR : List ℕ}
    {K : Fin SB → Fin SB → ℝ} (h : SeamOK mL pL mR pR K)
    (hsum : ∑ c, lawR mL pL c = 1)
    (hc : (18 / 17) * rhoR * ∑ c, ∑ s, lawR mL pL c * K c s ^ 2 < 1) :
    Real.log Grid3.Three.rho + Real.log (18 / 17) ≤
      ∑ c, lawR mL pL c * rowH K c := by
  have hb := row_entropy_of_collision _ K (lawR_nonneg mL pL) hsum h.nonneg h.rowsum
    ((18 / 17) * rhoR) (mul_pos (by norm_num) rhoR_pos) (by nlinarith [hc])
  rw [Real.log_mul (by norm_num : (18 / 17 : ℝ) ≠ 0) rhoR_pos.ne', add_comm] at hb
  exact hb

/-- The symbolic seam joins the same interface, with equality, not a strict certificate. -/
theorem parry_row_entropy :
    (∑ c, uLaw c * rowH KU c) = Real.log Grid3.Three.rho := parry_entropy

end Cert

/-- Marginal consistency is needed only up to the seam being used, not at future indices. -/
theorem lastMarg_eq_law_upto [DecidableEq S]
    (law : ℕ → S → ℝ) (K : ℕ → S → S → ℝ) (n : ℕ)
    (hstep : ∀ k, k < n → ∀ s, ∑ c, law k c * K k c s = law (k + 1) s) :
    ∀ k, k ≤ n → ∀ c, lastMarg (law 0) K k c = law k c := by
  intro k hk
  induction k with
  | zero => exact lastMarg_zero (law 0) K
  | succ k ih =>
    intro s
    rw [lastMarg_succ]
    simp_rw [ih (by omega)]
    exact hstep k (by omega) s

/-- Assemble mixed numerical/symbolic seams from their local Shannon lower bounds. -/
theorem entropy_from_row_bounds [DecidableEq S] (W N : ℕ)
    (law : ℕ → S → ℝ) (K : ℕ → S → S → ℝ)
    (hα : ∀ s, 0 ≤ law 0 s) (hαsum : ∑ s, law 0 s = 1)
    (hK : ∀ k c s, 0 ≤ K k c s) (hKn : ∀ k c, ∑ s, K k c s = 1)
    (hstep : ∀ k, k < W - 1 → ∀ s, ∑ c, law k c * K k c s = law (k + 1) s)
    (hN : 0 < N)
    (hcard : (Finset.univ.filter (fun p : PState S (W - 1) =>
      0 < mu (law 0) K (W - 1) p)).card ≤ N)
    (hroot : Real.log 12 ≤ H (law 0))
    (hseam : ∀ k, k < W - 1 → Real.log rho ≤ ∑ c, law k c * rowH (K k) c) :
    (a (W - 1) : ℝ) ≤ N := by
  apply entropy_bound_conditional W (law 0) K N hα hK hKn (by exact_mod_cast hN)
    (hsupp_from_card (law 0) K W N hα hK hαsum hKn hcard) hroot
  intro k hk
  rw [seamterm_marginal (law 0) K hKn k]
  simp_rw [lastMarg_eq_law_upto law K (W - 1) hstep k hk.le]
  exact hseam k hk

/-- The same assembly when one strong seam pays for a deficit at the initial column. -/
theorem entropy_from_row_bounds_one_bonus [DecidableEq S] (W N : ℕ)
    (law : ℕ → S → ℝ) (K : ℕ → S → S → ℝ) (j : Fin (W - 1)) (δ : ℝ)
    (hα : ∀ s, 0 ≤ law 0 s) (hαsum : ∑ s, law 0 s = 1)
    (hK : ∀ k c s, 0 ≤ K k c s) (hKn : ∀ k c, ∑ s, K k c s = 1)
    (hstep : ∀ k, k < W - 1 → ∀ s, ∑ c, law k c * K k c s = law (k + 1) s)
    (hN : 0 < N)
    (hcard : (Finset.univ.filter (fun p : PState S (W - 1) =>
      0 < mu (law 0) K (W - 1) p)).card ≤ N)
    (hroot : Real.log 12 - δ ≤ H (law 0))
    (hseam : ∀ k, k < W - 1 → Real.log rho ≤ ∑ c, law k c * rowH (K k) c)
    (hbonus : Real.log rho + δ ≤ ∑ c, law j c * rowH (K j) c) :
    (a (W - 1) : ℝ) ≤ N := by
  apply entropy_bound_conditional_one_bonus W (law 0) K N j δ hα hK hKn
    (by exact_mod_cast hN) (hsupp_from_card (law 0) K W N hα hK hαsum hKn hcard) hroot
  · intro k hk
    rw [seamterm_marginal (law 0) K hKn k]
    simp_rw [lastMarg_eq_law_upto law K (W - 1) hstep k hk.le]
    exact hseam k hk
  · rw [seamterm_marginal (law 0) K hKn j]
    simp_rw [lastMarg_eq_law_upto law K (W - 1) hstep j j.isLt.le]
    exact hbonus

end Grid3.Three
