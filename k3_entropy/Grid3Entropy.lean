import Mathlib

/-!
# The entropy half, fully assembled (conditional on the certificate).

`entropy_bound_conditional`: given a Markov model `(α, K)` of a saturated `3×W` grid — kernels
normalized and nonnegative — together with the **certificate** (`log 12 ≤ H(root)` and
`log ρ ≤ seamterm k` for every seam) and the max-entropy/support fact `H(μ_{W-1}) ≤ log N`, the
count dominates the uniform count: `a (W-1) ≤ N`.  Everything here is proved sorry-free from the
path chain rule and the telescoping bridge; the only inputs left abstract are exactly the
computationally-verified finite certificate and the grid→measure modeling.
-/

open Real Finset

namespace Grid3.Three

/-! ### Finite chain rule -/

theorem chain_rule_two {σ τ : Type*} [Fintype σ] [Fintype τ] (X : σ → τ → ℝ)
    (hX : ∀ s t, 0 ≤ X s t) :
    ∑ s, ∑ t, Real.negMulLog (X s t)
      = ∑ s, Real.negMulLog (∑ t, X s t)
        + ∑ s, ∑ t, X s t * (- Real.log (X s t / (∑ t', X s t'))) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  set a := ∑ t', X s t' with ha
  by_cases hazero : a = 0
  · have hXz : ∀ t, X s t = 0 := by
      intro t
      have hle : X s t ≤ a := Finset.single_le_sum (fun t' _ => hX s t') (Finset.mem_univ t)
      have := hX s t; rw [hazero] at hle; linarith
    simp [hXz, hazero, Real.negMulLog_zero]
  · have hapos : 0 < a := lt_of_le_of_ne (Finset.sum_nonneg (fun t' _ => hX s t')) (Ne.symm hazero)
    have perT : ∀ t, X s t * (- Real.log (X s t / a))
        = Real.negMulLog (X s t) + X s t * Real.log a := by
      intro t
      by_cases hxt : X s t = 0
      · simp [hxt, Real.negMulLog_zero]
      · have hxpos : 0 < X s t := lt_of_le_of_ne (hX s t) (Ne.symm hxt)
        rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hapos), Real.negMulLog]; ring
    calc ∑ t, Real.negMulLog (X s t)
        = ∑ t, (X s t * (- Real.log (X s t / a)) - X s t * Real.log a) :=
          Finset.sum_congr rfl (fun t _ => by rw [perT t]; ring)
      _ = (∑ t, X s t * (- Real.log (X s t / a))) - (∑ t, X s t) * Real.log a := by
          rw [Finset.sum_sub_distrib, Finset.sum_mul]
      _ = Real.negMulLog a + ∑ t, X s t * (- Real.log (X s t / a)) := by
          rw [← ha, Real.negMulLog]; ring

/-! ### Baseline -/

def a : ℕ → ℤ
  | 0 => 12
  | 1 => 54
  | (n + 2) => 5 * a (n + 1) - 2 * a n

noncomputable def rho : ℝ := (5 + Real.sqrt 17) / 2
noncomputable def lam : ℝ := (5 - Real.sqrt 17) / 2
noncomputable def Acoef : ℝ := 6 + (24 / 17) * Real.sqrt 17
noncomputable def Bcoef : ℝ := 6 - (24 / 17) * Real.sqrt 17

lemma sqrt17_sq : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
lemma sqrt17_nonneg : 0 ≤ Real.sqrt 17 := Real.sqrt_nonneg 17
lemma sqrt17_lt_5 : Real.sqrt 17 < 5 := by nlinarith [sqrt17_sq, sqrt17_nonneg]
lemma rho_sq : rho ^ 2 = 5 * rho - 2 := by simp only [rho]; nlinarith [sqrt17_sq]
lemma lam_sq : lam ^ 2 = 5 * lam - 2 := by simp only [lam]; nlinarith [sqrt17_sq]
lemma lam_pos : 0 < lam := by simp only [lam]; nlinarith [sqrt17_lt_5]
lemma lam_le_rho : lam ≤ rho := by simp only [lam, rho]; nlinarith [sqrt17_nonneg]
lemma rho_pos : 0 < rho := lt_of_lt_of_le lam_pos lam_le_rho
lemma AB_sum : Acoef + Bcoef = 12 := by simp only [Acoef, Bcoef]; ring
lemma AB_rho_lam : Acoef * rho + Bcoef * lam = 54 := by
  simp only [Acoef, Bcoef, rho, lam]; nlinarith [sqrt17_sq]
lemma Bcoef_nonneg : 0 ≤ Bcoef := by simp only [Bcoef]; nlinarith [sqrt17_sq, sqrt17_nonneg]

theorem a_closed (n : ℕ) : (a n : ℝ) = Acoef * rho ^ n + Bcoef * lam ^ n := by
  suffices h : ∀ m, ((a m : ℝ) = Acoef * rho ^ m + Bcoef * lam ^ m) ∧
      ((a (m + 1) : ℝ) = Acoef * rho ^ (m + 1) + Bcoef * lam ^ (m + 1)) from (h n).1
  intro m
  induction m with
  | zero =>
      refine ⟨?_, ?_⟩
      · simp only [a, pow_zero, mul_one]; push_cast; linarith [AB_sum]
      · simp only [zero_add, a, pow_one]; push_cast; linarith [AB_rho_lam]
  | succ k ih =>
      obtain ⟨h0, h1⟩ := ih
      refine ⟨h1, ?_⟩
      have hd : a (k + 1 + 1) = 5 * a (k + 1) - 2 * a k := rfl
      rw [hd]; push_cast
      rw [h0, h1, pow_succ rho (k + 1), pow_succ rho k, pow_succ lam (k + 1), pow_succ lam k]
      linear_combination (-(Acoef * rho ^ k)) * rho_sq + (-(Bcoef * lam ^ k)) * lam_sq

theorem a_le (n : ℕ) : (a n : ℝ) ≤ 12 * rho ^ n := by
  rw [a_closed]
  have h0 : (0 : ℝ) ≤ lam := lam_pos.le
  have hlr : lam ^ n ≤ rho ^ n := by gcongr; exact lam_le_rho
  calc Acoef * rho ^ n + Bcoef * lam ^ n
      ≤ Acoef * rho ^ n + Bcoef * rho ^ n := by
        have := mul_le_mul_of_nonneg_left hlr Bcoef_nonneg; linarith
    _ = (Acoef + Bcoef) * rho ^ n := by ring
    _ = 12 * rho ^ n := by rw [AB_sum]

/-! ### Telescoping bridges -/

theorem entropy_assembly (W : ℕ) (ρ Nr Hroot : ℝ) (Hseam : Fin (W - 1) → ℝ)
    (hρ : 0 < ρ) (hNpos : 0 < Nr)
    (hchain : Hroot + ∑ i, Hseam i ≤ Real.log Nr)
    (hroot : Real.log 12 ≤ Hroot) (hseam : ∀ i, Real.log ρ ≤ Hseam i) :
    12 * ρ ^ (W - 1) ≤ Nr := by
  have h2 : ∑ _i : Fin (W - 1), Real.log ρ ≤ ∑ i, Hseam i := Finset.sum_le_sum (fun i _ => hseam i)
  have h3 : ∑ _i : Fin (W - 1), Real.log ρ = (↑(W - 1) : ℝ) * Real.log ρ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have key : Real.log 12 + (↑(W - 1) : ℝ) * Real.log ρ ≤ Real.log Nr :=
    calc Real.log 12 + (↑(W - 1) : ℝ) * Real.log ρ
        = Real.log 12 + ∑ _i : Fin (W - 1), Real.log ρ := by rw [h3]
      _ ≤ Hroot + ∑ i, Hseam i := add_le_add hroot h2
      _ ≤ Real.log Nr := hchain
  have hlog : Real.log (12 * ρ ^ (W - 1)) = Real.log 12 + (↑(W - 1) : ℝ) * Real.log ρ := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have hA : (0 : ℝ) < 12 * ρ ^ (W - 1) := by positivity
  calc 12 * ρ ^ (W - 1) = Real.exp (Real.log (12 * ρ ^ (W - 1))) := (Real.exp_log hA).symm
    _ ≤ Real.exp (Real.log Nr) := Real.exp_le_exp.mpr (by rw [hlog]; exact key)
    _ = Nr := Real.exp_log hNpos

/-- A single seam may repay an endpoint entropy deficit.  This is the form needed when the first
column has the uniform Parry law: the root is short by `δ`, while the first seam entering a
nonuniform column has a matching `δ` bonus. -/
theorem entropy_assembly_one_bonus (W : ℕ) (ρ Nr Hroot : ℝ)
    (Hseam : Fin (W - 1) → ℝ) (j : Fin (W - 1)) (δ : ℝ)
    (hρ : 0 < ρ) (hNpos : 0 < Nr)
    (hchain : Hroot + ∑ i, Hseam i ≤ Real.log Nr)
    (hroot : Real.log 12 - δ ≤ Hroot)
    (hseam : ∀ i, Real.log ρ ≤ Hseam i)
    (hbonus : Real.log ρ + δ ≤ Hseam j) :
    12 * ρ ^ (W - 1) ≤ Nr := by
  have hrest : ∑ i ∈ (Finset.univ.erase j), Real.log ρ ≤
      ∑ i ∈ (Finset.univ.erase j), Hseam i :=
    Finset.sum_le_sum fun i _ => hseam i
  have hsum_decomp : ∑ i, Hseam i = Hseam j + ∑ i ∈ (Finset.univ.erase j), Hseam i := by
    rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  have hconst_decomp : (↑(W - 1) : ℝ) * Real.log ρ =
      Real.log ρ + ∑ _i ∈ (Finset.univ.erase j), Real.log ρ := by
    have hfull : ∑ _i : Fin (W - 1), Real.log ρ =
        (↑(W - 1) : ℝ) * Real.log ρ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← hfull, add_comm]
    exact (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm
  have key : Real.log 12 + (↑(W - 1) : ℝ) * Real.log ρ ≤ Real.log Nr := by
    calc
      Real.log 12 + (↑(W - 1) : ℝ) * Real.log ρ =
          (Real.log 12 - δ) + (Real.log ρ + δ) +
            ∑ i ∈ (Finset.univ.erase j), Real.log ρ := by rw [hconst_decomp]; ring
      _ ≤ Hroot + Hseam j + ∑ i ∈ (Finset.univ.erase j), Hseam i :=
        add_le_add (add_le_add hroot hbonus) hrest
      _ = Hroot + ∑ i, Hseam i := by rw [hsum_decomp]; ring
      _ ≤ Real.log Nr := hchain
  have hlog : Real.log (12 * ρ ^ (W - 1)) =
      Real.log 12 + (↑(W - 1) : ℝ) * Real.log ρ := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have hA : (0 : ℝ) < 12 * ρ ^ (W - 1) := by positivity
  calc
    12 * ρ ^ (W - 1) = Real.exp (Real.log (12 * ρ ^ (W - 1))) := (Real.exp_log hA).symm
    _ ≤ Real.exp (Real.log Nr) := Real.exp_le_exp.mpr (by rw [hlog]; exact key)
    _ = Nr := Real.exp_log hNpos

theorem entropy_bound_from_inputs (W : ℕ) (Nr : ℝ) (Hroot : ℝ) (Hseam : Fin (W - 1) → ℝ)
    (hNpos : 0 < Nr)
    (hchain : Hroot + ∑ i, Hseam i ≤ Real.log Nr)
    (hroot : Real.log 12 ≤ Hroot) (hseam : ∀ i, Real.log rho ≤ Hseam i) :
    (a (W - 1) : ℝ) ≤ Nr :=
  calc (a (W - 1) : ℝ) ≤ 12 * rho ^ (W - 1) := a_le (W - 1)
    _ ≤ Nr := entropy_assembly W rho Nr Hroot Hseam rho_pos hNpos hchain hroot hseam

theorem entropy_bound_from_inputs_one_bonus (W : ℕ) (Nr : ℝ) (Hroot : ℝ)
    (Hseam : Fin (W - 1) → ℝ) (j : Fin (W - 1)) (δ : ℝ)
    (hNpos : 0 < Nr)
    (hchain : Hroot + ∑ i, Hseam i ≤ Real.log Nr)
    (hroot : Real.log 12 - δ ≤ Hroot)
    (hseam : ∀ i, Real.log rho ≤ Hseam i)
    (hbonus : Real.log rho + δ ≤ Hseam j) :
    (a (W - 1) : ℝ) ≤ Nr :=
  calc
    (a (W - 1) : ℝ) ≤ 12 * rho ^ (W - 1) := a_le (W - 1)
    _ ≤ Nr := entropy_assembly_one_bonus W rho Nr Hroot Hseam j δ rho_pos hNpos hchain
      hroot hseam hbonus

/-! ### The path Markov measure and its chain rule -/

variable {S : Type*} [Fintype S]

def PState (S : Type*) : ℕ → Type _
  | 0 => S
  | (k + 1) => PState S k × S

instance fPState (S : Type*) [Fintype S] : ∀ k, Fintype (PState S k)
  | 0 => (inferInstance : Fintype S)
  | (k + 1) => by haveI := fPState S k; exact inferInstanceAs (Fintype (PState S k × S))

def lastCol (S : Type*) : ∀ k, PState S k → S
  | 0, s => s
  | (_ + 1), p => p.2

noncomputable def mu (alpha : S → ℝ) (K : ℕ → S → S → ℝ) : ∀ k, PState S k → ℝ
  | 0, s => alpha s
  | (k + 1), p => mu alpha K k p.1 * K k (lastCol S k p.1) p.2

noncomputable def Hsum {α : Type*} [Fintype α] (m : α → ℝ) : ℝ := ∑ x, Real.negMulLog (m x)

lemma mu_nonneg (alpha : S → ℝ) (K : ℕ → S → S → ℝ)
    (hα : ∀ s, 0 ≤ alpha s) (hK : ∀ k c s, 0 ≤ K k c s) :
    ∀ k x, 0 ≤ mu alpha K k x := by
  intro k
  induction k with
  | zero => intro x; exact hα x
  | succ k ih => intro p; exact mul_nonneg (ih p.1) (hK k _ p.2)

noncomputable def seamterm (alpha : S → ℝ) (K : ℕ → S → S → ℝ) (k : ℕ) : ℝ :=
  ∑ p : PState S k, ∑ s : S,
    mu alpha K (k + 1) (p, s) *
      (- Real.log (mu alpha K (k + 1) (p, s) / (∑ s', mu alpha K (k + 1) (p, s'))))

lemma chain_step (alpha : S → ℝ) (K : ℕ → S → S → ℝ)
    (hα : ∀ s, 0 ≤ alpha s) (hK : ∀ k c s, 0 ≤ K k c s)
    (hKnorm : ∀ k c, ∑ s, K k c s = 1) (k : ℕ) :
    Hsum (mu alpha K (k + 1)) = Hsum (mu alpha K k) + seamterm alpha K k := by
  have hXnn : ∀ (p : PState S k) (s : S), 0 ≤ mu alpha K (k + 1) (p, s) :=
    fun p s => mu_nonneg alpha K hα hK (k + 1) (p, s)
  have hct := chain_rule_two (σ := PState S k) (τ := S)
    (fun p s => mu alpha K (k + 1) (p, s)) hXnn
  have hLHS : Hsum (mu alpha K (k + 1))
      = ∑ p : PState S k, ∑ s : S, Real.negMulLog (mu alpha K (k + 1) (p, s)) := by
    rw [Hsum]
    exact Fintype.sum_prod_type (fun x : PState S k × S => Real.negMulLog (mu alpha K (k + 1) x))
  have hmarg : ∀ p : PState S k, (∑ s : S, mu alpha K (k + 1) (p, s)) = mu alpha K k p := by
    intro p
    have : ∀ s, mu alpha K (k + 1) (p, s) = mu alpha K k p * K k (lastCol S k p) s := fun s => rfl
    simp_rw [this, ← Finset.mul_sum, hKnorm, mul_one]
  rw [hLHS, hct]
  congr 1
  · rw [Hsum]
    exact Finset.sum_congr rfl (fun p _ => by rw [hmarg p])

theorem path_chain_rule (alpha : S → ℝ) (K : ℕ → S → S → ℝ)
    (hα : ∀ s, 0 ≤ alpha s) (hK : ∀ k c s, 0 ≤ K k c s)
    (hKnorm : ∀ k c, ∑ s, K k c s = 1) (W : ℕ) :
    Hsum (mu alpha K W) = Hsum (mu alpha K 0) + ∑ k ∈ Finset.range W, seamterm alpha K k := by
  induction W with
  | zero => simp
  | succ W ih =>
      rw [chain_step alpha K hα hK hKnorm W, ih, Finset.sum_range_succ]
      ring

/-! ### The assembled conditional entropy bound -/

/-- **Entropy half, assembled.**  For a normalized nonnegative Markov model `(α, K)` of the
    saturated `3×W` grid whose measure has `H(μ_{W-1}) ≤ log N`, if the certificate holds
    (`log 12 ≤ H(root)` and `log ρ ≤ seamterm k` for each seam `k < W-1`), then `a (W-1) ≤ N`. -/
theorem entropy_bound_conditional (W : ℕ)
    (alpha : S → ℝ) (K : ℕ → S → S → ℝ) (Nr : ℝ)
    (hα : ∀ s, 0 ≤ alpha s) (hK : ∀ k c s, 0 ≤ K k c s) (hKnorm : ∀ k c, ∑ s, K k c s = 1)
    (hNpos : 0 < Nr)
    (hsupp : Hsum (mu alpha K (W - 1)) ≤ Real.log Nr)
    (hroot : Real.log 12 ≤ Hsum (mu alpha K 0))
    (hseam : ∀ k, k < W - 1 → Real.log rho ≤ seamterm alpha K k) :
    (a (W - 1) : ℝ) ≤ Nr := by
  have hpc := path_chain_rule alpha K hα hK hKnorm (W - 1)
  set Hseam : Fin (W - 1) → ℝ := fun i => seamterm alpha K i.val with hHseam
  have hsum_eq : ∑ i, Hseam i = ∑ k ∈ Finset.range (W - 1), seamterm alpha K k := by
    rw [hHseam]; exact Fin.sum_univ_eq_sum_range (fun k => seamterm alpha K k) (W - 1)
  have hchain : Hsum (mu alpha K 0) + ∑ i, Hseam i ≤ Real.log Nr := by
    rw [hsum_eq, ← hpc]; exact hsupp
  have hseam' : ∀ i : Fin (W - 1), Real.log rho ≤ Hseam i := by
    intro i; rw [hHseam]; exact hseam i.val i.isLt
  exact entropy_bound_from_inputs W Nr (Hsum (mu alpha K 0)) Hseam hNpos hchain hroot hseam'

/-- The conditional entropy bound with one distinguished seam paying for a root deficit `δ`. -/
theorem entropy_bound_conditional_one_bonus (W : ℕ)
    (alpha : S → ℝ) (K : ℕ → S → S → ℝ) (Nr : ℝ)
    (j : Fin (W - 1)) (δ : ℝ)
    (hα : ∀ s, 0 ≤ alpha s) (hK : ∀ k c s, 0 ≤ K k c s)
    (hKnorm : ∀ k c, ∑ s, K k c s = 1)
    (hNpos : 0 < Nr)
    (hsupp : Hsum (mu alpha K (W - 1)) ≤ Real.log Nr)
    (hroot : Real.log 12 - δ ≤ Hsum (mu alpha K 0))
    (hseam : ∀ k, k < W - 1 → Real.log rho ≤ seamterm alpha K k)
    (hbonus : Real.log rho + δ ≤ seamterm alpha K j.val) :
    (a (W - 1) : ℝ) ≤ Nr := by
  have hpc := path_chain_rule alpha K hα hK hKnorm (W - 1)
  set Hseam : Fin (W - 1) → ℝ := fun i => seamterm alpha K i.val with hHseam
  have hsum_eq : ∑ i, Hseam i = ∑ k ∈ Finset.range (W - 1), seamterm alpha K k := by
    rw [hHseam]; exact Fin.sum_univ_eq_sum_range (fun k => seamterm alpha K k) (W - 1)
  have hchain : Hsum (mu alpha K 0) + ∑ i, Hseam i ≤ Real.log Nr := by
    rw [hsum_eq, ← hpc]; exact hsupp
  have hseam' : ∀ i : Fin (W - 1), Real.log rho ≤ Hseam i := by
    intro i; rw [hHseam]; exact hseam i.val i.isLt
  have hbonus' : Real.log rho + δ ≤ Hseam j := by simpa [hHseam] using hbonus
  exact entropy_bound_from_inputs_one_bonus W Nr (Hsum (mu alpha K 0)) Hseam j δ hNpos
    hchain hroot hseam' hbonus'


/-! ### Entropy inequalities (from Entropy.lean) -/
variable {ιE : Type*} [Fintype ιE]
theorem jensen_neg_log {J : Type*} [Fintype J] (w : J → ℝ) (hw0 : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j = 1) (y : J → ℝ) (hy : ∀ j, 0 < w j → 0 < y j) :
    - Real.log (∑ j, w j * y j) ≤ ∑ j, w j * (- Real.log (y j)) := by
  classical
  set S : Finset J := Finset.univ.filter (fun j => 0 < w j) with hS
  have hmemS : ∀ j, j ∈ S ↔ 0 < w j := by intro j; simp [hS]
  have hz : ∀ j, j ∉ S → w j = 0 := fun j hj =>
    le_antisymm (not_lt.mp (fun h => hj ((hmemS j).mpr h))) (hw0 j)
  have e_wy : ∑ j, w j * y j = ∑ j ∈ S, w j * y j :=
    (Finset.sum_subset (Finset.filter_subset _ _) (fun j _ hj => by rw [hz j hj]; ring)).symm
  have e_wl : ∑ j, w j * (- Real.log (y j)) = ∑ j ∈ S, w j * (- Real.log (y j)) :=
    (Finset.sum_subset (Finset.filter_subset _ _) (fun j _ hj => by rw [hz j hj]; ring)).symm
  rw [e_wy, e_wl]
  have hconv : ConvexOn ℝ (Set.Ioi 0) (fun x => - Real.log x) :=
    (strictConcaveOn_log_Ioi.concaveOn).neg
  have hw0S : ∀ j ∈ S, 0 ≤ w j := fun j hj => ((hmemS j).mp hj).le
  have hw1S : ∑ j ∈ S, w j = 1 := by
    rw [← hw1]; exact Finset.sum_subset (Finset.filter_subset _ _) (fun j _ hj => hz j hj)
  have hyS : ∀ j ∈ S, y j ∈ Set.Ioi 0 := fun j hj => hy j ((hmemS j).mp hj)
  have jensen := hconv.map_sum_le hw0S hw1S hyS
  simpa only [smul_eq_mul] using jensen

variable {ι : Type*} [Fintype ι]

/-- Finite Shannon entropy. -/
noncomputable def H (p : ι → ℝ) : ℝ := ∑ i, Real.negMulLog (p i)

/-- **Collision bound:** `H p ≥ -log (∑ p²)`. -/
theorem H_ge_neg_log_collision (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    - Real.log (∑ i, (p i) ^ 2) ≤ H p := by
  have key := jensen_neg_log p hp hsum p (fun i h => h)
  have e1 : ∑ i, p i * p i = ∑ i, (p i) ^ 2 := Finset.sum_congr rfl (fun i _ => by ring)
  have e2 : ∑ i, p i * (- Real.log (p i)) = H p := by
    rw [H]; exact Finset.sum_congr rfl (fun i _ => by rw [Real.negMulLog]; ring)
  rw [e1, e2] at key; exact key

/-- **Lemma A (root entropy):** `∑ p² ≤ 1/12 ⇒ H p ≥ log 12`. -/
theorem H_ge_log12 (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hcol : ∑ i, (p i) ^ 2 ≤ 1 / 12) : Real.log 12 ≤ H p := by
  have hex : ∃ i, p i ≠ 0 := by
    by_contra h
    push_neg at h
    rw [Finset.sum_eq_zero (fun i _ => h i)] at hsum
    norm_num at hsum
  have hpos : 0 < ∑ i, (p i) ^ 2 := by
    obtain ⟨i, hi⟩ := hex
    exact Finset.sum_pos' (fun j _ => sq_nonneg (p j)) ⟨i, Finset.mem_univ i, by positivity⟩
  calc Real.log 12 = - Real.log (1 / 12) := by rw [Real.log_div (by norm_num) (by norm_num)]; simp
    _ ≤ - Real.log (∑ i, (p i) ^ 2) := by exact neg_le_neg (Real.log_le_log hpos hcol)
    _ ≤ H p := H_ge_neg_log_collision p hp hsum

/-- The endpoint form for the uniform Parry law.  Collision at most `3/34` gives entropy at
least `log (34/3) = log 12 - log (18/17)`; the missing factor is exactly what one strong entering
seam supplies. -/
theorem H_ge_log34_div3 (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hcol : ∑ i, (p i) ^ 2 ≤ 3 / 34) :
    Real.log 12 - Real.log ((18 : ℝ) / 17) ≤ H p := by
  have hex : ∃ i, p i ≠ 0 := by
    by_contra h
    push Not at h
    rw [Finset.sum_eq_zero (fun i _ => h i)] at hsum
    norm_num at hsum
  have hpos : 0 < ∑ i, (p i) ^ 2 := by
    obtain ⟨i, hi⟩ := hex
    exact Finset.sum_pos' (fun q _ => sq_nonneg (p q)) ⟨i, Finset.mem_univ i, by positivity⟩
  have hid : Real.log 12 - Real.log ((18 : ℝ) / 17) = -Real.log ((3 : ℝ) / 34) := by
    rw [← Real.log_div (by norm_num : (12 : ℝ) ≠ 0) (by norm_num : (18 : ℝ) / 17 ≠ 0),
      show (12 : ℝ) / ((18 : ℝ) / 17) = 1 / ((3 : ℝ) / 34) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  rw [hid]
  exact le_trans (neg_le_neg (Real.log_le_log hpos hcol))
    (H_ge_neg_log_collision p hp hsum)

/-- **Lemma B core (seam bound):** for a coupling `X` with per-pair left-marginal `α`,
    `H(T|S) = ∑ X·(-log (X/α)) ≥ -4 log (∑ X·(X/α)^{1/4}) = -4 log R(X)`. -/
theorem seam_bound {J : Type*} [Fintype J] (X α : J → ℝ)
    (hX : ∀ j, 0 ≤ X j) (hsum : ∑ j, X j = 1) (hα : ∀ j, 0 < X j → 0 < α j) :
    - 4 * Real.log (∑ j, X j * (X j / α j) ^ ((1 : ℝ) / 4))
      ≤ ∑ j, X j * (- Real.log (X j / α j)) := by
  have key := jensen_neg_log X hX hsum (fun j => (X j / α j) ^ ((1 : ℝ) / 4))
    (fun j h => Real.rpow_pos_of_pos (div_pos h (hα j h)) _)
  have hmul : (4 : ℝ) * (- Real.log (∑ j, X j * (X j / α j) ^ ((1 : ℝ) / 4)))
      ≤ 4 * ∑ j, X j * (- Real.log ((X j / α j) ^ ((1 : ℝ) / 4))) :=
    mul_le_mul_of_nonneg_left key (by norm_num)
  have per : ∀ j, 4 * (X j * (- Real.log ((X j / α j) ^ ((1 : ℝ) / 4))))
      = X j * (- Real.log (X j / α j)) := by
    intro j
    by_cases h : 0 < X j
    · rw [Real.log_rpow (div_pos h (hα j h))]; ring
    · rw [le_antisymm (not_lt.mp h) (hX j)]; ring
  calc - 4 * Real.log (∑ j, X j * (X j / α j) ^ ((1 : ℝ) / 4))
      = 4 * (- Real.log (∑ j, X j * (X j / α j) ^ ((1 : ℝ) / 4))) := by ring
    _ ≤ 4 * ∑ j, X j * (- Real.log ((X j / α j) ^ ((1 : ℝ) / 4))) := hmul
    _ = ∑ j, 4 * (X j * (- Real.log ((X j / α j) ^ ((1 : ℝ) / 4)))) := by rw [Finset.mul_sum]
    _ = ∑ j, X j * (- Real.log (X j / α j)) := Finset.sum_congr rfl (fun j _ => per j)

/-- **Conditional-collision seam bound.**  This is the order-two analogue of `seam_bound`:
`H(T|S) ≥ -log (∑ X(s,t)²/α(s))`.  Unlike the fourth-root bound, its certificate contains only
one quadratic rational expression, so it is substantially cheaper for the kernel to check. -/
theorem seam_collision_bound {J : Type*} [Fintype J] (X α : J → ℝ)
    (hX : ∀ j, 0 ≤ X j) (hsum : ∑ j, X j = 1) (hα : ∀ j, 0 < X j → 0 < α j) :
    -Real.log (∑ j, X j * (X j / α j)) ≤
      ∑ j, X j * (-Real.log (X j / α j)) :=
  jensen_neg_log X hX hsum (fun j => X j / α j) (fun j hj => div_pos hj (hα j hj))

/-- A positive conditional-collision mass below `ρ⁻¹` supplies `log ρ` conditional entropy. -/
theorem collision_to_log (H C ρ : ℝ) (hρ : 0 < ρ) (hC : 0 < C)
    (hbound : -Real.log C ≤ H) (hcert : C * ρ < 1) : Real.log ρ ≤ H := by
  have hCle : C ≤ 1 / ρ := (le_div_iff₀ hρ).2 (le_of_lt hcert)
  have hlog := Real.log_le_log hC hCle
  have hloginv : Real.log (1 / ρ) = -Real.log ρ := by
    rw [one_div, Real.log_inv]
  rw [hloginv] at hlog
  linarith

/-! ### Max-entropy bound (from Entropy.lean) -/
theorem H_le_log_card (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    H p ≤ Real.log ((Finset.univ.filter (fun i => 0 < p i)).card : ℝ) := by
  have key := jensen_neg_log p hp hsum (fun i => (p i)⁻¹) (fun i h => by positivity)
  have hcard : ∑ i, p i * (p i)⁻¹ = ((Finset.univ.filter (fun i => 0 < p i)).card : ℝ) := by
    have per : ∀ i, p i * (p i)⁻¹ = if 0 < p i then (1 : ℝ) else 0 := by
      intro i
      by_cases h : 0 < p i
      · rw [if_pos h, mul_inv_cancel₀ (ne_of_gt h)]
      · rw [if_neg h, le_antisymm (not_lt.mp h) (hp i)]; simp
    rw [Finset.sum_congr rfl (fun i _ => per i), Finset.sum_boole]
  have e_rhs : H p = - ∑ i, p i * (- Real.log ((p i)⁻¹)) := by
    rw [H, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [Real.log_inv, Real.negMulLog]; ring)
  rw [hcard] at key
  rw [e_rhs]; linarith


/-! ### seam_to_logrho (from EntropyBound.lean) -/
/-- **Seam ⇒ `hseam`.** The certificate bound `R(X) ≤ ρ^(-1/4)` turns `seam_bound`'s output
    `-4·log R ≤ H(T|S)` into the per-seam hypothesis `log ρ ≤ H(T|S)`. -/
theorem seam_to_logrho (H R ρ : ℝ) (hρ : 0 < ρ) (hR : 0 < R)
    (hbound : -4 * Real.log R ≤ H)
    (hcert : R ≤ ρ ^ (-(1 : ℝ) / 4)) :
    Real.log ρ ≤ H := by
  have hle : Real.log R ≤ (-(1 : ℝ) / 4) * Real.log ρ := by
    have := Real.log_le_log hR hcert
    rwa [Real.log_rpow hρ] at this
  linarith

/-! ### Analytic bridge, relaxed to `0 ≤ α` -/
theorem entry_bound (X α r : ℝ) (hX : 0 ≤ X) (ha : 0 ≤ α) (hr : 0 ≤ r)
    (h : X ≤ r ^ 4 * α) : X * (X / α) ^ ((1 : ℝ) / 4) ≤ X * r := by
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · have hX0 : X = 0 := by rw [← ha0, mul_zero] at h; linarith
    rw [hX0]; simp
  · have hxa : X / α ≤ r ^ 4 := by rw [div_le_iff₀ hapos]; linarith
    have hxa0 : 0 ≤ X / α := div_nonneg hX hapos.le
    have hmono : (X / α) ^ ((1 : ℝ) / 4) ≤ (r ^ 4 : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow hxa0 hxa (by norm_num)
    have hr4 : ((r ^ 4 : ℝ)) ^ ((1 : ℝ) / 4) = r := by
      rw [← Real.rpow_natCast r 4, ← Real.rpow_mul hr]; norm_num
    rw [hr4] at hmono
    exact mul_le_mul_of_nonneg_left hmono hX

theorem R_le_Rplus {J : Type*} [Fintype J] (X α r : J → ℝ)
    (hX : ∀ j, 0 ≤ X j) (ha : ∀ j, 0 ≤ α j) (hr : ∀ j, 0 ≤ r j)
    (h : ∀ j, X j ≤ (r j) ^ 4 * α j) :
    ∑ j, X j * (X j / α j) ^ ((1 : ℝ) / 4) ≤ ∑ j, X j * r j :=
  Finset.sum_le_sum (fun j _ => entry_bound (X j) (α j) (r j) (hX j) (ha j) (hr j) (h j))

theorem Rplus_le (Rp ρ : ℝ) (hRp : 0 ≤ Rp) (hρ : 0 < ρ) (h : Rp ^ 4 * ρ < 1) :
    Rp ≤ ρ ^ (-(1 : ℝ) / 4) := by
  have h4 : Rp ^ 4 ≤ ρ ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg_one, inv_eq_one_div, le_div_iff₀ hρ]; linarith
  have hmono : (Rp ^ 4 : ℝ) ^ ((1 : ℝ) / 4) ≤ (ρ ^ (-(1 : ℝ))) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (by positivity) h4 (by norm_num)
  have hL : ((Rp ^ 4 : ℝ)) ^ ((1 : ℝ) / 4) = Rp := by
    rw [← Real.rpow_natCast Rp 4, ← Real.rpow_mul hRp]; norm_num
  have hR : ((ρ ^ (-(1 : ℝ))) : ℝ) ^ ((1 : ℝ) / 4) = ρ ^ (-(1 : ℝ) / 4) := by
    rw [← Real.rpow_mul hρ.le]; norm_num
  rw [hL, hR] at hmono; exact hmono

theorem R_bound {J : Type*} [Fintype J] (X α r : J → ℝ) (ρ : ℝ)
    (hX : ∀ j, 0 ≤ X j) (ha : ∀ j, 0 ≤ α j) (hr : ∀ j, 0 ≤ r j)
    (hentry : ∀ j, X j ≤ (r j) ^ 4 * α j) (hρ : 0 < ρ)
    (hRp : (∑ j, X j * r j) ^ 4 * ρ < 1) :
    ∑ j, X j * (X j / α j) ^ ((1 : ℝ) / 4) ≤ ρ ^ (-(1 : ℝ) / 4) := by
  have h1 := R_le_Rplus X α r hX ha hr hentry
  have hRpnn : 0 ≤ ∑ j, X j * r j := Finset.sum_nonneg (fun j _ => mul_nonneg (hX j) (hr j))
  exact le_trans h1 (Rplus_le _ ρ hRpnn hρ hRp)

/-! ### seamterm grouping + marginal recurrence (from PathChain.lean) -/
/-- Kernel row entropy `h(K c ·) = ∑_s K c s · (-log (K c s))`. -/
noncomputable def rowH (Kf : S → S → ℝ) (c : S) : ℝ := ∑ s, Kf c s * (- Real.log (Kf c s))

/-- The last-column marginal of `μ_k`. -/
noncomputable def lastMarg [DecidableEq S] (alpha : S → ℝ) (K : ℕ → S → S → ℝ) (k : ℕ) (c : S) : ℝ :=
  ∑ p : PState S k, if lastCol S k p = c then mu alpha K k p else 0

/-- **seamterm grouping.** `seamterm = ∑_c ν_k(c)·rowH(K_k)(c)` — the marginal-weighted sum of
    kernel-row entropies, the form `seam_bound` (Lemma B) bounds. -/
theorem seamterm_marginal [DecidableEq S] (alpha : S → ℝ) (K : ℕ → S → S → ℝ)
    (hKnorm : ∀ k c, ∑ s, K k c s = 1) (k : ℕ) :
    seamterm alpha K k = ∑ c, lastMarg alpha K k c * rowH (K k) c := by
  have step1 : ∀ (p : PState S k) (s : S),
      mu alpha K (k + 1) (p, s) *
        (- Real.log (mu alpha K (k + 1) (p, s) / (∑ s', mu alpha K (k + 1) (p, s'))))
      = mu alpha K k p * (K k (lastCol S k p) s * (- Real.log (K k (lastCol S k p) s))) := by
    intro p s
    have hmuval : ∀ s', mu alpha K (k + 1) (p, s') = mu alpha K k p * K k (lastCol S k p) s' :=
      fun s' => rfl
    have hmarg : (∑ s', mu alpha K (k + 1) (p, s')) = mu alpha K k p := by
      simp_rw [hmuval]; rw [← Finset.mul_sum, hKnorm, mul_one]
    rw [hmarg, hmuval s]
    by_cases hp : mu alpha K k p = 0
    · rw [hp]; ring
    · have hc : mu alpha K k p * K k (lastCol S k p) s / mu alpha K k p
          = K k (lastCol S k p) s := by
        rw [mul_comm (mu alpha K k p) (K k (lastCol S k p) s), mul_div_assoc, div_self hp, mul_one]
      rw [hc]; ring
  have step2 : seamterm alpha K k
      = ∑ p : PState S k, mu alpha K k p * rowH (K k) (lastCol S k p) := by
    rw [seamterm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_congr rfl (fun s _ => step1 p s), rowH, Finset.mul_sum]
  rw [step2,
    ← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset S)) (g := lastCol S k)
      (fun p _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_filter, lastMarg, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h : lastCol S k p = c
  · rw [if_pos h, if_pos h, h]
  · rw [if_neg h, if_neg h, zero_mul]

/-- **Root marginal.** `lastMarg 0 = α`. -/
theorem lastMarg_zero [DecidableEq S] (alpha : S → ℝ) (K : ℕ → S → S → ℝ) (c : S) :
    lastMarg alpha K 0 c = alpha c := by
  rw [lastMarg]
  show (∑ p : S, if p = c then alpha p else 0) = alpha c
  rw [Finset.sum_ite_eq']; simp

/-- **Marginal recurrence.** `ν_{k+1}(s) = ∑_c ν_k(c)·K_k(c,s)` (one Markov step). -/
theorem lastMarg_succ [DecidableEq S] (alpha : S → ℝ) (K : ℕ → S → S → ℝ) (k : ℕ) (s : S) :
    lastMarg alpha K (k + 1) s = ∑ c, lastMarg alpha K k c * K k c s := by
  have h1 : lastMarg alpha K (k + 1) s
      = ∑ p : PState S k, mu alpha K k p * K k (lastCol S k p) s := by
    rw [lastMarg]
    show (∑ q : PState S k × S, if lastCol S (k + 1) q = s then mu alpha K (k + 1) q else 0)
        = ∑ p : PState S k, mu alpha K k p * K k (lastCol S k p) s
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    show (∑ c' : S, if c' = s then mu alpha K k p * K k (lastCol S k p) c' else 0)
      = mu alpha K k p * K k (lastCol S k p) s
    rw [Finset.sum_ite_eq']; simp
  rw [h1,
    ← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset S)) (g := lastCol S k)
      (fun p _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_filter, lastMarg, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h : lastCol S k p = c
  · rw [if_pos h, if_pos h, h]
  · rw [if_neg h, if_neg h, zero_mul]

/-! ### Marginal consistency, normalization, and the hseam engine -/

theorem lastMarg_eq_law [DecidableEq S] (alpha : S → ℝ) (K : ℕ → S → S → ℝ) (law : ℕ → S → ℝ)
    (h0 : ∀ c, alpha c = law 0 c)
    (hstep : ∀ k s, (∑ c, law k c * K k c s) = law (k + 1) s) :
    ∀ k c, lastMarg alpha K k c = law k c := by
  intro k
  induction k with
  | zero => intro c; rw [lastMarg_zero]; exact h0 c
  | succ k ih =>
      intro s
      rw [lastMarg_succ,
        show (∑ c, lastMarg alpha K k c * K k c s) = ∑ c, law k c * K k c s from
          Finset.sum_congr rfl (fun c _ => by rw [ih c])]
      exact hstep k s

theorem mu_sum_one (alpha : S → ℝ) (K : ℕ → S → S → ℝ)
    (hα : ∑ s, alpha s = 1) (hKnorm : ∀ k c, ∑ s, K k c s = 1) :
    ∀ k, ∑ p : PState S k, mu alpha K k p = 1 := by
  intro k
  induction k with
  | zero => exact hα
  | succ k ih =>
      show (∑ q : PState S k × S, mu alpha K k q.1 * K k (lastCol S k q.1) q.2) = 1
      rw [Fintype.sum_prod_type]
      have hmarg : ∀ p : PState S k,
          (∑ s, mu alpha K k p * K k (lastCol S k p) s) = mu alpha K k p := by
        intro p; rw [← Finset.mul_sum, hKnorm, mul_one]
      rw [Finset.sum_congr rfl (fun p _ => hmarg p)]; exact ih

/-- **Per-seam entropy bound at an arbitrary positive factor.** Certificate (fourth-root witness
    `r`, `R₊⁴ρ<1`) plus marginal consistency implies `log ρ ≤ seamterm`. -/
theorem seamterm_ge_log [DecidableEq S] (ρ : ℝ) (hρ : 0 < ρ)
    (alpha : S → ℝ) (K : ℕ → S → S → ℝ)
    (hK0 : ∀ k c s, 0 ≤ K k c s) (hKnorm : ∀ k c, ∑ s, K k c s = 1)
    (k : ℕ) (αk : S → ℝ) (hαk0 : ∀ c, 0 ≤ αk c) (hαksum : ∑ c, αk c = 1)
    (hcons : ∀ c, lastMarg alpha K k c = αk c)
    (r : S → S → ℝ) (hr0 : ∀ c s, 0 ≤ r c s)
    (hentry : ∀ c s, αk c * K k c s ≤ (r c s) ^ 4 * αk c)
    (hRp : (∑ c, ∑ s, αk c * K k c s * r c s) ^ 4 * ρ < 1) :
    Real.log ρ ≤ seamterm alpha K k := by
  classical
  set X : S × S → ℝ := fun j => αk j.1 * K k j.1 j.2 with hXdef
  set αJ : S × S → ℝ := fun j => αk j.1 with hαJdef
  set rr : S × S → ℝ := fun j => r j.1 j.2 with hrrdef
  have hX0 : ∀ j, 0 ≤ X j := fun j => mul_nonneg (hαk0 j.1) (hK0 k j.1 j.2)
  have hαpos : ∀ j, 0 < X j → 0 < αJ j := by
    intro j hj
    rcases eq_or_lt_of_le (hαk0 j.1) with h0 | hpos
    · simp only [hXdef, ← h0, zero_mul] at hj; exact absurd hj (lt_irrefl 0)
    · exact hpos
  have hXsum : ∑ j, X j = 1 := by
    rw [Fintype.sum_prod_type]
    have hc : ∀ c, ∑ s, X (c, s) = αk c := by
      intro c; simp only [hXdef]; rw [← Finset.mul_sum, hKnorm, mul_one]
    rw [Finset.sum_congr rfl (fun c _ => hc c)]; exact hαksum
  have hentryJ : ∀ j, X j ≤ (rr j) ^ 4 * αJ j := fun j => hentry j.1 j.2
  have hRpJ : (∑ j, X j * rr j) ^ 4 * ρ < 1 := by
    have he : ∑ j, X j * rr j = ∑ c, ∑ s, αk c * K k c s * r c s := by rw [Fintype.sum_prod_type]
    rw [he]; exact hRp
  have hsb := seam_bound X αJ hX0 hXsum hαpos
  have hRle : (∑ j, X j * (X j / αJ j) ^ ((1 : ℝ) / 4)) ≤ ρ ^ (-(1 : ℝ) / 4) :=
    R_bound X αJ rr ρ hX0 (fun j => hαk0 j.1) (fun j => hr0 j.1 j.2) hentryJ hρ hRpJ
  have hRpos : 0 < ∑ j, X j * (X j / αJ j) ^ ((1 : ℝ) / 4) := by
    obtain ⟨j0, hj0⟩ : ∃ j, 0 < X j := by
      by_contra hnone; push_neg at hnone
      have hz : ∑ j, X j = 0 := Finset.sum_eq_zero (fun j _ => le_antisymm (hnone j) (hX0 j))
      rw [hXsum] at hz; exact one_ne_zero hz
    refine Finset.sum_pos' (fun j _ => mul_nonneg (hX0 j)
      (Real.rpow_nonneg (div_nonneg (hX0 j) (hαk0 j.1)) _)) ⟨j0, Finset.mem_univ j0, ?_⟩
    exact mul_pos hj0 (Real.rpow_pos_of_pos (div_pos hj0 (hαpos j0 hj0)) _)
  have hHeq : (∑ j, X j * (- Real.log (X j / αJ j))) = seamterm alpha K k := by
    rw [seamterm_marginal alpha K hKnorm k, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [hcons c, rowH, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [hXdef, hαJdef]
    by_cases hc : αk c = 0
    · rw [hc]; simp
    · have hdc : αk c * K k c s / αk c = K k c s := by
        rw [mul_comm (αk c) (K k c s), mul_div_assoc, div_self hc, mul_one]
      rw [hdc]; ring
  rw [← hHeq]
  exact seam_to_logrho _ _ ρ hρ hRpos hsb hRle

/-- **Cheap per-seam certificate.**  A conditional-collision inequality implies the same entropy
bound as the fourth-root certificate.  Its finite obligation is just the quadratic expression
`(∑ α(c) K(c,s)²) * ρ < 1`; the sharper `seamterm_ge_log` is needed only when this fails. -/
theorem seamterm_ge_log_collision [DecidableEq S] (ρ : ℝ) (hρ : 0 < ρ)
    (alpha : S → ℝ) (K : ℕ → S → S → ℝ)
    (hK0 : ∀ k c s, 0 ≤ K k c s) (hKnorm : ∀ k c, ∑ s, K k c s = 1)
    (k : ℕ) (αk : S → ℝ) (hαk0 : ∀ c, 0 ≤ αk c) (hαksum : ∑ c, αk c = 1)
    (hcons : ∀ c, lastMarg alpha K k c = αk c)
    (hcollision : (∑ c, ∑ s, αk c * (K k c s) ^ 2) * ρ < 1) :
    Real.log ρ ≤ seamterm alpha K k := by
  classical
  set X : S × S → ℝ := fun j => αk j.1 * K k j.1 j.2 with hXdef
  set αJ : S × S → ℝ := fun j => αk j.1 with hαJdef
  have hX0 : ∀ j, 0 ≤ X j := fun j => mul_nonneg (hαk0 j.1) (hK0 k j.1 j.2)
  have hαpos : ∀ j, 0 < X j → 0 < αJ j := by
    intro j hj
    rcases eq_or_lt_of_le (hαk0 j.1) with h0 | hpos
    · simp only [hXdef, ← h0, zero_mul] at hj
      exact absurd hj (lt_irrefl 0)
    · exact hpos
  have hXsum : ∑ j, X j = 1 := by
    rw [Fintype.sum_prod_type]
    have hc : ∀ c, ∑ s, X (c, s) = αk c := by
      intro c
      simp only [hXdef]
      rw [← Finset.mul_sum, hKnorm, mul_one]
    rw [Finset.sum_congr rfl (fun c _ => hc c)]
    exact hαksum
  have hCpos : 0 < ∑ j, X j * (X j / αJ j) := by
    obtain ⟨j0, hj0⟩ : ∃ j, 0 < X j := by
      by_contra hnone
      push Not at hnone
      have hz : ∑ j, X j = 0 :=
        Finset.sum_eq_zero (fun j _ => le_antisymm (hnone j) (hX0 j))
      rw [hXsum] at hz
      exact one_ne_zero hz
    refine Finset.sum_pos' (fun j _ => mul_nonneg (hX0 j)
      (div_nonneg (hX0 j) (hαk0 j.1))) ⟨j0, Finset.mem_univ j0, ?_⟩
    exact mul_pos hj0 (div_pos hj0 (hαpos j0 hj0))
  have hCeq : (∑ j, X j * (X j / αJ j)) =
      ∑ c, ∑ s, αk c * (K k c s) ^ 2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [hXdef, hαJdef]
    by_cases hc : αk c = 0
    · simp [hc]
    · have hdc : αk c * K k c s / αk c = K k c s := by
        rw [mul_comm (αk c) (K k c s), mul_div_assoc, div_self hc, mul_one]
      rw [hdc]
      ring
  have hHeq : (∑ j, X j * (-Real.log (X j / αJ j))) = seamterm alpha K k := by
    rw [seamterm_marginal alpha K hKnorm k, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [hcons c, rowH, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [hXdef, hαJdef]
    by_cases hc : αk c = 0
    · simp [hc]
    · have hdc : αk c * K k c s / αk c = K k c s := by
        rw [mul_comm (αk c) (K k c s), mul_div_assoc, div_self hc, mul_one]
      rw [hdc]
      ring
  have hbound := seam_collision_bound X αJ hX0 hXsum hαpos
  rw [← hHeq]
  exact collision_to_log _ _ ρ hρ hCpos hbound (by rw [hCeq]; exact hcollision)

/-- The basic certificate specialized to the height-three Perron factor `rho`. -/
theorem seamterm_ge_logrho [DecidableEq S] (alpha : S → ℝ) (K : ℕ → S → S → ℝ)
    (hK0 : ∀ k c s, 0 ≤ K k c s) (hKnorm : ∀ k c, ∑ s, K k c s = 1)
    (k : ℕ) (αk : S → ℝ) (hαk0 : ∀ c, 0 ≤ αk c) (hαksum : ∑ c, αk c = 1)
    (hcons : ∀ c, lastMarg alpha K k c = αk c)
    (r : S → S → ℝ) (hr0 : ∀ c s, 0 ≤ r c s)
    (hentry : ∀ c s, αk c * K k c s ≤ (r c s) ^ 4 * αk c)
    (hRp : (∑ c, ∑ s, αk c * K k c s * r c s) ^ 4 * rho < 1) :
    Real.log rho ≤ seamterm alpha K k :=
  seamterm_ge_log rho rho_pos alpha K hK0 hKnorm k αk hαk0 hαksum hcons r hr0 hentry hRp

/-- The cheap conditional-collision certificate at the height-three Perron factor `rho`. -/
theorem seamterm_ge_logrho_collision [DecidableEq S]
    (alpha : S → ℝ) (K : ℕ → S → S → ℝ)
    (hK0 : ∀ k c s, 0 ≤ K k c s) (hKnorm : ∀ k c, ∑ s, K k c s = 1)
    (k : ℕ) (αk : S → ℝ) (hαk0 : ∀ c, 0 ≤ αk c) (hαksum : ∑ c, αk c = 1)
    (hcons : ∀ c, lastMarg alpha K k c = αk c)
    (hcollision : (∑ c, ∑ s, αk c * (K k c s) ^ 2) * rho < 1) :
    Real.log rho ≤ seamterm alpha K k :=
  seamterm_ge_log_collision rho rho_pos alpha K hK0 hKnorm k αk hαk0 hαksum hcons
    hcollision

/-! ### Abstract capstone: the entropy half reduced to model instantiation -/

/-- **Entropy half (abstract).**  For a stochastic Markov model `(α, K)` over a finite state type
    `S` whose column laws `law` are marginal-consistent (`α = law 0`, `∑_c law_k(c)·K_k(c,s) =
    law_{k+1}(s)`), if every seam carries a fourth-root certificate (`hentry`, `hRp`), the root
    entropy is at least `log 12` (`hroot`), and the measure's support is bounded by `N` (`hsupp`),
    then the colouring count dominates the uniform count: `a (W-1) ≤ N`.

    Everything here is PROVED sorry-free from `entropy_bound_conditional`, `seamterm_ge_logrho`
    (= `seam_bound` + `R_bound` + `seam_to_logrho` + `seamterm_marginal`), and `lastMarg_eq_law`.
    Closing `grid3_three_ecc` now needs only: instantiate `S`/`K`/`law` from the saturated grid,
    supply the seam data `r` (the 43,364-seam ℚ certificate, via `Classical.choose`), and prove
    `hsupp` (the path→colouring injection). -/
theorem entropy_half_abstract [DecidableEq S] (W : ℕ)
    (alpha : S → ℝ) (K : ℕ → S → S → ℝ) (law : ℕ → S → ℝ) (Nr : ℝ)
    (hK0 : ∀ k c s, 0 ≤ K k c s) (hKnorm : ∀ k c, ∑ s, K k c s = 1)
    (hlaw0 : ∀ k c, 0 ≤ law k c) (hlawsum : ∀ k, ∑ c, law k c = 1)
    (hroot0 : ∀ c, alpha c = law 0 c)
    (hstep : ∀ k s, (∑ c, law k c * K k c s) = law (k + 1) s)
    (hNpos : 0 < Nr)
    (hsupp : Hsum (mu alpha K (W - 1)) ≤ Real.log Nr)
    (hroot : Real.log 12 ≤ Hsum (mu alpha K 0))
    (r : ℕ → S → S → ℝ) (hr0 : ∀ k c s, 0 ≤ r k c s)
    (hentry : ∀ k c s, law k c * K k c s ≤ (r k c s) ^ 4 * law k c)
    (hRp : ∀ k, (∑ c, ∑ s, law k c * K k c s * r k c s) ^ 4 * rho < 1) :
    (a (W - 1) : ℝ) ≤ Nr := by
  have hα0 : ∀ s, 0 ≤ alpha s := fun s => by rw [hroot0 s]; exact hlaw0 0 s
  have hseam : ∀ k, k < W - 1 → Real.log rho ≤ seamterm alpha K k := fun k _ =>
    seamterm_ge_logrho alpha K hK0 hKnorm k (law k) (hlaw0 k) (hlawsum k)
      (lastMarg_eq_law alpha K law hroot0 hstep k) (r k) (hr0 k) (hentry k) (hRp k)
  exact entropy_bound_conditional W alpha K Nr hα0 hK0 hKnorm hNpos hsupp hroot hseam

/-- **Entropy half with a uniform root and one strong entering seam.**  The uniform Parry root
only supplies `log (34/3) = log 12 - log (18/17)`.  A seam certified at
`(18/17) * rho` repays that deficit exactly. -/
theorem entropy_half_abstract_one_bonus [DecidableEq S] (W : ℕ)
    (alpha : S → ℝ) (K : ℕ → S → S → ℝ) (law : ℕ → S → ℝ) (Nr : ℝ)
    (j : Fin (W - 1))
    (hK0 : ∀ k c s, 0 ≤ K k c s) (hKnorm : ∀ k c, ∑ s, K k c s = 1)
    (hlaw0 : ∀ k c, 0 ≤ law k c) (hlawsum : ∀ k, ∑ c, law k c = 1)
    (hroot0 : ∀ c, alpha c = law 0 c)
    (hstep : ∀ k s, (∑ c, law k c * K k c s) = law (k + 1) s)
    (hNpos : 0 < Nr)
    (hsupp : Hsum (mu alpha K (W - 1)) ≤ Real.log Nr)
    (hroot : Real.log 12 - Real.log ((18 : ℝ) / 17) ≤ Hsum (mu alpha K 0))
    (r : ℕ → S → S → ℝ) (hr0 : ∀ k c s, 0 ≤ r k c s)
    (hentry : ∀ k c s, law k c * K k c s ≤ (r k c s) ^ 4 * law k c)
    (hRp : ∀ k, (∑ c, ∑ s, law k c * K k c s * r k c s) ^ 4 * rho < 1)
    (hRpBonus :
      (∑ c, ∑ s, law j.val c * K j.val c s * r j.val c s) ^ 4 *
        (((18 : ℝ) / 17) * rho) < 1) :
    (a (W - 1) : ℝ) ≤ Nr := by
  have hα0 : ∀ s, 0 ≤ alpha s := fun s => by rw [hroot0 s]; exact hlaw0 0 s
  have hcons : ∀ k c, lastMarg alpha K k c = law k c :=
    lastMarg_eq_law alpha K law hroot0 hstep
  have hseam : ∀ k, k < W - 1 → Real.log rho ≤ seamterm alpha K k := fun k _ =>
    seamterm_ge_logrho alpha K hK0 hKnorm k (law k) (hlaw0 k) (hlawsum k)
      (hcons k) (r k) (hr0 k) (hentry k) (hRp k)
  have hfactor : 0 < ((18 : ℝ) / 17) * rho := mul_pos (by norm_num) rho_pos
  have hbonus0 : Real.log (((18 : ℝ) / 17) * rho) ≤ seamterm alpha K j.val :=
    seamterm_ge_log (((18 : ℝ) / 17) * rho) hfactor alpha K hK0 hKnorm j.val
      (law j.val) (hlaw0 j.val) (hlawsum j.val) (hcons j.val) (r j.val) (hr0 j.val)
      (hentry j.val) hRpBonus
  have hbonus : Real.log rho + Real.log ((18 : ℝ) / 17) ≤ seamterm alpha K j.val := by
    rw [Real.log_mul (by norm_num : (18 : ℝ) / 17 ≠ 0) (ne_of_gt rho_pos)] at hbonus0
    linarith
  exact entropy_bound_conditional_one_bonus W alpha K Nr j (Real.log ((18 : ℝ) / 17))
    hα0 hK0 hKnorm hNpos hsupp hroot hseam hbonus

/-! ### hsupp reduced to a support-cardinality bound (the path→colouring injection) -/

/-- **Max-entropy for μ.**  `H(μ_{W-1}) ≤ log N` follows from `|supp μ_{W-1}| ≤ N`. -/
theorem hsupp_from_card [DecidableEq S] (alpha : S → ℝ) (K : ℕ → S → S → ℝ) (W N : ℕ)
    (hα0 : ∀ s, 0 ≤ alpha s) (hK0 : ∀ k c s, 0 ≤ K k c s)
    (hα1 : ∑ s, alpha s = 1) (hKnorm : ∀ k c, ∑ s, K k c s = 1)
    (hcard : (Finset.univ.filter (fun p : PState S (W - 1) => 0 < mu alpha K (W - 1) p)).card ≤ N) :
    Hsum (mu alpha K (W - 1)) ≤ Real.log (N : ℝ) := by
  have hnn : ∀ p, 0 ≤ mu alpha K (W - 1) p := mu_nonneg alpha K hα0 hK0 (W - 1)
  have hsum : ∑ p, mu alpha K (W - 1) p = 1 := mu_sum_one alpha K hα1 hKnorm (W - 1)
  have h1 := H_le_log_card (mu alpha K (W - 1)) hnn hsum
  have hcpos : 0 < (Finset.univ.filter (fun p : PState S (W - 1) => 0 < mu alpha K (W - 1) p)).card := by
    rw [Finset.card_pos]
    rcases Finset.eq_empty_or_nonempty
        (Finset.univ.filter (fun p : PState S (W - 1) => 0 < mu alpha K (W - 1) p)) with he | hne
    · exfalso
      have hall : ∀ p, mu alpha K (W - 1) p = 0 := by
        intro p; by_contra hp
        have hlt : 0 < mu alpha K (W - 1) p := lt_of_le_of_ne (hnn p) (Ne.symm hp)
        have hmem : p ∈ Finset.univ.filter (fun p => 0 < mu alpha K (W - 1) p) := by
          simp [hlt]
        rw [he] at hmem; simp at hmem
      have : ∑ p, mu alpha K (W - 1) p = 0 := Finset.sum_eq_zero (fun p _ => hall p)
      rw [hsum] at this; exact one_ne_zero this
    · exact hne
  exact le_trans h1 (Real.log_le_log (by exact_mod_cast hcpos) (by exact_mod_cast hcard))

/-- **Entropy half from a support-card bound.**  Same as `entropy_half_abstract`, but the support
    hypothesis is the combinatorial `|supp μ_{W-1}| ≤ N` (supplied by the path→colouring injection). -/
theorem entropy_half_from_card [DecidableEq S] (W : ℕ)
    (alpha : S → ℝ) (K : ℕ → S → S → ℝ) (law : ℕ → S → ℝ) (N : ℕ)
    (hK0 : ∀ k c s, 0 ≤ K k c s) (hKnorm : ∀ k c, ∑ s, K k c s = 1)
    (hlaw0 : ∀ k c, 0 ≤ law k c) (hlawsum : ∀ k, ∑ c, law k c = 1)
    (hroot0 : ∀ c, alpha c = law 0 c)
    (hstep : ∀ k s, (∑ c, law k c * K k c s) = law (k + 1) s)
    (hNpos : 0 < N)
    (hcard : (Finset.univ.filter (fun p : PState S (W - 1) => 0 < mu alpha K (W - 1) p)).card ≤ N)
    (hroot : Real.log 12 ≤ Hsum (mu alpha K 0))
    (r : ℕ → S → S → ℝ) (hr0 : ∀ k c s, 0 ≤ r k c s)
    (hentry : ∀ k c s, law k c * K k c s ≤ (r k c s) ^ 4 * law k c)
    (hRp : ∀ k, (∑ c, ∑ s, law k c * K k c s * r k c s) ^ 4 * rho < 1) :
    (a (W - 1) : ℝ) ≤ (N : ℝ) := by
  have hα0 : ∀ s, 0 ≤ alpha s := fun s => by rw [hroot0 s]; exact hlaw0 0 s
  have hα1 : ∑ s, alpha s = 1 := by
    rw [Finset.sum_congr rfl (fun s _ => hroot0 s)]; exact hlawsum 0
  have hsupp := hsupp_from_card alpha K W N hα0 hK0 hα1 hKnorm hcard
  exact entropy_half_abstract W alpha K law (N : ℝ) hK0 hKnorm hlaw0 hlawsum hroot0 hstep
    (by exact_mod_cast hNpos) hsupp hroot r hr0 hentry hRp

/-- Support-card version of `entropy_half_abstract_one_bonus`. -/
theorem entropy_half_from_card_one_bonus [DecidableEq S] (W : ℕ)
    (alpha : S → ℝ) (K : ℕ → S → S → ℝ) (law : ℕ → S → ℝ) (N : ℕ)
    (j : Fin (W - 1))
    (hK0 : ∀ k c s, 0 ≤ K k c s) (hKnorm : ∀ k c, ∑ s, K k c s = 1)
    (hlaw0 : ∀ k c, 0 ≤ law k c) (hlawsum : ∀ k, ∑ c, law k c = 1)
    (hroot0 : ∀ c, alpha c = law 0 c)
    (hstep : ∀ k s, (∑ c, law k c * K k c s) = law (k + 1) s)
    (hNpos : 0 < N)
    (hcard : (Finset.univ.filter (fun p : PState S (W - 1) => 0 < mu alpha K (W - 1) p)).card ≤ N)
    (hroot : Real.log 12 - Real.log ((18 : ℝ) / 17) ≤ Hsum (mu alpha K 0))
    (r : ℕ → S → S → ℝ) (hr0 : ∀ k c s, 0 ≤ r k c s)
    (hentry : ∀ k c s, law k c * K k c s ≤ (r k c s) ^ 4 * law k c)
    (hRp : ∀ k, (∑ c, ∑ s, law k c * K k c s * r k c s) ^ 4 * rho < 1)
    (hRpBonus :
      (∑ c, ∑ s, law j.val c * K j.val c s * r j.val c s) ^ 4 *
        (((18 : ℝ) / 17) * rho) < 1) :
    (a (W - 1) : ℝ) ≤ (N : ℝ) := by
  have hα0 : ∀ s, 0 ≤ alpha s := fun s => by rw [hroot0 s]; exact hlaw0 0 s
  have hα1 : ∑ s, alpha s = 1 := by
    rw [Finset.sum_congr rfl (fun s _ => hroot0 s)]; exact hlawsum 0
  have hsupp := hsupp_from_card alpha K W N hα0 hK0 hα1 hKnorm hcard
  exact entropy_half_abstract_one_bonus W alpha K law (N : ℝ) j hK0 hKnorm hlaw0
    hlawsum hroot0 hstep (by exact_mod_cast hNpos) hsupp hroot r hr0 hentry hRp hRpBonus

/-! ### The support-card bound from a path→colouring injection -/

/-- **`hcard` from an injection.**  If some `f` maps every positive-measure path to a distinct
    element of `properSet` (the grid's proper colourings), then `|supp μ_{W-1}| ≤ |properSet|`.
    This is the combinatorial content of the entropy support bound; the model supplies `f =`
    "read off the colouring a state-path spells out". -/
theorem hcard_from_inj [DecidableEq S] (alpha : S → ℝ) (K : ℕ → S → S → ℝ) (W : ℕ)
    {V : Type*} [DecidableEq V] (properSet : Finset (V → ℕ))
    (f : PState S (W - 1) → (V → ℕ))
    (hf_mem : ∀ p, 0 < mu alpha K (W - 1) p → f p ∈ properSet)
    (hf_inj : ∀ p q, 0 < mu alpha K (W - 1) p → 0 < mu alpha K (W - 1) q → f p = f q → p = q) :
    (Finset.univ.filter (fun p : PState S (W - 1) => 0 < mu alpha K (W - 1) p)).card
      ≤ properSet.card := by
  apply Finset.card_le_card_of_injOn f
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and] at hp
    exact hf_mem p hp
  · intro p hp q hq hpq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and] at hp hq
    exact hf_inj p q hp hq hpq

/-! ### Path → column-vector (backbone of the path→colouring injection) -/

/-- Read off the `k+1` column-states of a path. -/
def colAt : ∀ k, PState S k → Fin (k + 1) → S
  | 0, s => fun _ => s
  | (k + 1), q => Fin.snoc (colAt k q.1) q.2

/-- **The columns determine the path** — `colAt` is injective.  Composing with "a proper colouring
    determines its columns" gives the injectivity half of `hcard_from_inj`. -/
theorem colAt_injective : ∀ k, Function.Injective (colAt (S := S) k) := by
  intro k
  induction k with
  | zero => intro p q h; exact congrFun h 0
  | succ k ih =>
      intro p q h
      have hlast : p.2 = q.2 := by
        have := congrFun h (Fin.last (k + 1)); simpa [colAt, Fin.snoc_last] using this
      have hinit : colAt k p.1 = colAt k q.1 := by
        have h2 : Fin.init (colAt (k + 1) p) = Fin.init (colAt (k + 1) q) := by rw [h]
        simpa [colAt, Fin.init_snoc] using h2
      exact Prod.ext (ih hinit) hlast

end Grid3.Three
