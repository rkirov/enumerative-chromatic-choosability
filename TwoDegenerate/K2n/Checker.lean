/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.BigOperators.Fin

/-!
# A kernel-checkable certificate for sums of products of powers

The `K₂,ₙ` list-colouring bound reduces to inequalities of the following numeric shape. There
are `nt` *types* (rows) and `16` *pairs* (columns); a type `i` has a positive integer weight
`W i p` at pair `p`. For multiplicities `m` summing to `n`,

    F(m) = ∑_p c_p ∏_i W i p ^ m_i,

and the claim is `T ≤ F(m)` for every such `m`. `Goal T rows c rem` states it for the remaining
rows, with the partial products `c` of the rows already fixed.

A certificate is a binary tree (`Cert`).

* `leaf`: one row left; its multiplicity is forced, so evaluate.
* `split a b`: `a` covers "the first row has multiplicity 0" (drop the row), and `b` covers
  "multiplicity at least 1" (keep the row, multiply it into `c` once, and decrease `rem`).
* `bound k`: close the node by weighted AM–GM with integer weights `k`:

      (∏_p k_p^{k_p}) · (∑_p a_p)^D ≥ D^D · ∏_p a_p^{k_p},   D = ∑_p k_p,

  and `∏_p a_p^{k_p} = ∏_p c_p^{k_p} · ∏_i (∏_p W i p^{k_p})^{m_i} ≥ ∏_p c_p^{k_p} · g^rem`,
  where `g` is the least row value `∏_p W i p^{k_p}`.

`check_sound` proves that a certificate the checker accepts establishes its goal. The checker
is a plain `Bool` function, evaluated by `decide +kernel` on concrete data.
-/

namespace SimpleGraph.TwoDegenerate.K2n

open Finset

/-! ### Weighted AM–GM with integer weights -/

/-- Weighted AM–GM, cleared of denominators: `D^D ∏ a^k ≤ (∏ k^k) (∑ a)^D` with `D = ∑ k`. -/
theorem amgm_finset {ι : Type*} (s : Finset ι) (a k : ι → ℕ) :
    (∑ i ∈ s, k i) ^ (∑ i ∈ s, k i) * ∏ i ∈ s, a i ^ k i ≤
      (∏ i ∈ s, k i ^ k i) * (∑ i ∈ s, a i) ^ (∑ i ∈ s, k i) := by
  classical
  set D := ∑ i ∈ s, k i with hD
  -- Only the indices with positive weight matter.
  set t := s.filter (fun i => 0 < k i) with ht
  have hkt : ∀ i ∈ s, i ∉ t → k i = 0 := fun i hi hit => by
    simp only [ht, mem_filter, not_and, not_lt, nonpos_iff_eq_zero] at hit; exact hit hi
  have hprod : ∀ f : ι → ℕ, (∀ i ∈ s, k i = 0 → f i = 1) → ∏ i ∈ s, f i = ∏ i ∈ t, f i := by
    intro f hf
    exact (prod_subset (filter_subset _ _) fun i hi hit => hf i hi (hkt i hi hit)).symm
  have hDt : D = ∑ i ∈ t, k i :=
    (sum_subset (filter_subset _ _) fun i hi hit => hkt i hi hit).symm
  rw [hprod (fun i => a i ^ k i) (fun i _ h => by simp [h]),
    hprod (fun i => k i ^ k i) (fun i _ h => by simp [h])]
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  · have ht0 : t = ∅ := by
      refine eq_empty_of_forall_notMem fun i hi => ?_
      have h1 := (mem_filter.mp hi).2
      have h2 := (sum_eq_zero_iff.mp (hDt.symm.trans hD0)) i hi
      omega
    rw [ht0, hD0]; simp
  -- Real AM–GM on `t` with weights `k/D` and points `D a / k`.
  have hDr : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hkpos : ∀ i ∈ t, (0 : ℝ) < k i := fun i hi => by
    exact_mod_cast (mem_filter.mp hi).2
  have hw : ∀ i ∈ t, (0 : ℝ) ≤ (k i : ℝ) / D := fun i hi => by positivity
  have hw1 : ∑ i ∈ t, (k i : ℝ) / D = 1 := by
    rw [← sum_div, div_eq_one_iff_eq hDr.ne']; exact_mod_cast hDt.symm
  have hz : ∀ i ∈ t, (0 : ℝ) ≤ (D : ℝ) * a i / k i := fun i hi => by positivity
  have hgm := Real.geom_mean_le_arith_mean_weighted t (fun i => (k i : ℝ) / D)
    (fun i => (D : ℝ) * a i / k i) hw hw1 hz
  have hsum : ∑ i ∈ t, (k i : ℝ) / D * ((D : ℝ) * a i / k i) = ∑ i ∈ t, (a i : ℝ) := by
    refine sum_congr rfl fun i hi => ?_
    have := (hkpos i hi).ne'
    field_simp
  rw [hsum] at hgm
  have hsa : ∑ i ∈ t, (a i : ℝ) ≤ ∑ i ∈ s, (a i : ℝ) :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
  have hle := hgm.trans hsa
  have hl0 : 0 ≤ ∏ i ∈ t, ((D : ℝ) * a i / k i) ^ ((k i : ℝ) / D) :=
    prod_nonneg fun i hi => Real.rpow_nonneg (hz i hi) _
  have hpow := pow_le_pow_left₀ hl0 hle D
  -- `(∏ z^(k/D))^D = ∏ z^k`.
  have hlhs : (∏ i ∈ t, ((D : ℝ) * a i / k i) ^ ((k i : ℝ) / D)) ^ D =
      ∏ i ∈ t, ((D : ℝ) * a i / k i) ^ k i := by
    rw [← prod_pow]
    refine prod_congr rfl fun i hi => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hz i hi), div_mul_cancel₀ _ hDr.ne',
      Real.rpow_natCast]
  rw [hlhs] at hpow
  have hsplit : ∏ i ∈ t, ((D : ℝ) * a i / k i) ^ k i =
      (D : ℝ) ^ D * (∏ i ∈ t, (a i : ℝ) ^ k i) / ∏ i ∈ t, (k i : ℝ) ^ k i := by
    simp_rw [div_pow, mul_pow]
    rw [prod_div_distrib, prod_mul_distrib, prod_pow_eq_pow_sum, ← hDt]
  rw [hsplit, div_le_iff₀ (prod_pos fun i hi => pow_pos (hkpos i hi) _)] at hpow
  have hsa' : ((∑ i ∈ s, a i : ℕ) : ℝ) = ∑ i ∈ s, (a i : ℝ) := by push_cast; rfl
  have key : ((D ^ D * ∏ i ∈ t, a i ^ k i : ℕ) : ℝ) ≤
      ((∏ i ∈ t, k i ^ k i) * (∑ i ∈ s, a i) ^ D : ℕ) := by
    push_cast
    linarith [hpow, mul_comm ((∑ i ∈ s, (a i : ℝ)) ^ D) (∏ i ∈ t, (k i : ℝ) ^ k i)]
  exact_mod_cast key

/-! ### Lists of equal length -/

/-- `∏_p l_p ^ k_p`. -/
def powProd (l k : List ℕ) : ℕ := (List.zipWith (· ^ ·) l k).prod

/-- `∏_p k_p ^ k_p`. -/
def selfPow (k : List ℕ) : ℕ := (k.map fun x => x ^ x).prod

/-- Multiply each `c_p` by `row_p ^ j`. -/
def stepPow (c row : List ℕ) (j : ℕ) : List ℕ := List.zipWith (fun a w => a * w ^ j) c row

/-- The partial products after the multiplicities `ms` have been applied to `rows`. -/
def evalC : List (List ℕ) → List ℕ → List ℕ → List ℕ
  | row :: rows, c, m :: ms => evalC rows (stepPow c row m) ms
  | _, c, _ => c

/-- For all multiplicities of the remaining `rows` summing to `rem`, `T ≤ ∑_p` of the products. -/
def Goal (T : ℕ) (rows : List (List ℕ)) (c : List ℕ) (rem : ℕ) : Prop :=
  ∀ ms : List ℕ, ms.length = rows.length → ms.sum = rem → T ≤ (evalC rows c ms).sum

theorem prod_zipWith_eq (f : ℕ → ℕ → ℕ) {a k : List ℕ} (h : a.length = k.length) :
    (List.zipWith f a k).prod = ∏ i : Fin k.length, f a[i.1] k[i.1] := by
  have hl : (List.zipWith f a k).length = k.length := by simp [h]
  rw [← Fin.prod_univ_getElem, ← Fin.prod_congr' _ hl.symm]
  refine Fintype.prod_congr _ _ fun i => ?_
  simp [List.getElem_zipWith]

theorem sum_eq_fin {a k : List ℕ} (h : a.length = k.length) :
    a.sum = ∑ i : Fin k.length, a[i.1] := by
  rw [← Fin.sum_univ_getElem, ← Fin.sum_congr' _ h.symm]
  rfl

theorem amgm_list (a k : List ℕ) (h : a.length = k.length) :
    k.sum ^ k.sum * powProd a k ≤ selfPow k * a.sum ^ k.sum := by
  have hk : k.sum = ∑ i : Fin k.length, k[i.1] := sum_eq_fin rfl
  have hs : selfPow k = ∏ i : Fin k.length, k[i.1] ^ k[i.1] := by
    rw [selfPow, ← Fin.prod_univ_getElem, ← Fin.prod_congr' _ (List.length_map _).symm]
    simp
  rw [powProd, prod_zipWith_eq _ h, hs, sum_eq_fin h, hk]
  exact amgm_finset univ (fun i : Fin k.length => a[i.1]) (fun i => k[i.1])

/-! ### Products along the rows -/

theorem length_stepPow (c row : List ℕ) (j : ℕ) :
    (stepPow c row j).length = min c.length row.length := by
  simp [stepPow]

theorem stepPow_stepPow (c row : List ℕ) (i j : ℕ) :
    stepPow (stepPow c row i) row j = stepPow c row (i + j) := by
  induction c generalizing row with
  | nil => simp [stepPow]
  | cons x c ih =>
    cases row with
    | nil => simp [stepPow]
    | cons w row =>
      simp only [stepPow, List.zipWith_cons_cons] at ih ⊢
      rw [ih, pow_add, mul_assoc]

theorem length_evalC {n : ℕ} (rows : List (List ℕ)) (hrows : ∀ row ∈ rows, row.length = n)
    (c : List ℕ) (hc : c.length = n) (ms : List ℕ) : (evalC rows c ms).length = n := by
  induction rows generalizing c ms with
  | nil => cases ms <;> simpa [evalC] using hc
  | cons row rows ih =>
    cases ms with
    | nil => simpa [evalC] using hc
    | cons m ms =>
      simp only [evalC]
      refine ih (fun r hr => hrows r (List.mem_cons_of_mem _ hr)) _ ?_ ms
      rw [length_stepPow, hc, hrows row List.mem_cons_self, min_self]

theorem powProd_stepPow {c row k : List ℕ} (hc : c.length = k.length)
    (hr : row.length = k.length) (j : ℕ) :
    powProd (stepPow c row j) k = powProd c k * powProd row k ^ j := by
  have hl : (stepPow c row j).length = k.length := by rw [length_stepPow, hc, hr, min_self]
  rw [powProd, prod_zipWith_eq _ hl, powProd, prod_zipWith_eq _ hc, powProd,
    prod_zipWith_eq _ hr, ← prod_pow, ← prod_mul_distrib]
  refine Fintype.prod_congr _ _ fun i => ?_
  simp only [stepPow, List.getElem_zipWith]
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j]

theorem powProd_evalC_ge {k : List ℕ} (rows : List (List ℕ))
    (hrows : ∀ row ∈ rows, row.length = k.length) {g : ℕ}
    (hg : ∀ row ∈ rows, g ≤ powProd row k) (c : List ℕ) (hc : c.length = k.length)
    (ms : List ℕ) (hms : ms.length = rows.length) :
    powProd c k * g ^ ms.sum ≤ powProd (evalC rows c ms) k := by
  induction rows generalizing c ms with
  | nil =>
    rw [List.length_eq_zero_iff.mp hms]; simp [evalC]
  | cons row rows ih =>
    cases ms with
    | nil => simp at hms
    | cons m ms =>
      simp only [evalC, List.sum_cons]
      have hr := hrows row List.mem_cons_self
      have hc' : (stepPow c row m).length = k.length := by
        rw [length_stepPow, hc, hr, min_self]
      refine le_trans ?_ (ih (fun r h => hrows r (List.mem_cons_of_mem _ h))
        (fun r h => hg r (List.mem_cons_of_mem _ h)) _ hc' ms (by simpa using hms))
      rw [powProd_stepPow hc hr, pow_add, ← mul_assoc]
      exact Nat.mul_le_mul_right _
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hg row List.mem_cons_self) _))

/-- The least row value `∏_p row_p ^ k_p` (arbitrary when there are no rows). -/
def rowMin (rows : List (List ℕ)) (k : List ℕ) : ℕ :=
  match rows with
  | [] => 0
  | r :: rs => rs.foldl (fun g row => min g (powProd row k)) (powProd r k)

theorem foldl_min_le (f : List ℕ → ℕ) (rs : List (List ℕ)) (init : ℕ) :
    rs.foldl (fun g row => min g (f row)) init ≤ init ∧
      ∀ row ∈ rs, rs.foldl (fun g row => min g (f row)) init ≤ f row := by
  induction rs generalizing init with
  | nil => simp
  | cons r rs ih =>
    obtain ⟨h1, h2⟩ := ih (min init (f r))
    refine ⟨h1.trans (min_le_left _ _), fun row hrow => ?_⟩
    rcases List.mem_cons.mp hrow with rfl | h
    · exact h1.trans (min_le_right _ _)
    · exact h2 row h

theorem rowMin_le (rows : List (List ℕ)) (k : List ℕ) :
    ∀ row ∈ rows, rowMin rows k ≤ powProd row k := by
  cases rows with
  | nil => simp
  | cons r rs =>
    intro row hrow
    obtain ⟨h1, h2⟩ := foldl_min_le (fun row => powProd row k) rs (powProd r k)
    rcases List.mem_cons.mp hrow with rfl | h
    · exact h1
    · exact h2 row h

/-! ### The checker -/

/-- A certificate tree; see the module docstring. -/
inductive Cert where
  | leaf
  | bound (k : List ℕ)
  | split (a b : Cert)

/-- The AM–GM closing condition of a node. -/
def boundOK (T : ℕ) (rows : List (List ℕ)) (c k : List ℕ) (rem : ℕ) : Bool :=
  0 < k.sum && c.length == k.length && rows.all (fun row => row.length == k.length) &&
    decide (selfPow k * T ^ k.sum ≤ k.sum ^ k.sum * powProd c k * rowMin rows k ^ rem)

/-- The certificate checker. -/
def check (T : ℕ) : Cert → List (List ℕ) → List ℕ → ℕ → Bool
  | .leaf, [row], c, rem => decide (T ≤ (stepPow c row rem).sum)
  | .bound k, rows, c, rem => boundOK T rows c k rem
  | .split a b, row :: rows, c, rem =>
      check T a rows (stepPow c row 0) rem &&
        (rem == 0 || check T b (row :: rows) (stepPow c row 1) (rem - 1))
  | _, _, _, _ => false

theorem selfPow_pos (k : List ℕ) : 0 < selfPow k := by
  unfold selfPow
  refine List.prod_pos fun x hx => ?_
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp
  · exact Nat.pow_pos hy

theorem boundOK_sound {T : ℕ} {rows : List (List ℕ)} {c k : List ℕ} {rem : ℕ}
    (h : boundOK T rows c k rem = true) : Goal T rows c rem := by
  simp only [boundOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true]
    at h
  obtain ⟨⟨⟨hD, hc⟩, hrows⟩, hineq⟩ := h
  intro ms hms hsum
  set a := evalC rows c ms
  have ha : a.length = k.length := length_evalC rows hrows c hc ms
  have hamgm := amgm_list a k ha
  have hprod := powProd_evalC_ge rows hrows (rowMin_le rows k) c hc ms hms
  rw [hsum] at hprod
  have h1 : selfPow k * T ^ k.sum ≤ selfPow k * a.sum ^ k.sum := by
    calc selfPow k * T ^ k.sum ≤ k.sum ^ k.sum * powProd c k * rowMin rows k ^ rem := hineq
      _ = k.sum ^ k.sum * (powProd c k * rowMin rows k ^ rem) := by ring
      _ ≤ k.sum ^ k.sum * powProd a k := Nat.mul_le_mul_left _ hprod
      _ ≤ selfPow k * a.sum ^ k.sum := hamgm
  have h2 := Nat.le_of_mul_le_mul_left h1 (selfPow_pos k)
  exact (Nat.pow_le_pow_iff_left hD.ne').mp h2

theorem check_sound (T : ℕ) (t : Cert) :
    ∀ (rows : List (List ℕ)) (c : List ℕ) (rem : ℕ), check T t rows c rem = true →
      Goal T rows c rem := by
  induction t with
  | leaf =>
    intro rows c rem h
    match rows, h with
    | [row], h =>
      intro ms hms hsum
      match ms, hms with
      | [m], _ =>
        simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
        subst hsum
        simpa [check, evalC] using h
  | bound k => intro rows c rem h; exact boundOK_sound h
  | split a b iha ihb =>
    intro rows c rem h
    match rows, h with
    | row :: rows, h =>
      simp only [check, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      obtain ⟨ha, hb⟩ := h
      intro ms hms hsum
      match ms, hms with
      | m :: ms, hms =>
        simp only [List.length_cons, add_left_inj] at hms
        simp only [List.sum_cons] at hsum
        rcases m with _ | m
        · simp only [evalC]
          exact iha rows _ rem ha ms hms (by omega)
        · rcases hb with hb | hb
          · omega
          have := ihb (row :: rows) _ (rem - 1) hb (m :: ms) (by simp [hms])
            (by simp; omega)
          simpa only [evalC, stepPow_stepPow, add_comm 1 m] using this

end SimpleGraph.TwoDegenerate.K2n
