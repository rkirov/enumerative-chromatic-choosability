/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import TwoDegenerate.K2nSqrt.Classes
import TwoDegenerate.K2n.Reduction
import TwoDegenerate.K2n.Count

/-!
# `K₂,ₙ` is `k`-ECC whenever `n ≤ k²`, for `k ≥ 300`

Kaul, Kumar, Mudrock, Rewers, Shin and To (*On the list color function threshold*,
arXiv:2202.03431) prove `τ(K₂,ₗ) - χ_ℓ(K₂,ₗ) ≥ C √l` (their Theorem 4) and conjecture
`τ(K₂,ₗ) = Θ(√l)` (their Conjecture 5; Conjecture 4 of arXiv:2207.04831). The best upper bound in
the literature is linear, `τ(K₂,ₙ) ≤ ⌈(n + 2.05)/1.24⌉` (Kaul, Kumar, Liu, Mudrock, Rewers, Shin,
Tanahara and To, *Bounding the list color function threshold from above*, arXiv:2207.04831,
Theorem 9). Here:

* `completeBipartite_two_eccAt_of_sq_le`: `K₂,ₙ` is ECC at every `k ≥ 300` with `n ≤ k²`;
* `completeBipartite_two_eccAt_of_sqrt_lt`: hence `K₂,ₙ` is ECC at every `k ≥ 300` with
  `k > ⌊√n⌋`, i.e. `τ(K₂,ₙ) ≤ max 300 (⌊√n⌋ + 1) = O(√n)`. With their Theorem 4 this proves the
  conjecture: `τ(K₂,ₙ) = Θ(√n)`.

The proof, for a `k`-list assignment with hub lists `A`, `B`:

1. push every right list into `A ∪ B` (Lemma 5 of arXiv:2207.04831, `K2n.exists_push`);
2. overlap `r = |A ∩ B|`:
   * `1 ≤ r ≤ k - 2`: class AM–GM (`TwoDegenerate/K2nSqrt/Classes.lean`) and the analytic
     inequality (`TwoDegenerate/K2nSqrt/Analytic.lean`);
   * `r = 0`: the single class `A × B`, then `target_le_zero`;
   * `r = k - 1`: Lemma 6 of arXiv:2207.04831, reproved here as `lemma6`;
   * `r = k`: the lists are all equal to `A`.
-/

namespace SimpleGraph.TwoDegenerate.K2nSqrt

open Finset Real

/-! ### Product expansions -/

theorem prod_add_ge {ι : Type*} (s : Finset ι) {c : ℝ} (hc : 0 ≤ c) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    c ^ (s.card + 1) + c ^ s.card * ∑ i ∈ s, x i ≤ c * ∏ i ∈ s, (c + x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, card_insert_of_notMem ha]
    have ih' := ih fun i hi => hx i (mem_insert_of_mem hi)
    have hxa := hx a (mem_insert_self a s)
    have hS : 0 ≤ ∑ i ∈ s, x i := sum_nonneg fun i hi => hx i (mem_insert_of_mem hi)
    have h1 : (c + x a) * (c ^ (s.card + 1) + c ^ s.card * ∑ i ∈ s, x i) ≤
        (c + x a) * (c * ∏ i ∈ s, (c + x i)) := mul_le_mul_of_nonneg_left ih' (by linarith)
    have h2 : 0 ≤ x a * c ^ s.card * ∑ i ∈ s, x i := by positivity
    have e : c * ((c + x a) * ∏ i ∈ s, (c + x i)) = (c + x a) * (c * ∏ i ∈ s, (c + x i)) := by
      ring
    have e2 : (c + x a) * (c ^ (s.card + 1) + c ^ s.card * ∑ i ∈ s, x i) =
        c ^ (s.card + 1 + 1) + c ^ (s.card + 1) * (x a + ∑ i ∈ s, x i) +
          x a * c ^ s.card * ∑ i ∈ s, x i := by ring
    rw [e]
    linarith

theorem prod_sub_ge {ι : Type*} (s : Finset ι) {c : ℝ} (hc : 0 ≤ c) (y : ι → ℝ)
    (hy0 : ∀ i ∈ s, 0 ≤ y i) (hyc : ∀ i ∈ s, y i ≤ c) :
    c ^ (s.card + 1) - c ^ s.card * ∑ i ∈ s, y i ≤ c * ∏ i ∈ s, (c - y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, card_insert_of_notMem ha]
    have ih' := ih (fun i hi => hy0 i (mem_insert_of_mem hi)) fun i hi => hyc i (mem_insert_of_mem hi)
    have hya := hy0 a (mem_insert_self a s)
    have hyac := hyc a (mem_insert_self a s)
    have hS : 0 ≤ ∑ i ∈ s, y i := sum_nonneg fun i hi => hy0 i (mem_insert_of_mem hi)
    have h1 : (c - y a) * (c ^ (s.card + 1) - c ^ s.card * ∑ i ∈ s, y i) ≤
        (c - y a) * (c * ∏ i ∈ s, (c - y i)) := mul_le_mul_of_nonneg_left ih' (by linarith)
    have h2 : 0 ≤ y a * c ^ s.card * ∑ i ∈ s, y i := by positivity
    have e : c * ((c - y a) * ∏ i ∈ s, (c - y i)) = (c - y a) * (c * ∏ i ∈ s, (c - y i)) := by
      ring
    have e2 : (c - y a) * (c ^ (s.card + 1) - c ^ s.card * ∑ i ∈ s, y i) =
        c ^ (s.card + 1 + 1) - c ^ (s.card + 1) * (y a + ∑ i ∈ s, y i) +
          y a * c ^ s.card * ∑ i ∈ s, y i := by ring
    rw [e]
    linarith

/-! ### Facts about pushed lists -/

section Pushed

variable {k n : ℕ} {A B : Finset ℕ} {T : Fin n → Finset ℕ}

theorem card_sdiff_ge_real {T : Finset ℕ} (hT : T.card = k) (a b : ℕ) :
    (k : ℝ) - 2 ≤ ((T \ {a, b}).card : ℝ) := by
  rcases eq_or_ne a b with rfl | hab
  · rw [card_sdiff_single_real hT]
    simp only [ind]; split_ifs <;> linarith
  · rw [card_sdiff_pair_real hT hab]
    simp only [ind]; split_ifs <;> linarith

theorem pf_ge (hk : 3 ≤ k) (hT : ∀ w, (T w).card = k) (a b : ℕ) :
    ((k : ℝ) - 2) ^ n ≤ pf T a b := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  calc ((k : ℝ) - 2) ^ n = ∏ _w : Fin n, ((k : ℝ) - 2) := by simp
    _ ≤ pf T a b := prod_le_prod₀ (fun _ _ => by linarith) fun w _ => card_sdiff_ge_real (hT w) a b

theorem pf_diag_ge (hk : 3 ≤ k) (hT : ∀ w, (T w).card = k) (a : ℕ) :
    ((k : ℝ) - 1) ^ n ≤ pf T a a := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  calc ((k : ℝ) - 1) ^ n = ∏ _w : Fin n, ((k : ℝ) - 1) := by simp
    _ ≤ pf T a a := prod_le_prod₀ (fun _ _ => by linarith) fun w _ => by
        rw [card_sdiff_single_real (hT w)]; simp only [ind]; split_ifs <;> linarith

/-- Every pair other than the diagonal of `A ∩ B` contributes at least `(k - 2)ⁿ`. -/
theorem sum_ge_diag_add (hk : 3 ≤ k) (hA : A.card = k) (hB : B.card = k)
    (hT : ∀ w, (T w).card = k) :
    ∑ a ∈ A ∩ B, pf T a a + ((k : ℝ) ^ 2 - (A ∩ B).card) * ((k : ℝ) - 2) ^ n ≤
      ∑ a ∈ A, ∑ b ∈ B, pf T a b := by
  have hsplit := sum_split A B (pf T)
  have hdiag : ∑ a ∈ A ∩ B, pf T a a = ∑ p ∈ (A ∩ B).diag, pf T p.1 p.2 := by
    rw [diag, sum_map]; rfl
  have hAB : ∑ a ∈ A, ∑ b ∈ B, pf T a b = ∑ p ∈ A ×ˢ B, pf T p.1 p.2 := by rw [sum_product]
  have hsub : (A ∩ B).diag ⊆ A ×ˢ B := fun p hp => by
    rw [mem_diag] at hp
    rw [mem_product]
    exact ⟨(mem_inter.mp hp.1).1, hp.2 ▸ (mem_inter.mp hp.1).2⟩
  rw [hAB, ← sum_sdiff hsub, hdiag]
  have hcard : (((A ×ˢ B) \ (A ∩ B).diag).card : ℝ) = (k : ℝ) ^ 2 - (A ∩ B).card := by
    rw [card_sdiff_of_subset hsub, card_product, hA, hB, diag_card,
      Nat.cast_sub (by rw [← hA]; exact (card_le_card inter_subset_left).trans (by nlinarith))]
    push_cast; ring
  have : ((k : ℝ) ^ 2 - (A ∩ B).card) * ((k : ℝ) - 2) ^ n ≤
      ∑ p ∈ (A ×ˢ B) \ (A ∩ B).diag, pf T p.1 p.2 := by
    rw [← hcard, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun p _ => pf_ge hk hT _ _
  linarith

end Pushed

/-! ### Kaul et al. Lemma 6: overlap `k - 1` -/

section Lemma6

variable {k n : ℕ} {A B : Finset ℕ} {T : Fin n → Finset ℕ}

/-- **Kaul et al., Lemma 6** (arXiv:2207.04831): if the hub lists share `k - 1` colours and the
right lists lie in `A ∪ B`, the count is at least `P(K₂,ₙ, k)`. The diagonal of `A ∩ B` gains what
the one private pair `(p, q)` loses; both are Bernoulli bounds (`prod_add_ge`, `prod_sub_ge`). -/
theorem lemma6 (hk : 3 ≤ k) (hA : A.card = k) (hB : B.card = k) (hTsub : ∀ w, T w ⊆ A ∪ B)
    (hT : ∀ w, (T w).card = k) (hr : (A ∩ B).card + 1 = k) :
    (k : ℝ) * ((k : ℝ) - 1) ^ n + (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) ^ n ≤
      ∑ a ∈ A, ∑ b ∈ B, pf T a b := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hr' : ((A ∩ B).card : ℝ) = k - 1 := by
    have : ((A ∩ B).card : ℝ) + 1 = k := by exact_mod_cast hr
    linarith
  -- The private colours `p` and `q`.
  have hP1 : (A \ B).card = 1 := by have := card_sdiff_add_card_inter A B; omega
  have hQ1 : (B \ A).card = 1 := by
    have := card_sdiff_add_card_inter B A; rw [inter_comm] at this; omega
  obtain ⟨p, hp⟩ := card_eq_one.mp hP1
  obtain ⟨q, hq⟩ := card_eq_one.mp hQ1
  have hpA : p ∈ A \ B := hp ▸ mem_singleton_self p
  have hqB : q ∈ B \ A := hq ▸ mem_singleton_self q
  have hpq : p ≠ q := fun h => (mem_sdiff.mp hpA).2 (h ▸ (mem_sdiff.mp hqB).1)
  -- Per-list counts.
  have hsum3 : ∀ w, ((A ∩ B ∩ T w).card : ℝ) + ind (T w) p + ind (T w) q = k := by
    intro w
    have h := card_parts (hTsub w) (hT w)
    rw [hp, hq] at h
    have e1 : (({p} ∩ T w).card : ℝ) = ind (T w) p := by
      rw [← sum_ind, sum_singleton]
    have e2 : (({q} ∩ T w).card : ℝ) = ind (T w) q := by
      rw [← sum_ind, sum_singleton]
    have : ((A ∩ B ∩ T w).card : ℝ) + (({p} ∩ T w).card : ℝ) + (({q} ∩ T w).card : ℝ) = k := by
      exact_mod_cast h
    rw [e1, e2] at this; exact this
  have hir : ∀ w, ((A ∩ B ∩ T w).card : ℝ) ≤ k - 1 := fun w => by
    rw [← hr']; exact_mod_cast card_le_card inter_subset_left
  have hind : ∀ w a, 0 ≤ ind (T w) a ∧ ind (T w) a ≤ 1 := fun w a => by
    simp only [ind]; split_ifs <;> norm_num
  set y : Fin n → ℝ := fun w => (k - 1 : ℝ) - (A ∩ B ∩ T w).card with hy
  have hy0 : ∀ w, 0 ≤ y w := fun w => by simp only [hy]; linarith [hir w]
  have hy1 : ∀ w, y w ≤ k - 1 := fun w => by
    simp only [hy]; linarith [(Nat.cast_nonneg ((A ∩ B ∩ T w).card) : (0 : ℝ) ≤ _)]
  -- The private pair.
  have hPQ : ((k : ℝ) - 1) ^ (n + 1) - ((k : ℝ) - 1) ^ n * ∑ w, y w ≤
      ((k : ℝ) - 1) * pf T p q := by
    have h := prod_sub_ge (univ : Finset (Fin n)) (c := (k : ℝ) - 1) (by linarith) y
      (fun w _ => hy0 w) (fun w _ => hy1 w)
    rw [card_univ, Fintype.card_fin] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    refine prod_congr rfl fun w _ => ?_
    rw [card_sdiff_pair_real (hT w) hpq]
    simp only [hy]; linarith [hsum3 w]
  -- The diagonal.
  have hD : ∀ a ∈ A ∩ B, ((k : ℝ) - 1) ^ (n + 1) +
      ((k : ℝ) - 1) ^ n * ∑ w, (1 - ind (T w) a) ≤ ((k : ℝ) - 1) * pf T a a := by
    intro a _
    have h := prod_add_ge (univ : Finset (Fin n)) (c := (k : ℝ) - 1) (by linarith)
      (fun w => 1 - ind (T w) a) (fun w _ => by linarith [(hind w a).2])
    rw [card_univ, Fintype.card_fin] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    refine prod_congr rfl fun w _ => ?_
    rw [card_sdiff_single_real (hT w)]; ring
  have hDsum : ((A ∩ B).card : ℝ) * ((k : ℝ) - 1) ^ (n + 1) + ((k : ℝ) - 1) ^ n * ∑ w, y w ≤
      ((k : ℝ) - 1) * ∑ a ∈ A ∩ B, pf T a a := by
    have h := sum_le_sum hD
    rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum, ← mul_sum] at h
    refine le_trans (le_of_eq ?_) h
    congr 2
    rw [sum_comm]
    refine sum_congr rfl fun w _ => ?_
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, sum_ind, hr']
  -- The rest.
  have hrest := sum_ge_diag_add (T := T) hk hA hB hT
  -- `pf T p q` is one of the non-diagonal pairs; split it off.
  have hsplit := sum_split A B (pf T)
  rw [hp, hq] at hsplit
  simp only [sum_singleton] at hsplit
  have hIQ : ∑ a ∈ A ∩ B, pf T a q ≥ ((A ∩ B).card : ℝ) * ((k : ℝ) - 2) ^ n := by
    rw [ge_iff_le, ← nsmul_eq_mul, ← sum_const]; exact sum_le_sum fun a _ => pf_ge hk hT _ _
  have hPI : ∑ b ∈ A ∩ B, pf T p b ≥ ((A ∩ B).card : ℝ) * ((k : ℝ) - 2) ^ n := by
    rw [ge_iff_le, ← nsmul_eq_mul, ← sum_const]; exact sum_le_sum fun b _ => pf_ge hk hT _ _
  have hO : ∑ x ∈ (A ∩ B).offDiag, pf T x.1 x.2 ≥
      ((A ∩ B).card : ℝ) * ((A ∩ B).card - 1) * ((k : ℝ) - 2) ^ n := by
    have hc : ((A ∩ B).offDiag.card : ℝ) = ((A ∩ B).card : ℝ) * ((A ∩ B).card - 1) := by
      rw [offDiag_card, Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]; ring
    rw [ge_iff_le, ← hc, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun x _ => pf_ge hk hT _ _
  have hkpos : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hpow : ((k : ℝ) - 1) ^ (n + 1) = ((k : ℝ) - 1) ^ n * ((k : ℝ) - 1) := pow_succ _ _
  have hDPQ : (k : ℝ) * ((k : ℝ) - 1) ^ n ≤ ∑ a ∈ A ∩ B, pf T a a + pf T p q := by
    have h := add_le_add hDsum hPQ
    rw [hr', hpow] at h
    have e : ((k : ℝ) - 1) * (∑ a ∈ A ∩ B, pf T a a + pf T p q) ≥
        ((k : ℝ) - 1) * ((k : ℝ) * ((k : ℝ) - 1) ^ n) := by nlinarith
    exact le_of_mul_le_mul_left e hkpos
  rw [hsplit, hr'] at *
  rw [hr'] at hIQ hPI hO
  nlinarith

end Lemma6

/-! ### The main theorem -/

section MainTheorem

variable {k n : ℕ}

theorem hyp_of (hk : 300 ≤ k) (hn : n ≤ k ^ 2) :
    Hyp k (n * ell k) (n * del k) (del k / ell k) := by
  have hk3 : 3 ≤ k := by omega
  have hk' : (300 : ℝ) ≤ k := by exact_mod_cast hk
  have hℓ := ell_ge hk3
  have hℓ0 := ell_pos hk3
  have hd0 := del_nonneg hk3
  have hd1 := del_le hk3
  have hn' : (n : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hdk : del k * ((k : ℝ) - 2) ≤ ell k := by
    have : del k * ((k : ℝ) - 2) ≤ 1 / k := by
      calc del k * ((k : ℝ) - 2) ≤ 1 / (k * ((k : ℝ) - 2)) * ((k : ℝ) - 2) :=
            mul_le_mul_of_nonneg_right hd1 (by linarith)
        _ = 1 / k := by
            have : (k : ℝ) - 2 ≠ 0 := by linarith
            field_simp
    linarith
  refine ⟨hk', mul_nonneg hn0 hℓ0.le, mul_nonneg hn0 hd0, ?_, ?_, div_nonneg hd0 hℓ0.le, ?_⟩
  · calc (n : ℝ) * del k * ((k : ℝ) - 2) = n * (del k * ((k : ℝ) - 2)) := by ring
      _ ≤ n * ell k := mul_le_mul_of_nonneg_left hdk hn0
  · calc (n : ℝ) * del k ≤ (k : ℝ) ^ 2 * (1 / (k * ((k : ℝ) - 2))) :=
          mul_le_mul hn' hd1 hd0 (by positivity)
      _ = k / ((k : ℝ) - 2) := by
          have : (k : ℝ) - 2 ≠ 0 := by linarith
          field_simp
      _ ≤ 11 / 10 := by rw [div_le_iff₀ (by linarith)]; linarith
  · rw [div_mul_eq_mul_div, div_le_one hℓ0]; exact hdk

/-- `(k - 1)ⁿ · target = k (k-1)ⁿ + k (k-1) (k-2)ⁿ`. -/
theorem pow_mul_target (hk : 3 ≤ k) :
    ((k : ℝ) - 1) ^ n * target k (n * ell k) (n * del k) =
      (k : ℝ) * ((k : ℝ) - 1) ^ n + (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) ^ n := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 : ((k : ℝ) - 2) ^ n = ((k : ℝ) - 1) ^ n * exp (-(n * ell k) - n * del k) := by
    have e : ((k : ℝ) - 2) ^ n = exp (n * log ((k : ℝ) - 2)) := by
      rw [← log_pow, exp_log (pow_pos (by linarith) n)]
    rw [pow_eq_exp hk, ← exp_add, e]
    congr 1
    simp only [ell, del]; ring
  rw [h2]; simp only [target]; ring

/-- The real-valued core: for pushed lists, the count is at least `P(K₂,ₙ, k)`. -/
theorem colConst_le_sum (hk : 300 ≤ k) (hn : n ≤ k ^ 2) {A B : Finset ℕ} {T : Fin n → Finset ℕ}
    (hA : A.card = k) (hB : B.card = k) (hTsub : ∀ w, T w ⊆ A ∪ B)
    (hT : ∀ w, (T w).card = k) :
    (k : ℝ) * ((k : ℝ) - 1) ^ n + (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) ^ n ≤
      ∑ a ∈ A, ∑ b ∈ B, pf T a b := by
  have hk3 : 3 ≤ k := by omega
  have hk' : (300 : ℝ) ≤ k := by exact_mod_cast hk
  have H := hyp_of hk hn
  have hrk : (A ∩ B).card ≤ k := hA ▸ card_le_card inter_subset_left
  rw [← pow_mul_target hk3]
  have hpow0 : (0 : ℝ) ≤ ((k : ℝ) - 1) ^ n := pow_nonneg (by linarith) n
  rcases Nat.eq_zero_or_pos (A ∩ B).card with h0 | h1
  · -- `r = 0`: all of `A × B` is private.
    have hAB : A ∩ B = ∅ := card_eq_zero.mp h0
    have hPc : ((A \ B).card : ℝ) = k := by
      rw [Finset.sdiff_eq_self_iff_disjoint.mpr (Finset.disjoint_iff_inter_eq_empty.mpr hAB), hA]
    have hQc : ((B \ A).card : ℝ) = k := by
      rw [Finset.sdiff_eq_self_iff_disjoint.mpr
        (Finset.disjoint_iff_inter_eq_empty.mpr (inter_comm B A ▸ hAB)), hB]
    have hsum3 : ∀ w, ((A ∩ B ∩ T w).card : ℝ) + ((A \ B ∩ T w).card : ℝ) +
        ((B \ A ∩ T w).card : ℝ) = k := fun w => by
      exact_mod_cast card_parts (hTsub w) (hT w)
    have hPQ := termPQ (r := 0) hk3 hT (by linarith) hPc hQc hsum3 (by ring)
      (fun w => by rw [hAB, empty_inter, card_empty, Nat.cast_zero])
      (fun w => by rw [← hPc]; exact_mod_cast card_le_card inter_subset_left)
      (fun w => by rw [← hQc]; exact_mod_cast card_le_card inter_subset_left)
    simp only [zero_div, zero_mul, sub_zero, div_zero, mul_zero] at hPQ
    have hsplit := sum_split A B (pf T)
    rw [hAB] at hsplit
    simp only [sum_empty, offDiag_empty, zero_add, sum_const_zero] at hsplit
    rw [hsplit]
    have hz := target_le_zero H
    calc ((k : ℝ) - 1) ^ n * target k (n * ell k) (n * del k)
        ≤ ((k : ℝ) - 1) ^ n * ((k : ℝ) ^ 2 * exp (-(n * del k / 4))) :=
          mul_le_mul_of_nonneg_left hz hpow0
      _ ≤ _ := by
          exact hPQ
  rcases Nat.lt_or_ge ((A ∩ B).card + 1) k with h2 | h2
  · -- `1 ≤ r ≤ k - 2`.
    have hle := target_le_lowerG H (r := (A ∩ B).card) (by exact_mod_cast h1)
      (by have : ((A ∩ B).card : ℝ) + 1 + 1 ≤ k := by exact_mod_cast h2
          linarith)
      (w := ell k * (n * (A ∩ B).card - ∑ w, ((A ∩ B ∩ T w).card : ℝ)) / (A ∩ B).card) (by
        apply div_nonneg _ (Nat.cast_nonneg _)
        apply mul_nonneg (ell_pos hk3).le
        have : ∑ w, ((A ∩ B ∩ T w).card : ℝ) ≤ ∑ _w : Fin n, ((A ∩ B).card : ℝ) :=
          sum_le_sum fun w _ => by exact_mod_cast card_le_card inter_subset_left
        rw [sum_const_fin] at this; linarith)
    exact (mul_le_mul_of_nonneg_left hle hpow0).trans
      (lowerG_le_sum hk3 hA hB hTsub hT h1 h2.le)
  rcases Nat.lt_or_ge (A ∩ B).card k with h3 | h3
  · -- `r = k - 1`: Kaul et al. Lemma 6.
    rw [pow_mul_target hk3]
    exact lemma6 hk3 hA hB hTsub hT (by omega)
  · -- `r = k`: every list is `A`.
    rw [pow_mul_target hk3]
    have hr : (A ∩ B).card = k := le_antisymm hrk h3
    have h := sum_ge_diag_add (T := T) hk3 hA hB hT
    have hD : ((k : ℝ)) * ((k : ℝ) - 1) ^ n ≤ ∑ a ∈ A ∩ B, pf T a a := by
      have : ∑ _a ∈ A ∩ B, ((k : ℝ) - 1) ^ n ≤ ∑ a ∈ A ∩ B, pf T a a :=
        sum_le_sum fun a _ => pf_diag_ge hk3 hT a
      rw [sum_const, hr, nsmul_eq_mul] at this; exact this
    rw [hr] at h
    nlinarith

/-- **`K₂,ₙ` is ECC at every `k ≥ 300` with `n ≤ k²`.** -/
theorem completeBipartite_two_eccAt_of_sq_le (hk : 300 ≤ k) (hn : n ≤ k ^ 2) :
    (completeBipartiteGraph (Fin 2) (Fin n)).ECCAt k := by
  intro L hL
  have hk3 : 3 ≤ k := by omega
  rw [K2n.colConst_K2n, col_completeBipartite_two_right]
  set A := L (Sum.inl 0)
  set B := L (Sum.inl 1)
  have hA : A.card = k := hL _
  have hB : B.card = k := hL _
  choose T' hT'sub hT'card hT'le using fun w => K2n.exists_push (B := B) hA (hL (Sum.inr w))
  refine le_trans ?_ (sum_le_sum fun a ha => sum_le_sum fun b hb =>
    prod_le_prod fun w _ => hT'le w a ha b hb)
  have key := colConst_le_sum hk hn hA hB hT'sub hT'card
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk3
  have e : ((k * (k - 1) ^ n + k * (k - 1) * (k - 2) ^ n : ℕ) : ℝ) =
      (k : ℝ) * ((k : ℝ) - 1) ^ n + (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) ^ n := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_sub (by omega : 2 ≤ k)]; ring
  have e2 : ((∑ a ∈ A, ∑ b ∈ B, ∏ w, (T' w \ {a, b}).card : ℕ) : ℝ) =
      ∑ a ∈ A, ∑ b ∈ B, pf T' a b := by
    push_cast; rfl
  exact_mod_cast (e ▸ e2 ▸ key)

/-- **`τ(K₂,ₙ) = O(√n)`**: `K₂,ₙ` is ECC at every `k ≥ 300` with `k > ⌊√n⌋`. -/
theorem completeBipartite_two_eccAt_of_sqrt_lt (hk : 300 ≤ k) (hkn : Nat.sqrt n < k) :
    (completeBipartiteGraph (Fin 2) (Fin n)).ECCAt k :=
  completeBipartite_two_eccAt_of_sq_le hk (by
    have := Nat.lt_succ_sqrt n
    have h : Nat.sqrt n + 1 ≤ k := hkn
    calc n ≤ (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := this.le
      _ ≤ k * k := Nat.mul_le_mul h h
      _ = k ^ 2 := (sq k).symm)

end MainTheorem

end SimpleGraph.TwoDegenerate.K2nSqrt
