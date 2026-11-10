/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.WitnessFour

/-!
# The witness laws for `k = 3`

This is Step 5 of the outerplanar proof draft
(`ai_research_notes/OUTERPLANAR_PROOF_DRAFT_2026-11-09.md`), a result of this repository's 2026-11
AI research collaboration, not from the literature.

* `witness_three_three`: the triangle, where the cover without the cut thread is a full 2-cover
  of capacity `2`. The law is that of the zero set of a colouring of the twisted cover, written
  out: masses `2, 1, 1, 3, 2` out of `9` on `{0, 2}, {2}, {0}, {1}, ∅`; the entropy inequality is
  `3 ^ 3 ≤ 2 ^ 5`.
* `witness_three_zero`: `n ≥ 4` with `g0 = 0`, so the law may not charge `∅`.
  - `n` even (`witness_three_even`): the law `h` of the zero set, with its unit of mass on `∅`
    moved by `∅ + {0, n - 1} → {0} + {n - 1}`, which keeps the marginals.
  - `n ≥ 7` odd (`witness_three_odd`): the two units on `∅` are moved by
    `∅ + {0, n - 1} → {0} + {n - 1}` and `∅ + {0, 2, n - 1} → {0, 2} + {n - 1}`.
  - `n = 5` (`witness_three_zero_five`): an explicit integer law of total mass `33` on the twelve
    nonempty good sets (found by `ai_research_notes/outerplanar/k3z5.py`); the entropy
    inequality is `3 ^ 21 * 5 ^ 5 ≤ 2 ^ 46`.

For the two general cases the sets that are not touched are compared with `arcW` class by class
(`ell_le_plain`, from the peeling bounds of `Outerplanar/WitnessCount.lean` at `r = 1`), the
touched ones one by one (`up_one`, `up_two`, `up_four`, `down_one`), and the class masses come
from the transfer count. With `M = 2 ^ (n - 1)` and `ε = 2 log 2 - 3 log (3 / 2) ≥ 0` what is left
is `(M - 2) ε ≥ 0` for `n` even and `(M - 64) ε + 3 (41 log 2 - 69 log (3 / 2)) ≥ 0` for `n` odd,
the last bracket being `3 ^ 69 ≤ 2 ^ 110`.
-/

namespace Outerplanar

open Finset

section Generic

variable {n : ℕ} [NeZero n]

/-- A witness from unnormalised weights `x` of total mass `C`. -/
theorem witness_of_weights {k m : ℕ} {g0 C K : ℝ} (hm : k - 1 = m) (hK : (k : ℝ) = K)
    (hC : 0 < C) (x : Finset (Fin n) → ℝ)
    (hx0 : ∀ J, 0 ≤ x J) (hsupp : ∀ J, 0 < x J → Good (-1) J ∧ 0 < gW m g0 J)
    (hsum : ∑ J, x J = C) (hmarg : ∀ i, ∑ J with i ∈ J, x J = C / K)
    (hent : 0 ≤ ∑ J, x J * Real.log (gW m g0 J / x J)) : Witness (n := n) k (-1) g0 C := by
  subst hm hK
  unfold Witness
  refine ⟨fun J => x J / C, fun J => div_nonneg (hx0 J) hC.le, ?_, ?_, ?_, ?_⟩
  · intro J hJ
    exact hsupp J ((div_pos_iff_of_pos_right hC).1 hJ)
  · rw [← Finset.sum_div, hsum, div_self hC.ne']
  · intro i
    rw [← Finset.sum_div, hmarg, div_right_comm, div_self hC.ne']
  · have e : ∀ J, x J / C * Real.log (gW (k - 1) g0 J / (x J / C)) =
        (x J * Real.log C + x J * Real.log (gW (k - 1) g0 J / x J)) / C := by
      intro J
      by_cases h : x J = 0
      · simp [h]
      · have hx := lt_of_le_of_ne (hx0 J) (Ne.symm h)
        have hg := (hsupp J hx).2
        have e' : gW (k - 1) g0 J / (x J / C) = C * (gW (k - 1) g0 J / x J) := by field_simp
        rw [e', Real.log_mul hC.ne' (div_pos hg hx).ne']
        ring
    rw [Finset.sum_congr rfl (fun J _ => e J), ← Finset.sum_div, sum_add_distrib, ← Finset.sum_mul,
      hsum, le_div_iff₀ hC]
    linarith

/-- The weights given by a list of sets with their masses. -/
noncomputable def listW (L : List (Finset (Fin n) × ℝ)) (J : Finset (Fin n)) : ℝ :=
  (L.map fun e => if e.1 = J then e.2 else 0).sum

omit [NeZero n] in
theorem listW_eq_zero {L : List (Finset (Fin n) × ℝ)} {J : Finset (Fin n)}
    (hJ : J ∉ L.map Prod.fst) : listW L J = 0 := by
  unfold listW
  refine List.sum_eq_zero fun y hy => ?_
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
  rw [ite_eq_right]
  exact fun h => hJ (List.mem_map.2 ⟨e, he, h⟩)

omit [NeZero n] in
theorem listW_nonneg {L : List (Finset (Fin n) × ℝ)} (hL : ∀ e ∈ L, 0 ≤ e.2)
    (J : Finset (Fin n)) : 0 ≤ listW L J := by
  unfold listW
  refine List.sum_nonneg fun y hy => ?_
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
  split_ifs
  · exact hL e he
  · exact le_rfl

omit [NeZero n] in
theorem sum_listW (L : List (Finset (Fin n) × ℝ)) (hnd : (L.map Prod.fst).Nodup)
    (F : Finset (Fin n) → ℝ → ℝ) (hF : ∀ J, F J 0 = 0) :
    ∑ J, F J (listW L J) = (L.map fun e => F e.1 e.2).sum := by
  induction L with
  | nil => simp [listW, hF]
  | cons e L ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    have h0 := listW_eq_zero hnd.1
    have hcons : ∀ J, listW (e :: L) J = (if e.1 = J then e.2 else 0) + listW L J := by
      intro J; simp [listW]
    rw [List.map_cons, List.sum_cons, ← ih hnd.2,
      ← Finset.add_sum_erase univ _ (mem_univ e.1), ← Finset.add_sum_erase univ _ (mem_univ e.1),
      hcons, h0, ite_eq_left rfl, add_zero, hF, zero_add]
    congr 1
    refine Finset.sum_congr rfl fun J hJ => ?_
    rw [hcons, ite_eq_right (Ne.symm (mem_erase.1 hJ).1), zero_add]

/-- A witness given by an explicit list of sets with their masses. -/
theorem witness_of_list {k m : ℕ} {g0 C K : ℝ} (hm : k - 1 = m) (hK : (k : ℝ) = K)
    (hC : 0 < C) (L : List (Finset (Fin n) × ℝ)) (hnd : (L.map Prod.fst).Nodup)
    (hL : ∀ e ∈ L, 0 ≤ e.2) (hgood : ∀ J ∈ L.map Prod.fst, Good (-1) J ∧ 0 < gW m g0 J)
    (hsum : (L.map Prod.snd).sum = C)
    (hmarg : ∀ i : Fin n, (L.map fun e => if i ∈ e.1 then e.2 else 0).sum = C / K)
    (hent : 0 ≤ (L.map fun e => e.2 * Real.log (gW m g0 e.1 / e.2)).sum) :
    Witness (n := n) k (-1) g0 C := by
  refine witness_of_weights hm hK hC (listW L) (listW_nonneg hL) ?_ ?_ ?_ ?_
  · intro J hJ
    by_contra h
    exact hJ.ne' (listW_eq_zero fun hmem => h (hgood J hmem))
  · rw [sum_listW L hnd (fun _ x => x) (fun _ => rfl)]; exact hsum
  · intro i
    rw [Finset.sum_filter,
      sum_listW L hnd (fun J x => if i ∈ J then x else 0) (fun _ => ite_self _)]
    exact hmarg i
  · rw [sum_listW L hnd (fun J x => x * Real.log (gW m g0 J / x)) (fun _ => zero_mul _)]
    exact hent

/-- For two colours `arcW` is a power of two. -/
theorem arcW_two (J : Finset (Fin n)) : arcW 2 J = 2 ^ #{i ∈ Jᶜ | i - 1 ∈ J} := by
  unfold arcW
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  norm_num

theorem gW_two {g0 : ℝ} {J : Finset (Fin n)} (hJ : J ≠ ∅) {c : ℕ}
    (hc : #{i ∈ Jᶜ | i - 1 ∈ J} = c) : gW 2 g0 J = 2 ^ c := by
  rw [gW, ite_eq_right hJ, arcW_two, hc]

theorem gW_two_pos {g0 : ℝ} {J : Finset (Fin n)} (hJ : J ≠ ∅) : 0 < gW 2 g0 J := by
  rw [gW_two hJ rfl]; positivity

end Generic

/-! ### The triangle -/

/-- k = 3, triangle, the cover without the cut thread is a full 2-cover (capacity 2). -/
theorem witness_three_three : Witness (n := 3) 3 (-1) 2 (lam 3 3) := by
  have hlam : lam 3 3 = 9 := by norm_num [lam]
  rw [hlam]
  refine witness_of_list (m := 2) (K := 3) rfl (by norm_num) (by norm_num)
    [({0, 2}, 2), ({2}, 1), ({0}, 1), ({1}, 3), (∅, 2)] ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · have hg : ∀ J ∈ [({0, 2} : Finset (Fin 3)), {2}, {0}, {1}, ∅], Good (-1) J := by
      unfold Good; decide
    intro J hJ
    refine ⟨hg J hJ, ?_⟩
    by_cases h : J = ∅
    · rw [gW, ite_eq_left h]; norm_num
    · exact gW_two_pos h
  · norm_num
  · intro i
    fin_cases i <;> simp <;> norm_num
  · have g1 : gW 2 2 ({0, 2} : Finset (Fin 3)) = 2 ^ 1 := gW_two (by decide) (by decide)
    have g2 : gW 2 2 ({2} : Finset (Fin 3)) = 2 ^ 1 := gW_two (by decide) (by decide)
    have g3 : gW 2 2 ({0} : Finset (Fin 3)) = 2 ^ 1 := gW_two (by decide) (by decide)
    have g4 : gW 2 2 ({1} : Finset (Fin 3)) = 2 ^ 1 := gW_two (by decide) (by decide)
    have g5 : gW 2 2 (∅ : Finset (Fin 3)) = 2 := by simp [gW]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, g1, g2, g3, g4, g5]
    have e : Real.log ((2 : ℝ) ^ 1 / 3) = Real.log 2 - Real.log 3 := by
      rw [pow_one, Real.log_div (by norm_num) (by norm_num)]
    have h32 : 3 * Real.log 3 ≤ 5 * Real.log 2 := by
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 3 ^ 3) (by norm_num : (3 : ℝ) ^ 3 ≤ 2 ^ 5)
      rwa [Real.log_pow, Real.log_pow] at this
    norm_num [e]
    linarith

/-! ### The pentagon -/

/-- k = 3, n = 5: an integer law on the twelve nonempty good sets. -/
theorem witness_three_zero_five : Witness (n := 5) 3 (-1) 0 (lam 3 5) := by
  have hlam : lam 3 5 = 33 := by norm_num [lam]
  rw [hlam]
  refine witness_of_list (m := 2) (K := 3) rfl (by norm_num) (by norm_num)
    [({4}, 2), ({3}, 3), ({2}, 3), ({2, 4}, 3), ({1}, 3), ({1, 4}, 3), ({1, 3}, 5), ({0}, 2),
      ({0, 4}, 1), ({0, 3}, 3), ({0, 2}, 3), ({0, 2, 4}, 2)] ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num
  · have hg : ∀ J ∈ [({4} : Finset (Fin 5)), {3}, {2}, {2, 4}, {1}, {1, 4}, {1, 3}, {0},
        {0, 4}, {0, 3}, {0, 2}, {0, 2, 4}], Good (-1) J ∧ J ≠ ∅ := by
      unfold Good; decide
    intro J hJ
    exact ⟨(hg J hJ).1, gW_two_pos (hg J hJ).2⟩
  · norm_num
  · intro i
    fin_cases i <;> simp <;> norm_num
  · have g1 : gW 2 0 ({4} : Finset (Fin 5)) = 2 ^ 1 := gW_two (by decide) (by decide)
    have g2 : gW 2 0 ({3} : Finset (Fin 5)) = 2 ^ 1 := gW_two (by decide) (by decide)
    have g3 : gW 2 0 ({2} : Finset (Fin 5)) = 2 ^ 1 := gW_two (by decide) (by decide)
    have g4 : gW 2 0 ({2, 4} : Finset (Fin 5)) = 2 ^ 2 := gW_two (by decide) (by decide)
    have g5 : gW 2 0 ({1} : Finset (Fin 5)) = 2 ^ 1 := gW_two (by decide) (by decide)
    have g6 : gW 2 0 ({1, 4} : Finset (Fin 5)) = 2 ^ 2 := gW_two (by decide) (by decide)
    have g7 : gW 2 0 ({1, 3} : Finset (Fin 5)) = 2 ^ 2 := gW_two (by decide) (by decide)
    have g8 : gW 2 0 ({0} : Finset (Fin 5)) = 2 ^ 1 := gW_two (by decide) (by decide)
    have g9 : gW 2 0 ({0, 4} : Finset (Fin 5)) = 2 ^ 1 := gW_two (by decide) (by decide)
    have g10 : gW 2 0 ({0, 3} : Finset (Fin 5)) = 2 ^ 2 := gW_two (by decide) (by decide)
    have g11 : gW 2 0 ({0, 2} : Finset (Fin 5)) = 2 ^ 2 := gW_two (by decide) (by decide)
    have g12 : gW 2 0 ({0, 2, 4} : Finset (Fin 5)) = 2 ^ 2 := gW_two (by decide) (by decide)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, g1, g2, g3, g4, g5, g6,
      g7, g8, g9, g10, g11, g12]
    have e13 : Real.log ((2 : ℝ) ^ 1 / 3) = Real.log 2 - Real.log 3 := by
      rw [pow_one, Real.log_div (by norm_num) (by norm_num)]
    have e23 : Real.log ((2 : ℝ) ^ 2 / 3) = 2 * Real.log 2 - Real.log 3 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_pow]; norm_num
    have e25 : Real.log ((2 : ℝ) ^ 2 / 5) = 2 * Real.log 2 - Real.log 5 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_pow]; norm_num
    have e12 : Real.log ((2 : ℝ) ^ 1 / 2) = 0 := by norm_num
    have e11 : Real.log ((2 : ℝ) ^ 1 / 1) = Real.log 2 := by norm_num
    have e22 : Real.log ((2 : ℝ) ^ 2 / 2) = Real.log 2 := by norm_num
    have key : 21 * Real.log 3 + 5 * Real.log 5 ≤ 46 * Real.log 2 := by
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 3 ^ 21 * 5 ^ 5)
        (by norm_num : (3 : ℝ) ^ 21 * 5 ^ 5 ≤ 2 ^ 46)
      rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow, Real.log_pow]
        at this
      norm_num at this
      exact this
    rw [e13, e23, e25, e12, e11, e22]
    linarith

/-! ### Three colours: the twisted cover and its class bounds -/

section Three

variable {n : ℕ} [NeZero n]

theorem h3_le_both {J : Finset (Fin n)} (h0 : 0 ∈ J) (h1 : -1 ∈ J) :
    (hcount n 1 J : ℝ) ≤ arcW 2 J := by
  have e : (phi 1 Jᶜ : ℝ) = arcW 2 J := phi_compl_eq (Or.inl h0)
  rw [← e]
  exact_mod_cast (hcount_le_part J).trans (peel_both h0 h1)

theorem h3_le_one (hn : 2 ≤ n) {J : Finset (Fin n)}
    (h : (0 ∈ J ∧ -1 ∉ J) ∨ (0 ∉ J ∧ -1 ∈ J)) : 2 * (hcount n 1 J : ℝ) ≤ arcW 2 J := by
  have hle : (hcount n 1 J : ℝ) ≤ #(part n 1 Jᶜ) := by exact_mod_cast hcount_le_part J
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have e : (phi 1 Jᶜ : ℝ) = arcW 2 J := phi_compl_eq (Or.inl h0)
    have p : (#(part n 1 Jᶜ) : ℝ) * (1 + 1) ≤ 1 * phi 1 Jᶜ := by
      exact_mod_cast peel_last (r := 1) hn h0 h1
    rw [← e]; linarith
  · have e : (phi 1 Jᶜ : ℝ) = arcW 2 J := phi_compl_eq (Or.inr h1)
    have p : (#(part n 1 Jᶜ) : ℝ) * (1 + 1) ≤ 1 * phi 1 Jᶜ := by
      exact_mod_cast peel_zero (r := 1) hn h0 h1
    rw [← e]; linarith

theorem h3_le_none (hn : 3 ≤ n) {J : Finset (Fin n)} (h0 : 0 ∉ J) (h1 : -1 ∉ J) (hJ : J ≠ ∅) :
    2 * (hcount n 1 J : ℝ) ≤ 3 * arcW 2 J := by
  have hle : (hcount n 1 J : ℝ) ≤ #(part n 1 Jᶜ) := by exact_mod_cast hcount_le_part J
  obtain ⟨j, hj⟩ := nonempty_iff_ne_empty.2 hJ
  have e : (phi 1 Jᶜ : ℝ) * (1 : ℕ) = arcW 2 J * (((1 : ℕ) : ℝ) + 1) := phi_compl_mul h0 h1
  have p : (#(part n 1 Jᶜ) : ℝ) * ((1 + 1) * (1 + 1)) ≤ (1 * (1 + 1) + 1) * phi 1 Jᶜ := by
    exact_mod_cast peel_none (r := 1) hn h0 h1 hj
  push_cast at e
  linarith

/-- A good set containing both ends of the path is the zero set of a colouring. -/
theorem hcount_pos_both {J : Finset (Fin n)} (hJ : Good (-1) J) (h0 : 0 ∈ J) (h1 : -1 ∈ J) :
    0 < hcount n 1 J := by
  let f : Fin n → Fin (1 + 2) := fun i => if i ∈ J then 0 else if (i : ℕ) % 2 = 0 then 1 else 2
  have hf0 : ∀ i, i ∈ J → f i = 0 := fun i hi => by simp only [f, hi, ite_true]
  have hfn : ∀ i, i ∉ J → f i ≠ 0 := by
    intro i hi
    simp only [f, hi, ite_false]
    split_ifs <;> decide
  unfold hcount
  refine Finset.card_pos.2 ⟨f, ?_⟩
  rw [mem_filter, mem_twist]
  refine ⟨⟨fun i hi => ?_, ?_⟩, ?_⟩
  · by_cases hiJ : i ∈ J
    · rw [hf0 i hiJ]; exact (hfn _ (hJ i hi hiJ)).symm
    · by_cases hiJ' : i + 1 ∈ J
      · rw [hf0 _ hiJ']; exact hfn i hiJ
      · have hv := fin_val_add_one hi
        simp only [f, hiJ, hiJ', ite_false, hv]
        rcases Nat.mod_two_eq_zero_or_one (i : ℕ) with h | h
        · have h' : ((i : ℕ) + 1) % 2 ≠ 0 := by omega
          simp only [h, h', ite_true, ite_false]; decide
        · have h' : ((i : ℕ) + 1) % 2 = 0 := by omega
          have h'' : (i : ℕ) % 2 ≠ 0 := by omega
          simp only [h', h'', ite_true, ite_false]; decide
  · rw [hf0 0 h0, hf0 _ h1]; decide
  · ext i
    rw [mem_zset]
    exact ⟨fun h => by_contra fun hi => hfn i hi h, hf0 i⟩

/-- If no two elements of `J` are cyclically consecutive, every element starts an arc. -/
theorem arcW_two_indep {J : Finset (Fin n)} (hJ : ∀ j ∈ J, j + 1 ∉ J) : arcW 2 J = 2 ^ #J := by
  rw [arcW_two]
  congr 1
  have : {i ∈ Jᶜ | i - 1 ∈ J} = J.image (· + 1) := by
    ext i
    rw [mem_filter, mem_compl, mem_image]
    constructor
    · rintro ⟨_, h⟩; exact ⟨i - 1, h, sub_add_cancel i 1⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨hJ j hj, by rwa [add_sub_cancel_right]⟩
  rw [this, card_image_of_injective _ (add_left_injective 1)]

/-- The logarithm of the class constant: `0` if both ends are in `J`, `log 2` if one is,
`- log (3 / 2)` if none is. -/
noncomputable def ell (J : Finset (Fin n)) : ℝ :=
  -Real.log (3 / 2) + (Real.log 2 + Real.log (3 / 2)) * (if (0 : Fin n) ∈ J then 1 else 0) +
    (Real.log 2 + Real.log (3 / 2)) * (if (-1 : Fin n) ∈ J then 1 else 0) +
    (-2 * Real.log 2 - Real.log (3 / 2)) * (if (0 : Fin n) ∈ J ∧ (-1 : Fin n) ∈ J then 1 else 0)

theorem ell_both {J : Finset (Fin n)} (h0 : 0 ∈ J) (h1 : -1 ∈ J) : ell J = 0 := by
  simp only [ell, h0, h1, and_self, ite_true]; ring

theorem ell_one {J : Finset (Fin n)} (h : (0 ∈ J ∧ -1 ∉ J) ∨ (0 ∉ J ∧ -1 ∈ J)) :
    ell J = Real.log 2 := by
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
    simp only [ell, h0, h1, and_false, false_and, ite_true, ite_false] <;> ring

theorem ell_none {J : Finset (Fin n)} (h0 : 0 ∉ J) (h1 : -1 ∉ J) :
    ell J = -Real.log (3 / 2) := by
  simp only [ell, h0, h1, and_self, ite_false]; ring

theorem log_two_thirds : Real.log (2 / 3) = -Real.log (3 / 2) := by
  rw [← Real.log_inv]; norm_num

/-- The entropy term of an unmodified set. -/
theorem ell_le_plain (hn : 3 ≤ n) {J : Finset (Fin n)} (hJ : J ≠ ∅) :
    (hcount n 1 J : ℝ) * ell J ≤
      (hcount n 1 J : ℝ) * Real.log (arcW 2 J / (hcount n 1 J : ℝ)) := by
  by_cases hz : hcount n 1 J = 0
  · simp [hz]
  have hpos : (0 : ℝ) < hcount n 1 J := Nat.cast_pos.2 (Nat.pos_of_ne_zero hz)
  refine mul_le_mul_of_nonneg_left ?_ hpos.le
  by_cases h0 : (0 : Fin n) ∈ J
  · by_cases h1 : (-1 : Fin n) ∈ J
    · rw [ell_both h0 h1]
      exact Real.log_nonneg ((one_le_div hpos).2 (h3_le_both h0 h1))
    · rw [ell_one (Or.inl ⟨h0, h1⟩)]
      refine Real.log_le_log (by norm_num) ((le_div_iff₀ hpos).2 ?_)
      exact h3_le_one (by omega) (Or.inl ⟨h0, h1⟩)
  · by_cases h1 : (-1 : Fin n) ∈ J
    · rw [ell_one (Or.inr ⟨h0, h1⟩)]
      refine Real.log_le_log (by norm_num) ((le_div_iff₀ hpos).2 ?_)
      exact h3_le_one (by omega) (Or.inr ⟨h0, h1⟩)
    · rw [ell_none h0 h1, ← log_two_thirds]
      refine Real.log_le_log (by norm_num) ((le_div_iff₀ hpos).2 ?_)
      have := h3_le_none hn h0 h1 hJ
      linarith

/-- The masses of the classes for three colours. -/
theorem masses_three {j : ℕ} (hn : n = j + 1) :
    (∑ J, (hcount n 1 J : ℝ) = 2 * 2 ^ j + (-1) ^ j) ∧
    (∀ i : Fin n, 3 * ∑ J with i ∈ J, (hcount n 1 J : ℝ) = 2 * 2 ^ j + (-1) ^ j) ∧
    (3 * ∑ J with ((0 : Fin n) ∈ J ∧ (-1 : Fin n) ∈ J), (hcount n 1 J : ℝ) =
      2 ^ j + (-1) ^ j * 2) ∧
    2 * (hcount n 1 ∅ : ℝ) = 3 + (-1) ^ j := by
  have hD : (#(twist n 1) : ℝ) = 2 * 2 ^ j + (-1) ^ j := by
    rw [twist_card_real hn]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Nat.cast_sum, sum_hcount_univ, hD]
  · intro i
    rw [← Nat.cast_sum, sum_hcount_mem, ← hD, ← card_twist_fiber i]
    push_cast; ring
  · rw [← Nat.cast_sum, sum_hcount_both]
    have := twist_both_real (r := 1) hn
    norm_num at this ⊢
    linarith
  · rw [hcount_empty]
    have := twist_nozero_real' (r := 1) hn le_rfl
    norm_num at this ⊢
    linarith

/-- The class-weighted mass in closed form. -/
theorem sum_ell {j : ℕ} (hn : n = j + 1) :
    3 * ∑ J, (hcount n 1 J : ℝ) * ell J =
      -3 * Real.log (3 / 2) * (2 * 2 ^ j + (-1) ^ j) +
        2 * (Real.log 2 + Real.log (3 / 2)) * (2 * 2 ^ j + (-1) ^ j) +
        (-2 * Real.log 2 - Real.log (3 / 2)) * (2 ^ j + (-1) ^ j * 2) := by
  obtain ⟨h1, h2, h3, -⟩ := masses_three hn
  have e : ∀ J : Finset (Fin n), (hcount n 1 J : ℝ) * ell J =
      (hcount n 1 J : ℝ) * (-Real.log (3 / 2)) +
      (hcount n 1 J : ℝ) * ((Real.log 2 + Real.log (3 / 2)) * if (0 : Fin n) ∈ J then 1 else 0) +
      (hcount n 1 J : ℝ) * ((Real.log 2 + Real.log (3 / 2)) * if (-1 : Fin n) ∈ J then 1 else 0) +
      (hcount n 1 J : ℝ) * ((-2 * Real.log 2 - Real.log (3 / 2)) *
        if (0 : Fin n) ∈ J ∧ (-1 : Fin n) ∈ J then 1 else 0) := fun J => by
    rw [ell]; ring
  rw [Finset.sum_congr rfl (fun J _ => e J)]
  simp only [sum_add_distrib, sum_mul_ind, ← Finset.sum_mul, h1]
  have h20 := h2 0
  have h21 := h2 (-1)
  linear_combination (Real.log 2 + Real.log (3 / 2)) * h20 +
    (Real.log 2 + Real.log (3 / 2)) * h21 + (-2 * Real.log 2 - Real.log (3 / 2)) * h3

/-- Indicator of a set of vertices among all sets. -/
noncomputable def ind (S J : Finset (Fin n)) : ℝ := if J = S then 1 else 0

omit [NeZero n] in
theorem ind_self (S : Finset (Fin n)) : ind S S = 1 := by simp [ind]

omit [NeZero n] in
theorem ind_of_ne {S J : Finset (Fin n)} (h : J ≠ S) : ind S J = 0 := by simp [ind, h]

omit [NeZero n] in
theorem sum_ind (c : ℝ) (S : Finset (Fin n)) : ∑ J, c * ind S J = c := by
  simp [ind]

omit [NeZero n] in
theorem sum_ind_mem (c : ℝ) (S : Finset (Fin n)) (i : Fin n) :
    ∑ J with i ∈ J, c * ind S J = if i ∈ S then c else 0 := by
  rw [Finset.sum_filter]
  simp only [ind, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single S]
  · simp
  · intro J _ hJ; simp [hJ]
  · intro h; exact absurd (mem_univ _) h

/-- The common part of the two tweaked laws: the law of the zero set with masses `t` added. -/
theorem witness_three_of_tweak {j : ℕ} (hn : n = j + 1) (t cost : Finset (Fin n) → ℝ)
    (H1 : ∀ J, 0 ≤ (hcount n 1 J : ℝ) + t J) (H2 : (hcount n 1 ∅ : ℝ) + t ∅ = 0)
    (H3 : ∀ J, 0 < (hcount n 1 J : ℝ) + t J → Good (-1) J)
    (H4 : ∑ J, t J = 0) (H5 : ∀ i, ∑ J with i ∈ J, t J = 0)
    (H6 : ∀ J, (hcount n 1 J : ℝ) * ell J - cost J ≤
      ((hcount n 1 J : ℝ) + t J) * Real.log (gW 2 0 J / ((hcount n 1 J : ℝ) + t J)))
    (H7 : ∑ J, cost J ≤ ∑ J, (hcount n 1 J : ℝ) * ell J) :
    Witness (n := n) 3 (-1) 0 (lam 3 n) := by
  obtain ⟨h1, h2, -, -⟩ := masses_three hn
  have hσ := neg_one_pow_eq_or ℝ j
  have hlam : lam 3 n = 2 * 2 ^ j + (-1) ^ j := by
    rw [lam, hn, pow_succ, pow_succ]; norm_num; ring
  have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hlam0 : 0 < lam 3 n := by
    rcases hσ with h | h <;> rw [hlam, h] <;> linarith
  refine witness_of_weights (m := 2) (K := 3) rfl (by norm_num) hlam0
    (fun J => (hcount n 1 J : ℝ) + t J) H1 ?_ ?_ ?_ ?_
  · intro J hJ
    refine ⟨H3 J hJ, gW_two_pos ?_⟩
    rintro rfl
    rw [H2] at hJ
    exact lt_irrefl _ hJ
  · rw [sum_add_distrib, H4, h1, hlam, add_zero]
  · intro i
    rw [sum_add_distrib, H5, add_zero, hlam, eq_div_iff (by norm_num), ← h2 i]
    ring
  · have := Finset.sum_le_sum fun J (_ : J ∈ (univ : Finset (Finset (Fin n)))) => H6 J
    rw [Finset.sum_sub_distrib] at this
    linarith

end Three

section Points

variable {n : ℕ} [NeZero n]

theorem log_two_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem log_three_halves : Real.log (3 / 2) = Real.log 3 - Real.log 2 :=
  Real.log_div (by norm_num) (by norm_num)

theorem log_three_halves_nonneg : 0 ≤ Real.log (3 / 2) := Real.log_nonneg (by norm_num)

theorem eps_nonneg : 0 ≤ 2 * Real.log 2 - 3 * Real.log (3 / 2) := by
  have := Real.log_le_log (by norm_num : (0 : ℝ) < 3 ^ 3) (by norm_num : (3 : ℝ) ^ 3 ≤ 2 ^ 5)
  rw [Real.log_pow, Real.log_pow] at this
  rw [log_three_halves]
  norm_num at this
  linarith

theorem gW_of_one {J : Finset (Fin n)} (h : (0 ∈ J ∧ -1 ∉ J) ∨ (0 ∉ J ∧ -1 ∈ J)) :
    gW 2 0 J = arcW 2 J := by
  have hJ : J ≠ ∅ := by
    rintro rfl
    rcases h with ⟨h0, -⟩ | ⟨-, h1⟩
    · exact notMem_empty _ h0
    · exact notMem_empty _ h1
  rw [gW, ite_eq_right hJ]

/-- A set with one end, one arc: one more colouring. -/
theorem up_one (hn : 2 ≤ n) {J : Finset (Fin n)} (h : (0 ∈ J ∧ -1 ∉ J) ∨ (0 ∉ J ∧ -1 ∈ J))
    (hg : arcW 2 J = 2) :
    (hcount n 1 J : ℝ) * ell J - Real.log 2 ≤
      ((hcount n 1 J : ℝ) + 1) * Real.log (gW 2 0 J / ((hcount n 1 J : ℝ) + 1)) := by
  have hle := h3_le_one hn h
  rw [hg] at hle
  have hle' : hcount n 1 J ≤ 1 := by
    have : (hcount n 1 J : ℝ) ≤ 1 := by linarith
    exact_mod_cast this
  have hL := log_two_pos'
  rw [gW_of_one h, hg, ell_one h]
  obtain h | h : hcount n 1 J = 0 ∨ hcount n 1 J = 1 := by omega
  · rw [h]; norm_num; linarith
  · rw [h]; norm_num

/-- A set with one end, one arc: two more colourings. -/
theorem up_two (hn : 2 ≤ n) {J : Finset (Fin n)} (h : (0 ∈ J ∧ -1 ∉ J) ∨ (0 ∉ J ∧ -1 ∈ J))
    (hg : arcW 2 J = 2) :
    (hcount n 1 J : ℝ) * ell J - (Real.log 2 + 3 * Real.log (3 / 2)) ≤
      ((hcount n 1 J : ℝ) + 2) * Real.log (gW 2 0 J / ((hcount n 1 J : ℝ) + 2)) := by
  have hle := h3_le_one hn h
  rw [hg] at hle
  have hle' : hcount n 1 J ≤ 1 := by
    have : (hcount n 1 J : ℝ) ≤ 1 := by linarith
    exact_mod_cast this
  have hL := log_two_pos'
  have hL' := log_three_halves_nonneg
  rw [gW_of_one h, hg, ell_one h]
  obtain h | h : hcount n 1 J = 0 ∨ hcount n 1 J = 1 := by omega
  · rw [h]
    have e : ((0 : ℕ) : ℝ) + 2 = 2 := by norm_num
    rw [e, div_self (by norm_num), Real.log_one]
    norm_num; linarith
  · rw [h]
    have e : ((1 : ℕ) : ℝ) + 2 = 3 := by norm_num
    rw [e, log_two_thirds]
    norm_num

/-- A set with one end, two arcs: one more colouring. -/
theorem up_four (hn : 2 ≤ n) {J : Finset (Fin n)} (h : (0 ∈ J ∧ -1 ∉ J) ∨ (0 ∉ J ∧ -1 ∈ J))
    (hg : arcW 2 J = 4) :
    (hcount n 1 J : ℝ) * ell J - (3 * Real.log (3 / 2) - Real.log 2) ≤
      ((hcount n 1 J : ℝ) + 1) * Real.log (gW 2 0 J / ((hcount n 1 J : ℝ) + 1)) := by
  have hle := h3_le_one hn h
  rw [hg] at hle
  have hle' : hcount n 1 J ≤ 2 := by
    have : (hcount n 1 J : ℝ) ≤ 2 := by linarith
    exact_mod_cast this
  have hL := log_two_pos'
  have hL' := log_three_halves_nonneg
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h43 : Real.log (4 / 3) = Real.log 2 - Real.log (3 / 2) := by
    rw [log_three_halves, Real.log_div (by norm_num) (by norm_num), h4]; ring
  rw [gW_of_one h, hg, ell_one h]
  obtain h | h | h : hcount n 1 J = 0 ∨ hcount n 1 J = 1 ∨ hcount n 1 J = 2 := by omega
  · rw [h]
    have e : (4 : ℝ) / (((0 : ℕ) : ℝ) + 1) = 4 := by norm_num
    rw [e, h4]; norm_num; linarith
  · rw [h]
    have e : (4 : ℝ) / (((1 : ℕ) : ℝ) + 1) = 2 := by norm_num
    rw [e]; norm_num; linarith
  · rw [h]
    have e : (4 : ℝ) / (((2 : ℕ) : ℝ) + 1) = 4 / 3 := by norm_num
    rw [e, h43]; norm_num; linarith

/-- A set with both ends: one colouring fewer. -/
theorem down_one {J : Finset (Fin n)} (h0 : 0 ∈ J) (h1 : -1 ∈ J) (hpos : 0 < hcount n 1 J) :
    (hcount n 1 J : ℝ) * ell J - 0 ≤
      ((hcount n 1 J : ℝ) + -1) * Real.log (gW 2 0 J / ((hcount n 1 J : ℝ) + -1)) := by
  have hJ : J ≠ ∅ := fun h => notMem_empty _ (h ▸ h0)
  have hle := h3_le_both h0 h1
  have h1' : (1 : ℝ) ≤ hcount n 1 J := by exact_mod_cast hpos
  rw [ell_both h0 h1, mul_zero, sub_zero, gW, ite_eq_right hJ]
  rcases eq_or_lt_of_le h1' with h | h
  · rw [← h]; norm_num
  · have hx : (0 : ℝ) < (hcount n 1 J : ℝ) + -1 := by linarith
    exact mul_nonneg hx.le (Real.log_nonneg ((one_le_div hx).2 (by linarith)))

end Points

section Even

variable {n : ℕ} [NeZero n]

/-- `n` even: the unit of mass on `∅` is moved to `{0}` and `{n - 1}`, and one unit is taken
from `{0, n - 1}`. -/
theorem witness_three_even {j : ℕ} (hn : n = j + 1) (hj : Odd j) (hj3 : 3 ≤ j) :
    Witness (n := n) 3 (-1) 0 (lam 3 n) := by
  have hn4 : 4 ≤ n := by omega
  have hσ : (-1 : ℝ) ^ j = -1 := hj.neg_one_pow
  obtain ⟨-, -, -, hh0⟩ := masses_three hn
  have hE : (hcount n 1 ∅ : ℝ) = 1 := by rw [hσ] at hh0; linarith
  have h0m : (0 : Fin n) ≠ -1 := (fin_neg_one_ne_zero (by omega)).symm
  have h0v : ((0 : Fin n) : ℕ) = 0 := by simp
  have hmv := fin_val_neg_one (n := n)
  have h1v : ((0 + 1 : Fin n) : ℕ) = 1 := by rw [fin_val_add_one h0m, h0v]
  have h10 : (0 + 1 : Fin n) ≠ 0 := Fin.ne_of_val_ne (by rw [h1v, h0v]; omega)
  have h1m : (0 + 1 : Fin n) ≠ -1 := Fin.ne_of_val_ne (by rw [h1v, hmv]; omega)
  have hm0 : (-1 + 1 : Fin n) = 0 := neg_add_cancel 1
  -- the special sets are distinct
  have hEA : (∅ : Finset (Fin n)) ≠ {0} := (singleton_ne_empty _).symm
  have hEB : (∅ : Finset (Fin n)) ≠ {-1} := (singleton_ne_empty _).symm
  have hEC : (∅ : Finset (Fin n)) ≠ {0, -1} := (insert_ne_empty _ _).symm
  have hAB : ({0} : Finset (Fin n)) ≠ {-1} := fun h => h0m (singleton_injective h)
  have hAC : ({0} : Finset (Fin n)) ≠ {0, -1} := fun h => by
    have := Finset.ext_iff.1 h (-1); simp [h0m.symm] at this
  have hBC : ({-1} : Finset (Fin n)) ≠ {0, -1} := fun h => by
    have := Finset.ext_iff.1 h 0; simp [h0m] at this
  -- they are good
  have gA : Good (-1) ({0} : Finset (Fin n)) := by
    intro i _ hi hi'
    rw [mem_singleton] at hi hi'
    rw [hi] at hi'; exact h10 hi'
  have gB : Good (-1) ({-1} : Finset (Fin n)) := fun i hi hi' _ => hi (mem_singleton.1 hi')
  have gC : Good (-1) ({0, -1} : Finset (Fin n)) := by
    intro i hi hiJ hiJ'
    rw [mem_insert, mem_singleton] at hiJ hiJ'
    rcases hiJ with rfl | rfl
    · exact hiJ'.elim h10 h1m
    · exact hi rfl
  have wA : arcW 2 ({0} : Finset (Fin n)) = 2 := by
    rw [arcW_two_indep, card_singleton, pow_one]
    intro i hi hi'
    rw [mem_singleton] at hi hi'
    rw [hi] at hi'; exact h10 hi'
  have wB : arcW 2 ({-1} : Finset (Fin n)) = 2 := by
    rw [arcW_two_indep, card_singleton, pow_one]
    intro i hi hi'
    rw [mem_singleton] at hi hi'
    rw [hi, hm0] at hi'; exact h0m hi'
  have cA : ((0 : Fin n) ∈ ({0} : Finset (Fin n)) ∧ (-1 : Fin n) ∉ ({0} : Finset (Fin n))) ∨
      ((0 : Fin n) ∉ ({0} : Finset (Fin n)) ∧ (-1 : Fin n) ∈ ({0} : Finset (Fin n))) :=
    Or.inl ⟨mem_singleton_self _, fun h => h0m (mem_singleton.1 h).symm⟩
  have cB : ((0 : Fin n) ∈ ({-1} : Finset (Fin n)) ∧ (-1 : Fin n) ∉ ({-1} : Finset (Fin n))) ∨
      ((0 : Fin n) ∉ ({-1} : Finset (Fin n)) ∧ (-1 : Fin n) ∈ ({-1} : Finset (Fin n))) :=
    Or.inr ⟨fun h => h0m (mem_singleton.1 h), mem_singleton_self _⟩
  have c0C : (0 : Fin n) ∈ ({0, -1} : Finset (Fin n)) := mem_insert_self _ _
  have c1C : (-1 : Fin n) ∈ ({0, -1} : Finset (Fin n)) := mem_insert_of_mem (mem_singleton_self _)
  have pC := hcount_pos_both gC c0C c1C
  obtain ⟨t, ht⟩ : ∃ t : Finset (Fin n) → ℝ, t = fun J =>
      (-1) * ind ∅ J + 1 * ind {0} J + 1 * ind {-1} J + (-1) * ind {0, -1} J := ⟨_, rfl⟩
  obtain ⟨cost, hc⟩ : ∃ cost : Finset (Fin n) → ℝ, cost = fun J =>
      (-Real.log (3 / 2)) * ind ∅ J + Real.log 2 * ind {0} J + Real.log 2 * ind {-1} J :=
    ⟨_, rfl⟩
  have hcases : ∀ J : Finset (Fin n),
      (J = ∅ ∧ t J = -1 ∧ cost J = -Real.log (3 / 2)) ∨
      (J = {0} ∧ t J = 1 ∧ cost J = Real.log 2) ∨
      (J = {-1} ∧ t J = 1 ∧ cost J = Real.log 2) ∨
      (J = {0, -1} ∧ t J = -1 ∧ cost J = 0) ∨
      (J ≠ ∅ ∧ J ≠ {0} ∧ J ≠ {-1} ∧ J ≠ {0, -1} ∧ t J = 0 ∧ cost J = 0) := by
    intro J
    by_cases h1 : J = ∅
    · left; subst h1
      refine ⟨rfl, ?_, ?_⟩ <;>
        simp only [ht, hc, ind_self, ind_of_ne hEA, ind_of_ne hEB, ind_of_ne hEC] <;> ring
    right
    by_cases h2 : J = {0}
    · left; subst h2
      refine ⟨rfl, ?_, ?_⟩ <;>
        simp only [ht, hc, ind_self, ind_of_ne h1, ind_of_ne hAB, ind_of_ne hAC] <;> ring
    right
    by_cases h3 : J = {-1}
    · left; subst h3
      refine ⟨rfl, ?_, ?_⟩ <;>
        simp only [ht, hc, ind_self, ind_of_ne h1, ind_of_ne h2, ind_of_ne hBC] <;> ring
    right
    by_cases h4 : J = {0, -1}
    · left; subst h4
      refine ⟨rfl, ?_, ?_⟩ <;>
        simp only [ht, hc, ind_self, ind_of_ne h1, ind_of_ne h2, ind_of_ne h3] <;> ring
    right
    refine ⟨h1, h2, h3, h4, ?_, ?_⟩ <;>
      simp only [ht, hc, ind_of_ne h1, ind_of_ne h2, ind_of_ne h3, ind_of_ne h4] <;> ring
  refine witness_three_of_tweak hn t cost ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro J
    have hnn : (0 : ℝ) ≤ hcount n 1 J := Nat.cast_nonneg _
    rcases hcases J with ⟨rfl, ht', -⟩ | ⟨rfl, ht', -⟩ | ⟨rfl, ht', -⟩ | ⟨rfl, ht', -⟩ |
      ⟨-, -, -, -, ht', -⟩ <;> rw [ht']
    · rw [hE]; norm_num
    · linarith
    · linarith
    · have : (1 : ℝ) ≤ hcount n 1 ({0, -1} : Finset (Fin n)) := by exact_mod_cast pC
      linarith
    · linarith
  · rcases hcases ∅ with ⟨-, ht', -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rw [ht', hE]; norm_num
    · exact absurd h hEA
    · exact absurd h hEB
    · exact absurd h hEC
    · exact absurd rfl h
  · intro J hJ
    rcases hcases J with ⟨rfl, ht', -⟩ | ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ |
      ⟨-, -, -, -, ht', -⟩
    · rw [ht', hE] at hJ; norm_num at hJ
    · exact gA
    · exact gB
    · exact gC
    · rw [ht', add_zero] at hJ
      exact good_of_hcount_pos (Nat.cast_pos.1 hJ)
  · simp only [ht, sum_add_distrib, sum_ind]; norm_num
  · intro i
    simp only [ht, sum_add_distrib, sum_ind_mem, notMem_empty, mem_singleton, mem_insert,
      ite_false]
    by_cases hi0 : i = 0
    · subst hi0; simp [h0m]
    · by_cases hi1 : i = -1
      · subst hi1; simp [h0m.symm]
      · simp [hi0, hi1]
  · intro J
    rcases hcases J with ⟨rfl, ht', hc'⟩ | ⟨rfl, ht', hc'⟩ | ⟨rfl, ht', hc'⟩ | ⟨rfl, ht', hc'⟩ |
      ⟨h1, -, -, -, ht', hc'⟩ <;> rw [ht', hc']
    · rw [hE, ell_none (notMem_empty _) (notMem_empty _)]; norm_num
    · exact up_one (by omega) cA wA
    · exact up_one (by omega) cB wB
    · exact down_one c0C c1C pC
    · rw [sub_zero, add_zero, gW, ite_eq_right h1]
      exact ell_le_plain (by omega) h1
  · have hs := sum_ell (n := n) hn
    rw [hσ] at hs
    have hM : (2 : ℝ) ≤ 2 ^ j := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one _).symm
        _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
    have hprod := mul_nonneg (sub_nonneg.2 hM) eps_nonneg
    have hcs : ∑ J, cost J = -Real.log (3 / 2) + Real.log 2 + Real.log 2 := by
      simp only [hc, sum_add_distrib, sum_ind]
    rw [hcs]
    nlinarith

end Even

section Odd

variable {n : ℕ} [NeZero n]

theorem key_odd : 0 ≤ 41 * Real.log 2 - 69 * Real.log (3 / 2) := by
  have := Real.log_le_log (by norm_num : (0 : ℝ) < 3 ^ 69) (by norm_num : (3 : ℝ) ^ 69 ≤ 2 ^ 110)
  rw [Real.log_pow, Real.log_pow] at this
  rw [log_three_halves]
  norm_num at this
  linarith

/-- `n ≥ 7` odd: the two units of mass on `∅` are moved by `∅ + {0, n - 1} → {0} + {n - 1}` and
`∅ + {0, 2, n - 1} → {0, 2} + {n - 1}`. -/
theorem witness_three_odd {j : ℕ} (hn : n = j + 1) (hj : Even j) (hj6 : 6 ≤ j) :
    Witness (n := n) 3 (-1) 0 (lam 3 n) := by
  have hn7 : 7 ≤ n := by omega
  have hσ : (-1 : ℝ) ^ j = 1 := hj.neg_one_pow
  obtain ⟨-, -, -, hh0⟩ := masses_three hn
  have hE : (hcount n 1 ∅ : ℝ) = 2 := by rw [hσ] at hh0; linarith
  obtain ⟨a, hav⟩ : ∃ a : Fin n, (a : ℕ) = 2 := ⟨⟨2, by omega⟩, rfl⟩
  have h0v : ((0 : Fin n) : ℕ) = 0 := by simp
  have hmv := fin_val_neg_one (n := n)
  have h0m : (0 : Fin n) ≠ -1 := (fin_neg_one_ne_zero (by omega)).symm
  have h0a : (0 : Fin n) ≠ a := Fin.ne_of_val_ne (by rw [h0v, hav]; omega)
  have ham : a ≠ -1 := Fin.ne_of_val_ne (by rw [hav, hmv]; omega)
  have h1v : ((0 + 1 : Fin n) : ℕ) = 1 := by rw [fin_val_add_one h0m, h0v]
  have h3v : ((a + 1 : Fin n) : ℕ) = 3 := by rw [fin_val_add_one ham, hav]
  have h10 : (0 + 1 : Fin n) ≠ 0 := Fin.ne_of_val_ne (by rw [h1v, h0v]; omega)
  have h1a : (0 + 1 : Fin n) ≠ a := Fin.ne_of_val_ne (by rw [h1v, hav]; omega)
  have h1m : (0 + 1 : Fin n) ≠ -1 := Fin.ne_of_val_ne (by rw [h1v, hmv]; omega)
  have h30 : (a + 1 : Fin n) ≠ 0 := Fin.ne_of_val_ne (by rw [h3v, h0v]; omega)
  have h3a : (a + 1 : Fin n) ≠ a := Fin.ne_of_val_ne (by rw [h3v, hav]; omega)
  have h3m : (a + 1 : Fin n) ≠ -1 := Fin.ne_of_val_ne (by rw [h3v, hmv]; omega)
  have hm0 : (-1 + 1 : Fin n) = 0 := neg_add_cancel 1
  -- the special sets are distinct
  have hEA : (∅ : Finset (Fin n)) ≠ {0} := (singleton_ne_empty _).symm
  have hEB : (∅ : Finset (Fin n)) ≠ {-1} := (singleton_ne_empty _).symm
  have hEC : (∅ : Finset (Fin n)) ≠ {0, -1} := (insert_ne_empty _ _).symm
  have hES : (∅ : Finset (Fin n)) ≠ {0, a} := (insert_ne_empty _ _).symm
  have hEU : (∅ : Finset (Fin n)) ≠ {0, a, -1} := (insert_ne_empty _ _).symm
  have hAB : ({0} : Finset (Fin n)) ≠ {-1} := fun h => h0m (singleton_injective h)
  have hAC : ({0} : Finset (Fin n)) ≠ {0, -1} := fun h => by
    have := Finset.ext_iff.1 h (-1); simp [h0m.symm] at this
  have hAS : ({0} : Finset (Fin n)) ≠ {0, a} := fun h => by
    have := Finset.ext_iff.1 h a; simp [h0a.symm] at this
  have hAU : ({0} : Finset (Fin n)) ≠ {0, a, -1} := fun h => by
    have := Finset.ext_iff.1 h a; simp [h0a.symm] at this
  have hBC : ({-1} : Finset (Fin n)) ≠ {0, -1} := fun h => by
    have := Finset.ext_iff.1 h 0; simp [h0m] at this
  have hBS : ({-1} : Finset (Fin n)) ≠ {0, a} := fun h => by
    have := Finset.ext_iff.1 h 0; simp [h0m] at this
  have hBU : ({-1} : Finset (Fin n)) ≠ {0, a, -1} := fun h => by
    have := Finset.ext_iff.1 h 0; simp [h0m] at this
  have hCS : ({0, -1} : Finset (Fin n)) ≠ {0, a} := fun h => by
    have := Finset.ext_iff.1 h a; simp [h0a.symm, ham] at this
  have hCU : ({0, -1} : Finset (Fin n)) ≠ {0, a, -1} := fun h => by
    have := Finset.ext_iff.1 h a; simp [h0a.symm, ham] at this
  have hSU : ({0, a} : Finset (Fin n)) ≠ {0, a, -1} := fun h => by
    have := Finset.ext_iff.1 h (-1); simp [h0m.symm, ham.symm] at this
  -- they are good
  have gA : Good (-1) ({0} : Finset (Fin n)) := by
    intro i _ hi hi'
    rw [mem_singleton] at hi hi'
    rw [hi] at hi'; exact h10 hi'
  have gB : Good (-1) ({-1} : Finset (Fin n)) := fun i hi hi' _ => hi (mem_singleton.1 hi')
  have gC : Good (-1) ({0, -1} : Finset (Fin n)) := by
    intro i hi hiJ hiJ'
    rw [mem_insert, mem_singleton] at hiJ hiJ'
    rcases hiJ with rfl | rfl
    · exact hiJ'.elim h10 h1m
    · exact hi rfl
  have gS : Good (-1) ({0, a} : Finset (Fin n)) := by
    intro i hi hiJ hiJ'
    rw [mem_insert, mem_singleton] at hiJ hiJ'
    rcases hiJ with rfl | rfl
    · exact hiJ'.elim h10 h1a
    · exact hiJ'.elim h30 h3a
  have gU : Good (-1) ({0, a, -1} : Finset (Fin n)) := by
    intro i hi hiJ hiJ'
    rw [mem_insert, mem_insert, mem_singleton] at hiJ hiJ'
    rcases hiJ with rfl | rfl | rfl
    · rcases hiJ' with h | h | h
      · exact h10 h
      · exact h1a h
      · exact h1m h
    · rcases hiJ' with h | h | h
      · exact h30 h
      · exact h3a h
      · exact h3m h
    · exact hi rfl
  have wA : arcW 2 ({0} : Finset (Fin n)) = 2 := by
    rw [arcW_two_indep, card_singleton, pow_one]
    intro i hi hi'
    rw [mem_singleton] at hi hi'
    rw [hi] at hi'; exact h10 hi'
  have wB : arcW 2 ({-1} : Finset (Fin n)) = 2 := by
    rw [arcW_two_indep, card_singleton, pow_one]
    intro i hi hi'
    rw [mem_singleton] at hi hi'
    rw [hi, hm0] at hi'; exact h0m hi'
  have wS : arcW 2 ({0, a} : Finset (Fin n)) = 4 := by
    rw [arcW_two_indep, card_pair h0a]
    · norm_num
    · intro i hiJ hiJ'
      rw [mem_insert, mem_singleton] at hiJ hiJ'
      rcases hiJ with rfl | rfl
      · exact hiJ'.elim h10 h1a
      · exact hiJ'.elim h30 h3a
  have cA : ((0 : Fin n) ∈ ({0} : Finset (Fin n)) ∧ (-1 : Fin n) ∉ ({0} : Finset (Fin n))) ∨
      ((0 : Fin n) ∉ ({0} : Finset (Fin n)) ∧ (-1 : Fin n) ∈ ({0} : Finset (Fin n))) :=
    Or.inl ⟨mem_singleton_self _, fun h => h0m (mem_singleton.1 h).symm⟩
  have cB : ((0 : Fin n) ∈ ({-1} : Finset (Fin n)) ∧ (-1 : Fin n) ∉ ({-1} : Finset (Fin n))) ∨
      ((0 : Fin n) ∉ ({-1} : Finset (Fin n)) ∧ (-1 : Fin n) ∈ ({-1} : Finset (Fin n))) :=
    Or.inr ⟨fun h => h0m (mem_singleton.1 h), mem_singleton_self _⟩
  have cS : ((0 : Fin n) ∈ ({0, a} : Finset (Fin n)) ∧
      (-1 : Fin n) ∉ ({0, a} : Finset (Fin n))) ∨
      ((0 : Fin n) ∉ ({0, a} : Finset (Fin n)) ∧ (-1 : Fin n) ∈ ({0, a} : Finset (Fin n))) :=
    Or.inl ⟨mem_insert_self _ _, fun h => by
      rw [mem_insert, mem_singleton] at h
      exact h.elim (fun h => h0m h.symm) (fun h => ham h.symm)⟩
  have c0C : (0 : Fin n) ∈ ({0, -1} : Finset (Fin n)) := mem_insert_self _ _
  have c1C : (-1 : Fin n) ∈ ({0, -1} : Finset (Fin n)) := mem_insert_of_mem (mem_singleton_self _)
  have c0U : (0 : Fin n) ∈ ({0, a, -1} : Finset (Fin n)) := mem_insert_self _ _
  have c1U : (-1 : Fin n) ∈ ({0, a, -1} : Finset (Fin n)) :=
    mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))
  have pC := hcount_pos_both gC c0C c1C
  have pU := hcount_pos_both gU c0U c1U
  obtain ⟨t, ht⟩ : ∃ t : Finset (Fin n) → ℝ, t = fun J =>
      (-2) * ind ∅ J + 1 * ind {0} J + 2 * ind {-1} J + (-1) * ind {0, -1} J +
        1 * ind {0, a} J + (-1) * ind {0, a, -1} J := ⟨_, rfl⟩
  obtain ⟨cost, hc⟩ : ∃ cost : Finset (Fin n) → ℝ, cost = fun J =>
      (-2 * Real.log (3 / 2)) * ind ∅ J + Real.log 2 * ind {0} J +
        (Real.log 2 + 3 * Real.log (3 / 2)) * ind {-1} J +
        (3 * Real.log (3 / 2) - Real.log 2) * ind {0, a} J := ⟨_, rfl⟩
  have hcases : ∀ J : Finset (Fin n),
      (J = ∅ ∧ t J = -2 ∧ cost J = -2 * Real.log (3 / 2)) ∨
      (J = {0} ∧ t J = 1 ∧ cost J = Real.log 2) ∨
      (J = {-1} ∧ t J = 2 ∧ cost J = Real.log 2 + 3 * Real.log (3 / 2)) ∨
      (J = {0, -1} ∧ t J = -1 ∧ cost J = 0) ∨
      (J = {0, a} ∧ t J = 1 ∧ cost J = 3 * Real.log (3 / 2) - Real.log 2) ∨
      (J = {0, a, -1} ∧ t J = -1 ∧ cost J = 0) ∨
      (J ≠ ∅ ∧ J ≠ {0} ∧ J ≠ {-1} ∧ J ≠ {0, -1} ∧ J ≠ {0, a} ∧ J ≠ {0, a, -1} ∧
        t J = 0 ∧ cost J = 0) := by
    intro J
    by_cases h1 : J = ∅
    · left; subst h1
      refine ⟨rfl, ?_, ?_⟩ <;>
        simp only [ht, hc, ind_self, ind_of_ne hEA, ind_of_ne hEB, ind_of_ne hEC, ind_of_ne hES,
          ind_of_ne hEU] <;> ring
    right
    by_cases h2 : J = {0}
    · left; subst h2
      refine ⟨rfl, ?_, ?_⟩ <;>
        simp only [ht, hc, ind_self, ind_of_ne h1, ind_of_ne hAB, ind_of_ne hAC, ind_of_ne hAS,
          ind_of_ne hAU] <;> ring
    right
    by_cases h3 : J = {-1}
    · left; subst h3
      refine ⟨rfl, ?_, ?_⟩ <;>
        simp only [ht, hc, ind_self, ind_of_ne h1, ind_of_ne h2, ind_of_ne hBC, ind_of_ne hBS,
          ind_of_ne hBU] <;> ring
    right
    by_cases h4 : J = {0, -1}
    · left; subst h4
      refine ⟨rfl, ?_, ?_⟩ <;>
        simp only [ht, hc, ind_self, ind_of_ne h1, ind_of_ne h2, ind_of_ne h3, ind_of_ne hCS,
          ind_of_ne hCU] <;> ring
    right
    by_cases h5 : J = {0, a}
    · left; subst h5
      refine ⟨rfl, ?_, ?_⟩ <;>
        simp only [ht, hc, ind_self, ind_of_ne h1, ind_of_ne h2, ind_of_ne h3, ind_of_ne h4,
          ind_of_ne hSU] <;> ring
    right
    by_cases h6 : J = {0, a, -1}
    · left; subst h6
      refine ⟨rfl, ?_, ?_⟩ <;>
        simp only [ht, hc, ind_self, ind_of_ne h1, ind_of_ne h2, ind_of_ne h3, ind_of_ne h4,
          ind_of_ne h5] <;> ring
    right
    refine ⟨h1, h2, h3, h4, h5, h6, ?_, ?_⟩ <;>
      simp only [ht, hc, ind_of_ne h1, ind_of_ne h2, ind_of_ne h3, ind_of_ne h4, ind_of_ne h5,
        ind_of_ne h6] <;> ring
  refine witness_three_of_tweak hn t cost ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro J
    have hnn : (0 : ℝ) ≤ hcount n 1 J := Nat.cast_nonneg _
    rcases hcases J with ⟨rfl, ht', -⟩ | ⟨rfl, ht', -⟩ | ⟨rfl, ht', -⟩ | ⟨rfl, ht', -⟩ |
      ⟨rfl, ht', -⟩ | ⟨rfl, ht', -⟩ | ⟨-, -, -, -, -, -, ht', -⟩ <;> rw [ht']
    · rw [hE]; norm_num
    · linarith
    · linarith
    · have : (1 : ℝ) ≤ hcount n 1 ({0, -1} : Finset (Fin n)) := by exact_mod_cast pC
      linarith
    · linarith
    · have : (1 : ℝ) ≤ hcount n 1 ({0, a, -1} : Finset (Fin n)) := by exact_mod_cast pU
      linarith
    · linarith
  · rcases hcases ∅ with ⟨-, ht', -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rw [ht', hE]; norm_num
    · exact absurd h hEA
    · exact absurd h hEB
    · exact absurd h hEC
    · exact absurd h hES
    · exact absurd h hEU
    · exact absurd rfl h
  · intro J hJ
    rcases hcases J with ⟨rfl, ht', -⟩ | ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ |
      ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ | ⟨-, -, -, -, -, -, ht', -⟩
    · rw [ht', hE] at hJ; norm_num at hJ
    · exact gA
    · exact gB
    · exact gC
    · exact gS
    · exact gU
    · rw [ht', add_zero] at hJ
      exact good_of_hcount_pos (Nat.cast_pos.1 hJ)
  · simp only [ht, sum_add_distrib, sum_ind]; norm_num
  · intro i
    simp only [ht, sum_add_distrib, sum_ind_mem, notMem_empty, mem_singleton, mem_insert,
      ite_false]
    by_cases hi0 : i = 0
    · subst hi0; simp [h0m, h0a]
    · by_cases hi1 : i = -1
      · subst hi1; simp [h0m.symm, ham.symm]; norm_num
      · by_cases hia : i = a
        · subst hia; simp [h0a.symm, ham]
        · simp [hi0, hi1, hia]
  · intro J
    rcases hcases J with ⟨rfl, ht', hc'⟩ | ⟨rfl, ht', hc'⟩ | ⟨rfl, ht', hc'⟩ | ⟨rfl, ht', hc'⟩ |
      ⟨rfl, ht', hc'⟩ | ⟨rfl, ht', hc'⟩ | ⟨h1, -, -, -, -, -, ht', hc'⟩ <;> rw [ht', hc']
    · rw [hE, ell_none (notMem_empty _) (notMem_empty _)]; norm_num
    · exact up_one (by omega) cA wA
    · exact up_two (by omega) cB wB
    · exact down_one c0C c1C pC
    · exact up_four (by omega) cS wS
    · exact down_one c0U c1U pU
    · rw [sub_zero, add_zero, gW, ite_eq_right h1]
      exact ell_le_plain (by omega) h1
  · have hs := sum_ell (n := n) hn
    rw [hσ] at hs
    have hM : (64 : ℝ) ≤ 2 ^ j := by
      calc (64 : ℝ) = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj6
    have hprod := mul_nonneg (sub_nonneg.2 hM) eps_nonneg
    have hk := key_odd
    have hcs : ∑ J, cost J = -2 * Real.log (3 / 2) + Real.log 2 +
        (Real.log 2 + 3 * Real.log (3 / 2)) + (3 * Real.log (3 / 2) - Real.log 2) := by
      simp only [hc, sum_add_distrib, sum_ind]
    rw [hcs]
    nlinarith

end Odd

/-- k = 3, n ≥ 4, nothing known about the cover without the cut thread (g0 = 0). -/
theorem witness_three_zero {n : ℕ} [NeZero n] (hn : 4 ≤ n) :
    Witness (n := n) 3 (-1) 0 (lam 3 n) := by
  obtain ⟨j, hj⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rcases Nat.even_or_odd j with he | ho
  · by_cases h5 : n = 5
    · subst h5
      exact witness_three_zero_five
    · have hj6 : 6 ≤ j := by
        obtain ⟨m, hm⟩ := he
        omega
      exact witness_three_odd hj he hj6
  · exact witness_three_even hj ho (by omega)

end Outerplanar
