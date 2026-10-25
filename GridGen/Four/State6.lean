/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.CountBound6
import GridGen.Four.Fibre6
import GridGen.Four.Seam

/-!
# Height four, `k = 6`: the bound for one state

* `count_data6`: `countBound6` (the chord costs and the minimum errors) bounds the log count ratio
  of one state.
* **The pattern lemma** (`pattern_six`). Write the average pattern weight of the actual successor
  columns as `1 - (1-a)p₁ - (1-b)p₂ - (1-c)p₃`, where `p₁, p₂, p₃` are the shares of the classes
  `0102/0121`, `0120`, `0123`. The fibre bound gives `p₁ ≤ 2/3`, `p₂ ≤ 1/3`, and `p₁ + p₂ + p₃ ≤ 1`.
  The uniform side has exact class shares (`vA`, …, `vD` at `ℓ = 4`). At each corner of the box the
  ratio is then at least `R = 14123/14332`; the worst corner is `c = ρ` with the actual columns all
  in class `0123` against the uniform `0101` column. So the pattern term is at least
  `1 - 1/R = -209/14123`, about `0.554` of the cap `(1-ρ)/ρ`.
* `state_bound6`: `GB ≥ GU · (1 + Λ₆)`, with the pattern term capped at `209/14123`.
-/

namespace GridGen.Four

open Finset Real

theorem zz_le_two (B C : Finset ℕ) (a b : ℕ) : zz B C a b ≤ 2 := by
  unfold zz; split_ifs <;> norm_num

theorem count_data6 {k : ℕ} (hk6 : 6 ≤ k) (hkle : k ≤ 7) {B₁ B₂ B₃ B₄ : Finset ℕ}
    (hB₁ : B₁.card = k) (hB₂ : B₂.card = k) (hB₃ : B₃.card = k) (hB₄ : B₄.card = k)
    {s : T4} (hs : Proper s) :
    countBound6 ((k : ℝ) - 1) (mu k B₁ B₂) (mu k B₂ B₃) (mu k B₃ B₄)
        (zz B₁ B₂ (r1 s) (r2 s)) (zz B₂ B₃ (r2 s) (r3 s)) (zz B₃ B₄ (r3 s) (r4 s))
        (hb B₁ (r1 s)) (hb B₂ (r2 s)) (hb B₃ (r3 s)) (hb B₄ (r4 s)) (c13 s) (c24 s)
      ≤ log (((sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))).card : ℝ)
          / (sts ((range k).erase (r1 (canon s))) ((range k).erase (r2 (canon s)))
              ((range k).erase (r3 (canon s))) ((range k).erase (r4 (canon s)))).card) := by
  have hs' := hs
  obtain ⟨p12, p23, p34⟩ := hs'
  obtain ⟨hc13, hc24, hc14, h1314, h2414⟩ := cbits hs
  rw [card_sts_canon (by omega) hs, card_sts_rates]
  set A₁ := B₁.erase (r1 s) with hA₁
  set A₂ := B₂.erase (r2 s) with hA₂
  set A₃ := B₃.erase (r3 s) with hA₃
  set A₄ := B₄.erase (r4 s) with hA₄
  have eN : (A₄.card : ℝ) * ((A₃.card : ℝ) * ((A₁.card : ℝ) * A₂.card - (A₁ ∩ A₂).card)
          - ((A₁.card : ℝ) * (A₂ ∩ A₃).card - (A₁ ∩ A₂ ∩ A₃).card))
        - ((A₁.card : ℝ) * ((A₂.card : ℝ) * (A₃ ∩ A₄).card - (A₂ ∩ A₃ ∩ A₄).card)
          - ((A₁ ∩ A₂).card * (A₃ ∩ A₄).card - (A₁ ∩ A₂ ∩ A₃ ∩ A₄).card))
      = N4 A₁.card A₂.card A₃.card A₄.card (A₁ ∩ A₂).card (A₂ ∩ A₃).card (A₃ ∩ A₄).card
          (A₁ ∩ A₂ ∩ A₃).card (A₂ ∩ A₃ ∩ A₄).card (A₁ ∩ A₂ ∩ A₃ ∩ A₄).card := by
    unfold N4; ring
  rw [eN]
  have cr : ∀ X Y : Finset ℕ, X ⊆ Y → (X.card : ℝ) ≤ Y.card := fun X Y h => by
    exact_mod_cast Finset.card_le_card h
  obtain ⟨hM30, hM3N⟩ := M3_bounds A₁ A₂ A₃
  obtain ⟨hM40, hM4N⟩ := M4_bounds A₁ A₂ A₃ A₄
  refine count_log_bound6 hk6 hkle rfl (hb_cases _ _) (hb_cases _ _) (hb_cases _ _) (hb_cases _ _)
    (card_erase_hb hB₁ _) (card_erase_hb hB₂ _) (card_erase_hb hB₃ _) (card_erase_hb hB₄ _)
    (mu_nonneg hB₁) (mu_nonneg hB₂) (mu_nonneg hB₃)
    (by have := mu_le (k := k) B₁ B₂; linarith) (by have := mu_le (k := k) B₂ B₃; linarith)
    (by have := mu_le (k := k) B₃ B₄; linarith)
    (zz_nonneg _ _ _ _) (zz_nonneg _ _ _ _) (zz_nonneg _ _ _ _)
    (by rw [card_inter_erase hB₁ hB₂ p12]; ring) (by rw [card_inter_erase hB₂ hB₃ p23]; ring)
    (by rw [card_inter_erase hB₃ hB₄ p34]; ring)
    (Nat.cast_nonneg _) (cr _ _ inter_subset_left) (cr _ _ inter_subset_right)
    (Nat.cast_nonneg _) (cr _ _ inter_subset_left) (cr _ _ inter_subset_right)
    (Nat.cast_nonneg _) (cr _ _ inter_subset_left)
    (triple_ge A₁ A₂ A₃) (Nat.cast_nonneg _)
    (cr _ _ (inter_subset_left.trans inter_subset_left))
    (triple_ge A₂ A₃ A₄) (cr _ _ inter_subset_left)
    hM30 hM3N (by linarith) (by linarith) hc13 hc24 hc14 h1314 h2414 ?_ ?_
    (zz_le_two _ _ _ _) (zz_le_two _ _ _ _) (zz_le_two _ _ _ _) (Nat.cast_nonneg _)
  · -- defect-free first three rows
    intro hμ2 hμ3 hh1 hh2 hh3
    have e12 := eq_of_mu_zero hB₁ hB₂ hμ2
    have e23 := eq_of_mu_zero hB₂ hB₃ hμ3
    have m1 := mem_of_hb_zero hh1
    have m2 := mem_of_hb_zero hh2
    have m3 := mem_of_hb_zero hh3
    rw [← e12] at m2 hB₂ ⊢
    rw [← e23, ← e12] at m3 ⊢
    refine ⟨zz_self _ _ _, zz_self _ _ _, ?_⟩
    rw [hA₁, hA₂, hA₃, ← e23, ← e12, card_erase3 hB₁ m1 m2 m3 p12 p23]
    unfold c13; ring
  · -- defect-free last three rows
    intro hμ2 hμ3 hμ4 hh2 hh3 hh4
    have e12 := eq_of_mu_zero hB₁ hB₂ hμ2
    have e23 := eq_of_mu_zero hB₂ hB₃ hμ3
    have e34 := eq_of_mu_zero hB₃ hB₄ hμ4
    have m2 := mem_of_hb_zero hh2
    have m3 := mem_of_hb_zero hh3
    have m4 := mem_of_hb_zero hh4
    rw [← e23, ← e12] at m3
    rw [← e34, ← e23, ← e12] at m4
    rw [← e12] at m2
    have z3 : zz B₂ B₃ (r2 s) (r3 s) = 0 := by rw [← e23]; exact zz_self _ _ _
    have z4 : zz B₃ B₄ (r3 s) (r4 s) = 0 := by rw [← e34]; exact zz_self _ _ _
    have z2 : zz B₁ B₂ (r1 s) (r2 s) = 0 := by rw [← e12]; exact zz_self _ _ _
    have t234 : ((A₂ ∩ A₃ ∩ A₄).card : ℝ) = (k : ℝ) - 1 - 2 + c24 s := by
      rw [hA₂, hA₃, hA₄, ← e34, ← e23, ← e12, card_erase3 hB₁ m2 m3 m4 p23 p34]
      unfold c24; ring
    refine ⟨z2, z3, z4, t234, ?_, ?_⟩
    · intro hh1
      have m1 := mem_of_hb_zero hh1
      constructor
      · rw [hA₁, hA₂, hA₃, ← e23, ← e12, card_erase3 hB₁ m1 m2 m3 p12 p23]
        unfold c13; ring
      · rw [hA₁, hA₂, hA₃, hA₄, ← e34, ← e23, ← e12, card_erase4 hB₁ m1 m2 m3 m4 p12 p23 p34]
        unfold c13 c24 c14; ring
    · intro hh1
      have n1 := notMem_of_hb_one hh1
      have a1 : A₁ = B₁ := by rw [hA₁]; exact Finset.erase_eq_of_notMem n1
      have n13 : r1 s ≠ r3 s := fun h => n1 (h ▸ m3)
      have n14 : r1 s ≠ r4 s := fun h => n1 (h ▸ m4)
      refine ⟨?_, ?_, by unfold c13; simp [n13], by unfold c14; simp [n14]⟩
      · have : A₁ ∩ A₂ ∩ A₃ = (B₁.erase (r2 s)) ∩ (B₁.erase (r3 s)) := by
          rw [a1, hA₂, hA₃, ← e23, ← e12]
          ext x; simp only [Finset.mem_inter, Finset.mem_erase]; tauto
        rw [this, card_erase2 hB₁ m2 m3 p23]; ring
      · congr 2
        rw [a1, hA₂, hA₃, hA₄, ← e34, ← e23, ← e12]
        ext x; simp only [Finset.mem_inter, Finset.mem_erase]; tauto


/-! ### The pattern lemma -/

/-- All weights one: the plain count. -/
theorem G_one (A B C D : Finset ℕ) : G ⟨1, 1, 1⟩ A B C D = (sts A B C D).card := by
  unfold G gw
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  split_ifs <;> simp

/-- **The corner inequality** of the pattern lemma, for one uniform row `aff c₀ c₁ c₂ c₃`. Here
`N` counts the actual columns, `n₁₃, n₂₄, n₁₄` the columns with `r₁ = r₃`, `r₂ = r₄`, `r₁ = r₄`, and
`m` those with both of the first two. -/
theorem pat_corner {c0 c1 c2 c3 N n13 n24 m n14 : ℝ} {w : Wt} (hw : BoxR (487 / 500) w)
    (hN : 0 ≤ N) (h13 : 3 * n13 ≤ N) (h24 : 3 * n24 ≤ N) (h14 : 3 * n14 ≤ N) (hm0 : 0 ≤ m)
    (hm13 : m ≤ n13) (hm24 : m ≤ n24) (h140 : 0 ≤ n14) (hcov : n13 + n24 - m + n14 ≤ N)
    (hc : ∀ x y z : ℝ, (x = 487 / 500 ∨ x = 1) → (y = 487 / 500 ∨ y = 1) →
      (z = 487 / 500 ∨ z = 1) → ∀ N n13 n24 m n14 : ℝ, 0 ≤ N → 3 * n13 ≤ N → 3 * n24 ≤ N →
        3 * n14 ≤ N → 0 ≤ m → m ≤ n13 → m ≤ n24 → 0 ≤ n14 → n13 + n24 - m + n14 ≤ N →
        14123 / 14332 * aff c0 c1 c2 c3 ⟨x, y, z⟩ * N
          ≤ (z * N + (x - z) * (n13 + n24) + (1 - 2 * x + z) * m + (y - z) * n14)
            * (c0 + c1 + c2 + c3)) :
    14123 / 14332 * aff c0 c1 c2 c3 w * N
      ≤ (w.c * N + (w.a - w.c) * (n13 + n24) + (1 - 2 * w.a + w.c) * m + (w.b - w.c) * n14)
        * (c0 + c1 + c2 + c3) := by
  obtain ⟨ha, ha', hb, hb', hcc, hcc'⟩ := hw
  rw [← sub_nonneg]
  have e : (w.c * N + (w.a - w.c) * (n13 + n24) + (1 - 2 * w.a + w.c) * m + (w.b - w.c) * n14)
        * (c0 + c1 + c2 + c3) - 14123 / 14332 * aff c0 c1 c2 c3 w * N
      = aff (-(14123 / 14332) * c0 * N + m * (c0 + c1 + c2 + c3))
          ((n13 + n24 - 2 * m) * (c0 + c1 + c2 + c3) - 14123 / 14332 * c1 * N)
          (n14 * (c0 + c1 + c2 + c3) - 14123 / 14332 * c2 * N)
          ((N - n13 - n24 + m - n14) * (c0 + c1 + c2 + c3) - 14123 / 14332 * c3 * N) w := by
    unfold aff; ring
  rw [e]
  refine aff_nonneg ha ha' hb hb' hcc hcc' (fun x y z hx hy hz => ?_)
  have := hc x y z hx hy hz N n13 n24 m n14 hN h13 h24 h14 hm0 hm13 hm24 h140 hcov
  have e' : (z * N + (x - z) * (n13 + n24) + (1 - 2 * x + z) * m + (y - z) * n14)
        * (c0 + c1 + c2 + c3) - 14123 / 14332 * aff c0 c1 c2 c3 ⟨x, y, z⟩ * N
      = aff (-(14123 / 14332) * c0 * N + m * (c0 + c1 + c2 + c3))
          ((n13 + n24 - 2 * m) * (c0 + c1 + c2 + c3) - 14123 / 14332 * c1 * N)
          (n14 * (c0 + c1 + c2 + c3) - 14123 / 14332 * c2 * N)
          ((N - n13 - n24 + m - n14) * (c0 + c1 + c2 + c3) - 14123 / 14332 * c3 * N)
          ⟨x, y, z⟩ := by
    unfold aff; ring
  linarith

/-- The four uniform rows at `ℓ = 4` satisfy the corner inequality. -/
theorem pat_rows :
    (∀ x y z : ℝ, (x = 487 / 500 ∨ x = 1) → (y = 487 / 500 ∨ y = 1) →
      (z = 487 / 500 ∨ z = 1) → ∀ N n13 n24 m n14 : ℝ, 0 ≤ N → 3 * n13 ≤ N → 3 * n24 ≤ N →
        3 * n14 ≤ N → 0 ≤ m → m ≤ n13 → m ≤ n24 → 0 ≤ n14 → n13 + n24 - m + n14 ≤ N →
        14123 / 14332 * aff 21 136 52 168 ⟨x, y, z⟩ * N
          ≤ (z * N + (x - z) * (n13 + n24) + (1 - 2 * x + z) * m + (y - z) * n14)
            * (21 + 136 + 52 + 168)) ∧
    (∀ x y z : ℝ, (x = 487 / 500 ∨ x = 1) → (y = 487 / 500 ∨ y = 1) →
      (z = 487 / 500 ∨ z = 1) → ∀ N n13 n24 m n14 : ℝ, 0 ≤ N → 3 * n13 ≤ N → 3 * n24 ≤ N →
        3 * n14 ≤ N → 0 ≤ m → m ≤ n13 → m ≤ n24 → 0 ≤ n14 → n13 + n24 - m + n14 ≤ N →
        14123 / 14332 * aff 17 127 55 174 ⟨x, y, z⟩ * N
          ≤ (z * N + (x - z) * (n13 + n24) + (1 - 2 * x + z) * m + (y - z) * n14)
            * (17 + 127 + 55 + 174)) ∧
    (∀ x y z : ℝ, (x = 487 / 500 ∨ x = 1) → (y = 487 / 500 ∨ y = 1) →
      (z = 487 / 500 ∨ z = 1) → ∀ N n13 n24 m n14 : ℝ, 0 ≤ N → 3 * n13 ≤ N → 3 * n24 ≤ N →
        3 * n14 ≤ N → 0 ≤ m → m ≤ n13 → m ≤ n24 → 0 ≤ n14 → n13 + n24 - m + n14 ≤ N →
        14123 / 14332 * aff 13 110 71 174 ⟨x, y, z⟩ * N
          ≤ (z * N + (x - z) * (n13 + n24) + (1 - 2 * x + z) * m + (y - z) * n14)
            * (13 + 110 + 71 + 174)) ∧
    (∀ x y z : ℝ, (x = 487 / 500 ∨ x = 1) → (y = 487 / 500 ∨ y = 1) →
      (z = 487 / 500 ∨ z = 1) → ∀ N n13 n24 m n14 : ℝ, 0 ≤ N → 3 * n13 ≤ N → 3 * n24 ≤ N →
        3 * n14 ≤ N → 0 ≤ m → m ≤ n13 → m ≤ n24 → 0 ≤ n14 → n13 + n24 - m + n14 ≤ N →
        14123 / 14332 * aff 14 116 58 181 ⟨x, y, z⟩ * N
          ≤ (z * N + (x - z) * (n13 + n24) + (1 - 2 * x + z) * m + (y - z) * n14)
            * (14 + 116 + 58 + 181)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rintro x y z (rfl | rfl) (rfl | rfl) (rfl | rfl) N n13 n24 m n14 hN h13 h24 h14 hm0 hm13 hm24
      h140 hcov <;>
    · simp only [aff]; linarith

/-- The counts of a column system with lists of at least five colours. -/
theorem pat_counts {A₁ A₂ A₃ A₄ : Finset ℕ} (h₁ : 5 ≤ A₁.card) (h₂ : 5 ≤ A₂.card)
    (h₃ : 5 ≤ A₃.card) (h₄ : 5 ≤ A₄.card) :
    let Ω := sts A₁ A₂ A₃ A₄
    3 * ((Ω.filter (fun t => r1 t = r3 t)).card : ℝ) ≤ Ω.card ∧
    3 * ((Ω.filter (fun t => r2 t = r4 t)).card : ℝ) ≤ Ω.card ∧
    3 * ((Ω.filter (fun t => r1 t = r4 t)).card : ℝ) ≤ Ω.card ∧
    ((Ω.filter (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card : ℝ)
      ≤ (Ω.filter (fun t => r1 t = r3 t)).card ∧
    ((Ω.filter (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card : ℝ)
      ≤ (Ω.filter (fun t => r2 t = r4 t)).card ∧
    ((Ω.filter (fun t => r1 t = r3 t)).card : ℝ) + (Ω.filter (fun t => r2 t = r4 t)).card
      - (Ω.filter (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card
      + (Ω.filter (fun t => r1 t = r4 t)).card ≤ Ω.card := by
  intro Ω
  have hA₁ : 6 - 1 ≤ A₁.card := by omega
  have hA₂ : 6 - 1 ≤ A₂.card := by omega
  have hA₃ : 6 - 1 ≤ A₃.card := by omega
  have hA₄ : 6 - 1 ≤ A₄.card := by omega
  have hR : ∀ t ∈ Ω, ∀ t' ∈ Ω, (fun _ : T4 => (1 : ℝ)) t ≤ 1 * (fun _ : T4 => (1 : ℝ)) t' :=
    fun _ _ _ _ => by norm_num
  have one : ∀ (P : T4 → Prop) [DecidablePred P], ∑ t ∈ Ω.filter P, (fun _ : T4 => (1 : ℝ)) t
      = ((Ω.filter P).card : ℝ) := fun P _ => by simp
  have oneΩ : ∑ t ∈ Ω, (fun _ : T4 => (1 : ℝ)) t = (Ω.card : ℝ) := by simp
  have f13 := fibre_sts1 (k := 6) (fun _ => (1 : ℝ)) (fun _ => zero_le_one) (fun t => r1 t = r3 t)
    hA₁ hA₂ hA₃ hA₄ zero_le_one hR r3 (fun _ _ => rfl) (fun _ h => h)
  have f24 := fibre_sts2 (k := 6) (fun _ => (1 : ℝ)) (fun _ => zero_le_one) (fun t => r2 t = r4 t)
    hA₁ hA₂ hA₃ hA₄ zero_le_one hR r4 (fun _ _ => rfl) (fun _ h => h)
  have f14 := fibre_sts1 (k := 6) (fun _ => (1 : ℝ)) (fun _ => zero_le_one) (fun t => r1 t = r4 t)
    hA₁ hA₂ hA₃ hA₄ zero_le_one hR r4 (fun _ _ => rfl) (fun _ h => h)
  rw [one, oneΩ] at f13 f24 f14
  norm_num at f13 f24 f14
  refine ⟨f13, f24, f14, ?_, ?_, ?_⟩
  · exact_mod_cast Finset.card_le_card (fun t ht => by
      simp only [Finset.mem_filter] at ht ⊢; exact ⟨ht.1, ht.2.1⟩)
  · exact_mod_cast Finset.card_le_card (fun t ht => by
      simp only [Finset.mem_filter] at ht ⊢; exact ⟨ht.1, ht.2.2⟩)
  · -- the union of the two equality classes, and the disjoint `r₁ = r₄` class
    have hu : (Ω.filter (fun t => r1 t = r3 t)).card + (Ω.filter (fun t => r2 t = r4 t)).card
        = (Ω.filter (fun t => r1 t = r3 t ∨ r2 t = r4 t)).card
          + (Ω.filter (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card := by
      rw [← Finset.card_union_add_card_inter, ← Finset.filter_or, ← Finset.filter_and]
    have hd : Disjoint (Ω.filter (fun t => r1 t = r3 t ∨ r2 t = r4 t))
        (Ω.filter (fun t => r1 t = r4 t)) := by
      rw [Finset.disjoint_filter]
      intro t ht h1 h2
      obtain ⟨-, -, -, -, p12, p23, p34⟩ := mem_sts.mp ht
      rcases h1 with h1 | h1
      · exact p34 (h1.symm.trans h2)
      · exact p12 (h2.trans h1.symm)
    have hsub : Ω.filter (fun t => r1 t = r3 t ∨ r2 t = r4 t) ∪ Ω.filter (fun t => r1 t = r4 t)
        ⊆ Ω := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd] at hc
    have : ((Ω.filter (fun t => r1 t = r3 t)).card : ℝ) + (Ω.filter (fun t => r2 t = r4 t)).card
        = ((Ω.filter (fun t => r1 t = r3 t ∨ r2 t = r4 t)).card : ℝ)
          + (Ω.filter (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card := by exact_mod_cast hu
    have hc' : ((Ω.filter (fun t => r1 t = r3 t ∨ r2 t = r4 t)).card : ℝ)
        + (Ω.filter (fun t => r1 t = r4 t)).card ≤ Ω.card := by exact_mod_cast hc
    linarith

/-- **The pattern lemma at `k = 6`.** The average pattern weight of any column system with lists
of at least five colours is at least `14123/14332` of the uniform one. -/
theorem pattern_six {w : Wt} (hw : InBox 6 w) {s : T4} (hs : Proper s)
    {A₁ A₂ A₃ A₄ : Finset ℕ} (h₁ : 5 ≤ A₁.card) (h₂ : 5 ≤ A₂.card) (h₃ : 5 ≤ A₃.card)
    (h₄ : 5 ≤ A₄.card) :
    14123 / 14332 * (GU 6 w s / (sts ((range 6).erase (r1 (canon s)))
        ((range 6).erase (r2 (canon s))) ((range 6).erase (r3 (canon s)))
        ((range 6).erase (r4 (canon s)))).card)
      ≤ G w A₁ A₂ A₃ A₄ / (sts A₁ A₂ A₃ A₄).card := by
  have hb : BoxR (487 / 500) w := by rw [← rho_six]; exact hw
  obtain ⟨c13, c24, c14, m13, m24, cov⟩ := pat_counts h₁ h₂ h₃ h₄
  set N : ℝ := ((sts A₁ A₂ A₃ A₄).card : ℝ) with hN
  have hNp : 0 < N := by
    rw [hN]; exact_mod_cast (sts_nonempty (by omega) (by omega) (by omega) (by omega)).card_pos
  -- the uniform count is the weight-one uniform sum
  have hU1 : ((sts ((range 6).erase (r1 (canon s))) ((range 6).erase (r2 (canon s)))
      ((range 6).erase (r3 (canon s))) ((range 6).erase (r4 (canon s)))).card : ℝ)
      = GU 6 ⟨1, 1, 1⟩ s := by unfold GU; rw [G_one]
  rw [hU1]
  have hsplit := G_split w A₁ A₂ A₃ A₄
  simp only [Int.cast_natCast] at hsplit
  rw [hsplit]
  have e4 : ((6 : ℕ) : ℝ) - 2 = 4 := by norm_num
  have key : ∀ c0 c1 c2 c3 : ℝ, (c0 + c1 + c2 + c3 > 0) →
      (∀ x y z : ℝ, (x = 487 / 500 ∨ x = 1) → (y = 487 / 500 ∨ y = 1) →
        (z = 487 / 500 ∨ z = 1) → ∀ N n13 n24 m n14 : ℝ, 0 ≤ N → 3 * n13 ≤ N → 3 * n24 ≤ N →
          3 * n14 ≤ N → 0 ≤ m → m ≤ n13 → m ≤ n24 → 0 ≤ n14 → n13 + n24 - m + n14 ≤ N →
          14123 / 14332 * aff c0 c1 c2 c3 ⟨x, y, z⟩ * N
            ≤ (z * N + (x - z) * (n13 + n24) + (1 - 2 * x + z) * m + (y - z) * n14)
              * (c0 + c1 + c2 + c3)) →
      GU 6 w s = aff c0 c1 c2 c3 w → GU 6 ⟨1, 1, 1⟩ s = c0 + c1 + c2 + c3 →
      14123 / 14332 * (GU 6 w s / GU 6 ⟨1, 1, 1⟩ s)
        ≤ (w.c * N + (w.a - w.c) * (((sts A₁ A₂ A₃ A₄).filter (fun t => r1 t = r3 t)).card
            + ((sts A₁ A₂ A₃ A₄).filter (fun t => r2 t = r4 t)).card)
          + (1 - 2 * w.a + w.c)
            * ((sts A₁ A₂ A₃ A₄).filter (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card
          + (w.b - w.c) * ((sts A₁ A₂ A₃ A₄).filter (fun t => r1 t = r4 t)).card) / N := by
    intro c0 c1 c2 c3 hS hc hG hG1
    rw [hG, hG1, ← mul_div_assoc, div_le_div_iff₀ hS hNp]
    exact pat_corner hb hNp.le c13 c24 c14 (Nat.cast_nonneg _) m13 m24 (Nat.cast_nonneg _) cov hc
  obtain ⟨rA, rB, rC, rD⟩ := pat_rows
  have hk : 4 ≤ 6 := by norm_num
  have vA4 : ∀ w : Wt, vA ((6 : ℕ) - 2 : ℝ) w = aff 21 136 52 168 w := fun w => by
    rw [e4]; unfold vA; norm_num
  have vB4 : ∀ w : Wt, vB ((6 : ℕ) - 2 : ℝ) w = aff 17 127 55 174 w := fun w => by
    rw [e4]; unfold vB; norm_num
  have vC4 : ∀ w : Wt, vC ((6 : ℕ) - 2 : ℝ) w = aff 13 110 71 174 w := fun w => by
    rw [e4]; unfold vC; norm_num
  have vD4 : ∀ w : Wt, vD ((6 : ℕ) - 2 : ℝ) w = aff 14 116 58 181 w := fun w => by
    rw [e4]; unfold vD; norm_num
  have one_aff : ∀ c0 c1 c2 c3 : ℝ, aff c0 c1 c2 c3 ⟨1, 1, 1⟩ = c0 + c1 + c2 + c3 := fun _ _ _ _ => by
    unfold aff; ring
  rcases canon_cases hs with h | h | h | h | h
  · refine key 21 136 52 168 (by norm_num) rA ?_ ?_
    · rw [GU_eq_of_canon w h (by decide), GU_0101 hk, vA4]
    · rw [GU_eq_of_canon _ h (by decide), GU_0101 hk, vA4, one_aff]
  · refine key 17 127 55 174 (by norm_num) rB ?_ ?_
    · rw [GU_eq_of_canon w h (by decide), GU_0102 hk, vB4]
    · rw [GU_eq_of_canon _ h (by decide), GU_0102 hk, vB4, one_aff]
  · refine key 17 127 55 174 (by norm_num) rB ?_ ?_
    · rw [GU_eq_of_canon w h (by decide), GU_0121 hk, vB4]
    · rw [GU_eq_of_canon _ h (by decide), GU_0121 hk, vB4, one_aff]
  · refine key 13 110 71 174 (by norm_num) rC ?_ ?_
    · rw [GU_eq_of_canon w h (by decide), GU_0120 hk, vC4]
    · rw [GU_eq_of_canon _ h (by decide), GU_0120 hk, vC4, one_aff]
  · refine key 14 116 58 181 (by norm_num) rD ?_ ?_
    · rw [GU_eq_of_canon w h (by decide), GU_0123 hk, vD4]
    · rw [GU_eq_of_canon _ h (by decide), GU_0123 hk, vD4, one_aff]

/-! ### The bound for one state -/

/-- The count bound of a state at `k = 6`. -/
noncomputable def CB6 (B₁ B₂ B₃ B₄ : Finset ℕ) (s : T4) : ℝ :=
  countBound6 ((6 : ℕ) - 1 : ℝ) (mu 6 B₁ B₂) (mu 6 B₂ B₃) (mu 6 B₃ B₄)
    (zz B₁ B₂ (r1 s) (r2 s)) (zz B₂ B₃ (r2 s) (r3 s)) (zz B₃ B₄ (r3 s) (r4 s))
    (hb B₁ (r1 s)) (hb B₂ (r2 s)) (hb B₃ (r3 s)) (hb B₄ (r4 s)) (c13 s) (c24 s)

/-- **The gain at `k = 6`**, with the pattern term capped at `209/14123` (`pattern_six`). -/
noncomputable def Lamc6 (B₁ B₂ B₃ B₄ : Finset ℕ) (s : T4) : ℝ :=
  CB6 B₁ B₂ B₃ B₄ s - min (eta 6 * PS 6 B₁ B₂ B₃ B₄ s) (209 / 14123)

/-- **The log gain of one state at `k = 6`**, with the pattern term capped at `209/14123`. -/
theorem state_log_bound6 {k : ℕ} (hk : k = 6) {w : Wt} (hw : InBox k w)
    {B₁ B₂ B₃ B₄ : Finset ℕ}
    (hB₁ : B₁.card = k) (hB₂ : B₂.card = k) (hB₃ : B₃.card = k) (hB₄ : B₄.card = k)
    {s : T4} (hs : Proper s) :
    0 < GU k w s ∧ 0 < GB w B₁ B₂ B₃ B₄ s ∧
      Lamc6 B₁ B₂ B₃ B₄ s ≤ log (GB w B₁ B₂ B₃ B₄ s / GU k w s) := by
  subst hk
  obtain ⟨P, f, hPc, hPr, hf, hdiff⟩ := exists_palette (by omega) hB₂ s
  have hk5 : 5 ≤ 6 := by omega
  have hρ := rho_pos' hk5
  have hρ1 := rho_le_one 6 hk5
  -- the pattern term
  have hpat := pattern_log_ge (A₁ := B₁.erase (r1 s)) (A₂ := B₂.erase (r2 s))
    (A₃ := B₃.erase (r3 s)) (A₄ := B₄.erase (r4 s)) (U₁ := P.erase (r1 s)) (U₂ := P.erase (r2 s))
    (U₃ := P.erase (r3 s)) (U₄ := P.erase (r4 s)) (by omega)
    (card_ge_of_erase hB₁ _) (card_ge_of_erase hB₂ _) (card_ge_of_erase hB₃ _)
    (card_ge_of_erase hB₄ _) (card_ge_of_erase hPc _) (card_ge_of_erase hPc _)
    (card_ge_of_erase hPc _) (card_ge_of_erase hPc _) w hρ hρ1 (gw_mem hw)
  rw [G_erase_eq_GU w (by omega) hs hPc hPr, card_erase_eq_canon (by omega) hs hPc hPr] at hpat
  -- the size of the differences
  have m12 := card_sdiff_mu hB₁ B₂
  have m21 := card_sdiff_mu hB₂ B₁
  have m23 := card_sdiff_mu hB₂ B₃
  have m32 := card_sdiff_mu hB₃ B₂
  have m34 := card_sdiff_mu hB₃ B₄
  have m43 := card_sdiff_mu hB₄ B₃
  rw [mu_comm 6 B₂ B₁] at m21
  rw [mu_comm 6 B₃ B₂] at m32
  rw [mu_comm 6 B₄ B₃] at m43
  have t42 := card_sdiff_tri B₄ B₃ B₂
  have t24 := card_sdiff_tri B₂ B₃ B₄
  have s22 : ((B₂ \ B₂).card : ℝ) = 0 := by simp
  obtain ⟨d1, d1'⟩ := hdiff B₁ (r1 s)
  obtain ⟨d2, d2'⟩ := hdiff B₂ (r2 s)
  obtain ⟨d3, d3'⟩ := hdiff B₃ (r3 s)
  obtain ⟨d4, d4'⟩ := hdiff B₄ (r4 s)
  have hj : jsum B₂ s ≤ (hb B₁ (r1 s) + hb B₂ (r2 s) + hb B₃ (r3 s) + hb B₄ (r4 s))
      + (xin B₁ B₂ (r1 s) + xin B₃ B₂ (r3 s) + xin B₄ B₂ (r4 s)) := by
    unfold jsum
    have j1 := notin_le B₁ B₂ (r1 s)
    have j3 := notin_le B₃ B₂ (r3 s)
    have j4 := notin_le B₄ B₂ (r4 s)
    have j2 : (if r2 s ∈ B₂ then (0 : ℝ) else 1) = hb B₂ (r2 s) := rfl
    linarith
  set T := mu 6 B₁ B₂ + 2 * mu 6 B₂ B₃ + mu 6 B₃ B₄ with hT
  set Hs := hb B₁ (r1 s) + hb B₂ (r2 s) + hb B₃ (r3 s) + hb B₄ (r4 s) with hHs
  set Xs := xin B₁ B₂ (r1 s) + xin B₃ B₂ (r3 s) + xin B₄ B₂ (r4 s) with hXs
  set SA : ℝ := (((B₁.erase (r1 s)) \ (P.erase (r1 s))).card : ℝ)
    + ((B₂.erase (r2 s)) \ (P.erase (r2 s))).card + ((B₃.erase (r3 s)) \ (P.erase (r3 s))).card
    + ((B₄.erase (r4 s)) \ (P.erase (r4 s))).card with hSA
  set SU : ℝ := (((P.erase (r1 s)) \ (B₁.erase (r1 s))).card : ℝ)
    + ((P.erase (r2 s)) \ (B₂.erase (r2 s))).card + ((P.erase (r3 s)) \ (B₃.erase (r3 s))).card
    + ((P.erase (r4 s)) \ (B₄.erase (r4 s))).card with hSU
  have hmax : max SA SU ≤ T + 4 * Hs + 4 * Xs := by
    apply max_le <;> linarith
  have hk3 : (0 : ℝ) < ((6 - 3 : ℕ) : ℝ) := by
    have : 0 < 6 - 3 := by omega
    exact_mod_cast this
  have hη : -(eta 6 * (T + 4 * Hs + 4 * Xs))
      ≤ -((1 - rho 6) / rho 6 * (max SA SU / ((6 - 3 : ℕ) : ℝ))) := by
    have e : eta 6 * (T + 4 * Hs + 4 * Xs)
        = (1 - rho 6) / rho 6 * ((T + 4 * Hs + 4 * Xs) / ((6 - 3 : ℕ) : ℝ)) := by
      unfold eta; ring
    rw [e, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hmax hk3.le)
      (div_nonneg (by linarith) hρ.le)
  -- the count term
  have hcnt := count_data6 (k := 6) (by norm_num) (by norm_num) hB₁ hB₂ hB₃ hB₄ hs
  -- positivity
  have c1 := card_ge_of_erase hB₁ (r1 s)
  have c2 := card_ge_of_erase hB₂ (r2 s)
  have c3 := card_ge_of_erase hB₃ (r3 s)
  have c4 := card_ge_of_erase hB₄ (r4 s)
  have u : ∀ i, 3 ≤ ((range 6).erase i).card := fun i => by
    have := card_ge_of_erase (card_range 6) i; omega
  have hGA : 0 < G w (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s)) :=
    G_pos hk5 hw (by omega) (by omega) (by omega) (by omega)
  have hGU : 0 < GU 6 w s := G_pos hk5 hw (u _) (u _) (u _) (u _)
  have hNA : (0 : ℝ) < (sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s))
      (B₄.erase (r4 s))).card := by
    exact_mod_cast (sts_nonempty (by omega) (by omega) (by omega) (by omega)).card_pos
  have hNU : (0 : ℝ) < (sts ((range 6).erase (r1 (canon s))) ((range 6).erase (r2 (canon s)))
      ((range 6).erase (r3 (canon s))) ((range 6).erase (r4 (canon s)))).card := by
    exact_mod_cast (sts_nonempty (u _) (u _) (u _) (u _)).card_pos
  -- combine
  have hlog : Lamc6 B₁ B₂ B₃ B₄ s ≤ log (GB w B₁ B₂ B₃ B₄ s / GU 6 w s) := by
    have e : GB w B₁ B₂ B₃ B₄ s / GU 6 w s
        = ((sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))).card
            / (sts ((range 6).erase (r1 (canon s))) ((range 6).erase (r2 (canon s)))
              ((range 6).erase (r3 (canon s))) ((range 6).erase (r4 (canon s)))).card)
          * ((G w (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))
              / (sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))).card)
            / (GU 6 w s / (sts ((range 6).erase (r1 (canon s))) ((range 6).erase (r2 (canon s)))
              ((range 6).erase (r3 (canon s))) ((range 6).erase (r4 (canon s)))).card)) := by
      unfold GB; field_simp
    rw [e, Real.log_mul (by positivity) (by positivity)]
    -- the pattern term is at least `log (14123/14332) ≥ -209/14123` (`pattern_six`)
    have hcap : -(209 / 14123 : ℝ)
        ≤ log ((G w (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))
              / (sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))).card)
            / (GU 6 w s / (sts ((range 6).erase (r1 (canon s))) ((range 6).erase (r2 (canon s)))
              ((range 6).erase (r3 (canon s))) ((range 6).erase (r4 (canon s)))).card)) := by
      have hp := pattern_six hw hs (A₁ := B₁.erase (r1 s)) (A₂ := B₂.erase (r2 s))
        (A₃ := B₃.erase (r3 s)) (A₄ := B₄.erase (r4 s)) (by omega) (by omega) (by omega)
        (by omega)
      have hx : (14123 / 14332 : ℝ) ≤ (G w (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s))
            (B₄.erase (r4 s)) / (sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s))
              (B₄.erase (r4 s))).card)
            / (GU 6 w s / (sts ((range 6).erase (r1 (canon s))) ((range 6).erase (r2 (canon s)))
              ((range 6).erase (r3 (canon s))) ((range 6).erase (r4 (canon s)))).card) := by
        rw [le_div_iff₀ (div_pos hGU hNU)]; exact hp
      have hl := Real.log_le_log (by norm_num) hx
      have hl2 : 1 - 1 / (14123 / 14332 : ℝ) ≤ log (14123 / 14332) := by
        have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 14123 / 14332)
        simpa [one_div] using this
      norm_num at hl2
      linarith
    have hη' : -(eta 6 * PS 6 B₁ B₂ B₃ B₄ s) ≤ -((1 - rho 6) / rho 6 * (max SA SU
        / ((6 - 3 : ℕ) : ℝ))) := hη
    unfold Lamc6 CB6
    rcases le_total (eta 6 * PS 6 B₁ B₂ B₃ B₄ s) (209 / 14123) with hm | hm
    · rw [min_eq_left hm]; linarith
    · rw [min_eq_right hm]; linarith
  exact ⟨hGU, by unfold GB; exact hGA, hlog⟩


/-- **The bound for one state at `k = 6`**: `GB ≥ GU · (1 + Λ₆)`. -/
theorem state_bound6 {w : Wt} (hw : InBox 6 w) {B₁ B₂ B₃ B₄ : Finset ℕ}
    (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6) (hB₄ : B₄.card = 6)
    {s : T4} (hs : Proper s) :
    GU 6 w s * (1 + Lamc6 B₁ B₂ B₃ B₄ s) ≤ GB w B₁ B₂ B₃ B₄ s := by
  obtain ⟨hu, hb, hl⟩ := state_log_bound6 rfl hw hB₁ hB₂ hB₃ hB₄ hs
  exact mul_one_add_le_of_log hu hb hl

end GridGen.Four
