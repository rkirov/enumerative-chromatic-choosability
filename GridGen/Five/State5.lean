/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Kappa5b
import GridGen.Five.Pattern5

/-!
# Height five, `k = 6`: the bound for one state

`ai_research_notes/H5_K6_ANALYTIC_2026-10-23.md` (★). For a proper previous column `s` and next
`6`-lists `B₁, …, B₅`, the successor lists are `Aᵢ = Bᵢ ∖ {sᵢ}` with `nᵢ = |Aᵢ| = 5 + hᵢ`.

* **The count** (`count_state`). By greedy minimality and the universal constant
  (`GridGen/Five/Count5.lean`, `Kappa5a/b.lean`), `|sts A| ≥ κ · n₁ ∏ⱼ r̃ⱼ` with
  `r̃ⱼ = nⱼ - eⱼ/nⱼ₋₁`, `eⱼ = |Aⱼ₋₁ ∩ Aⱼ|`. Height four's row bounds (`GridGen.Lookback.rate_first`,
  `GridGen.Lookback.rate_main_chord`) then give
  `log (|sts A| / (5 t⁴)) ≥ log κ + Σⱼ [log (1 + μⱼ/21) - zⱼ · zslope μⱼ]`, `t = 21/5`; the bonuses
  of the rows with `hᵢ = 1` are dropped (each is at least `2/15 - 7/120 > 0`).
* **The state bound** (`state_bound5`). With the pattern lemma (`GridGen/Five/Pattern5.lean`),
  `GB ≥ GU · (1 + Λ)`, `Λ = Kr (o(s)) + Σⱼ Lr j`, where
  `Kr i = log c_P + log κ + log (5 t⁴ / Rᵢ)` and `Rᵢ = Σⱼ Vᵢⱼ` is the number of uniform successors
  of a column in orbit `i`.
-/

namespace GridGen.Five

open Finset Real

/-- The main term of one row, with the cost of the state colours in the difference sets. -/
noncomputable def Lr (B C : Finset ℕ) (a b : ℕ) : ℝ :=
  log (1 + Lookback.mu 6 B C / 21) - Lookback.zz B C a b * Lookback.zslope 5 (Lookback.mu 6 B C)

/-- The constant part of the gain of a state in orbit `i`. -/
noncomputable def Kr (i : Fin 11) : ℝ :=
  log (971038 / 1000000) + log (123125 / 128018) + log (194481 / 125) - log (∑ j, (Vmat i j : ℝ))

theorem card_erase_56 {B : Finset ℕ} (hB : B.card = 6) (c : ℕ) :
    (B.erase c).card = 5 ∨ (B.erase c).card = 6 := by
  by_cases h : c ∈ B
  · left; rw [Finset.card_erase_of_mem h, hB]
  · right; rw [Finset.erase_eq_of_notMem h, hB]

theorem inter3_ge (X Y Z : Finset ℕ) :
    ((X ∩ Y).card : ℤ) + (Y ∩ Z).card - Y.card ≤ (X ∩ Y ∩ Z).card := by
  have h := Lookback.triple_ge X Y Z
  have h' : (((X ∩ Y).card : ℤ) + (Y ∩ Z).card - Y.card : ℤ) ≤ (X ∩ Y ∩ Z).card := by
    exact_mod_cast h
  exact h'

/-- **Greedy minimality for actual lists**: `N5(greedy) ≤ |sts A|` for lists of at least five
colours. -/
theorem N5g_le_card {A₁ A₂ A₃ A₄ A₅ : Finset ℕ} (h₁ : 5 ≤ A₁.card) (h₂ : 5 ≤ A₂.card)
    (h₄ : 5 ≤ A₄.card) (h₅ : 5 ≤ A₅.card) :
    N5g A₁.card A₂.card A₃.card A₄.card A₅.card (A₁ ∩ A₂).card (A₂ ∩ A₃).card (A₃ ∩ A₄).card
      (A₄ ∩ A₅).card ≤ (sts A₁ A₂ A₃ A₄ A₅).card := by
  have cl : ∀ {U V : Finset ℕ}, U ⊆ V → (U.card : ℤ) ≤ V.card := fun h => by
    exact_mod_cast Finset.card_le_card h
  have g := greedy_min (n1 := A₁.card) (n2 := A₂.card) (n3 := A₃.card) (n4 := A₄.card)
    (n5 := A₅.card) (a := (A₁ ∩ A₂).card) (b := (A₂ ∩ A₃).card) (c := (A₃ ∩ A₄).card)
    (d := (A₄ ∩ A₅).card) (t1 := (A₁ ∩ A₂ ∩ A₃).card) (t2 := (A₂ ∩ A₃ ∩ A₄).card)
    (t3 := (A₃ ∩ A₄ ∩ A₅).card) (q1 := (A₁ ∩ A₂ ∩ A₃ ∩ A₄).card)
    (q2 := (A₂ ∩ A₃ ∩ A₄ ∩ A₅).card) (f := (A₁ ∩ A₂ ∩ A₃ ∩ A₄ ∩ A₅).card)
    (by exact_mod_cast h₁) (by exact_mod_cast h₂) (by exact_mod_cast h₄) (by exact_mod_cast h₅)
    (cl inter_subset_left) (cl inter_subset_right) (Nat.cast_nonneg _) (inter3_ge _ _ _)
    (Nat.cast_nonneg _) (inter3_ge _ _ _) (Nat.cast_nonneg _) (inter3_ge _ _ _)
    (cl inter_subset_left)
    (cl (fun x => by simp only [mem_inter]; tauto))
    (cl (fun x => by simp only [mem_inter]; tauto))
    (cl (fun x => by simp only [mem_inter]; tauto))
    (Nat.cast_nonneg _)
    (by
      have h := Finset.card_union_add_card_inter (A₁ ∩ A₂ ∩ A₃ ∩ A₄) (A₂ ∩ A₃ ∩ A₄ ∩ A₅)
      have hi : A₁ ∩ A₂ ∩ A₃ ∩ A₄ ∩ (A₂ ∩ A₃ ∩ A₄ ∩ A₅) = A₁ ∩ A₂ ∩ A₃ ∩ A₄ ∩ A₅ := by
        ext x; simp only [mem_inter]; tauto
      have hu : (A₁ ∩ A₂ ∩ A₃ ∩ A₄ ∪ A₂ ∩ A₃ ∩ A₄ ∩ A₅).card ≤ (A₂ ∩ A₃ ∩ A₄).card :=
        Finset.card_le_card (fun x => by simp only [mem_union, mem_inter]; tauto)
      rw [hi] at h
      have : (((A₁ ∩ A₂ ∩ A₃ ∩ A₄).card + (A₂ ∩ A₃ ∩ A₄ ∩ A₅).card : ℕ) : ℤ)
          ≤ (A₂ ∩ A₃ ∩ A₄).card + (A₁ ∩ A₂ ∩ A₃ ∩ A₄ ∩ A₅).card := by
        exact_mod_cast (by omega : (A₁ ∩ A₂ ∩ A₃ ∩ A₄).card + (A₂ ∩ A₃ ∩ A₄ ∩ A₅).card
          ≤ (A₂ ∩ A₃ ∩ A₄).card + (A₁ ∩ A₂ ∩ A₃ ∩ A₄ ∩ A₅).card)
      push_cast at this
      linarith)
  rw [← card_sts_N5z] at g
  exact g

/-- **The universal count bound for actual lists**:
`123125 · ∏ⱼ (nⱼ₋₁nⱼ - eⱼ) ≤ 128018 · |sts A| · n₂n₃n₄` for lists of five or six colours. -/
theorem kappa_lists {A₁ A₂ A₃ A₄ A₅ : Finset ℕ} (h₁ : A₁.card = 5 ∨ A₁.card = 6)
    (h₂ : A₂.card = 5 ∨ A₂.card = 6) (h₃ : A₃.card = 5 ∨ A₃.card = 6)
    (h₄ : A₄.card = 5 ∨ A₄.card = 6) (h₅ : A₅.card = 5 ∨ A₅.card = 6) :
    123125 * (((A₁.card : ℤ) * A₂.card - (A₁ ∩ A₂).card)
        * ((A₂.card : ℤ) * A₃.card - (A₂ ∩ A₃).card) * ((A₃.card : ℤ) * A₄.card - (A₃ ∩ A₄).card)
        * ((A₄.card : ℤ) * A₅.card - (A₄ ∩ A₅).card))
      ≤ 128018 * (sts A₁ A₂ A₃ A₄ A₅).card * (A₂.card * A₃.card * A₄.card) := by
  have cl : ∀ {U V : Finset ℕ}, U ⊆ V → (U.card : ℤ) ≤ V.card := fun h => by
    exact_mod_cast Finset.card_le_card h
  have mn : ∀ U V : Finset ℕ, (U ∩ V).card ≤ min U.card V.card := fun U V =>
    le_min (Finset.card_le_card inter_subset_left) (Finset.card_le_card inter_subset_right)
  have hk := kapOK_sound (kapOK_all h₁ h₂ h₃ h₄ h₅) (mn A₁ A₂) (mn A₂ A₃) (mn A₃ A₄) (mn A₄ A₅)
  have g := N5g_le_card (A₁ := A₁) (A₂ := A₂) (A₃ := A₃) (A₄ := A₄) (A₅ := A₅)
    (by rcases h₁ with h | h <;> omega)
    (by rcases h₂ with h | h <;> omega) (by rcases h₄ with h | h <;> omega)
    (by rcases h₅ with h | h <;> omega)
  have hP : (0 : ℤ) ≤ (A₂.card : ℤ) * A₃.card * A₄.card := by positivity
  have := mul_le_mul_of_nonneg_right g hP
  calc _ ≤ 128018 * N5g A₁.card A₂.card A₃.card A₄.card A₅.card (A₁ ∩ A₂).card
        (A₂ ∩ A₃).card (A₃ ∩ A₄).card (A₄ ∩ A₅).card * (A₂.card * A₃.card * A₄.card) := hk
    _ ≤ _ := by nlinarith

theorem zmu5 (B C : Finset ℕ) (hB : B.card = 6) :
    0 ≤ Lookback.mu 6 B C ∧ Lookback.mu 6 B C ≤ 5 + 1 := by
  refine ⟨Lookback.mu_nonneg hB, ?_⟩
  have := Lookback.mu_le (k := 6) B C
  norm_num at this ⊢; linarith

/-- One row of the main term, from height four's chord bound (`n = 5`). -/
theorem row5 (B C : Finset ℕ) (a b : ℕ) (hB : B.card = 6) (hC : C.card = 6) (hab : a ≠ b) :
    Lr B C a b + 4 / 5 * Lookback.hb C b / 6 - (Lookback.mu 6 B C + 1) * Lookback.hb B a / 120
      ≤ log (((5 + Lookback.hb C b)
          - (((B.erase a) ∩ (C.erase b)).card : ℝ) / (5 + Lookback.hb B a)) / (21 / 5)) := by
  obtain ⟨m0, m1⟩ := zmu5 B C hB
  have he := Lookback.card_inter_erase hB hC hab
  have hle : (((B.erase a) ∩ (C.erase b)).card : ℝ) ≤ 5 + Lookback.hb B a := by
    have := Finset.card_le_card (inter_subset_left (s₁ := B.erase a) (s₂ := C.erase b))
    have h' : (((B.erase a) ∩ (C.erase b)).card : ℝ) ≤ (B.erase a).card := by exact_mod_cast this
    rw [Lookback.card_erase_hb hB] at h'
    have e6 : ((6 : ℕ) : ℝ) - 1 + Lookback.hb B a = 5 + Lookback.hb B a := by norm_num
    linarith
  have h := Lookback.rate_main_chord (n := 5) (by norm_num) (Lookback.hb_cases B a)
    (Lookback.hb_cases C b)
    (Lookback.zz_nonneg B C a b) (Lookback.zz_le_two B C a b) m0 m1
    (e := (((B.erase a) ∩ (C.erase b)).card : ℝ)) (by rw [he]; ring) (Nat.cast_nonneg _) hle
  have e1 : (5 : ℝ) ^ 2 - 5 + 1 = 21 := by norm_num
  have e2 : ((5 : ℝ) - 1) / 5 = 4 / 5 := by norm_num
  have e3 : (5 : ℝ) + 1 = 6 := by norm_num
  have e4 : (5 : ℝ) * 6 * (5 - 1) = 120 := by norm_num
  rw [e1, e2, e3, e4] at h
  unfold Lr
  linarith

theorem first5 {h : ℝ} (hh : h = 0 ∨ h = 1) : 4 / 5 * h / 6 ≤ log ((5 + h) / 5) := by
  have f := Lookback.rate_first (n := 5) (h1 := h) (by norm_num) hh
  have e2 : ((5 : ℝ) - 1) / 5 = 4 / 5 := by norm_num
  have e3 : (5 : ℝ) + 1 = 6 := by norm_num
  rw [e2, e3] at f
  exact f

theorem bonus_le5 {μ h : ℝ} (hh : 0 ≤ h) (hμ : μ ≤ 6) : (μ + 1) * h / 120 ≤ 4 / 5 * h / 6 := by
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith

/-- **The count part, in the reals.** -/
theorem count_real {h1 h2 h3 h4 h5 e2 e3 e4 e5 μ2 μ3 μ4 μ5 L2 L3 L4 L5 N : ℝ}
    (hh1 : h1 = 0 ∨ h1 = 1) (hh2 : h2 = 0 ∨ h2 = 1) (hh3 : h3 = 0 ∨ h3 = 1)
    (hh4 : h4 = 0 ∨ h4 = 1) (hh5 : h5 = 0 ∨ h5 = 1)
    (le2 : e2 ≤ 5 + h1) (le3 : e3 ≤ 5 + h2) (le4 : e4 ≤ 5 + h3) (le5 : e5 ≤ 5 + h4)
    (m2 : μ2 ≤ 6) (m3 : μ3 ≤ 6) (m4 : μ4 ≤ 6) (m5 : μ5 ≤ 6)
    (hk : 123125 * (((5 + h1) * (5 + h2) - e2) * ((5 + h2) * (5 + h3) - e3)
        * ((5 + h3) * (5 + h4) - e4) * ((5 + h4) * (5 + h5) - e5))
      ≤ 128018 * N * ((5 + h2) * (5 + h3) * (5 + h4)))
    (w2 : L2 + 4 / 5 * h2 / 6 - (μ2 + 1) * h1 / 120 ≤ log (((5 + h2) - e2 / (5 + h1)) / (21 / 5)))
    (w3 : L3 + 4 / 5 * h3 / 6 - (μ3 + 1) * h2 / 120 ≤ log (((5 + h3) - e3 / (5 + h2)) / (21 / 5)))
    (w4 : L4 + 4 / 5 * h4 / 6 - (μ4 + 1) * h3 / 120 ≤ log (((5 + h4) - e4 / (5 + h3)) / (21 / 5)))
    (w5 : L5 + 4 / 5 * h5 / 6 - (μ5 + 1) * h4 / 120 ≤ log (((5 + h5) - e5 / (5 + h4)) / (21 / 5))) :
    0 < N ∧ log (123125 / 128018) + (L2 + L3 + L4 + L5) ≤ log (N / (194481 / 125)) := by
  have hb0 : ∀ {h : ℝ}, h = 0 ∨ h = 1 → 0 ≤ h ∧ h ≤ 1 := fun hh => by
    rcases hh with rfl | rfl <;> norm_num
  obtain ⟨h1a, h1b⟩ := hb0 hh1
  obtain ⟨h2a, h2b⟩ := hb0 hh2
  obtain ⟨h3a, h3b⟩ := hb0 hh3
  obtain ⟨h4a, h4b⟩ := hb0 hh4
  obtain ⟨h5a, h5b⟩ := hb0 hh5
  have q1 : (0 : ℝ) < 5 + h1 := by linarith
  have q2 : (0 : ℝ) < 5 + h2 := by linarith
  have q3 : (0 : ℝ) < 5 + h3 := by linarith
  have q4 : (0 : ℝ) < 5 + h4 := by linarith
  set ρ2 := (5 + h2) - e2 / (5 + h1) with hρ2
  set ρ3 := (5 + h3) - e3 / (5 + h2) with hρ3
  set ρ4 := (5 + h4) - e4 / (5 + h3) with hρ4
  set ρ5 := (5 + h5) - e5 / (5 + h4) with hρ5
  have g2 : 4 ≤ ρ2 := by
    have : e2 / (5 + h1) ≤ 1 := (div_le_one q1).mpr le2
    rw [hρ2]; linarith
  have g3 : 4 ≤ ρ3 := by
    have : e3 / (5 + h2) ≤ 1 := (div_le_one q2).mpr le3
    rw [hρ3]; linarith
  have g4 : 4 ≤ ρ4 := by
    have : e4 / (5 + h3) ≤ 1 := (div_le_one q3).mpr le4
    rw [hρ4]; linarith
  have g5 : 4 ≤ ρ5 := by
    have : e5 / (5 + h4) ≤ 1 := (div_le_one q4).mpr le5
    rw [hρ5]; linarith
  have eprod : ((5 + h1) * (5 + h2) - e2) * ((5 + h2) * (5 + h3) - e3)
        * ((5 + h3) * (5 + h4) - e4) * ((5 + h4) * (5 + h5) - e5)
      = (5 + h1) * ρ2 * ρ3 * ρ4 * ρ5 * ((5 + h2) * (5 + h3) * (5 + h4)) := by
    rw [hρ2, hρ3, hρ4, hρ5]; field_simp
  rw [eprod] at hk
  have hP : 0 < (5 + h2) * (5 + h3) * (5 + h4) := by positivity
  have hNk : 123125 / 128018 * ((5 + h1) * ρ2 * ρ3 * ρ4 * ρ5) ≤ N := by
    have h' : (123125 * ((5 + h1) * ρ2 * ρ3 * ρ4 * ρ5)) * ((5 + h2) * (5 + h3) * (5 + h4))
        ≤ (128018 * N) * ((5 + h2) * (5 + h3) * (5 + h4)) := by linarith only [hk]
    have := le_of_mul_le_mul_right h' hP
    linarith only [this]
  have p2 : 0 < ρ2 := by linarith
  have p3 : 0 < ρ3 := by linarith
  have p4 : 0 < ρ4 := by linarith
  have p5 : 0 < ρ5 := by linarith
  have hR0 : 0 < 123125 / 128018 * ((5 + h1) * ρ2 * ρ3 * ρ4 * ρ5) := by positivity
  refine ⟨lt_of_lt_of_le hR0 hNk, ?_⟩
  have hlogN : log (123125 / 128018 * ((5 + h1) * ρ2 * ρ3 * ρ4 * ρ5) / (194481 / 125))
      ≤ log (N / (194481 / 125)) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hNk (by norm_num))
  have esplit : 123125 / 128018 * ((5 + h1) * ρ2 * ρ3 * ρ4 * ρ5) / (194481 / 125)
      = 123125 / 128018 * ((5 + h1) / 5) * (ρ2 / (21 / 5)) * (ρ3 / (21 / 5))
        * (ρ4 / (21 / 5)) * (ρ5 / (21 / 5)) := by ring
  rw [esplit, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    at hlogN
  have f1 := first5 hh1
  have b1 := bonus_le5 h1a m2
  have b2 := bonus_le5 h2a m3
  have b3 := bonus_le5 h3a m4
  have b4 := bonus_le5 h4a m5
  have b5 : 0 ≤ 4 / 5 * h5 / 6 := by positivity
  linarith

/-- **The count part of one state.** -/
theorem count_state {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6)
    (hB₃ : B₃.card = 6) (hB₄ : B₄.card = 6) (hB₅ : B₅.card = 6) {s : T5} (hs : Proper s) :
    0 < ((sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))
        (B₅.erase (r5 s))).card : ℝ) ∧
    log (123125 / 128018) + (Lr B₁ B₂ (r1 s) (r2 s) + Lr B₂ B₃ (r2 s) (r3 s)
        + Lr B₃ B₄ (r3 s) (r4 s) + Lr B₄ B₅ (r4 s) (r5 s))
      ≤ log (((sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))
        (B₅.erase (r5 s))).card : ℝ) / (194481 / 125)) := by
  obtain ⟨p12, p23, p34, p45⟩ := hs
  have hk := kappa_lists (card_erase_56 hB₁ (r1 s)) (card_erase_56 hB₂ (r2 s))
    (card_erase_56 hB₃ (r3 s)) (card_erase_56 hB₄ (r4 s)) (card_erase_56 hB₅ (r5 s))
  have hkR := (Int.cast_le (R := ℝ)).mpr hk
  push_cast at hkR
  have n : ∀ (B : Finset ℕ) (c : ℕ), B.card = 6 → ((B.erase c).card : ℝ) = 5 + Lookback.hb B c :=
    fun B c hB => by rw [Lookback.card_erase_hb hB]; norm_num
  have le : ∀ (B C : Finset ℕ) (a b : ℕ), B.card = 6 →
      (((B.erase a) ∩ (C.erase b)).card : ℝ) ≤ 5 + Lookback.hb B a := fun B C a b hB => by
    rw [← n B a hB]; exact_mod_cast Finset.card_le_card inter_subset_left
  rw [n B₁ _ hB₁, n B₂ _ hB₂, n B₃ _ hB₃, n B₄ _ hB₄, n B₅ _ hB₅] at hkR
  exact count_real (Lookback.hb_cases _ _) (Lookback.hb_cases _ _) (Lookback.hb_cases _ _)
    (Lookback.hb_cases _ _) (Lookback.hb_cases _ _) (le B₁ B₂ _ _ hB₁) (le B₂ B₃ _ _ hB₂)
    (le B₃ B₄ _ _ hB₃) (le B₄ B₅ _ _ hB₄) (by linarith [(zmu5 B₁ B₂ hB₁).2])
    (by linarith [(zmu5 B₂ B₃ hB₂).2]) (by linarith [(zmu5 B₃ B₄ hB₃).2])
    (by linarith [(zmu5 B₄ B₅ hB₄).2]) hkR
    (row5 B₁ B₂ _ _ hB₁ hB₂ p12) (row5 B₂ B₃ _ _ hB₂ hB₃ p23) (row5 B₃ B₄ _ _ hB₃ hB₄ p34)
    (row5 B₄ B₅ _ _ hB₄ hB₅ p45)

end GridGen.Five
