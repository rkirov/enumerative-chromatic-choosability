/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.K5.Pattern
import GridGen.Five.K5.Pins
import GridGen.Five.Count5

/-!
# Height five at `k = 5`: the bound for one state

For a proper previous column `s` and next `5`-lists `B₁, …, B₅`, the successors are the proper
colourings from `Aᵢ = Bᵢ.erase sᵢ`, of sizes `nᵢ = 4 + [sᵢ ∉ Bᵢ]`.

* **The count** (`N5g_le_card4`): `|sts A|` is at least its value `N5g` at the greedy profile of
  the interval relaxation (`GridGen/Five/Count5.lean`, `greedy_min4`, for lists of at least four
  colours; the greedy profile is the relaxation minimum, Codex's `N*`, verified at all 24,481
  relaxations in `H5_K5_REVIEW_2026-10-28.md` (c); only the inequality is needed here).
* **Row codes** (`rcode`): `0` if the colour misses its list, else `1 + [∉ previous] + 2 [∉ next]`.
  The consecutive intersections are `3 - μⱼ + hⱼ₋₁ + xⱼ₋₁⁺ + hⱼ + xⱼ⁻` (`card_inter_rcode`).
* **The state bound** (`state55`): with the pattern lemma (`pattern55`),
  `10⁹ · N5g(n, e) · GU ≤ R(n, o(s)) · NUo · GB`, i.e. `GB ≥ GU · (1 + V)`,
  `V = 10⁹ N5g / (R · NU) - 1` (the review's state value (1)).
-/

namespace GridGen.Five.K5

open Finset GridGen.Five GridGen.Five.Ex5

/-! ### Greedy minimality for lists of at least four colours -/

/-- **Greedy minimality** (`GridGen.Five.greedy_min` with lists of at least four colours). -/
theorem greedy_min4 {n1 n2 n3 n4 n5 a b c d t1 t2 t3 q1 q2 f : ℤ}
    (hn1 : 4 ≤ n1) (hn2 : 4 ≤ n2) (hn4 : 4 ≤ n4) (hn5 : 4 ≤ n5)
    (ha : a ≤ n1) (hd : d ≤ n5)
    (ht1 : 0 ≤ t1) (ht1' : a + b - n2 ≤ t1) (ht2 : 0 ≤ t2) (ht2' : b + c - n3 ≤ t2)
    (ht3 : 0 ≤ t3) (ht3' : c + d - n4 ≤ t3)
    (hq1 : q1 ≤ t1) (hq1' : q1 ≤ t2) (hq2 : q2 ≤ t2) (hq2' : q2 ≤ t3)
    (hf : 0 ≤ f) (hf' : q1 + q2 - t2 ≤ f) :
    N5g n1 n2 n3 n4 n5 a b c d ≤ N5z n1 n2 n3 n4 n5 a b c d t1 t2 t3 q1 q2 f := by
  unfold N5g
  set T1 := max 0 (a + b - n2) with hT1
  set T2 := max 0 (b + c - n3) with hT2
  set T3 := max 0 (c + d - n4) with hT3
  set M1 := min T1 T2 with hM1
  set M2 := min T2 T3 with hM2
  set F := max 0 (M1 + M2 - T2) with hF
  set m1 := min t1 t2 with hm1
  set m2 := min t2 t3 with hm2
  have D1 : T1 ≤ t1 := max_le ht1 ht1'
  have D2 : T2 ≤ t2 := max_le ht2 ht2'
  have D3 : T3 ≤ t3 := max_le ht3 ht3'
  have hT10 : 0 ≤ T1 := le_max_left _ _
  have hT20 : 0 ≤ T2 := le_max_left _ _
  have hT30 : 0 ≤ T3 := le_max_left _ _
  have e1 : q1 ≤ m1 := le_min hq1 hq1'
  have e2 : q2 ≤ m2 := le_min hq2 hq2'
  have g1 : m1 - M1 ≤ (t1 - T1) + (t2 - T2) := by
    rw [hm1, hM1]; rcases le_total t1 t2 with h | h <;> rcases le_total T1 T2 with h' | h' <;>
      simp only [min_eq_left, min_eq_right, h, h'] <;> linarith
  have g2 : m2 - M2 ≤ (t2 - T2) + (t3 - T3) := by
    rw [hm2, hM2]; rcases le_total t2 t3 with h | h <;> rcases le_total T2 T3 with h' | h' <;>
      simp only [min_eq_left, min_eq_right, h, h'] <;> linarith
  have g1' : M1 ≤ m1 := min_le_min D1 D2
  have g2' : M2 ≤ m2 := min_le_min D2 D3
  have hm1t2 : m1 ≤ t2 := min_le_right _ _
  have hm2t2 : m2 ≤ t2 := min_le_left _ _
  have gF : F ≤ f + (m1 - q1) + (m2 - q2) + (t2 - T2) := by
    rw [hF]; refine max_le (by linarith) (by linarith)
  have s1 : 0 ≤ (n4 * n5 - d - n5) * (t1 - T1) := by
    apply mul_nonneg _ (by linarith); nlinarith
  have s2 : 0 ≤ (n1 * n5 - n1 - n5 - 1) * (t2 - T2) := by
    apply mul_nonneg _ (by linarith); nlinarith
  have s3 : 0 ≤ (n1 * n2 - a - n1) * (t3 - T3) := by
    apply mul_nonneg _ (by linarith); nlinarith
  have s4 : 0 ≤ (n5 - 1) * (m1 - q1) := mul_nonneg (by linarith) (by linarith)
  have s5 : 0 ≤ (n1 - 1) * (m2 - q2) := mul_nonneg (by linarith) (by linarith)
  have s6 : n5 * (q1 - M1) ≤ n5 * ((t1 - T1) + (t2 - T2) - (m1 - q1)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have s7 : n1 * (q2 - M2) ≤ n1 * ((t2 - T2) + (t3 - T3) - (m2 - q2)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  unfold N5z
  nlinarith

theorem inter3_ge4 (X Y Z : Finset ℕ) :
    ((X ∩ Y).card : ℤ) + (Y ∩ Z).card - Y.card ≤ (X ∩ Y ∩ Z).card := by
  have h := Lookback.triple_ge X Y Z
  exact_mod_cast h

/-- **Greedy minimality for actual lists** of at least four colours. -/
theorem N5g_le_card4 {A₁ A₂ A₃ A₄ A₅ : Finset ℕ} (h₁ : 4 ≤ A₁.card) (h₂ : 4 ≤ A₂.card)
    (h₄ : 4 ≤ A₄.card) (h₅ : 4 ≤ A₅.card) :
    N5g A₁.card A₂.card A₃.card A₄.card A₅.card (A₁ ∩ A₂).card (A₂ ∩ A₃).card (A₃ ∩ A₄).card
      (A₄ ∩ A₅).card ≤ (sts A₁ A₂ A₃ A₄ A₅).card := by
  have cl : ∀ {U V : Finset ℕ}, U ⊆ V → (U.card : ℤ) ≤ V.card := fun h => by
    exact_mod_cast Finset.card_le_card h
  have g := greedy_min4 (n1 := A₁.card) (n2 := A₂.card) (n3 := A₃.card) (n4 := A₄.card)
    (n5 := A₅.card) (a := (A₁ ∩ A₂).card) (b := (A₂ ∩ A₃).card) (c := (A₃ ∩ A₄).card)
    (d := (A₄ ∩ A₅).card) (t1 := (A₁ ∩ A₂ ∩ A₃).card) (t2 := (A₂ ∩ A₃ ∩ A₄).card)
    (t3 := (A₃ ∩ A₄ ∩ A₅).card) (q1 := (A₁ ∩ A₂ ∩ A₃ ∩ A₄).card)
    (q2 := (A₂ ∩ A₃ ∩ A₄ ∩ A₅).card) (f := (A₁ ∩ A₂ ∩ A₃ ∩ A₄ ∩ A₅).card)
    (by exact_mod_cast h₁) (by exact_mod_cast h₂) (by exact_mod_cast h₄) (by exact_mod_cast h₅)
    (cl inter_subset_left) (cl inter_subset_right) (Nat.cast_nonneg _) (inter3_ge4 _ _ _)
    (Nat.cast_nonneg _) (inter3_ge4 _ _ _) (Nat.cast_nonneg _) (inter3_ge4 _ _ _)
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

/-! ### Row codes -/

/-- The code of one row: `0` if the colour misses its list, else `1` (in both neighbours' lists),
`2` (not in the previous one), `3` (not in the next one), `4` (in neither). -/
def rcode (Bp Bi Bn : Finset ℕ) (x : ℕ) : ℕ :=
  if x ∈ Bi then (if x ∈ Bp then (if x ∈ Bn then 1 else 3) else (if x ∈ Bn then 2 else 4))
  else 0

def kH (c : ℕ) : ℕ := if c = 0 then 1 else 0
def kM (c : ℕ) : ℕ := if c = 2 ∨ c = 4 then 1 else 0
def kX (c : ℕ) : ℕ := if c = 3 ∨ c = 4 then 1 else 0
def kU (c : ℕ) : ℕ := if c = 2 ∨ c = 3 ∨ c = 4 then 1 else 0

section codes
variable (Bp Bi Bn : Finset ℕ) (x : ℕ)

theorem kH_code : kH (rcode Bp Bi Bn x) = if x ∈ Bi then 0 else 1 := by
  unfold kH rcode; split_ifs <;> simp_all

theorem kM_code : kM (rcode Bp Bi Bn x) = if x ∈ Bi \ Bp then 1 else 0 := by
  unfold kM rcode; simp only [mem_sdiff]; split_ifs <;> simp_all

theorem kX_code : kX (rcode Bp Bi Bn x) = if x ∈ Bi \ Bn then 1 else 0 := by
  unfold kX rcode; simp only [mem_sdiff]; split_ifs <;> simp_all

theorem kU_code : kU (rcode Bp Bi Bn x) = if x ∈ (Bi \ Bp) ∪ (Bi \ Bn) then 1 else 0 := by
  unfold kU rcode; simp only [mem_union, mem_sdiff]; split_ifs <;> simp_all

theorem rcode_le : rcode Bp Bi Bn x ≤ 4 := by
  unfold rcode; split_ifs <;> norm_num

end codes

theorem card_erase_rcode {B : Finset ℕ} (hB : B.card = 5) (Bp Bn : Finset ℕ) (x : ℕ) :
    (B.erase x).card = 4 + kH (rcode Bp B Bn x) := by
  rw [kH_code]
  by_cases h : x ∈ B
  · rw [Finset.card_erase_of_mem h, hB]; simp [h]
  · rw [Finset.erase_eq_of_notMem h, hB]; simp [h]

theorem mu_eq_of5 {B C : Finset ℕ} {m : ℕ} (h : (B ∩ C).card + m = 5) :
    Lookback.mu 5 B C = m := by
  unfold Lookback.mu
  have : ((B ∩ C).card : ℝ) + m = 5 := by exact_mod_cast h
  push_cast; linarith

/-- **The consecutive intersection from the codes.** -/
theorem card_inter_rcode {B C : Finset ℕ} (hB : B.card = 5) (hC : C.card = 5) {m : ℕ}
    (hm : (B ∩ C).card + m = 5) (Bp Cn : Finset ℕ) {x y : ℕ} (hxy : x ≠ y) :
    ((B.erase x) ∩ (C.erase y)).card + m
      = 3 + kH (rcode Bp B C x) + kX (rcode Bp B C x) + kH (rcode B C Cn y)
        + kM (rcode B C Cn y) := by
  have h := Lookback.card_inter_erase hB hC hxy
  rw [mu_eq_of5 hm] at h
  have e1 : Lookback.hb B x = (kH (rcode Bp B C x) : ℝ) := by
    rw [kH_code]; unfold Lookback.hb; split_ifs <;> simp
  have e2 : Lookback.hb C y = (kH (rcode B C Cn y) : ℝ) := by
    rw [kH_code]; unfold Lookback.hb; split_ifs <;> simp
  have e3 : Lookback.zz B C x y = (kX (rcode Bp B C x) : ℝ) + (kM (rcode B C Cn y) : ℝ) := by
    rw [kX_code, kM_code, Lookback.zz_eq]; split_ifs <;> simp
  rw [e1, e2, e3] at h
  push_cast at h
  have : (((B.erase x) ∩ (C.erase y)).card : ℝ) + m
      = ((3 + kH (rcode Bp B C x) + kX (rcode Bp B C x) + kH (rcode B C Cn y)
        + kM (rcode B C Cn y) : ℕ) : ℝ) := by
    push_cast; linarith
  exact_mod_cast this

/-- The codes of a state. -/
def kcodes (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (s : T5) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  (rcode B₁ B₁ B₂ (r1 s), rcode B₁ B₂ B₃ (r2 s), rcode B₂ B₃ B₄ (r3 s),
    rcode B₃ B₄ B₅ (r4 s), rcode B₄ B₅ B₅ (r5 s))

/-! ### The state bound -/

theorem card_erase45 {B : Finset ℕ} (hB : B.card = 5) (c : ℕ) :
    (B.erase c).card = 4 ∨ (B.erase c).card = 5 := by
  by_cases h : c ∈ B
  · left; rw [Finset.card_erase_of_mem h, hB]
  · right; rw [Finset.erase_eq_of_notMem h, hB]

/-- **The bound for one state**, in the sizes of the successor lists. -/
theorem state55 {w : Wt5} (hw : InCone5 w) {B₁ B₂ B₃ B₄ B₅ : Finset ℕ}
    (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5) (hB₃ : B₃.card = 5) (hB₄ : B₄.card = 5)
    (hB₅ : B₅.card = 5) {s : T5} (hs : Proper s) :
    (1000000000 : ℝ) * (N5g (B₁.erase (r1 s)).card (B₂.erase (r2 s)).card (B₃.erase (r3 s)).card
        (B₄.erase (r4 s)).card (B₅.erase (r5 s)).card
        ((B₁.erase (r1 s)) ∩ (B₂.erase (r2 s))).card ((B₂.erase (r2 s)) ∩ (B₃.erase (r3 s))).card
        ((B₃.erase (r3 s)) ∩ (B₄.erase (r4 s))).card ((B₄.erase (r4 s)) ∩ (B₅.erase (r5 s))).card
        : ℝ) * GU 5 w s
      ≤ Rof (B₁.erase (r1 s)).card (B₂.erase (r2 s)).card (B₃.erase (r3 s)).card
          (B₄.erase (r4 s)).card (B₅.erase (r5 s)).card (orb s) * NUo (orb s)
        * GB w B₁ B₂ B₃ B₄ B₅ s := by
  have c1 := card_erase45 hB₁ (r1 s)
  have c2 := card_erase45 hB₂ (r2 s)
  have c3 := card_erase45 hB₃ (r3 s)
  have c4 := card_erase45 hB₄ (r4 s)
  have c5 := card_erase45 hB₅ (r5 s)
  have hp := pattern55 hw (orb s) c1 c2 c3 c4 c5
  have hN := N5g_le_card4 (A₁ := B₁.erase (r1 s)) (A₂ := B₂.erase (r2 s))
    (A₃ := B₃.erase (r3 s)) (A₄ := B₄.erase (r4 s)) (A₅ := B₅.erase (r5 s))
    (by omega) (by omega) (by omega) (by omega)
  have hN' : (N5g (B₁.erase (r1 s)).card (B₂.erase (r2 s)).card (B₃.erase (r3 s)).card
        (B₄.erase (r4 s)).card (B₅.erase (r5 s)).card
        ((B₁.erase (r1 s)) ∩ (B₂.erase (r2 s))).card ((B₂.erase (r2 s)) ∩ (B₃.erase (r3 s))).card
        ((B₃.erase (r3 s)) ∩ (B₄.erase (r4 s))).card ((B₄.erase (r4 s)) ∩ (B₅.erase (r5 s))).card
        : ℝ) ≤ (sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))
          (B₅.erase (r5 s))).card := by exact_mod_cast hN
  have hU : 0 ≤ GU 5 w s := GU_nonneg55 hw s
  rw [GU_five w hs] at hU ⊢
  unfold GB
  have := mul_le_mul_of_nonneg_left hN' (by positivity : (0 : ℝ) ≤ 1000000000)
  have := mul_le_mul_of_nonneg_right this hU
  linarith

end GridGen.Five.K5
