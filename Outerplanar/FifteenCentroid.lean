/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Cover15
import Outerplanar.ThirteenCentroid

/-!
# The centroid closing through fifteen even faces

Research note `ai_research_notes/OUTERPLANAR_FIFTEEN_EVEN_2026-11-25.md`, step 5 (with
`ai_research_notes/outerplanar/fivemarks/results.md` §3 and `audit.md` §3): at a centroid face all
of whose sides carry at most seven marks, at most fourteen in all around an even face, the count of
the face glued to its sides is at least the ordinary count.

A term of the expansion gives every side a pure type with a code (`Outerplanar/Code15.lean`):

* **odd faces** (`term_close_odd15`): all tables are in `H`; the odd hexagon closure and the glue;
* **even faces of length at least six** (`term_close_long15`, the note's long-face centroid, audit
  gap G2): if one side is in `A H` (scale at least `A ≥ K`) or two are in `D₆ H` (`D₆² ≥ K`), the
  centre law `hexEvenSix`; otherwise every active side carries at least five marks, so there are at
  most two, and one of two is a ball part: one-load closure at the other;
* **squares** (`term_close_sq15`, `Outerplanar/Cover15.lean`).

**`centroid_close15`** assembles the expansion; the side classes are `Kc15`, the root side included.

Formalized by Claude (milestone M5 of `ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`).
-/

namespace Outerplanar.F15

open Finset Outerplanar C15

variable {m : ℕ}

/-! ### Odd faces -/

theorem term_close_odd15 (hm : Odd m) (C : Fin (m + 2) → Finset ℕ) (hC : ∀ i, (C i).card = 3)
    (G : Fin (m + 2) → ℕ → ℕ → ℝ) (hG0 : ∀ i c d, 0 ≤ G i c d) (w : Fin (m + 2) → ℝ)
    (hw : ∀ i, 0 < w i) (τ : Fin (m + 2) → ℕ) (ρ : Fin (m + 2) → Fin 3)
    (hpt : ∀ i, PT (τ i) (ρ i) (C i) (C (i + 1)) (G i) (w i)) :
    6 * (faceConst3 m * ∏ i, w i) ≤ cycSum C G := by
  have hX := side_root (fun i S T Y => Hex S T Y (w i))
    (fun i => pt_hex (hw i) (hG0 i) (hpt i)) 0
  have hface : Hex (C (0 + 1)) (C 0) (faceSum (fun k : Fin m => C (k.castSucc.succ + (0 + 1)))
      (fun _ _ => 1) (fun j => G (j.castSucc + (0 + 1))))
      (1 * faceConst3 m * ∏ j : Fin (m + 1), (w (j.castSucc + (0 + 1)) * 1)) := by
    simp only [mul_one, one_mul]
    exact odd_hex hm (hC _) (hC _) (fun k => hC _) _ (fun j c d => hG0 _ c d) _ (fun j => hw _) hX
  exact close_scaled C hC G hG0 w hw 0 (κ := 1) (t := 1) (fun _ => 1) one_pos (fun _ => one_pos)
    one_pos hface (by rw [mul_one]; exact pt_hex (hw 0) (hG0 0) (hpt 0)) (by simp)

/-! ### Even faces of length at least six -/

/-- The codes with a hexagon scale at least `A`. -/
def hA15 : C15 → Bool
  | L1 => true | L2 => true | T3 => true | T4 => true | H6 => true | _ => false

theorem hA15_ge {c : C15} (h : hA15 c = true) : 17 / 16 ≤ c.hV.val := by
  cases c
  all_goals first
    | exact absurd h (by decide)
    | (simp only [C15.hV, Sc.val_a5]; exact a5_ge)
    | (simp only [C15.hV, Sc.val_A]; norm_num)

theorem term_close_long15 (hm : Even m) (hm4 : 4 ≤ m) (C : Fin (m + 2) → Finset ℕ)
    (hC : ∀ i, (C i).card = 3) (G : Fin (m + 2) → ℕ → ℕ → ℝ) (hG0 : ∀ i c d, 0 ≤ G i c d)
    (w : Fin (m + 2) → ℝ) (hw : ∀ i, 0 < w i) (τ : Fin (m + 2) → ℕ) (ρ : Fin (m + 2) → Fin 3)
    (hpt : ∀ i, PT (τ i) (ρ i) (C i) (C (i + 1)) (G i) (w i))
    (hmk : ∑ i, (code15 (τ i) (ρ i)).marks ≤ 14) :
    6 * (faceConst3 m * ∏ i, w i) ≤ cycSum C G := by
  set cd : Fin (m + 2) → C15 := fun i => code15 (τ i) (ρ i) with hcd
  have hmk' : ∑ i, (cd i).marks ≤ 14 := hmk
  have hcap := fun i => cap_hex15 (hw i) (hG0 i) (hpt i)
  -- the centre law
  have centre : 59 / 56 ≤ ∏ i, (cd i).hV.val → 6 * (faceConst3 m * ∏ i, w i) ≤ cycSum C G := by
    intro hK
    have hX := side_root (fun i S T Y => Hex S T Y (w i * (cd i).hV.val)) hcap 0
    have key := hexEvenSix m hm hm4 _ _ _ (hC _) (fun k => hC _)
      (fun j => G (j.castSucc + (0 + 1))) (fun j c d => hG0 _ c d)
      (fun j => w (j.castSucc + (0 + 1)) * (cd (j.castSucc + (0 + 1))).hV.val)
      (fun j => mul_pos (hw _) (Sc.val_pos _)) hX
    refine close_scaled C hC G hG0 w hw 0 (κ := 56 / 59) (t := (cd 0).hV.val)
      (fun j => (cd (j.castSucc + (0 + 1))).hV.val) (by norm_num)
      (fun j => Sc.val_pos _) (Sc.val_pos _) key (hcap 0) ?_
    have := prod_root (fun i => (cd i).hV.val) 0
    rw [mul_assoc, this]
    nlinarith
  have hge : ∀ i, 1 ≤ (cd i).hV.val := fun i => C15.hV_ge _
  have hprodge : ∀ i₀, (cd i₀).hV.val ≤ ∏ i, (cd i).hV.val := fun i₀ => by
    rw [← Finset.mul_prod_erase univ _ (mem_univ i₀)]
    have : 1 ≤ ∏ i ∈ univ.erase i₀, (cd i).hV.val := Finset.one_le_prod₀ fun i _ => hge i
    nlinarith [hge i₀]
  by_cases hA : ∃ i, hA15 (cd i) = true
  · obtain ⟨i, hi⟩ := hA
    exact centre (le_trans (by norm_num) ((hA15_ge hi).trans (hprodge i)))
  push Not at hA
  by_cases hbig : ∃ i₁ i₂, i₁ ≠ i₂ ∧ cd i₁ = .H7 ∧ cd i₂ = .H7
  · obtain ⟨i₁, i₂, h12, h1, h2⟩ := hbig
    refine centre ?_
    have h2s : (cd i₁).hV.val * (cd i₂).hV.val ≤ ∏ i, (cd i).hV.val :=
      prod_scale_two h12 (fun i => (cd i).hV.val) hge
    rw [h1, h2, show C15.H7.hV.val = Outerplanar.d6 from Sc.val_d6] at h2s
    have := d6_sq
    linarith
  push Not at hbig
  -- every active side carries at least five marks and is a ball part or the hexagon part of seven
  have hact : ∀ i, cd i ≠ .I → 5 ≤ (cd i).marks ∧ (cd i ≠ .H7 → (cd i).hasB = true ∧
      (cd i).bV = Sc.one) := by
    intro i hi
    have hAi := hA i
    generalize cd i = c at hi hAi ⊢
    cases c <;> simp_all [hA15, C15.marks, C15.hasB, C15.bV]
  by_cases h2 : ∃ i₁ i₂, i₁ ≠ i₂ ∧ cd i₁ ≠ .I ∧ cd i₂ ≠ .I
  · obtain ⟨i₁, i₂, h12, ha1, ha2⟩ := h2
    have hthird : ∀ i, i ≠ i₁ → i ≠ i₂ → cd i = .I := by
      intro i hi1 hi2
      by_contra hi
      have s3 : (cd i₁).marks + (cd i₂).marks + (cd i).marks ≤ ∑ i, (cd i).marks := by
        have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => (cd i).marks)
          (subset_univ ({i₁, i₂, i} : Finset (Fin (m + 2)))) fun _ _ _ => Nat.zero_le _
        rw [Finset.sum_insert (by simp [h12, Ne.symm hi1]), Finset.sum_pair (Ne.symm hi2)] at this
        omega
      have := (hact i₁ ha1).1
      have := (hact i₂ ha2).1
      have := (hact i hi).1
      omega
    obtain ⟨a, b, hab, hbB, hbI, hrest⟩ : ∃ a b, a ≠ b ∧ ((cd b).hasB = true ∧
        (cd b).bV = Sc.one) ∧ cd b ≠ .I ∧ ∀ i, i ≠ a → i ≠ b → cd i = .I := by
      by_cases hb2 : cd i₂ = .H7
      · have hb1 : cd i₁ ≠ .H7 := fun h => hbig i₁ i₂ h12 h hb2
        exact ⟨i₂, i₁, Ne.symm h12, (hact i₁ ha1).2 hb1, ha1, fun i h1 h2 => hthird i h2 h1⟩
      · exact ⟨i₁, i₂, h12, (hact i₂ ha2).2 hb2, ha2, hthird⟩
    obtain ⟨j₀, hj₀⟩ := exists_posIdx a b (Ne.symm hab)
    have hX := side_root (fun i S T Y => (i = b → InBall S T Y (w i * (cd i).bV.val)) ∧
      (i ≠ b → i ≠ a → Dominant S T Y (w i)))
      (fun i => ⟨fun h => h ▸ cap_B15 (hw b) hbB.1 (h ▸ hpt i),
        fun h1 h2 => cap_I15 (hrest i h2 h1) (hpt i)⟩) a
    have key := ball_one (j₀ := j₀) (hC _) (hC _) (fun k => hC _) (fun j c d => hG0 _ c d)
      (fun j => hw (j.castSucc + (a + 1))) one_pos (by
        have := (hX j₀).1 hj₀
        rw [hj₀] at this ⊢
        rw [hbB.2, Sc.val_one] at this
        exact this)
      fun j hj => (hX j).2 (fun h => hj (pos_inj a (h.trans hj₀.symm))) (pos_ne a j)
    rw [mul_one] at key
    have hH : Hex (C (a + 1)) (C a) (faceSum (fun k : Fin m => C (k.castSucc.succ + (a + 1)))
        (fun _ _ => 1) (fun j => G (j.castSucc + (a + 1))))
        (1 * faceConst3 m * ∏ j : Fin (m + 1), (w (j.castSucc + (a + 1)) * 1)) := by
      simp only [one_mul, mul_one]
      exact fun _ _ hm' hpq => key.hex (fc_prod_nonneg
        (w := fun j : Fin (m + 1) => w (j.castSucc + (a + 1))) fun j => hw _)
        (faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one) fun j c d => hG0 _ c d) hm' hpq
    exact close_scaled C hC G hG0 w hw a (κ := 1) (t := 1) (fun _ => 1) one_pos
      (fun _ => one_pos) one_pos hH (by rw [mul_one]; exact pt_hex (hw a) (hG0 a) (hpt a))
      (by simp)
  · push Not at h2
    have hm2 : 2 ≤ m := by omega
    by_cases h1 : ∃ i₀, cd i₀ ≠ .I
    · obtain ⟨i₀, hi₀⟩ := h1
      exact close_bare hm hm2 C hC G hG0 w hw i₀ (pt_hex (hw i₀) (hG0 i₀) (hpt i₀))
        fun i hi => cap_I15 (by by_contra h; exact hi₀ (h2 i i₀ hi h)) (hpt i)
    · push Not at h1
      exact close_bare hm hm2 C hC G hG0 w hw 0 (pt_hex (hw 0) (hG0 0) (hpt 0))
        fun i _ => cap_I15 (h1 i) (hpt i)

/-! ### All faces -/

theorem pt_valid1' {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} {k : ℕ} {r : Fin 3} (hv : 0 < v)
    (h : PT k r S T Y v) : r = 1 → 1 ≤ k := by
  rintro rfl; exact pt_ge1 hv (by decide) h

theorem pt_valid2' {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} {k : ℕ} {r : Fin 3} (hv : 0 < v)
    (h : PT k r S T Y v) : r = 2 → 6 ≤ k := by
  rintro rfl; exact pt_ge6 hv rfl h

/-- **A term of the centroid face closes.** -/
theorem term_close15 (hm1 : 1 ≤ m) (C : Fin (m + 2) → Finset ℕ) (hC : ∀ i, (C i).card = 3)
    (G : Fin (m + 2) → ℕ → ℕ → ℝ) (hG0 : ∀ i c d, 0 ≤ G i c d) (w : Fin (m + 2) → ℝ)
    (hw : ∀ i, 0 < w i) (τ : Fin (m + 2) → ℕ) (ρ : Fin (m + 2) → Fin 3)
    (hpt : ∀ i, PT (τ i) (ρ i) (C i) (C (i + 1)) (G i) (w i)) (hτ7 : ∀ i, τ i ≤ 7)
    (hmk : Even m → ∑ i, (code15 (τ i) (ρ i)).marks ≤ 14) :
    6 * (faceConst3 m * ∏ i, w i) ≤ cycSum C G := by
  rcases Nat.even_or_odd m with hev | hodd
  · rcases Nat.lt_or_ge m 4 with h4 | h4
    · obtain rfl : m = 2 := by obtain ⟨k, hk⟩ := hev; omega
      refine term_close_sq15 C hC G hG0 w hw τ ρ hpt hτ7 ?_
      have := hmk hev
      rwa [Fin.sum_univ_four] at this
    · exact term_close_long15 hev h4 C hC G hG0 w hw τ ρ hpt (hmk hev)
  · exact term_close_odd15 hodd C hC G hG0 w hw τ ρ hpt

/-- **The centroid closing**: a face with `m` interior vertices whose path edges carry the classes
`Kc15 (τ j)`, glued along its root edge to a table of the class `Kc15 k₀`, every side with at most
seven marks and at most fourteen on the sides of an even face, has at least the ordinary number of
colourings. -/
theorem centroid_close15 (hm1 : 1 ≤ m) (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ)
    (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 < A j) (τ : Fin (m + 1) → ℕ) (hτ7 : ∀ j, τ j ≤ 7)
    (hE : ∀ j, Kc15 (τ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j))
    (k₀ : ℕ) (hk₀ : k₀ ≤ 7) (W' : ℕ → ℕ → ℝ) (hW'0 : ∀ c d, 0 ≤ W' c d) (A' : ℝ) (hA' : 0 < A')
    (hW' : Kc15 k₀ Lv Lu W' A') (hsum : Even m → k₀ + ∑ j, τ j ≤ 14) :
    6 * ((faceConst3 m * ∏ j, A j) * A')
      ≤ ∑ d ∈ Lv, ∑ c ∈ Lu, (if c ≠ d then W' d c * faceSum Li (fun _ _ => 1) E c d else 0) := by
  classical
  set W'' : ℕ → ℕ → ℝ := fun d c => if c ≠ d then W' d c else 0 with hW''
  have hW''0 : ∀ d c, 0 ≤ W'' d c := fun d c => by simp only [hW'']; split_ifs <;> simp [hW'0]
  have hW''k : Kc15 k₀ Lv Lu W'' A' :=
    Kc15_mono_table (fun d _ c _ hdc => by simp [hW'', Ne.symm hdc]) hW'
  have hsumEq : ∑ d ∈ Lv, ∑ c ∈ Lu, (if c ≠ d then W' d c * faceSum Li (fun _ _ => 1) E c d
      else 0) = ∑ d ∈ Lv, ∑ c ∈ Lu, W'' d c * faceSum Li (fun _ _ => 1) E c d :=
    Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => by
      simp only [hW'']; split_ifs <;> simp
  rw [hsumEq, closing_eq]
  set C := pathList Lu Lv Li with hCdef
  set F := cycF E W'' with hFdef
  obtain ⟨τc, hτl, hτs⟩ : ∃ τc : Fin (m + 2) → ℕ, τc (Fin.last (m + 1)) = k₀ ∧
      ∀ j : Fin (m + 1), τc j.castSucc = τ j :=
    ⟨Fin.lastCases (motive := fun _ => ℕ) k₀ τ, by simp, by simp⟩
  obtain ⟨Ac, hAl, hAs⟩ : ∃ Ac : Fin (m + 2) → ℝ, Ac (Fin.last (m + 1)) = A' ∧
      ∀ j : Fin (m + 1), Ac j.castSucc = A j :=
    ⟨Fin.lastCases (motive := fun _ => ℝ) A' A, by simp, by simp⟩
  have hC : ∀ i, (C i).card = 3 := pathList_card hLu hLv hLi
  have hlast : C (Fin.last (m + 1)) = Lv := consSnoc_last _ _ _ _ (by simp)
  have hzero : C 0 = Lu := consSnoc_zero _ _ _ _ rfl
  have hcls : ∀ i, Kc15 (τc i) (C i) (C (i + 1)) (F i) (Ac i) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hτl, hAl, hFdef, cycF_last, hlast, Fin.last_add_one, hzero]
      exact hW''k
    · rw [hτs, hAs, hFdef, cycF_castSucc, Fin.coeSucc_eq_succ]
      exact hE j
  have hτc7 : ∀ i, τc i ≤ 7 := fun i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hτl]; exact hk₀
    · rw [hτs]; exact hτ7 j
  have hAc0 : ∀ i, 0 ≤ Ac i := fun i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hAl]; exact hA'.le
    · rw [hAs]; exact (hA j).le
  obtain ⟨u, v₁, v₂, Y₁, Y₂, hu, hv₁, hv₂, huv, hY₁, hY₂, hP1, hP2, hEY⟩ :=
    face15_data τc C (fun i => C (i + 1)) F Ac hAc0 hcls
  have hG0 := gT3_nonneg hu hY₁ hY₂
  have hF0 : ∀ i c d, 0 ≤ F i c d := fun i c d => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [hFdef, cycF_last]; exact hW''0 c d
    · simp only [hFdef, cycF_castSucc]; exact hE0 j c d
  have hexp := cycSum_expand C F (gT3 u Y₁ Y₂) hG0
    (fun i => sum_gT3_le i (hF0 i) (hEY i))
  refine le_trans ?_ hexp
  have hw0 := wT3_nonneg hu hv₁ hv₂
  have hα := faceConst3_pos m
  have hconst : 6 * ((faceConst3 m * ∏ j, A j) * A')
      ≤ ∑ ρ : Fin (m + 2) → Fin 3, 6 * (faceConst3 m * ∏ i, wT3 u v₁ v₂ i (ρ i)) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have e : (∏ j, A j) * A' = ∏ i, Ac i := by
      rw [Fin.prod_univ_castSucc (f := Ac), hAl]
      simp only [hAs]
    rw [mul_assoc, e]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hα.le) (by norm_num)
    calc ∏ i, Ac i ≤ ∏ i, (u i + v₁ i + v₂ i) :=
          Finset.prod_le_prod₀ (fun i _ => hAc0 i) fun i _ => huv i
      _ = ∑ ρ : Fin (m + 2) → Fin 3, ∏ i, wT3 u v₁ v₂ i (ρ i) := by
          simp only [← sum_wT3]
          rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine hconst.trans (Finset.sum_le_sum fun ρ _ => ?_)
  by_cases hz : ∃ i, wT3 u v₁ v₂ i (ρ i) = 0
  · obtain ⟨i, hi⟩ := hz
    rw [Finset.prod_eq_zero (mem_univ i) hi, mul_zero, mul_zero]
    exact cycSum_nonneg C fun i c d => hG0 i (ρ i) c d
  push Not at hz
  have hρ : ∀ i, 0 < wT3 u v₁ v₂ i (ρ i) := fun i => lt_of_le_of_ne (hw0 i (ρ i)) (hz i).symm
  have hpt : ∀ i, PT (τc i) (ρ i) (C i) (C (i + 1)) (gT3 u Y₁ Y₂ i (ρ i)) (wT3 u v₁ v₂ i (ρ i)) :=
    fun i => gT3_pt15 (k := τc i) i (ρ i) (hY₁ i) (hY₂ i) (hP1 i) (hP2 i)
  refine term_close15 hm1 C hC _ (fun i c d => hG0 i (ρ i) c d) _ hρ τc ρ hpt hτc7 fun hev => ?_
  calc ∑ i, (code15 (τc i) (ρ i)).marks ≤ ∑ i, τc i := Finset.sum_le_sum fun i _ => by
        have := code15_marks (τc i) (ρ i) (pt_valid1' (hρ i) (hpt i)) (pt_valid2' (hρ i) (hpt i))
        split_ifs at this <;> omega
    _ = k₀ + ∑ j, τ j := by
        rw [Fin.sum_univ_castSucc, hτl]
        simp only [hτs]
        ring
    _ ≤ 14 := hsum hev

end Outerplanar.F15
