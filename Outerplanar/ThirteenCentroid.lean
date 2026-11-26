/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.SqCover
import Outerplanar.MarkFiveSixRule

/-!
# The centroid closing through thirteen even faces

Research note `ai_research_notes/OUTERPLANAR_THIRTEEN_AND_GAUGE_OBSTRUCTION_2026-11-23.md`, Step 3
(another AI session of this repository's collaboration; audited): at a centroid face all of whose
sides carry at most six marks, at most twelve in all around an even face, the count of the face
glued to its sides is at least the ordinary count.

A term of the expansion gives every side a pure type with a code (`Outerplanar/SqClose.lean`):

* **odd faces** (`term_close_odd`): all tables are in `H`; the odd hexagon closure and the glue;
* **even faces of length at least six** (`term_close_long`): if one side is in `A H`, or two are in
  `D₆ H`, the centre law `hexEvenSix` (cost `K ≤ A ≤ D₆²`); otherwise every active side carries at
  least five marks, so there are at most two, and one of two is a ball part: one-load closure (or
  the bare face) at the other;
* **squares** (`term_close_sq`, `Outerplanar/SqCover.lean`).

**`centroid_close`** assembles the expansion: the side classes are `Kc6`, the root side included.
The note's case analysis (heavy and light sides, multi-branch heavy sides) is not needed in this
form: every side is a single class (branches at a vertex are merged by the vertex rule), and the
codes of a term carry all the information the laws use.

Formalized by Claude (milestone M3 of `ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`).
-/

namespace Outerplanar

open Finset Code

variable {m : ℕ}

/-! ### Positions in the path of a root -/

theorem exists_posIdx (r i : Fin (m + 2)) (h : i ≠ r) : ∃ j : Fin (m + 1), j.castSucc + (r + 1) = i := by
  have hx : i - (r + 1) ≠ Fin.last (m + 1) := fun e => by
    apply h
    have : i = Fin.last (m + 1) + (r + 1) := by rw [← e, sub_add_cancel]
    rw [this, add_comm r 1, ← add_assoc, Fin.last_add_one, zero_add]
  exact ⟨(i - (r + 1)).castPred hx, by rw [Fin.castSucc_castPred, sub_add_cancel]⟩

theorem pos_ne (r : Fin (m + 2)) (j : Fin (m + 1)) : j.castSucc + (r + 1) ≠ r := fun e => by
  have h : j.castSucc + 1 = Fin.last (m + 1) + 1 := by
    rw [Fin.last_add_one]
    calc j.castSucc + 1 = j.castSucc + (r + 1) - r := by abel
      _ = 0 := by rw [e, sub_self]
  exact Fin.castSucc_ne_last j (add_right_cancel h)

theorem pos_inj (r : Fin (m + 2)) {j j' : Fin (m + 1)}
    (h : j.castSucc + (r + 1) = j'.castSucc + (r + 1)) : j = j' :=
  Fin.castSucc_injective _ (add_right_cancel h)

/-! ### Odd faces -/

theorem term_close_odd (hm : Odd m) (C : Fin (m + 2) → Finset ℕ) (hC : ∀ i, (C i).card = 3)
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
    rcases Nat.lt_or_ge m 3 with h3 | h3
    · obtain rfl : m = 1 := by obtain ⟨k, hk⟩ := hm; omega
      rw [faceConst3_one, one_mul]
      exact hex_tri (fun k => hC _) (fun j c d => hG0 _ c d) (fun j => (hw _).le) hX
    · exact hexOddClosed m hm h3 _ _ _ (hC _) (hC _) (fun k => hC _) _ (fun j c d => hG0 _ c d) _
        (fun j => hw _) hX
  exact close_scaled C hC G hG0 w hw 0 (κ := 1) (t := 1) (fun _ => 1) one_pos (fun _ => one_pos)
    one_pos hface (by rw [mul_one]; exact pt_hex (hw 0) (hG0 0) (hpt 0)) (by simp)

/-! ### Even faces of length at least six -/

/-- The bare even face read at `r`, all other sides constant. -/
theorem close_bare (hm : Even m) (hm2 : 2 ≤ m) (C : Fin (m + 2) → Finset ℕ)
    (hC : ∀ i, (C i).card = 3) (G : Fin (m + 2) → ℕ → ℕ → ℝ) (hG0 : ∀ i c d, 0 ≤ G i c d)
    (w : Fin (m + 2) → ℝ) (hw : ∀ i, 0 < w i) (r : Fin (m + 2))
    (hroot : Hex (C r) (C (r + 1)) (G r) (w r))
    (hD : ∀ i, i ≠ r → Dominant (C i) (C (i + 1)) (G i) (w i)) :
    6 * (faceConst3 m * ∏ i, w i) ≤ cycSum C G := by
  have hX := side_root (fun i S T Y => i ≠ r → Dominant S T Y (w i)) hD r
  have key := mx1_even_bare hm hm2 _ _ _ (hC _) (hC _) (fun k => hC _)
    (fun j => G (j.castSucc + (r + 1))) (fun j c d => hG0 _ c d) (fun j => w (j.castSucc + (r + 1)))
    (fun j => (hw _).le) fun j => hX j (pos_ne r j)
  have hH := Kc_hex (fc_prod_nonneg (w := fun j : Fin (m + 1) => w (j.castSucc + (r + 1)))
    fun j => hw _)
    (faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one) fun j c d => hG0 _ c d) 1 key
  exact close_scaled C hC G hG0 w hw r (κ := 1) (t := 1) (fun _ => 1) one_pos (fun _ => one_pos)
    one_pos (by simpa using hH) (by rwa [mul_one]) (by simp)

theorem term_close_long (hm : Even m) (hm4 : 4 ≤ m) (C : Fin (m + 2) → Finset ℕ)
    (hC : ∀ i, (C i).card = 3) (G : Fin (m + 2) → ℕ → ℕ → ℝ) (hG0 : ∀ i c d, 0 ≤ G i c d)
    (w : Fin (m + 2) → ℝ) (hw : ∀ i, 0 < w i) (τ : Fin (m + 2) → ℕ) (ρ : Fin (m + 2) → Fin 3)
    (hpt : ∀ i, PT (τ i) (ρ i) (C i) (C (i + 1)) (G i) (w i))
    (hmk : ∑ i, (code (τ i) (ρ i)).marks ≤ 12) :
    6 * (faceConst3 m * ∏ i, w i) ≤ cycSum C G := by
  set cd : Fin (m + 2) → Code := fun i => code (τ i) (ρ i) with hcd
  have hmk' : ∑ i, (cd i).marks ≤ 12 := hmk
  have hcap := fun i => cap_hex (hw i) (hG0 i) (hpt i)
  -- the centre law
  have centre : 59 / 56 ≤ ∏ i, (cd i).hsc → 6 * (faceConst3 m * ∏ i, w i) ≤ cycSum C G := by
    intro hK
    have hX := side_root (fun i S T Y => Hex S T Y (w i * (cd i).hsc)) hcap 0
    have key := hexEvenSix m hm hm4 _ _ _ (hC _) (fun k => hC _)
      (fun j => G (j.castSucc + (0 + 1))) (fun j c d => hG0 _ c d)
      (fun j => w (j.castSucc + (0 + 1)) * (cd (j.castSucc + (0 + 1))).hsc)
      (fun j => mul_pos (hw _) (lt_of_lt_of_le one_pos (Code.hsc_ge _))) hX
    refine close_scaled C hC G hG0 w hw 0 (κ := 56 / 59) (t := (cd 0).hsc)
      (fun j => (cd (j.castSucc + (0 + 1))).hsc) (by norm_num)
      (fun j => lt_of_lt_of_le one_pos (Code.hsc_ge _)) (lt_of_lt_of_le one_pos (Code.hsc_ge _))
      key (hcap 0) ?_
    have := prod_root (fun i => (cd i).hsc) 0
    rw [mul_assoc, this]
    nlinarith
  have hge : ∀ i, 1 ≤ (cd i).hsc := fun i => Code.hsc_ge _
  have hprodge : ∀ i₀, (cd i₀).hsc ≤ ∏ i, (cd i).hsc := fun i₀ => by
    rw [← Finset.mul_prod_erase univ _ (mem_univ i₀)]
    have : 1 ≤ ∏ i ∈ univ.erase i₀, (cd i).hsc := Finset.one_le_prod₀ fun i _ => hge i
    nlinarith [hge i₀]
  by_cases hA : ∃ i, (cd i).hA = true
  · obtain ⟨i, hi⟩ := hA
    exact centre (le_trans (by norm_num) ((Code.hsc_A hi).trans (hprodge i)))
  push Not at hA
  by_cases hbig : ∃ i₁ i₂, i₁ ≠ i₂ ∧ (cd i₁).hbig = true ∧ (cd i₂).hbig = true
  · obtain ⟨i₁, i₂, h12, h1, h2⟩ := hbig
    refine centre ?_
    have : (cd i₁).hsc * (cd i₂).hsc ≤ ∏ i, (cd i).hsc := by
      rw [← Finset.mul_prod_erase univ _ (mem_univ i₁),
        ← Finset.mul_prod_erase (univ.erase i₁) _ (mem_erase.mpr ⟨Ne.symm h12, mem_univ i₂⟩)]
      have h1 : 1 ≤ ∏ i ∈ (univ.erase i₁).erase i₂, (cd i).hsc :=
        Finset.one_le_prod₀ fun i _ => hge i
      have h0 : 0 ≤ (cd i₁).hsc * (cd i₂).hsc := by nlinarith [hge i₁, hge i₂]
      have := mul_le_mul_of_nonneg_left h1 h0
      linarith [mul_assoc ((cd i₁).hsc) ((cd i₂).hsc) (∏ i ∈ (univ.erase i₁).erase i₂, (cd i).hsc)]
    have b1 := Code.hsc_big h1
    have b2 := Code.hsc_big h2
    have := d6_sq
    have := d6_pos
    nlinarith
  push Not at hbig
  -- every active side is a ball part or the hexagon part of six marks, with at least five marks
  have hact : ∀ i, cd i ≠ .I → 5 ≤ (cd i).marks ∧ ((cd i).hbig = false → (cd i).hasB = true) := by
    intro i hi
    have hAi := hA i
    generalize cd i = c at hi hAi ⊢
    cases c <;> simp [Code.hA, Code.marks, Code.hbig, Code.hasB] at hi hAi ⊢
  by_cases h2 : ∃ i₁ i₂, i₁ ≠ i₂ ∧ cd i₁ ≠ .I ∧ cd i₂ ≠ .I
  · obtain ⟨i₁, i₂, h12, ha1, ha2⟩ := h2
    -- no third active side
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
    -- one of the two is a ball part
    obtain ⟨a, b, hab, hbB, hbI, hrest⟩ : ∃ a b, a ≠ b ∧ (cd b).hasB = true ∧ cd b ≠ .I ∧
        ∀ i, i ≠ a → i ≠ b → cd i = .I := by
      by_cases hb2 : (cd i₂).hbig = true
      · have hb1 : (cd i₁).hbig = false := by
          by_contra h
          exact hbig i₁ i₂ h12 (by simpa using h) hb2
        exact ⟨i₂, i₁, Ne.symm h12, (hact i₁ ha1).2 hb1, ha1, fun i h1 h2 => hthird i h2 h1⟩
      · exact ⟨i₁, i₂, h12, (hact i₂ ha2).2 (by simpa using hb2), ha2, hthird⟩
    obtain ⟨j₀, hj₀⟩ := exists_posIdx a b (Ne.symm hab)
    have hX := side_root (fun i S T Y => (i = b → InBall S T Y (w i * (cd i).bsc)) ∧
      (i ≠ b → i ≠ a → Dominant S T Y (w i)))
      (fun i => ⟨fun h => h ▸ cap_B (hw b) (hG0 b) hbB (h ▸ hpt i),
        fun h1 h2 => cap_I (hrest i h2 h1) (hpt i)⟩) a
    have hbsc : (cd b).bsc = 1 := by
      have hAb := hA b
      have hbB' := hbB
      have hbI' := hbI
      generalize cd b = c at hAb hbB' hbI' ⊢
      cases c <;> simp [Code.bsc, Code.hA, Code.hasB] at hAb hbB' hbI' ⊢
    have key := ball_one (j₀ := j₀) (hC _) (hC _) (fun k => hC _) (fun j c d => hG0 _ c d)
      (fun j => hw (j.castSucc + (a + 1))) one_pos (by
        have := (hX j₀).1 hj₀
        rw [hj₀] at this ⊢
        rw [hbsc] at this
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
        fun i hi => cap_I (by by_contra h; exact hi₀ (h2 i i₀ hi h)) (hpt i)
    · push Not at h1
      exact close_bare hm hm2 C hC G hG0 w hw 0 (pt_hex (hw 0) (hG0 0) (hpt 0))
        fun i _ => cap_I (h1 i) (hpt i)

/-! ### All faces -/

theorem pt_valid1 {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} {k : ℕ} {r : Fin 3} (hv : 0 < v)
    (h : PT k r S T Y v) : r = 1 → 1 ≤ k := by
  rintro rfl; exact pt_one_ge hv h

theorem pt_valid2 {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} {k : ℕ} {r : Fin 3} (hv : 0 < v)
    (h : PT k r S T Y v) : r = 2 → 5 ≤ k := by
  rintro rfl; exact pt_two_ge hv h

/-- **A term of the centroid face closes.** -/
theorem term_close (hm1 : 1 ≤ m) (C : Fin (m + 2) → Finset ℕ) (hC : ∀ i, (C i).card = 3)
    (G : Fin (m + 2) → ℕ → ℕ → ℝ) (hG0 : ∀ i c d, 0 ≤ G i c d) (w : Fin (m + 2) → ℝ)
    (hw : ∀ i, 0 < w i) (τ : Fin (m + 2) → ℕ) (ρ : Fin (m + 2) → Fin 3)
    (hpt : ∀ i, PT (τ i) (ρ i) (C i) (C (i + 1)) (G i) (w i))
    (hmk : Even m → ∑ i, (code (τ i) (ρ i)).marks ≤ 12) :
    6 * (faceConst3 m * ∏ i, w i) ≤ cycSum C G := by
  rcases Nat.even_or_odd m with hev | hodd
  · rcases Nat.lt_or_ge m 4 with h4 | h4
    · obtain rfl : m = 2 := by obtain ⟨k, hk⟩ := hev; omega
      refine term_close_sq C hC G hG0 w hw τ ρ hpt ?_
      have := hmk hev
      rwa [Fin.sum_univ_four] at this
    · exact term_close_long hev h4 C hC G hG0 w hw τ ρ hpt (hmk hev)
  · exact term_close_odd hodd C hC G hG0 w hw τ ρ hpt

/-- **The centroid closing**: a face with `m` interior vertices whose path edges carry the classes
`Kc6 (τ j)`, glued along its root edge to a table of the class `Kc6 k₀`, at most twelve marks on
the sides of an even face, has at least the ordinary number of colourings. -/
theorem centroid_close (hm1 : 1 ≤ m) (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ)
    (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 < A j) (τ : Fin (m + 1) → ℕ)
    (hE : ∀ j, Kc6 (τ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j))
    (k₀ : ℕ) (W' : ℕ → ℕ → ℝ) (hW'0 : ∀ c d, 0 ≤ W' c d) (A' : ℝ) (hA' : 0 < A')
    (hW' : Kc6 k₀ Lv Lu W' A') (hsum : Even m → k₀ + ∑ j, τ j ≤ 12) :
    6 * ((faceConst3 m * ∏ j, A j) * A')
      ≤ ∑ d ∈ Lv, ∑ c ∈ Lu, (if c ≠ d then W' d c * faceSum Li (fun _ _ => 1) E c d else 0) := by
  classical
  set W'' : ℕ → ℕ → ℝ := fun d c => if c ≠ d then W' d c else 0 with hW''
  have hW''0 : ∀ d c, 0 ≤ W'' d c := fun d c => by simp only [hW'']; split_ifs <;> simp [hW'0]
  have hW''k : Kc6 k₀ Lv Lu W'' A' :=
    Kc6_mono_table (fun d _ c _ hdc => by simp [hW'', Ne.symm hdc]) k₀ hW'
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
  have hcls : ∀ i, Kc6 (τc i) (C i) (C (i + 1)) (F i) (Ac i) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hτl, hAl, hFdef, cycF_last, hlast, Fin.last_add_one, hzero]
      exact hW''k
    · rw [hτs, hAs, hFdef, cycF_castSucc, Fin.coeSucc_eq_succ]
      exact hE j
  have hAc0 : ∀ i, 0 ≤ Ac i := fun i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hAl]; exact hA'.le
    · rw [hAs]; exact (hA j).le
  obtain ⟨u, v₁, v₂, Y₁, Y₂, hu, hv₁, hv₂, huv, hY₁, hY₂, hP1, hP2, hEY⟩ :=
    face_data τc C (fun i => C (i + 1)) F Ac hAc0 hcls
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
  -- the constants
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
    fun i => gT3_pt (k := τc i) i (ρ i) (hY₁ i) (hY₂ i) (hP1 i) (hP2 i)
  refine term_close hm1 C hC _ (fun i c d => hG0 i (ρ i) c d) _ hρ τc ρ hpt fun hev => ?_
  calc ∑ i, (code (τc i) (ρ i)).marks ≤ ∑ i, τc i := Finset.sum_le_sum fun i _ => by
        have := code_marks (τc i) (ρ i) (pt_valid1 (hρ i) (hpt i)) (pt_valid2 (hρ i) (hpt i))
        split_ifs at this <;> omega
    _ = k₀ + ∑ j, τ j := by
        rw [Fin.sum_univ_castSucc, hτl]
        simp only [hτs]
        ring
    _ ≤ 12 := hsum hev

end Outerplanar
