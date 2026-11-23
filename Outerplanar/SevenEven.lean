/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.LightTriangles
import Outerplanar.GainOdd

/-!
# Polygon dissections with at most seven even faces are 3-ECC

The tags of the six-even-face theorem (`Outerplanar/SixEvenBuild.lean`), with two more classes
(research note `ai_research_notes/OUTERPLANAR_SEVEN_AND_CUTS_2026-11-23.md`):

* `ball` — the ball class `InBall`, demanded on the sides with one to three even faces;
* `gain` — the gain class `Gain1` of `Outerplanar/Gain.lean`, demanded on the sides with exactly
  one even face.

The face rule `sevenRule` adds to `numRule`:

* the ball class at odd faces from the ball class on all sides (`ballTriClosed`,
  `ballOddClosed`), at even faces from one ball side (`ballFaceClosed_of_bare`) or from gain
  classes on all sides (`ball_even_gain`);
* the gain class at bare even faces (`gain1_even_bare`) and at odd faces with one gain side
  (`gain1_odd`);
* the hexagon bound (alone) at an even face with one ball side, as an alternative to the
  numeric rule: three marks below one side of an even face.

**`ecc_three_of_seven_even`**: a polygon dissection with at most seven even faces is 3-ECC. The
base edge is a chord with three or four marks inside if there is one (both sides then have at
most four marks: a side with at most three is in the ball class, a side with four has the
hexagon bound, at an even face over three marks by the ball route), and otherwise a narrowest
chord with at least five marks (its root face has children with at most two marks, the outside
has at most two), or the outer edge.

The theorem of the note is due to another AI session of this repository's collaboration;
audited and formalized by Claude.
-/

namespace Outerplanar

open Finset

/-! ### The tag system -/

/-- A numeric tag with two more demands. -/
structure STag where
  /-- The numeric part. -/
  base : NTag
  /-- The ball class. -/
  ball : Bool
  /-- The gain class. -/
  gain : Bool

/-- The plain tag. -/
def STag.plain : STag := ⟨NTag.plain, false, false⟩

/-- The class of a tag. -/
def scls (t : STag) (S T : Finset ℕ) (W : ℕ → ℕ → ℝ) (A : ℝ) : Prop :=
  ncls t.base S T W A ∧ (t.ball = true → InBall S T W A) ∧ (t.gain = true → Gain1 S T W A)

/-- The class system of the seven-even-face theorem. -/
def sevenSys : ClassSys where
  Tag := STag
  plain := STag.plain
  cls := scls
  of_dom t S T W A hA h :=
    ⟨numSys.of_dom t.base S T W A hA h, fun _ => h.inBall hA, fun _ => h.gain1⟩
  dom_of_plain S T W A h := numSys.dom_of_plain S T W A h.1
  mul_dom t S T W W' A A' hA hA' h0 h0' hd h :=
    ⟨numSys.mul_dom t.base S T W W' A A' hA hA' h0 h0' hd h.1,
      fun hb => InBall.mul hA' hA (hd.inBall hA') (h.2.1 hb),
      fun hg => (h.2.2 hg).mul_dom hA hA' hd⟩

/-- A ball side or a plain side. -/
def STag.isBall (t : STag) : Prop := t.ball = true ∨ t = STag.plain

/-- A gain side or a plain side. -/
def STag.isGain (t : STag) : Prop := t.gain = true ∨ t = STag.plain

/-- The face rule. -/
def sevenRule (t : STag) (m : ℕ) (τ : Fin (m + 1) → STag) : Prop :=
  (numRule t.base m (fun j => (τ j).base) ∨
    (t.base = tHex ∧ 1 ≤ m ∧ Even m ∧ ∃ j₀, (τ j₀).ball = true ∧
      ∀ j, j ≠ j₀ → τ j = STag.plain)) ∧
  (t.ball = true →
    (Odd m ∧ ∀ j, (τ j).isBall) ∨
    (Even m ∧ 2 ≤ m ∧ ∃ j₀, (τ j₀).isBall ∧ ∀ j, j ≠ j₀ → τ j = STag.plain) ∨
    (Even m ∧ 2 ≤ m ∧ ∀ j, (τ j).isGain)) ∧
  (t.gain = true →
    (Even m ∧ 2 ≤ m ∧ ∀ j, τ j = STag.plain) ∨
    (Odd m ∧ ∃ j₀, (τ j₀).isGain ∧ ∀ j, j ≠ j₀ → τ j = STag.plain))

section Sound

variable {t : STag} {m : ℕ} {τ : Fin (m + 1) → STag} {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {A : ℝ}

theorem scls_plain_dom (h : scls STag.plain S T W A) : Dominant S T W A :=
  numSys.dom_of_plain S T W A h.1

theorem scls_ball (hA : 0 ≤ A) {t : STag} (ht : t.isBall) (h : scls t S T W A) :
    InBall S T W A := by
  rcases ht with hb | rfl
  · exact h.2.1 hb
  · exact (scls_plain_dom h).inBall hA

theorem scls_gain {t : STag} (ht : t.isGain) (h : scls t S T W A) : Gain1 S T W A := by
  rcases ht with hg | rfl
  · exact h.2.2 hg
  · exact (scls_plain_dom h).gain1

theorem sevenRule_sound (hr : sevenRule t m τ) : sevenSys.RuleSound t m τ := by
  intro Lu Lv Li hLu hLv hLi E hE0 A hA hE
  change ∀ j, scls (τ j) _ _ (E j) (A j) at hE
  change scls t Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j)
  obtain ⟨hbase, hball, hgain⟩ := hr
  have hN : 0 < faceConst3 m * ∏ j, A j :=
    mul_pos (faceConst3_pos m) (Finset.prod_pos fun j _ => hA j)
  have hF0 : ∀ c d, 0 ≤ faceSum Li (fun _ _ => 1) E c d :=
    faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one) hE0
  have hplain : ∀ j, τ j = STag.plain →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j) :=
    fun j hj => scls_plain_dom (by have := hE j; rwa [hj] at this)
  -- the ball route at an even face with one ball side
  have hone : Even m → ∀ j₀, (τ j₀).isBall → (∀ j, j ≠ j₀ → τ j = STag.plain) →
      InBall Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) :=
    fun _ j₀ hb hpl => ballFaceClosed_of_bare (ballFaceBare_all m) Lu Lv Li hLu hLv hLi j₀ E hE0
      A hA (scls_ball (hA j₀).le hb (hE j₀)) fun j hj => hplain j (hpl j hj)
  refine ⟨?_, fun hb => ?_, fun hg => ?_⟩
  · rcases hbase with hnum | ⟨htb, hm1, hev, j₀, hj₀, hpl⟩
    · exact numRule_sound hnum Lu Lv Li hLu hLv hLi E hE0 A hA fun j => (hE j).1
    · have hI := hone hev j₀ (Or.inl hj₀) hpl
      rw [htb]
      refine ⟨fun p q hm hpq => hI.hex hN.le hF0 hm hpq, fun h => absurd h (by decide),
        TB.zero hF0, fun c _ d _ _ => ?_, fun h => absurd h (by decide)⟩
      show (0 : ℝ) * _ ≤ _
      rw [zero_mul]
      exact hF0 c d
  · rcases hball hb with ⟨hodd, hall⟩ | ⟨hev, -, j₀, hj₀, hpl⟩ | ⟨hev, hm2, hall⟩
    · have hI : ∀ j, InBall (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j)
          (A j) := fun j => scls_ball (hA j).le (hall j) (hE j)
      rcases Nat.lt_or_ge m 3 with hlt | h3
      · obtain rfl : m = 1 := by obtain ⟨k, hk⟩ := hodd; omega
        have := ballTriClosed Lu Lv Li hLu hLv hLi E hE0 A hA hI
        rwa [faceConst3_one, one_mul]
      · exact ballOddClosed m hodd h3 Lu Lv Li hLu hLv hLi E hE0 A hA hI
    · exact hone hev j₀ hj₀ hpl
    · exact ball_even_gain hev hm2 Lu Lv Li hLu hLv hLi E hE0 A hA fun j =>
        scls_gain (hall j) (hE j)
  · rcases hgain hg with ⟨hev, hm2, hall⟩ | ⟨hodd, j₀, hj₀, hpl⟩
    · exact gain1_even_bare hev hm2 Lu Lv Li hLu hLv hLi E hE0 A (fun j => (hA j).le)
        fun j => hplain j (hall j)
    · exact gain1_odd hodd Lu Lv Li hLu hLv hLi j₀ E hE0 A hA (scls_gain hj₀ (hE j₀))
        fun j hj => hplain j (hpl j hj)

theorem seven_glue (t₁ t₂ : STag) : sevenSys.GlueSound t₁ t₂ :=
  fun S T W W' A A' hS hT h0 h0' hA hA' h₁ h₂ =>
    num_glue t₁.base t₂.base S T W W' A A' hS hT h0 h0' hA hA' h₁.1 h₂.1

end Sound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Every graph built by ears following `sevenRule` is 3-ECC.** -/
theorem ecc_three_of_sevenBuilt {tg : V → V → STag}
    (h : TagBuilt G sevenSys sevenRule (fun _ _ => True) univ tg) : G.ECCAt 3 :=
  ecc_three_of_tagBuilt G (fun _ _ _ hr => sevenRule_sound hr) (fun t₁ t₂ _ => seven_glue t₁ t₂) h

/-! ### The tags of the dissection -/

variable {n : ℕ}

open Classical in
/-- The tag demanded on `(a, b)` from the side `[a, b]`. -/
noncomputable def tag7 (H : SimpleGraph (Fin n)) (a b : Fin n) : STag :=
  ⟨tagOf H a b, decide (1 ≤ marks H a b ∧ marks H a b ≤ 3), decide (marks H a b = 1)⟩

/-- A side with at most four marks, or a good side. -/
def Good7 (H : SimpleGraph (Fin n)) (a b : Fin n) : Prop := marks H a b ≤ 4 ∨ GoodP H a b

section Rule

variable {H : SimpleGraph (Fin n)} {a b : Fin n} {m : ℕ} {r : Fin (m + 2) → Fin n}

theorem tag7_zero (h : marks H a b = 0) : tag7 H a b = STag.plain := by
  unfold tag7 STag.plain
  rw [tagOf_zero h]
  simp [h]

theorem tag7_ball (h1 : 1 ≤ marks H a b) (h3 : marks H a b ≤ 3) : (tag7 H a b).ball = true := by
  unfold tag7
  simp [h1, h3]

theorem tag7_isBall (h3 : marks H a b ≤ 3) : (tag7 H a b).isBall := by
  rcases Nat.eq_zero_or_pos (marks H a b) with h | h
  · exact Or.inr (tag7_zero h)
  · exact Or.inl (tag7_ball h h3)

theorem tag7_isGain (h1 : marks H a b ≤ 1) : (tag7 H a b).isGain := by
  rcases Nat.eq_zero_or_pos (marks H a b) with h | h
  · exact Or.inr (tag7_zero h)
  · left
    unfold tag7
    simp only [decide_eq_true_eq]
    omega

theorem tag7_ball_le (h : (tag7 H a b).ball = true) : 1 ≤ marks H a b ∧ marks H a b ≤ 3 := by
  unfold tag7 at h
  simpa using h

theorem tag7_gain_eq (h : (tag7 H a b).gain = true) : marks H a b = 1 := by
  unfold tag7 at h
  simpa using h

/-- **The face rule holds at the root face of a good side.** -/
theorem rule7_of_enum (hH : IsDissection H) (hadj : H.Adj a b) (he : RootEnum H a b m r)
    (hab : a < b) (hg : Good7 H a b) :
    sevenRule (tag7 H a b) m (fun i => tag7 H (r i.castSucc) (r i.succ)) := by
  classical
  set f : Fin (m + 1) → ℕ := fun i => marks H (r i.castSucc) (r i.succ) with hf
  have hM : marks H a b = (if Even (m + 2) then 1 else 0) + ∑ i, f i := he.marks_eq hH hadj hab
  have hm1 := he.one_le
  have hevm : Even (m + 2) ↔ Even m := by
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
    · rintro ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
  have hle : ∀ j, f j ≤ marks H a b := fun j => by
    rw [hM]
    have : f j ≤ ∑ i, f i := Finset.single_le_sum (fun i _ => Nat.zero_le (f i)) (mem_univ j)
    split_ifs <;> omega
  refine ⟨?_, fun hb => ?_, fun hgn => ?_⟩
  · -- the numeric part
    by_cases hloc : 3 ≤ marks H a b → Even m → ∀ j : Fin (m + 1), f j ≤ 2
    · exact Or.inl (rule_of_enum' hH hadj he hab hloc)
    · right
      push Not at hloc
      obtain ⟨h3, hev, j₀, hj₀⟩ := hloc
      have h4 : marks H a b ≤ 4 := by
        rcases hg with h | h
        · exact h
        · have h2 : f j₀ ≤ 2 := h.root hH hadj he h3 hev j₀
          omega
      have hsum : marks H a b = 1 + ∑ i, f i := by
        rw [hM]; simp only [hevm.mpr hev, ↓reduceIte]
      have hsingle : f j₀ ≤ ∑ i, f i :=
        Finset.single_le_sum (fun i _ => Nat.zero_le (f i)) (mem_univ j₀)
      have hrest : ∀ j, j ≠ j₀ → f j = 0 := fun j hj => by
        have : f j₀ + f j ≤ ∑ i, f i :=
          Finset.add_le_sum (fun i _ => Nat.zero_le (f i)) (mem_univ j₀) (mem_univ j) (Ne.symm hj)
        omega
      refine ⟨tagOf_three h3, hm1, hev, j₀, tag7_ball (show 1 ≤ f j₀ by omega)
        (show f j₀ ≤ 3 by omega), fun j hj =>
        tag7_zero (hrest j hj)⟩
  · -- the ball class
    obtain ⟨hk1, hk3⟩ := tag7_ball_le hb
    rcases Nat.even_or_odd m with hev | hodd
    · have hsum : ∑ i, f i ≤ 2 := by
        rw [hM] at hk3; simp only [hevm.mpr hev, ↓reduceIte] at hk3; omega
      have hm2 : 2 ≤ m := by obtain ⟨k, hk⟩ := hev; omega
      rcases sum_le_two_cases f hsum with h0 | ⟨j, hj, hz⟩ | ⟨j, hj, hz⟩ |
          ⟨j₁, j₂, -, hj₁, hj₂, hz⟩
      · refine Or.inr (Or.inr ⟨hev, hm2, fun i => tag7_isGain ?_⟩)
        show f i ≤ 1
        rw [h0 i]; omega
      · refine Or.inr (Or.inr ⟨hev, hm2, fun i => tag7_isGain ?_⟩)
        show f i ≤ 1
        by_cases hi : i = j
        · rw [hi, hj]
        · rw [hz i hi]; omega
      · exact Or.inr (Or.inl ⟨hev, hm2, j, tag7_isBall (by show f j ≤ 3; omega), fun i hi =>
          tag7_zero (hz i hi)⟩)
      · refine Or.inr (Or.inr ⟨hev, hm2, fun i => tag7_isGain ?_⟩)
        show f i ≤ 1
        by_cases h1 : i = j₁
        · rw [h1, hj₁]
        · by_cases h2 : i = j₂
          · rw [h2, hj₂]
          · rw [hz i h1 h2]; omega
    · exact Or.inl ⟨hodd, fun i => tag7_isBall ((hle i).trans hk3)⟩
  · -- the gain class
    have hk := tag7_gain_eq hgn
    rcases Nat.even_or_odd m with hev | hodd
    · have hsum : ∑ i, f i = 0 := by
        rw [hM] at hk; simp only [hevm.mpr hev, ↓reduceIte] at hk; omega
      refine Or.inl ⟨hev, by obtain ⟨k, hk⟩ := hev; omega, fun i => tag7_zero ?_⟩
      exact (Finset.sum_eq_zero_iff.mp hsum) i (mem_univ i)
    · have hodd' : ¬ Even (m + 2) := fun h => (Nat.not_even_iff_odd.mpr hodd) (hevm.mp h)
      have hsum : ∑ i, f i = 1 := by
        rw [hM] at hk; simp only [hodd', ↓reduceIte] at hk; omega
      rcases sum_le_two_cases f (by omega) with h0 | ⟨j, hj, hz⟩ | ⟨j, hj, hz⟩ |
          ⟨j₁, j₂, h12, hj₁, hj₂, hz⟩
      · exfalso
        rw [Finset.sum_eq_zero fun i _ => h0 i] at hsum
        omega
      · exact Or.inr ⟨hodd, j, tag7_isGain (by show f j ≤ 1; omega), fun i hi =>
          tag7_zero (hz i hi)⟩
      · exfalso
        have : f j ≤ ∑ i, f i := Finset.single_le_sum (fun i _ => Nat.zero_le (f i)) (mem_univ j)
        omega
      · exfalso
        have : f j₁ + f j₂ ≤ ∑ i, f i := Finset.add_le_sum (fun i _ => Nat.zero_le (f i))
          (mem_univ j₁) (mem_univ j₂) (ne_of_lt h12)
        omega

end Rule

/-! ### The theorem -/

/-- A side whose shorter chords carry at most two marks each is good. -/
theorem goodP_of_narrow (G : SimpleGraph (Fin n)) (a b : Fin n)
    (hmin : ∀ a' b' : Fin n, a' < b' → G.Adj a' b' → b'.val - a'.val < b.val - a.val →
      marks G a' b' ≤ 2) : GoodP G a b := by
  intro F hF hev f hf f' hf' hff hgap
  obtain ⟨hFf, hsub⟩ := mem_facesIn.mp hF
  have hadj' : G.Adj f f' := (hFf.adj_iff hf hf' hff).mpr (Or.inl hgap)
  obtain ⟨h1, -⟩ := mem_Icc.mp (hsub hf)
  obtain ⟨-, h2⟩ := mem_Icc.mp (hsub hf')
  have hne : ¬ (f = a ∧ f' = b) := by
    rintro ⟨rfl, rfl⟩
    have := card_le_two_of_gap hsub hgap
    have := hFf.1
    omega
  have hw : f'.val - f.val < b.val - a.val := by
    have : a.val ≤ f.val := h1
    have : f'.val ≤ b.val := h2
    have : f.val < f'.val := hff
    by_cases e1 : f = a
    · have : f' ≠ b := fun e => hne ⟨e1, e⟩
      have : f'.val ≠ b.val := fun e => this (Fin.ext e)
      rw [e1]; omega
    · have : f.val ≠ a.val := fun e => e1 (Fin.ext e)
      omega
  exact hmin f f' hff hadj' hw

open Classical in
/-- **A polygon dissection with at most seven even faces is 3-ECC**: every assignment of lists of
three colours has at least as many proper colourings as there are `3`-colourings. -/
theorem ecc_three_of_seven_even {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : IsDissection G) (hn : 3 ≤ n)
    (h7 : (univ.filter fun F : Finset (Fin n) => IsFace G F ∧ Even F.card).card ≤ 7) :
    G.ECCAt 3 := by
  have h7' : numEvenFaces G ≤ 7 := h7
  have : NeZero n := ⟨by omega⟩
  suffices h : ∃ tg, TagBuilt G sevenSys sevenRule (fun _ _ => True) univ tg by
    obtain ⟨tg, h⟩ := h
    exact ecc_three_of_sevenBuilt G h
  have hbuild := exists_build (R := sevenSys) (rule := sevenRule) G hG (fun H => tag7 H)
    (fun H => Good7 H) (fun H hH _ _ _ _ hadj hab he hg => rule7_of_enum hH hadj he hab hg)
    (fun _ _ _ _ _ he hg i => by
      rcases hg with h | h
      · exact Or.inl ((marks_mono (he.ge i.castSucc) (he.le i.succ)).trans h)
      · exact Or.inr (h.mono (he.ge _) (he.le _)))
  by_cases hmid : ∃ a b : Fin n, a < b ∧ G.Adj a b ∧ 3 ≤ marks G a b ∧ marks G a b ≤ 4
  · -- a chord with three or four marks inside
    obtain ⟨a, b, hab, hadj, h3, h4⟩ := hmid
    have := marks_add_rot hG hab hadj
    exact hbuild a b hab hadj (Or.inl h4) (Or.inl (by omega))
  push Not at hmid
  by_cases hheavy : ∃ a b : Fin n, a < b ∧ G.Adj a b ∧ 5 ≤ marks G a b
  · -- a narrowest chord with at least five marks inside
    have hex : ∃ d, ∃ a b : Fin n, a < b ∧ G.Adj a b ∧ 5 ≤ marks G a b ∧ b.val - a.val = d := by
      obtain ⟨a, b, h1, h2, h3⟩ := hheavy
      exact ⟨_, a, b, h1, h2, h3, rfl⟩
    obtain ⟨a, b, hab, hadj, h5, hd⟩ := Nat.find_spec hex
    have hmin : ∀ a' b' : Fin n, a' < b' → G.Adj a' b' → b'.val - a'.val < b.val - a.val →
        marks G a' b' ≤ 2 := by
      intro a' b' h1 h2 hw
      by_contra h
      have h3 : 3 ≤ marks G a' b' := by omega
      by_cases h5' : 5 ≤ marks G a' b'
      · exact Nat.find_min hex (hd ▸ hw) ⟨a', b', h1, h2, h5', rfl⟩
      · exact absurd (hmid a' b' h1 h2 h3) (by omega)
    have := marks_add_rot hG hab hadj
    exact hbuild a b hab hadj (Or.inr (goodP_of_narrow G a b hmin)) (Or.inl (by omega))
  · -- every chord has at most two marks: the outer edge
    push Not at hheavy
    obtain ⟨l, h0l, hadj, -, hl1⟩ := outer_edge (by omega) hG
    have hgood := goodP_of_narrow G 0 l fun a' b' h1 h2 _ => by
      have := hheavy a' b' h1 h2
      by_contra h
      exact absurd (hmid a' b' h1 h2 (by omega)) (by omega)
    refine hbuild 0 l h0l hadj (Or.inr hgood) (Or.inl ?_)
    rw [marks_edge (by rw [hl1]; simp)]
    omega

end Outerplanar
