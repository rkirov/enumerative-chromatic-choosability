/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.SevenEven

/-!
# An unbounded criterion: even faces over single marks

A rooted criterion with any number of even faces (research note
`ai_research_notes/OUTERPLANAR_SEVEN_AND_CUTS_2026-11-23.md`, "A second unbounded criterion"):
seen from a root edge, every even face either has at most one child side carrying even faces, or
all its child sides carry at most one even face each. Odd faces are unrestricted.

The proof keeps every side in the ball class `InBall`, and the sides with exactly one even face
also in the gain class `Gain1` (`Outerplanar/Gain.lean`):

* odd faces map ball classes on all sides to the ball class (`ballTriClosed`, `ballOddClosed`),
  and one gain side with greedy sides to the gain class (`gain1_odd`);
* an even face maps one ball side with greedy sides to the ball class
  (`ballFaceClosed_of_bare`), gain classes on all sides to the ball class (`ball_even_gain`), and
  greedy sides to the gain class (`gain1_even_bare`);
* two ball sides glue (the hexagon bound).

**`ecc_three_of_goodB`**: a polygon dissection with an edge both of whose sides satisfy the
criterion (`GoodB`) is 3-ECC.

The criterion is due to another AI session of this repository's collaboration (the seven-face
note); formalized by Claude.
-/

namespace Outerplanar

open Finset

/-! ### The class system -/

/-- The three tags: greedy, ball, and ball with gain. -/
inductive BTag
  | plain
  | ball
  | gain
  deriving DecidableEq

/-- The class of a tag. -/
def bcls : BTag → Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop
  | .plain, S, T, W, A => Dominant S T W A
  | .ball, S, T, W, A => InBall S T W A
  | .gain, S, T, W, A => Gain1 S T W A ∧ InBall S T W A

/-- The class system. -/
def ballSys : ClassSys where
  Tag := BTag
  plain := .plain
  cls := bcls
  of_dom t S T W A hA h := by
    cases t
    · exact h
    · exact h.inBall hA
    · exact ⟨h.gain1, h.inBall hA⟩
  dom_of_plain S T W A h := h
  mul_dom t S T W W' A A' hA hA' h0 h0' hd h := by
    cases t
    · exact Dominant.mul hA' hA hd h
    · exact InBall.mul hA' hA (hd.inBall hA') h
    · exact ⟨h.1.mul_dom hA hA' hd, InBall.mul hA' hA (hd.inBall hA') h.2⟩

section Sound

variable {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {A : ℝ}

theorem bcls_ball {t : BTag} (hA : 0 ≤ A) (h : bcls t S T W A) : InBall S T W A := by
  cases t
  · exact (show Dominant S T W A from h).inBall hA
  · exact h
  · exact h.2

theorem bcls_hex {t : BTag} (hA : 0 ≤ A) (h0 : ∀ c d, 0 ≤ W c d) (h : bcls t S T W A) :
    Hex S T W A := fun _ _ hm hpq => (bcls_ball hA h).hex hA h0 hm hpq

theorem bcls_gain {t : BTag} (ht : t ≠ .ball) (h : bcls t S T W A) : Gain1 S T W A := by
  cases t
  · exact (show Dominant S T W A from h).gain1
  · exact absurd rfl ht
  · exact h.1

/-- The face rule. -/
def ballRule (t : BTag) (m : ℕ) (τ : Fin (m + 1) → BTag) : Prop :=
  1 ≤ m ∧ match t with
  | .plain => Odd m ∧ ∀ j, τ j = .plain
  | .gain => (Even m ∧ 2 ≤ m ∧ ∀ j, τ j = .plain) ∨
      (Odd m ∧ ∃ j₀, τ j₀ ≠ .ball ∧ ∀ j, j ≠ j₀ → τ j = .plain)
  | .ball => Odd m ∨
      (Even m ∧ 2 ≤ m ∧ ((∃ j₀, ∀ j, j ≠ j₀ → τ j = .plain) ∨ ∀ j, τ j ≠ .ball))

theorem ballRule_sound {t : BTag} {m : ℕ} {τ : Fin (m + 1) → BTag} (hr : ballRule t m τ) :
    ballSys.RuleSound t m τ := by
  intro Lu Lv Li hLu hLv hLi E hE0 A hA hE
  change ∀ j, bcls (τ j) _ _ (E j) (A j) at hE
  change bcls t Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j)
  obtain ⟨hm1, hr⟩ := hr
  have hplain : ∀ j, τ j = .plain →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j) :=
    fun j hj => by have := hE j; rw [hj] at this; exact this
  have hballs : ∀ j, InBall (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j) :=
    fun j => bcls_ball (hA j).le (hE j)
  have hodd_ball : Odd m → InBall Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) :=
    fun hodd => by
      rcases Nat.lt_or_ge m 3 with hlt | h3
      · obtain rfl : m = 1 := by obtain ⟨k, hk⟩ := hodd; omega
        have := ballTriClosed Lu Lv Li hLu hLv hLi E hE0 A hA hballs
        rwa [faceConst3_one, one_mul]
      · exact ballOddClosed m hodd h3 Lu Lv Li hLu hLv hLi E hE0 A hA hballs
  have hone : ∀ j₀, (∀ j, j ≠ j₀ → τ j = .plain) →
      InBall Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) :=
    fun j₀ hpl => ballFaceClosed_of_bare (ballFaceBare_all m) Lu Lv Li hLu hLv hLi j₀ E hE0
      A hA (hballs j₀) fun j hj => hplain j (hpl j hj)
  cases t with
  | plain =>
    obtain ⟨hodd, hall⟩ := hr
    exact domFaceClosed_odd m hodd Lu Lv Li hLi E hE0 A hA fun j => hplain j (hall j)
  | ball =>
    rcases hr with hodd | ⟨hev, hm2, ⟨j₀, hpl⟩ | hall⟩
    · exact hodd_ball hodd
    · exact hone j₀ hpl
    · exact ball_even_gain hev hm2 Lu Lv Li hLu hLv hLi E hE0 A hA fun j =>
        bcls_gain (hall j) (hE j)
  | gain =>
    rcases hr with ⟨hev, hm2, hall⟩ | ⟨hodd, j₀, hj₀, hpl⟩
    · exact ⟨gain1_even_bare hev hm2 Lu Lv Li hLu hLv hLi E hE0 A (fun j => (hA j).le)
        fun j => hplain j (hall j), hone 0 fun j _ => hall j⟩
    · exact ⟨gain1_odd hodd Lu Lv Li hLu hLv hLi j₀ E hE0 A hA (bcls_gain hj₀ (hE j₀))
        fun j hj => hplain j (hpl j hj), hodd_ball hodd⟩

theorem ball_glue (t₁ t₂ : BTag) : ballSys.GlueSound t₁ t₂ := by
  intro S T W W' A A' hS hT h0 h0' hA hA' h₁ h₂
  have h := Hex.glue hS hT (bcls_hex hA.le h0 h₁) (bcls_hex hA'.le h0' h₂).swap hA hA' h0
    fun c d => h0' d c
  rw [Finset.sum_comm]
  refine h.trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => mul_comm _ _

end Sound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem ecc_three_of_ballBuilt {tg : V → V → BTag}
    (h : TagBuilt G ballSys ballRule (fun _ _ => True) univ tg) : G.ECCAt 3 :=
  ecc_three_of_tagBuilt G (fun _ _ _ hr => ballRule_sound hr) (fun t₁ t₂ _ => ball_glue t₁ t₂) h

/-! ### The criterion on a dissection -/

variable {n : ℕ}

open Classical in
/-- The tag of a side: by its number of even faces. -/
noncomputable def btag (H : SimpleGraph (Fin n)) (a b : Fin n) : BTag :=
  if marks H a b = 0 then .plain else if marks H a b = 1 then .gain else .ball

/-- **The criterion**: every even face inside `[a, b]` has its child sides all with at most one
mark, or at most one child side with marks. -/
def GoodB (H : SimpleGraph (Fin n)) (a b : Fin n) : Prop :=
  ∀ F ∈ facesIn H a b, Even F.card →
    (∀ f ∈ F, ∀ f' ∈ F, f < f' → (∀ z ∈ F, ¬ (f < z ∧ z < f')) → marks H f f' ≤ 1) ∨
    (∀ f ∈ F, ∀ f' ∈ F, f < f' → (∀ z ∈ F, ¬ (f < z ∧ z < f')) →
      ∀ g ∈ F, ∀ g' ∈ F, g < g' → (∀ z ∈ F, ¬ (g < z ∧ z < g')) → (f ≠ g ∨ f' ≠ g') →
        marks H f f' = 0 ∨ marks H g g' = 0)

section Rule

variable {H : SimpleGraph (Fin n)} {a b : Fin n} {m : ℕ} {r : Fin (m + 2) → Fin n}

theorem GoodB.mono {a' b' : Fin n} (h : GoodB H a b) (h1 : a ≤ a') (h2 : b' ≤ b) :
    GoodB H a' b' := fun F hF => h F (facesIn_mono h1 h2 hF)

theorem btag_zero (h : marks H a b = 0) : btag H a b = .plain := by simp [btag, h]

theorem btag_one (h : marks H a b = 1) : btag H a b = .gain := by simp [btag, h]

theorem btag_ne_ball (h : marks H a b ≤ 1) : btag H a b ≠ .ball := by
  unfold btag; split_ifs <;> simp_all; omega

theorem btag_two (h : 2 ≤ marks H a b) : btag H a b = .ball := by
  unfold btag; split_ifs <;> first | omega | rfl

/-- The criterion at the root face. -/
theorem GoodB.root (hH : IsDissection H) (hadj : H.Adj a b) (he : RootEnum H a b m r)
    (hg : GoodB H a b) (hev : Even m) :
    (∀ j : Fin (m + 1), marks H (r j.castSucc) (r j.succ) ≤ 1) ∨
    (∀ j j' : Fin (m + 1), j ≠ j' →
      marks H (r j.castSucc) (r j.succ) = 0 ∨ marks H (r j'.castSucc) (r j'.succ) = 0) := by
  have hm1 := he.one_le
  have hevm : Even (m + 2) := by obtain ⟨k, hk⟩ := hev; exact ⟨k + 1, by omega⟩
  have h2 : a.val + 2 ≤ b.val := by
    have := he.card
    by_contra h
    have := card_le_two_of_gap (rootFace_sub (H := H) (a := a) (b := b)) fun z _ ⟨h1, h2⟩ => by
      have : a.val < z.val := h1
      have : z.val < b.val := h2
      omega
    omega
  rcases hg (rootFace H a b) (mem_facesIn.mpr ⟨rootFace_isFace hH hadj h2, rootFace_sub⟩)
    (by rw [he.card]; exact hevm) with h | h
  · exact Or.inl fun j => h _ (he.mem _) _ (he.mem _) (he.lt j) (he.gap j)
  · refine Or.inr fun j j' hjj => h _ (he.mem _) _ (he.mem _) (he.lt j) (he.gap j) _ (he.mem _) _
      (he.mem _) (he.lt j') (he.gap j') ?_
    by_contra hc
    push Not at hc
    exact hjj (Fin.castSucc_injective _ (he.mono.injective hc.1))

/-- **The face rule holds at the root face of a good side.** -/
theorem ruleB_of_enum (hH : IsDissection H) (hadj : H.Adj a b) (he : RootEnum H a b m r)
    (hab : a < b) (hg : GoodB H a b) :
    ballRule (btag H a b) m (fun i => btag H (r i.castSucc) (r i.succ)) := by
  classical
  set f : Fin (m + 1) → ℕ := fun i => marks H (r i.castSucc) (r i.succ) with hf
  have hM : marks H a b = (if Even (m + 2) then 1 else 0) + ∑ i, f i := he.marks_eq hH hadj hab
  have hm1 := he.one_le
  have hevm : Even (m + 2) ↔ Even m := by
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
    · rintro ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
  refine ⟨hm1, ?_⟩
  rcases Nat.even_or_odd m with hev | hodd
  · have hs : marks H a b = 1 + ∑ i, f i := by rw [hM]; simp only [hevm.mpr hev, ↓reduceIte]
    have hm2 : 2 ≤ m := by obtain ⟨k, hk⟩ := hev; omega
    by_cases hz : ∑ i, f i = 0
    · rw [btag_one (by omega)]
      exact Or.inl ⟨hev, hm2, fun j => btag_zero ((Finset.sum_eq_zero_iff.mp hz) j (mem_univ j))⟩
    · rw [btag_two (by omega)]
      refine Or.inr ⟨hev, hm2, ?_⟩
      rcases hg.root hH hadj he hev with h | h
      · exact Or.inr fun j => btag_ne_ball (h j)
      · left
        obtain ⟨j₀, hj₀⟩ : ∃ j₀, f j₀ ≠ 0 := by
          by_contra hc
          push Not at hc
          exact hz (Finset.sum_eq_zero fun i _ => hc i)
        refine ⟨j₀, fun j hj => btag_zero ?_⟩
        rcases h j j₀ hj with h' | h'
        · exact h'
        · exact absurd h' hj₀
  · have hodd' : ¬ Even (m + 2) := fun h => (Nat.not_even_iff_odd.mpr hodd) (hevm.mp h)
    have hs : marks H a b = ∑ i, f i := by rw [hM]; simp only [hodd', ↓reduceIte, zero_add]
    by_cases h0 : marks H a b = 0
    · rw [btag_zero h0]
      refine ⟨hodd, fun j => btag_zero ?_⟩
      have : f j ≤ ∑ i, f i := Finset.single_le_sum (fun i _ => Nat.zero_le (f i)) (mem_univ j)
      show f j = 0
      omega
    · by_cases h1 : marks H a b = 1
      · rw [btag_one h1]
        right
        refine ⟨hodd, ?_⟩
        rcases sum_le_two_cases f (by omega) with hz | ⟨j, hj, hz⟩ | ⟨j, hj, hz⟩ |
            ⟨j₁, j₂, h12, hj₁, hj₂, hz⟩
        · exfalso; rw [Finset.sum_eq_zero fun i _ => hz i] at hs; omega
        · exact ⟨j, btag_ne_ball (show f j ≤ 1 by omega), fun i hi => btag_zero (hz i hi)⟩
        · exfalso
          have : f j ≤ ∑ i, f i := Finset.single_le_sum (fun i _ => Nat.zero_le (f i)) (mem_univ j)
          omega
        · exfalso
          have : f j₁ + f j₂ ≤ ∑ i, f i := Finset.add_le_sum (fun i _ => Nat.zero_le (f i))
            (mem_univ j₁) (mem_univ j₂) (ne_of_lt h12)
          omega
      · rw [btag_two (by omega)]
        exact Or.inl hodd

end Rule

/-! ### The theorem -/

open Classical in
/-- **A polygon dissection with an edge both of whose sides satisfy the criterion is 3-ECC**:
seen from that edge, every even face has either at most one child side with even faces, or child
sides with at most one even face each. -/
theorem ecc_three_of_goodB {n : ℕ} [NeZero n] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : IsDissection G) (a b : Fin n) (hab : a < b) (hadj : G.Adj a b) (h₁ : GoodB G a b)
    (h₂ : GoodB (G.comap (rot b)) 0 (a - b)) : G.ECCAt 3 := by
  obtain ⟨tg, h⟩ := exists_build (R := ballSys) (rule := ballRule) G hG (fun H => btag H)
    (fun H => GoodB H) (fun H hH _ _ _ _ hadj hab he hg => ruleB_of_enum hH hadj he hab hg)
    (fun _ _ _ _ _ he hg _ => hg.mono (he.ge _) (he.le _)) a b hab hadj h₁ h₂
  exact ecc_three_of_ballBuilt G h

/-- The criterion from the outer edge `(0, n - 1)`: every even face, seen from that edge, has
either at most one child side with even faces or child sides with at most one even face each. -/
theorem ecc_three_of_goodB_outer {n : ℕ} [NeZero n] (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : IsDissection G) (hn : 3 ≤ n) (h : GoodB G 0 ⟨n - 1, by omega⟩) :
    G.ECCAt 3 := by
  obtain ⟨l, h0l, hadj, hle, hl1⟩ := outer_edge (by omega) hG
  have hl : l = ⟨n - 1, by omega⟩ :=
    Fin.ext (le_antisymm (by have := l.isLt; show l.val ≤ n - 1; omega)
      (hle ⟨n - 1, by omega⟩))
  rw [hl] at h0l hadj hl1
  refine ecc_three_of_goodB G hG 0 _ h0l hadj h fun F hF => ?_
  exfalso
  rw [facesIn_edge (by rw [hl1]; simp)] at hF
  simp at hF

end Outerplanar
