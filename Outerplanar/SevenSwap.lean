/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.SevenVertex
import Outerplanar.TagBuiltW

/-!
# The seven-even-face classes are invariant under transposition

Every class of `Outerplanar/SevenEven.lean` (`Hex`, `HasPot`, `TB`, the floor, `HullC`, `InBall`,
`Gain1`) is a statement about all matched six-families, all bijections, or all proper cells,
which a transposition permutes. So `sevenSys` is `Transposable`, and graphs built by ears,
pendant edges and reorientations under the seven-even-face rules are 3-ECC
(**`ecc_three_of_sevenBuiltW`**).

Part of the formalization of the seven-even-face theorem with cut vertices (research note
`ai_research_notes/OUTERPLANAR_SEVEN_AND_CUTS_2026-11-23.md`); formalized by Claude.
-/

namespace Outerplanar

open Finset

variable {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {A τ : ℝ}

theorem TB.swap (h : TB S T W A τ) : TB T S (fun d c => W c d) A τ :=
  fun p q hm hpq i j k l h1 h2 h3 h4 h5 h6 =>
    h q p hm.symm (fun i => (hpq i).symm) i j k l h1 h2 h3 h4 h5 h6

theorem HullC.swap (h : HullC S T W A) : HullC T S (fun d c => W c d) A :=
  ⟨fun p q hm hpq => h.1 q p hm.symm fun i => (hpq i).symm, h.2.swap⟩

theorem BijGe.swap {N Q : ℝ} (h : BijGe S T W N Q) : BijGe T S (fun d c => W c d) N Q :=
  fun α β hα hβ hαm hβm hne => h β α hβ hα hβm hαm fun a => (hne a).symm

theorem ZGood.swap (h : ZGood S T W) : ZGood T S (fun d c => W c d) :=
  ⟨fun _ _ => h.1 _ _, h.2.1.swap, h.2.2.1.swap, h.2.2.2.swap⟩

theorem Gain1.swap (h : Gain1 S T W A) : Gain1 T S (fun d c => W c d) A := by
  obtain ⟨t, Z, h0, h1, hZ, hle⟩ := h
  exact ⟨t, fun d c => Z c d, h0, h1, hZ.swap, fun d hd c hc hdc => hle c hc d hd (Ne.symm hdc)⟩

theorem ncls_swap {t : NTag} (h : ncls t S T W A) : ncls t T S (fun d c => W c d) A :=
  ⟨Hex.swap h.1, fun hm => (h.2.1 hm).swap, h.2.2.1.swap, h.2.2.2.1.swap,
    fun hh => (h.2.2.2.2 hh).swap⟩

/-- **The seven-even-face classes are invariant under transposition.** -/
theorem sevenSys_transposable : sevenSys.Transposable := fun _ _ _ _ _ h =>
  ⟨ncls_swap h.1, fun hb => (h.2.1 hb).swap, fun hg => (h.2.2 hg).swap⟩

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Every graph built by ears, pendant edges and reorientations under the seven-even-face
rules is 3-ECC.** -/
theorem ecc_three_of_sevenBuiltW {tg : V → V → STag}
    (h : TagBuiltW G sevenSys sevenRule (fun _ _ => True) VCond univ tg) : G.ECCAt 3 :=
  ecc_three_of_tagBuiltW G (fun _ _ _ hr => sevenRule_sound hr) (fun t₁ t₂ _ => seven_glue t₁ t₂)
    (fun _ _ _ hr => vcond_sound hr) sevenSys_transposable h

end Outerplanar
