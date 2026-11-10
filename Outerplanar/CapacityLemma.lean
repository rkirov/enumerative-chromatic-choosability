/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Capacity
import Outerplanar.WitnessFour
import Outerplanar.TriangleThree

/-!
# The capacity lemma

`CL k n` holds for `k ≥ 4`, `n ≥ 2` and for `k = 3`, `n ≥ 3`
(`ai_research_notes/OUTERPLANAR_PROOF_DRAFT_2026-11-09.md`, section 3). It fails for
`k = 3`, `n = 2`. This file assembles the induction on `k`; the base `k = 3` is stated here
relative to the two witness laws for three colours.
-/

namespace Outerplanar

open Finset

/-- A full `1`-fold cover has a closed thread. -/
theorem Cover.not_full_one {n : ℕ} [NeZero n] (P : Cover n) (hcard : ∀ i, (P.F i).card = 1)
    (hno : P.NoClosedThread) (hfull : ∀ i, ∀ x ∈ P.F i, ∃ y ∈ P.F (i + 1), P.M i x y) : False := by
  have hne : ∀ i, (P.F i).Nonempty := fun i => by rw [← Finset.card_pos, hcard]; exact one_pos
  choose f hf using hne
  refine hno ⟨f, hf, fun i => ?_⟩
  obtain ⟨y, hy, hM⟩ := hfull i (f i) (hf i)
  have : y = f (i + 1) := Finset.card_le_one.mp (hcard (i + 1)).le y hy _ (hf _)
  rwa [this] at hM

theorem fin3_third : ∀ e e' e'' a : Fin 3, e ≠ e' → e ≠ e'' → e' ≠ e'' → a ≠ e → a ≠ e' →
    a = e'' := by
  intro e e' e'' a h1 h2 h3 h4 h5
  simp only [ne_eq, Fin.ext_iff] at *
  omega

/-- **The capacity lemma for three colours**, on cycles of length at least three, from the
two witness laws. -/
theorem cl_three_of (hW3 : Witness (n := 3) 3 (-1) 2 (lam 3 3))
    (hW0 : ∀ (n : ℕ) [NeZero n], 4 ≤ n → Witness (n := n) 3 (-1) 0 (lam 3 n))
    (n : ℕ) [NeZero n] (hn : 3 ≤ n) : CL 3 n := by
  refine Cover.capGE_of_maximal fun P hcard hM hno hmax b => ?_
  rcases Cover.full_or_cutSection hcard hM hno hmax with hfull | ⟨c, e, hc⟩
  · exact P.capGE_full (by omega) hcard hM hfull hno b
  have hcard' := Cover.erase_card hcard hc.1
  have hM' := Cover.erase_isMatching hM c
  have hno' := Cover.erase_noClosedThread hno c
  have hmax' := Cover.maximal_erase hM hno hmax hc
  have hpos : 0 < lam 3 n := lam_pos (le_refl 3) (by omega)
  rcases eq_or_lt_of_le hn with h3 | h4
  · subst h3
    rcases Cover.full_or_cutSection hcard' hM' hno' hmax' with hfull' | ⟨c', e', hc'⟩
    · have h0 := (P.erase c).capGE_full (by norm_num) hcard' hM' hfull' hno' c
      have hg : lam (3 - 1) 3 = 2 := by norm_num [lam]
      rw [hg] at h0
      exact P.capGE_of_witness (le_refl 3) hcard hM hc hpos h0 (hW3.rotate e) b
    · -- three cut sections
      have hcard'' := Cover.erase_card hcard' hc'.1
      have hM'' := Cover.erase_isMatching hM' c'
      have hno'' := Cover.erase_noClosedThread hno' c'
      have hmax'' := Cover.maximal_erase hM' hno' hmax' hc'
      rcases Cover.full_or_cutSection hcard'' hM'' hno'' hmax'' with hfull'' | ⟨c'', e'', hc''⟩
      · exact (Cover.not_full_one _ hcard'' hno'' hfull'').elim
      have hc'P := Cover.isCutSection_of_erase hM hc hc'
      have hc''P' := Cover.isCutSection_of_erase hM' hc' hc''
      have hc''P := Cover.isCutSection_of_erase hM hc hc''P'
      have d1 : ∀ i, c' i ≠ c i := fun i => (Finset.mem_erase.mp (hc'.1 i)).1
      have d2 : ∀ i, c'' i ≠ c' i := fun i => (Finset.mem_erase.mp (hc''.1 i)).1
      have d3 : ∀ i, c'' i ≠ c i := fun i =>
        (Finset.mem_erase.mp (Finset.mem_erase.mp (hc''.1 i)).2).1
      have e1 : e ≠ e' := Cover.cut_edge_ne hM hno hmax hc hc'P (d1 e).symm
      have e2 : e ≠ e'' := Cover.cut_edge_ne hM hno hmax hc hc''P (d3 e).symm
      have e3 : e' ≠ e'' := Cover.cut_edge_ne hM' hno' hmax' hc' hc''P' (d2 e').symm
      let cc : Fin 3 → Fin 3 → ℕ := fun a => if a = e then c else if a = e' then c' else c''
      refine P.capGE_three_sections hcard hM cc (fun a => ?_) (fun a a' i haa => ?_) b
      · by_cases h1 : a = e
        · simp only [cc, h1, ite_true]; exact hc
        · by_cases h2 : a = e'
          · simp only [cc, h2, ite_true, e1.symm, ite_false]; exact hc'P
          · have h3 := fin3_third e e' e'' a e1 e2 e3 h1 h2
            simp only [cc, h1, h2, ite_false]
            rw [h3]; exact hc''P
      · have key : ∀ a : Fin 3, cc a i = c i ∧ a = e ∨ cc a i = c' i ∧ a = e' ∨
            cc a i = c'' i ∧ a = e'' := by
          intro a
          by_cases h1 : a = e
          · left; simp [cc, h1]
          · by_cases h2 : a = e'
            · right; left; simp [cc, h2, e1.symm]
            · right; right
              exact ⟨by simp [cc, h1, h2], fin3_third e e' e'' a e1 e2 e3 h1 h2⟩
        rcases key a with ⟨h, ha⟩ | ⟨h, ha⟩ | ⟨h, ha⟩ <;>
          rcases key a' with ⟨h', ha'⟩ | ⟨h', ha'⟩ | ⟨h', ha'⟩ <;> rw [h, h']
        · exact absurd (ha.trans ha'.symm) haa
        · exact (d1 i).symm
        · exact (d3 i).symm
        · exact d1 i
        · exact absurd (ha.trans ha'.symm) haa
        · exact (d2 i).symm
        · exact d3 i
        · exact d2 i
        · exact absurd (ha.trans ha'.symm) haa
  · have h0 : (P.erase c).CapGE univ c 0 := fun w hw =>
      (P.erase c).Z_nonneg fun i hi => (hw i hi).1
    exact P.capGE_of_witness (le_refl 3) hcard hM hc hpos h0 ((hW0 n (by omega)).rotate e) b

/-- **The capacity lemma for at least four colours**, from the one for three. -/
theorem cl_of_four_le (h3 : ∀ (n : ℕ) [NeZero n], 3 ≤ n → CL 3 n) :
    ∀ k, 4 ≤ k → ∀ (n : ℕ) [NeZero n], 2 ≤ n → CL k n := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro n _ hn
    rcases eq_or_lt_of_le hn with h2 | h3'
    · subst h2
      exact cl_four_two
    · refine cl_step (le_refl 4) hn (h3 n (by omega)) ?_
      rw [lam_pred (by norm_num)]
      exact witness_of_four_le (le_refl 4) (by omega)
  | succ k hk ih =>
    intro n _ hn
    refine cl_step (by omega) hn (ih n hn) ?_
    rw [lam_pred (by omega)]
    rcases eq_or_lt_of_le hn with h2 | h3'
    · subst h2
      have := witness_two (k := k + 1) (by omega)
      convert this using 1
      · rfl
      · norm_num
    · exact witness_of_four_le (by omega) (by omega)

end Outerplanar
