/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.K4.Comp

/-!
# Height four at `k = 4`: the endpoint-fibre argument

Codex's (OpenAI) depth-two argument (`ai_research_notes/cx/h4k4/NOTE.md`, "A much smaller
certificate route"; `ai_research_notes/cx/h4k4b/NOTE.md`, "Closing the depth-two argument").
For lists `X` of three or four colours and lists `A`, `B` of four colours, the depth-two slack is

  `∑_{u ∈ sts X} Sw w (A ∖ u) B`.

Under the classification (`Classify4`) only bad terms can be negative. Choose the endpoint row by
`B` alone: the last row if `B₀ = B₁ = B₂` (the only shape that can carry a forward edge pattern),
the first otherwise (reversed edge or central). Split `sts X` into fibres along that row. In a
fibre

* at most one term is bad: the bad endpoint list is determined by `B` and the neighbouring list
  (`badF_target`, `badR_target`, `badM_target`), and it has three colours, so it determines the
  erased colour (`eq_of_erase_eq`);
* the fibre has another state, since the endpoint list has at least three colours and only the
  neighbour's colour is excluded;
* a bad term and any other term of its fibre have a sum nonnegative on `K` (`compF`, `compR`,
  `compM`).

So every fibre sum is nonnegative (`sum_nonneg_of_pair`), hence the whole sum (`depth_two`).
-/

namespace GridGen.Four.K4

open Finset

/-- A sum with at most one bad term, which pairs with another term to a nonnegative sum, is
nonnegative when the good terms are. -/
theorem sum_nonneg_of_pair {α : Type*} [DecidableEq α] (F : Finset α) (h : α → ℤ)
    (bad : α → Prop) (hgood : ∀ u ∈ F, ¬ bad u → 0 ≤ h u)
    (huniq : ∀ u ∈ F, ∀ u' ∈ F, bad u → bad u' → u = u')
    (hpair : ∀ u ∈ F, bad u → ∃ u' ∈ F, u' ≠ u ∧ 0 ≤ h u + h u') :
    0 ≤ ∑ u ∈ F, h u := by
  by_cases hb : ∃ u ∈ F, bad u
  · obtain ⟨u, hu, hbu⟩ := hb
    obtain ⟨u', hu', hne, hsum⟩ := hpair u hu hbu
    have hu'e : u' ∈ F.erase u := Finset.mem_erase.mpr ⟨hne, hu'⟩
    rw [← Finset.add_sum_erase F h hu, ← Finset.add_sum_erase (F.erase u) h hu'e]
    have hrest : 0 ≤ ∑ v ∈ (F.erase u).erase u', h v := by
      refine Finset.sum_nonneg fun v hv => ?_
      have hvu : v ∈ F.erase u := Finset.mem_of_mem_erase hv
      have hvF : v ∈ F := Finset.mem_of_mem_erase hvu
      exact hgood v hvF fun hbv => Finset.ne_of_mem_erase hvu (huniq u hu v hvF hbu hbv).symm
    linarith
  · push Not at hb
    exact Finset.sum_nonneg fun u hu => hgood u hu (hb u hu)

/-! ### Lists -/

theorem cards_ers {A : Col} (hA : CardsIn 4 4 A) (u : T4) : CardsIn 3 4 (ers A u) := by
  obtain ⟨⟨a1, a1'⟩, ⟨a2, a2'⟩, ⟨a3, a3'⟩, ⟨a4, a4'⟩⟩ := hA
  have l1 := Finset.pred_card_le_card_erase (s := A.1) (a := r1 u)
  have l2 := Finset.pred_card_le_card_erase (s := A.2.1) (a := r2 u)
  have l3 := Finset.pred_card_le_card_erase (s := A.2.2.1) (a := r3 u)
  have l4 := Finset.pred_card_le_card_erase (s := A.2.2.2) (a := r4 u)
  have m1 := Finset.card_erase_le (s := A.1) (a := r1 u)
  have m2 := Finset.card_erase_le (s := A.2.1) (a := r2 u)
  have m3 := Finset.card_erase_le (s := A.2.2.1) (a := r3 u)
  have m4 := Finset.card_erase_le (s := A.2.2.2) (a := r4 u)
  simp only [CardsIn, ers]
  omega

theorem mem_of_erase_card {A : Finset ℕ} {p : ℕ} (hA : A.card = 4) (h : (A.erase p).card = 3) :
    p ∈ A := by
  by_contra hp
  rw [Finset.erase_eq_of_notMem hp] at h
  omega

/-- A three-colour puncture of a four-list determines the erased colour. -/
theorem eq_of_erase_eq {A : Finset ℕ} {p p' : ℕ} (hA : A.card = 4) (h : A.erase p = A.erase p')
    (h3 : (A.erase p).card = 3) : p = p' :=
  Finset.erase_injOn A (mem_of_erase_card hA h3) (mem_of_erase_card hA (h ▸ h3)) h

/-! ### The two orientations -/

variable {X A B : Col} {w : Q}

/-- The fibres along the last row, for a next column with `B₀ = B₁ = B₂`. -/
theorem depth_two_last (hC : Classify4) (hX : CardsIn 3 4 X) (hA : CardsIn 4 4 A)
    (hB : CardsIn 4 4 B) (hw : ∀ d, RaysOK d → 0 ≤ dot d w)
    (hF : B.1 = B.2.1 ∧ B.2.1 = B.2.2.1) :
    0 ≤ ∑ u ∈ stsC X, dot (dvec (ers A u) B) w := by
  classical
  let π : T4 → ℕ × ℕ × ℕ := fun u => (r1 u, r2 u, r3 u)
  rw [← Finset.sum_fiberwise_of_maps_to (g := π) (t := (stsC X).image π)
    (fun u hu => Finset.mem_image_of_mem π hu)]
  refine Finset.sum_nonneg fun v _ => ?_
  have hA4 : A.2.2.2.card = 4 := le_antisymm hA.2.2.2.2 hA.2.2.2.1
  refine sum_nonneg_of_pair _ _ (fun u => Bad (ers A u) B) ?_ ?_ ?_
  · intro u _ hnb
    exact hw _ (hC _ _ (cards_ers hA u) hB hnb)
  · intro u hu u' hu' hb hb'
    have hv : π u = π u' := (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hu').2.symm
    simp only [π, Prod.mk.injEq] at hv
    obtain ⟨e1, e2, e3⟩ := hv
    obtain ⟨t, t3⟩ := badF_target (bad_fwd hF hb)
    obtain ⟨t', -⟩ := badF_target (bad_fwd hF hb')
    simp only [ers] at t t' t3
    rw [e3] at t
    have e4 := eq_of_erase_eq hA4 (t.trans t'.symm) t3
    obtain ⟨u1, u2, u3, u4⟩ := u
    obtain ⟨u1', u2', u3', u4'⟩ := u'
    simp only [r1, r2, r3, r4] at e1 e2 e3 e4
    rw [e1, e2, e3, e4]
  · intro u hu hb
    have huX := (Finset.mem_filter.mp hu).1
    have hbF := bad_fwd hF hb
    obtain ⟨-, t3⟩ := badF_target hbF
    have hp : r4 u ∈ A.2.2.2 := mem_of_erase_card hA4 t3
    -- another colour for the last row
    have hX4 : 3 ≤ X.2.2.2.card := hX.2.2.2.1
    have hne : ((X.2.2.2.erase (r4 u)).erase (r3 u)).Nonempty := by
      rw [← Finset.card_pos]
      have := Finset.pred_card_le_card_erase (s := X.2.2.2.erase (r4 u)) (a := r3 u)
      have := Finset.pred_card_le_card_erase (s := X.2.2.2) (a := r4 u)
      omega
    obtain ⟨q, hq⟩ := hne
    simp only [Finset.mem_erase] at hq
    obtain ⟨hq3, hq4, hqX⟩ := hq
    refine ⟨(r1 u, r2 u, r3 u, q), ?_, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨?_, (Finset.mem_filter.mp hu).2⟩
      unfold stsC at huX ⊢
      rw [mem_sts] at huX ⊢
      exact ⟨huX.1, huX.2.1, huX.2.2.1, hqX, huX.2.2.2.2.1, huX.2.2.2.2.2.1, Ne.symm hq3⟩
    · intro h
      apply hq4
      have := congrArg r4 h
      simpa [r4] using this
    · have key := compF hbF (p := r4 u) (q := q) (Finset.notMem_erase _ _) hq4
      have e : setL4 (ers A u) ((insert (r4 u) (ers A u).2.2.2).erase q)
          = ers A (r1 u, r2 u, r3 u, q) := by
        simp only [setL4, ers, Finset.insert_erase hp]
      rw [e] at key
      have := hw _ key
      rw [dot_add] at this
      exact this

/-- The fibres along the first row, for any other next column. -/
theorem depth_two_first (hC : Classify4) (hX : CardsIn 3 4 X) (hA : CardsIn 4 4 A)
    (hB : CardsIn 4 4 B) (hw : ∀ d, RaysOK d → 0 ≤ dot d w)
    (hF : ¬ (B.1 = B.2.1 ∧ B.2.1 = B.2.2.1)) :
    0 ≤ ∑ u ∈ stsC X, dot (dvec (ers A u) B) w := by
  classical
  let π : T4 → ℕ × ℕ × ℕ := fun u => (r2 u, r3 u, r4 u)
  rw [← Finset.sum_fiberwise_of_maps_to (g := π) (t := (stsC X).image π)
    (fun u hu => Finset.mem_image_of_mem π hu)]
  refine Finset.sum_nonneg fun v _ => ?_
  have hA1 : A.1.card = 4 := le_antisymm hA.1.2 hA.1.1
  refine sum_nonneg_of_pair _ _ (fun u => Bad (ers A u) B) ?_ ?_ ?_
  · intro u _ hnb
    exact hw _ (hC _ _ (cards_ers hA u) hB hnb)
  · intro u hu u' hu' hb hb'
    have hv : π u = π u' := (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hu').2.symm
    simp only [π, Prod.mk.injEq] at hv
    obtain ⟨e2, e3, e4⟩ := hv
    have e1 : r1 u = r1 u' := by
      rcases bad_nfwd hF hb with h | h <;> rcases bad_nfwd hF hb' with h' | h'
      · obtain ⟨t, t3⟩ := badR_target h
        obtain ⟨t', -⟩ := badR_target h'
        simp only [ers] at t t' t3
        rw [e2] at t
        exact eq_of_erase_eq hA1 (t.trans t'.symm) t3
      · exact (not_badR_badM h h').elim
      · exact (not_badR_badM h' h).elim
      · obtain ⟨t, t3⟩ := badM_target h
        obtain ⟨t', -⟩ := badM_target h'
        simp only [ers] at t t' t3
        exact eq_of_erase_eq hA1 (t.trans t'.symm) t3
    obtain ⟨u1, u2, u3, u4⟩ := u
    obtain ⟨u1', u2', u3', u4'⟩ := u'
    simp only [r1, r2, r3, r4] at e1 e2 e3 e4
    rw [e1, e2, e3, e4]
  · intro u hu hb
    have huX := (Finset.mem_filter.mp hu).1
    have t3 : (A.1.erase (r1 u)).card = 3 := by
      rcases bad_nfwd hF hb with h | h
      · exact (badR_target h).2
      · exact (badM_target h).2
    have hp : r1 u ∈ A.1 := mem_of_erase_card hA1 t3
    have hX1 : 3 ≤ X.1.card := hX.1.1
    have hne : ((X.1.erase (r1 u)).erase (r2 u)).Nonempty := by
      rw [← Finset.card_pos]
      have := Finset.pred_card_le_card_erase (s := X.1.erase (r1 u)) (a := r2 u)
      have := Finset.pred_card_le_card_erase (s := X.1) (a := r1 u)
      omega
    obtain ⟨q, hq⟩ := hne
    simp only [Finset.mem_erase] at hq
    obtain ⟨hq2, hq1, hqX⟩ := hq
    refine ⟨(q, r2 u, r3 u, r4 u), ?_, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨?_, (Finset.mem_filter.mp hu).2⟩
      unfold stsC at huX ⊢
      rw [mem_sts] at huX ⊢
      exact ⟨hqX, huX.2.1, huX.2.2.1, huX.2.2.2.1, hq2, huX.2.2.2.2.2.1, huX.2.2.2.2.2.2⟩
    · intro h
      apply hq1
      have := congrArg r1 h
      simpa [r1] using this
    · have key : RaysOK (dvec (ers A u) B
          + dvec (setL1 (ers A u) ((insert (r1 u) (ers A u).1).erase q)) B) := by
        rcases bad_nfwd hF hb with h | h
        · exact compR h (Finset.notMem_erase _ _) hq1
        · exact compM h (Finset.notMem_erase _ _) hq1
      have e : setL1 (ers A u) ((insert (r1 u) (ers A u).1).erase q)
          = ers A (q, r2 u, r3 u, r4 u) := by
        simp only [setL1, ers, Finset.insert_erase hp]
      rw [e] at key
      have := hw _ key
      rw [dot_add] at this
      exact this

/-- **The depth-two seam, from the classification.** For lists `X` of three or four colours and
lists `A`, `B` of four colours, the depth-two slack is nonnegative at every weight in `K`. -/
theorem depth_two (hC : Classify4) (hX : CardsIn 3 4 X) (hA : CardsIn 4 4 A)
    (hB : CardsIn 4 4 B) (hw : ∀ d, RaysOK d → 0 ≤ dot d w) :
    0 ≤ ∑ u ∈ stsC X, dot (dvec (ers A u) B) w := by
  by_cases hF : B.1 = B.2.1 ∧ B.2.1 = B.2.2.1
  · exact depth_two_last hC hX hA hB hw hF
  · exact depth_two_first hC hX hA hB hw hF

end GridGen.Four.K4
