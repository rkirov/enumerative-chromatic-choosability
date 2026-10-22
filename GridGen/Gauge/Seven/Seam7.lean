/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Seven.Core7
import GridGen.Gauge.Eight.Core8

/-!
# The seam at `k = 7`: the induction over the lookahead process

The old column `A` has a vertically consistent labelling `β`; the new column `B` gets the
labelling `βx = tilde` (old labels on kept colours, star labels on new ones). The lookahead
process `proc` makes the new column vertically consistent, colour by colour and edge by edge.
Along it we keep the moves `O`, the deleted stars `Del` and the charged units `U` of the old
column's vertical difference, with the invariant `Inv`:

* every edge already processed, and every colour already processed at the current edge, is
  matched; so is every colour matched at the start (`βx` agrees);
* every deleted star is the star of a new colour whose moves are all done (the colour is matched
  at both edges of the star's row);
* every charged unit `(e, c)` has `c ∈ A_{e+1} \ A_e` and `c` matched at `e`;
* `(1 - γ_V)^{|U|} Z(start) ≤ Z(now)`.

A colour step keeps the invariant (`inv_step`): its star is not yet deleted (the invariant would
have it matched), its label is a hole once the star is deleted, and its unit is fresh.
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m : ℕ} {P A B : Fin m → Finset ℕ} {β : ℕ → ℕ → ℕ}

section Inv

variable (A B β) in
/-- The star of a new colour `c` of row `r`: a leaving colour of row `r` with the label of `c`. -/
noncomputable def starOf (r c : ℕ) : ℕ :=
  if h : ∃ s ∈ extR A r \ extR B r, β r s = tilde (extR A) (extR B) β r c then h.choose else 0

theorem starOf_spec (hA : ∀ v, (A v).card = 7) (hB : ∀ v, (B v).card = 7)
    (hβ : ∀ v : Fin m, Set.InjOn (β v.val) (A v) ∧ ∀ a ∈ A v, β v.val a < 7) {r cc : ℕ}
    (hcc : cc ∈ extR B r \ extR A r) :
    starOf A B β r cc ∈ extR A r \ extR B r ∧
      β r (starOf A B β r cc) = tilde (extR A) (extR B) β r cc := by
  have hcard : ∀ v, (extR A v).card = (extR B v).card := by
    intro v; simp only [extR]; split_ifs with h
    · rw [hA, hB]
    · rfl
  have hβx : ∀ v, Set.InjOn (β v) (extR A v) := by
    intro v; simp only [extR]; split_ifs with h
    · exact (hβ ⟨v, h⟩).1
    · simp
  have hex : ∃ s ∈ extR A r \ extR B r, β r s = tilde (extR A) (extR B) β r cc := by
    have := starMap_mem hcard hβx hcc
    rw [mem_image] at this
    obtain ⟨s, hs, e⟩ := this
    refine ⟨s, hs, ?_⟩
    rw [e]; unfold tilde; rw [ite_eq_right (mem_sdiff.mp hcc).2]
  unfold starOf
  rw [dite_eq_left hex]
  exact hex.choose_spec

end Inv

section Invariant

variable (A B β) in
/-- The matching facts of the invariant at the edge below row `e`, with the colours `done` of that
edge processed. -/
structure MatchFacts (e : ℕ) (done : Finset ℕ) (O : List GOp) (Del : Finset (Fin m × ℕ))
    (U : Finset (ℕ × ℕ)) : Prop where
  past : ∀ e' < e, ∀ c ∈ extR B e' ∩ extR B (e' + 1),
    Matched (βx := tilde (extR A) (extR B) β) O e' c
  cur : ∀ c ∈ done, c ∈ extR B e ∩ extR B (e + 1) ∧
    Matched (βx := tilde (extR A) (extR B) β) O e c
  stat : ∀ e' c, c ∈ extR B e' ∩ extR B (e' + 1) →
    tilde (extR A) (extR B) β (e' + 1) c = tilde (extR A) (extR B) β e' c →
      Matched (βx := tilde (extR A) (extR B) β) O e' c
  del : ∀ p ∈ Del, ∃ c, c ∈ extR B p.1.val \ extR A p.1.val ∧ p.2 = starOf A B β p.1.val c ∧
    (1 ≤ p.1.val → c ∈ extR B (p.1.val - 1) →
      Matched (βx := tilde (extR A) (extR B) β) O (p.1.val - 1) c) ∧
    (c ∈ extR B (p.1.val + 1) → c ∈ extR A (p.1.val + 1) →
      Matched (βx := tilde (extR A) (extR B) β) O p.1.val c)
  units : ∀ u ∈ U, u.2 ∈ extR A (u.1 + 1) \ extR A u.1 ∧ u.2 ∈ extR B u.1 ∧
    u.2 ∈ extR B (u.1 + 1) ∧ Matched (βx := tilde (extR A) (extR B) β) O u.1 u.2

/-- **All matching facts survive a move on one colour.** -/
theorem matchFacts_snoc (hR : RowLab 7 (extR B) (tilde (extR A) (extR B) β))
    {e : ℕ} {done : Finset ℕ} {O : List GOp} {Del : Finset (Fin m × ℕ)} {U : Finset (ℕ × ℕ)}
    (hF : MatchFacts A B β e done O Del U) {e' d : ℕ} {o : GOp}
    (ho : OnColour (Bx := extR B) (βx := tilde (extR A) (extR B) β) O e' d o) :
    MatchFacts A B β e done (O ++ [o]) Del U := by
  have keep : ∀ {e₁ c₁}, c₁ ∈ extR B e₁ → c₁ ∈ extR B (e₁ + 1) →
      Matched (βx := tilde (extR A) (extR B) β) O e₁ c₁ →
        Matched (βx := tilde (extR A) (extR B) β) (O ++ [o]) e₁ c₁ :=
    fun h1 h2 hm => matched_snoc hR ho ⟨h1, h2⟩ hm
  refine ⟨fun e₁ he₁ c₁ hc₁ => ?_, fun c₁ hc₁ => ?_, fun e₁ c₁ hc₁ hst => ?_, fun p hp => ?_,
    fun u hu => ?_⟩
  · rw [mem_inter] at hc₁
    exact keep hc₁.1 hc₁.2 (hF.past e₁ he₁ c₁ (mem_inter.mpr hc₁))
  · obtain ⟨hmem, hm⟩ := hF.cur c₁ hc₁
    rw [mem_inter] at hmem
    exact ⟨mem_inter.mpr hmem, keep hmem.1 hmem.2 hm⟩
  · have hm := hF.stat e₁ c₁ hc₁ hst
    rw [mem_inter] at hc₁
    exact keep hc₁.1 hc₁.2 hm
  · obtain ⟨c₁, hc₁, hs, h1, h2⟩ := hF.del p hp
    refine ⟨c₁, hc₁, hs, fun hr hb => ?_, fun hb ha => ?_⟩
    · have := h1 hr hb
      exact keep hb (by rw [show p.1.val - 1 + 1 = p.1.val by omega]; exact (mem_sdiff.mp hc₁).1)
        this
    · exact keep (mem_sdiff.mp hc₁).1 hb (h2 hb ha)
  · obtain ⟨h1, h2, h3, h4⟩ := hF.units u hu
    exact ⟨h1, h2, h3, keep h2 h3 h4⟩

end Invariant

section Step

variable {hc : 1 ≤ c}

variable (B β) in
/-- The invariant: the matching facts, small moves, and the count. -/
structure Inv (Bnd : Bounds7 c m P A hc) (e : ℕ) (done : Finset ℕ) (O : List GOp)
    (Del : Finset (Fin m × ℕ)) (U : Finset (ℕ × ℕ)) : Prop where
  facts : MatchFacts A B β e done O Del U
  small : OpsSmall 7 O
  count : (1 - Bnd.γV) ^ U.card * (Z c m 7 P A (cov 7 β [] ∅) : ℚ) ≤ Z c m 7 P A (cov 7 β O Del)

theorem lt_of_mem_extR {X : Fin m → Finset ℕ} {v a : ℕ} (h : a ∈ extR X v) : v < m := by
  by_contra hv; rw [extR_ge X (by omega)] at h; simp at h

variable (hA : ∀ v, (A v).card = 7) (hB : ∀ v, (B v).card = 7)
  (hβ : ∀ v : Fin m, Set.InjOn (β v.val) (A v) ∧ ∀ a ∈ A v, β v.val a < 7)
  (hP : ∀ v a, a ∈ A v → 6 ≤ (P v).card ∨ a ∉ P v)
  (hR : RowLab 7 (extR B) (tilde (extR A) (extR B) β))

include hA hB hβ hR in
/-- Stars of distinct new colours are distinct. -/
theorem starOf_inj {r c₁ c₂ : ℕ} (h₁ : c₁ ∈ extR B r \ extR A r) (h₂ : c₂ ∈ extR B r \ extR A r)
    (e : starOf A B β r c₁ = starOf A B β r c₂) : c₁ = c₂ := by
  have s₁ := (starOf_spec hA hB hβ h₁).2
  have s₂ := (starOf_spec hA hB hβ h₂).2
  rw [e] at s₁
  exact (hR r).1 (mem_sdiff.mp h₁).1 (mem_sdiff.mp h₂).1 (s₁.symm.trans s₂)

include hA hB hβ in
/-- The cover reads a star's key as the current label of its new colour. -/
theorem cov_star {O : List GOp} {Del : Finset (Fin m × ℕ)} {r : Fin m} {cc : ℕ}
    (hcc : cc ∈ extR B r.val \ extR A r.val) (hnd : (r, starOf A B β r.val cc) ∉ Del) :
    cov 7 β O Del r (starOf A B β r.val cc) = curL O r.val (tilde (extR A) (extR B) β r.val cc) := by
  unfold cov
  rw [ite_eq_right hnd, (starOf_spec hA hB hβ hcc).2]

/-- Extending the matching facts by a processed colour, deleted stars and charged units. -/
theorem matchFacts_ext {e : ℕ} {done : Finset ℕ} {O : List GOp} {Del : Finset (Fin m × ℕ)}
    {U : Finset (ℕ × ℕ)} (hF : MatchFacts A B β e done O Del U) {cc : ℕ}
    (hcur : cc ∈ extR B e ∩ extR B (e + 1) ∧ Matched (βx := tilde (extR A) (extR B) β) O e cc)
    {D' : Finset (Fin m × ℕ)}
    (hdel : ∀ p ∈ D', ∃ c, c ∈ extR B p.1.val \ extR A p.1.val ∧ p.2 = starOf A B β p.1.val c ∧
      (1 ≤ p.1.val → c ∈ extR B (p.1.val - 1) →
        Matched (βx := tilde (extR A) (extR B) β) O (p.1.val - 1) c) ∧
      (c ∈ extR B (p.1.val + 1) → c ∈ extR A (p.1.val + 1) →
        Matched (βx := tilde (extR A) (extR B) β) O p.1.val c))
    {U' : Finset (ℕ × ℕ)}
    (hunits : ∀ u ∈ U', u.2 ∈ extR A (u.1 + 1) \ extR A u.1 ∧ u.2 ∈ extR B u.1 ∧
      u.2 ∈ extR B (u.1 + 1) ∧ Matched (βx := tilde (extR A) (extR B) β) O u.1 u.2) :
    MatchFacts A B β e (insert cc done) O (D' ∪ Del) (U' ∪ U) := by
  refine ⟨hF.past, fun c hc => ?_, hF.stat, fun p hp => ?_, fun u hu => ?_⟩
  · rcases mem_insert.mp hc with rfl | hc
    · exact hcur
    · exact hF.cur c hc
  · rcases mem_union.mp hp with hp | hp
    · exact hdel p hp
    · exact hF.del p hp
  · rcases mem_union.mp hu with hu | hu
    · exact hunits u hu
    · exact hF.units u hu

theorem opsSmall_append {O O' : List GOp} (h : OpsSmall 7 O) (h' : OpsSmall 7 O') :
    OpsSmall 7 (O ++ O') := by
  intro o ho
  rcases List.mem_append.mp ho with ho | ho
  · exact h o ho
  · exact h' o ho

include hA hB hβ hP hR in
/-- **An H-move** (the colour is new in the lower row): its star of the lower row is fresh, its
current label a hole; the count does not drop. -/
theorem inv_step_H (Bnd : Bounds7 c m P A hc) {e : ℕ} {done : Finset ℕ} {O : List GOp}
    {Del : Finset (Fin m × ℕ)} {U : Finset (ℕ × ℕ)} (hI : Inv B β Bnd e done O Del U) {cc : ℕ}
    (hH : cc ∉ extR A (e + 1))
    (hl : ¬ (Look (extR A) (extR B) e cc ∧
      ¬ Matched (βx := tilde (extR A) (extR B) β) O (e + 1) cc))
    {o : GOp} (ho : OnColour (Bx := extR B) (βx := tilde (extR A) (extR B) β) O e cc o) :
    ∃ Del', Inv B β Bnd e (insert cc done) (O ++ [o]) Del' U := by
  obtain ⟨hcc0, hcc1, ho', hm⟩ := ho
  have hr : e + 1 < m := lt_of_mem_extR hcc1
  set r : Fin m := ⟨e + 1, hr⟩ with hr_def
  have hnew : cc ∈ extR B r.val \ extR A r.val := mem_sdiff.mpr ⟨hcc1, hH⟩
  set s := starOf A B β r.val cc
  obtain ⟨hsA, hsβ⟩ := starOf_spec hA hB hβ hnew
  have hsA' : s ∈ A r := by have := (mem_sdiff.mp hsA).1; rwa [extR_val] at this
  have hnd : (r, s) ∉ Del := by
    intro hd
    obtain ⟨c', hc', hs', h1, -⟩ := hI.facts.del _ hd
    have := starOf_inj hA hB hβ hR hnew hc' hs'
    subst this
    exact hm (h1 (by simp [r]) (by simpa [r] using hcc0))
  set g := curL O (e + 1) (tilde (extR A) (extR B) β (e + 1) cc)
  set h := curL O e (tilde (extR A) (extR B) β e cc)
  have hMg : cov 7 β O Del r s = g := cov_star hA hB hβ hnew hnd
  have hg : g < 7 := curL_lt hI.small _ ((hR (e + 1)).2 cc hcc1)
  have hh : h < 7 := curL_lt hI.small _ ((hR e).2 cc hcc0)
  have hgh : g ≠ h := hm
  have hhole : ∀ a ∈ A r, unpair 7 (cov 7 β O Del) r s r a ≠ g := by
    rw [← cov_insert]
    intro a ha
    have := hole_of_del hβ hI.small hsA' (mem_insert_self (r, s) Del) a ha
    rwa [hsβ] at this
  obtain ⟨hZ, -⟩ := step_slab_single Bnd (keyInj_cov (fun v => (hβ v).1) Del) hsA' hMg hg
    (hP r s hsA') (w := e) hg hh hgh (Or.inr rfl) (Or.inl rfl) hhole
  have hcov : moveKey (unpair 7 (cov 7 β O Del) r s) e g h =
      cov 7 β (O ++ [o]) (insert (r, s) Del) := by
    rw [← cov_insert, ho', ← cov_snoc _ _ _ hg hh]
  rw [hcov] at hZ
  have ho2 : OnColour (Bx := extR B) (βx := tilde (extR A) (extR B) β) O e cc o :=
    ⟨hcc0, hcc1, ho', hm⟩
  have hF := matchFacts_snoc hR hI.facts ho2
  have hself := matched_snoc_self ho2
  refine ⟨insert (r, s) Del, ⟨?_, ?_, ?_⟩⟩
  · rw [insert_eq]
    have := matchFacts_ext (U' := ∅) hF ⟨mem_inter.mpr ⟨hcc0, hcc1⟩, hself⟩
      (D' := {(r, s)}) (fun p hp => ?_) (fun u hu => by simp at hu)
    · rwa [empty_union] at this
    · rw [mem_singleton] at hp
      subst hp
      refine ⟨cc, hnew, rfl, fun _ _ => by simpa [r] using hself, fun hb ha => ?_⟩
      -- the edge below row `e + 1`: matched already (no lookahead)
      have hlook : Look (extR A) (extR B) e cc := ⟨hb, hH, ha⟩
      have hm1 : Matched (βx := tilde (extR A) (extR B) β) O (e + 1) cc := by
        by_contra hn; exact hl ⟨hlook, hn⟩
      exact matched_snoc hR ho2 ⟨hcc1, hb⟩ hm1
  · refine opsSmall_append hI.small fun o' ho'' => ?_
    rw [List.mem_singleton] at ho''
    subst ho''; rw [ho']; exact ⟨hg, hh⟩
  · exact hI.count.trans (by exact_mod_cast hZ)

include hA hB hβ hP hR in
/-- **A D-move** (the colour is old in the lower row, new in the upper): its star of the upper row
is fresh, and so is its unit of the vertical difference; the count drops by at most `1 - γ_V`. -/
theorem inv_step_D (Bnd : Bounds7 c m P A hc)
    (hN : NewMis (extR A) (extR B) (tilde (extR A) (extR B) β)) {e : ℕ} {done : Finset ℕ}
    {O : List GOp} {Del : Finset (Fin m × ℕ)} {U : Finset (ℕ × ℕ)}
    (hI : Inv B β Bnd e done O Del U) {cc : ℕ} (hD : cc ∈ extR A (e + 1)) {o : GOp}
    (ho : OnColour (Bx := extR B) (βx := tilde (extR A) (extR B) β) O e cc o) :
    ∃ Del', Inv B β Bnd e (insert cc done) (O ++ [o]) Del' (insert (e, cc) U) := by
  have ho2 := ho
  obtain ⟨hcc0, hcc1, ho', hm⟩ := ho
  -- statically mismatched, hence new in row `e`
  have hst : tilde (extR A) (extR B) β (e + 1) cc ≠ tilde (extR A) (extR B) β e cc :=
    fun h => hm (hI.facts.stat e cc (mem_inter.mpr ⟨hcc0, hcc1⟩) h)
  have hAe : cc ∉ extR A e := by
    rcases hN e cc (mem_inter.mpr ⟨hcc0, hcc1⟩) hst with h | h
    · exact h
    · exact absurd hD h
  have hr : e < m := lt_of_mem_extR hcc0
  set r : Fin m := ⟨e, hr⟩ with hr_def
  have hnew : cc ∈ extR B r.val \ extR A r.val := mem_sdiff.mpr ⟨hcc0, hAe⟩
  set s := starOf A B β r.val cc
  obtain ⟨hsA, hsβ⟩ := starOf_spec hA hB hβ hnew
  have hsA' : s ∈ A r := by have := (mem_sdiff.mp hsA).1; rwa [extR_val] at this
  have hnd : (r, s) ∉ Del := by
    intro hd
    obtain ⟨c', hc', hs', -, h2⟩ := hI.facts.del _ hd
    have := starOf_inj hA hB hβ hR hnew hc' hs'
    subst this
    exact hm (h2 hcc1 hD)
  have hfresh : (e, cc) ∉ U := fun hu => hm (hI.facts.units _ hu).2.2.2
  set g := curL O (e + 1) (tilde (extR A) (extR B) β (e + 1) cc)
  set h := curL O e (tilde (extR A) (extR B) β e cc)
  have hMh : cov 7 β O Del r s = h := cov_star hA hB hβ hnew hnd
  have hg : g < 7 := curL_lt hI.small _ ((hR (e + 1)).2 cc hcc1)
  have hh : h < 7 := curL_lt hI.small _ ((hR e).2 cc hcc0)
  have hgh : g ≠ h := hm
  have hhole : ∀ a ∈ A r, unpair 7 (cov 7 β O Del) r s r a ≠ h := by
    rw [← cov_insert]
    intro a ha
    have := hole_of_del hβ hI.small hsA' (mem_insert_self (r, s) Del) a ha
    rwa [hsβ] at this
  obtain ⟨-, hZ⟩ := step_slab_single Bnd (keyInj_cov (fun v => (hβ v).1) Del) hsA' hMh hh
    (hP r s hsA') (w := e) hg hh hgh (Or.inl rfl) (Or.inr rfl) hhole
  have hcov : moveKey (unpair 7 (cov 7 β O Del) r s) e g h =
      cov 7 β (O ++ [o]) (insert (r, s) Del) := by
    rw [← cov_insert, ho', ← cov_snoc _ _ _ hg hh]
  rw [hcov] at hZ
  have hF := matchFacts_snoc hR hI.facts ho2
  have hself := matched_snoc_self ho2
  refine ⟨insert (r, s) Del, ⟨?_, ?_, ?_⟩⟩
  · rw [insert_eq (r, s) Del, insert_eq (e, cc) U]
    refine matchFacts_ext hF ⟨mem_inter.mpr ⟨hcc0, hcc1⟩, hself⟩ (fun p hp => ?_) (fun u hu => ?_)
    · rw [mem_singleton] at hp
      subst hp
      refine ⟨cc, hnew, rfl, fun he hb => ?_, fun _ _ => hself⟩
      have hpast := hI.facts.past (e - 1) (by simp [r] at he ⊢; omega) cc
        (mem_inter.mpr ⟨hb, by simpa [r, show e - 1 + 1 = e by simp [r] at he; omega] using hcc0⟩)
      exact matched_snoc hR ho2 ⟨hb, by simpa [r, show e - 1 + 1 = e by simp [r] at he; omega]
        using hcc0⟩ hpast
    · rw [mem_singleton] at hu
      subst hu
      exact ⟨mem_sdiff.mpr ⟨hD, hAe⟩, hcc0, hcc1, hself⟩
  · refine opsSmall_append hI.small fun o' ho'' => ?_
    rw [List.mem_singleton] at ho''
    subst ho''; rw [ho']; exact ⟨hg, hh⟩
  · rw [card_insert_of_notMem hfresh, pow_succ]
    have h1 : 0 ≤ 1 - Bnd.γV := by linarith [Bnd.hγV1]
    calc (1 - Bnd.γV) ^ U.card * (1 - Bnd.γV) * (Z c m 7 P A (cov 7 β [] ∅) : ℚ)
        = (1 - Bnd.γV) * ((1 - Bnd.γV) ^ U.card * Z c m 7 P A (cov 7 β [] ∅)) := by ring
      _ ≤ (1 - Bnd.γV) * Z c m 7 P A (cov 7 β O Del) := mul_le_mul_of_nonneg_left hI.count h1
      _ ≤ _ := hZ

include hA hB hβ hP hR in
/-- **A double**: the star of row `e + 1` serves the move at the edge below row `e + 1` and then
the move at the edge below row `e`; the unit of the former is charged. -/
theorem inv_step_dbl (Bnd : Bounds7 c m P A hc) {e : ℕ} {done : Finset ℕ}
    {O : List GOp} {Del : Finset (Fin m × ℕ)} {U : Finset (ℕ × ℕ)}
    (hI : Inv B β Bnd e done O Del U) {cc : ℕ} (hl : Look (extR A) (extR B) e cc)
    (hm1 : ¬ Matched (βx := tilde (extR A) (extR B) β) O (e + 1) cc) {o₂ o₁ : GOp}
    (ho₂ : OnColour (Bx := extR B) (βx := tilde (extR A) (extR B) β) O (e + 1) cc o₂)
    (ho₁ : OnColour (Bx := extR B) (βx := tilde (extR A) (extR B) β) (O ++ [o₂]) e cc o₁) :
    ∃ Del', Inv B β Bnd e (insert cc done) (O ++ [o₂] ++ [o₁]) Del' (insert (e + 1, cc) U) := by
  have ho₂' := ho₂
  have ho₁' := ho₁
  obtain ⟨hcc1, hcc2, ho₂e, -⟩ := ho₂
  obtain ⟨hcc0, -, ho₁e, hm⟩ := ho₁
  obtain ⟨-, hH, hA2⟩ := hl
  have hr : e + 1 < m := lt_of_mem_extR hcc1
  set r : Fin m := ⟨e + 1, hr⟩ with hr_def
  have hnew : cc ∈ extR B r.val \ extR A r.val := mem_sdiff.mpr ⟨hcc1, hH⟩
  set s := starOf A B β r.val cc
  obtain ⟨hsA, hsβ⟩ := starOf_spec hA hB hβ hnew
  have hsA' : s ∈ A r := by have := (mem_sdiff.mp hsA).1; rwa [extR_val] at this
  -- the labels after the first move, in rows `e` and `e + 1`, are unchanged
  have hrow1 : ∀ z, curL (O ++ [o₂]) (e + 1) z = curL O (e + 1) z := fun z => by
    rw [curL_snoc, ho₂e]; simp
  have hrow0 : ∀ z, curL (O ++ [o₂]) e z = curL O e z := fun z => by
    rw [curL_snoc, ho₂e]; simp
  have hm' : ¬ Matched (βx := tilde (extR A) (extR B) β) O e cc := by
    intro h; apply hm; unfold Matched at h ⊢; rw [hrow1, hrow0]; exact h
  have hnd : (r, s) ∉ Del := by
    intro hd
    obtain ⟨c', hc', hs', h1, -⟩ := hI.facts.del _ hd
    have := starOf_inj hA hB hβ hR hnew hc' hs'
    subst this
    exact hm' (h1 (by simp [r]) (by simpa [r] using hcc0))
  have hfresh : (e + 1, cc) ∉ U := fun hu => hm1 (hI.facts.units _ hu).2.2.2
  set x₂ := curL O (e + 2) (tilde (extR A) (extR B) β (e + 2) cc)
  set g := curL O (e + 1) (tilde (extR A) (extR B) β (e + 1) cc)
  set h := curL O e (tilde (extR A) (extR B) β e cc)
  have hMg : cov 7 β O Del r s = g := cov_star hA hB hβ hnew hnd
  have hg : g < 7 := curL_lt hI.small _ ((hR (e + 1)).2 cc hcc1)
  have hh : h < 7 := curL_lt hI.small _ ((hR e).2 cc hcc0)
  have hx₂ : x₂ < 7 := curL_lt hI.small _ ((hR (e + 2)).2 cc hcc2)
  have hx₂g : x₂ ≠ g := hm1
  have hgh : g ≠ h := hm'
  have ho₁v : o₁ = (e, g, h) := by rw [ho₁e, hrow1, hrow0]
  have hhole : ∀ a ∈ A r, unpair 7 (cov 7 β O Del) r s r a ≠ g := by
    rw [← cov_insert]
    intro a ha
    have := hole_of_del hβ hI.small hsA' (mem_insert_self (r, s) Del) a ha
    rwa [hsβ] at this
  have hZ := step_slab_double Bnd (keyInj_cov (fun v => (hβ v).1) Del) hsA' hMg hg
    (hP r s hsA') hx₂ hx₂g hg hh hgh (w₁ := e) rfl (Or.inl rfl) hhole
  have hcov : moveKey (moveKey (unpair 7 (cov 7 β O Del) r s) r.val x₂ g) e g h =
      cov 7 β (O ++ [o₂] ++ [o₁]) (insert (r, s) Del) := by
    rw [ho₁v, cov_snoc _ _ _ hg hh, ho₂e, cov_snoc _ _ _ hx₂ hg, cov_insert]
  rw [hcov] at hZ
  have hF₂ := matchFacts_snoc hR hI.facts ho₂'
  have hF := matchFacts_snoc hR hF₂ ho₁'
  have hself₁ : Matched (βx := tilde (extR A) (extR B) β) (O ++ [o₂] ++ [o₁]) (e + 1) cc :=
    matched_snoc hR ho₁' ⟨hcc1, hcc2⟩ (matched_snoc_self ho₂')
  have hself₀ := matched_snoc_self ho₁'
  refine ⟨insert (r, s) Del, ⟨?_, ?_, ?_⟩⟩
  · rw [insert_eq (r, s) Del, insert_eq (e + 1, cc) U]
    refine matchFacts_ext hF ⟨mem_inter.mpr ⟨hcc0, hcc1⟩, hself₀⟩ (fun p hp => ?_)
      (fun u hu => ?_)
    · rw [mem_singleton] at hp
      subst hp
      exact ⟨cc, hnew, rfl, fun _ _ => by simpa [r] using hself₀, fun _ _ => hself₁⟩
    · rw [mem_singleton] at hu
      subst hu
      exact ⟨mem_sdiff.mpr ⟨hA2, hH⟩, hcc1, hcc2, hself₁⟩
  · refine opsSmall_append (opsSmall_append hI.small fun o' ho'' => ?_) fun o' ho'' => ?_
    · rw [List.mem_singleton] at ho''
      subst ho''; rw [ho₂e]; exact ⟨hx₂, hg⟩
    · rw [List.mem_singleton] at ho''
      subst ho''; rw [ho₁v]; exact ⟨hg, hh⟩
  · rw [card_insert_of_notMem hfresh, pow_succ]
    have h1 : 0 ≤ 1 - Bnd.γV := by linarith [Bnd.hγV1]
    calc (1 - Bnd.γV) ^ U.card * (1 - Bnd.γV) * (Z c m 7 P A (cov 7 β [] ∅) : ℚ)
        = (1 - Bnd.γV) * ((1 - Bnd.γV) ^ U.card * Z c m 7 P A (cov 7 β [] ∅)) := by ring
      _ ≤ (1 - Bnd.γV) * Z c m 7 P A (cov 7 β O Del) := mul_le_mul_of_nonneg_left hI.count h1
      _ ≤ _ := hZ

include hA hB hβ hP hR in
/-- **One colour step keeps the invariant.** -/
theorem inv_step (Bnd : Bounds7 c m P A hc)
    (hN : NewMis (extR A) (extR B) (tilde (extR A) (extR B) β)) {e : ℕ} {done : Finset ℕ}
    {O : List GOp} {Del : Finset (Fin m × ℕ)} {U : Finset (ℕ × ℕ)}
    (hI : Inv B β Bnd e done O Del U) {cc : ℕ} (hcc : cc ∈ extR B e ∩ extR B (e + 1)) :
    ∃ Del' U', Inv B β Bnd e (insert cc done)
      (stepC (extR A) (extR B) (tilde (extR A) (extR B) β) e O cc) Del' U' := by
  rcases stepC_cases (Ax := extR A) (Bx := extR B) (βx := tilde (extR A) (extR B) β) e O hcc with
    ⟨hm, he⟩ | ⟨hm, hl, o, ho, he⟩ | ⟨hm, hl, hm1, o₂, o₁, ho₂, ho₁, he⟩
  · rw [he]
    refine ⟨Del, U, ⟨?_, hI.small, hI.count⟩⟩
    have := matchFacts_ext (D' := ∅) (U' := ∅) hI.facts ⟨hcc, hm⟩ (fun p hp => by simp at hp)
      (fun u hu => by simp at hu)
    simpa using this
  · rw [he]
    by_cases hH : cc ∉ extR A (e + 1)
    · obtain ⟨Del', h⟩ := inv_step_H hA hB hβ hP hR Bnd hI hH hl ho
      exact ⟨Del', U, h⟩
    · obtain ⟨Del', h⟩ := inv_step_D hA hB hβ hP hR Bnd hN hI (not_not.mp hH) ho
      exact ⟨Del', _, h⟩
  · rw [he]
    obtain ⟨Del', h⟩ := inv_step_dbl hA hB hβ hP hR Bnd hI hl hm1 ho₂ ho₁
    exact ⟨Del', _, h⟩

include hA hB hβ hP hR in
/-- **A run of colour steps.** -/
theorem inv_fold (Bnd : Bounds7 c m P A hc)
    (hN : NewMis (extR A) (extR B) (tilde (extR A) (extR B) β)) (e : ℕ) :
    ∀ (L : List ℕ) (done : Finset ℕ) (O : List GOp) (Del : Finset (Fin m × ℕ))
      (U : Finset (ℕ × ℕ)), Inv B β Bnd e done O Del U →
        (∀ cc ∈ L, cc ∈ extR B e ∩ extR B (e + 1)) →
      ∃ Del' U', Inv B β Bnd e (L.toFinset ∪ done)
        (L.foldl (stepC (extR A) (extR B) (tilde (extR A) (extR B) β) e) O) Del' U' := by
  intro L
  induction L with
  | nil => intro done O Del U hI _; exact ⟨Del, U, by simpa using hI⟩
  | cons cc L ih =>
      intro done O Del U hI hL
      obtain ⟨Del₁, U₁, h₁⟩ := inv_step hA hB hβ hP hR Bnd hN hI (hL cc (by simp))
      obtain ⟨Del₂, U₂, h₂⟩ := ih _ _ _ _ h₁ (fun c' hc' => hL c' (by simp [hc']))
      refine ⟨Del₂, U₂, ?_⟩
      simp only [List.foldl_cons]
      have e₁ : L.toFinset ∪ insert cc done = (cc :: L).toFinset ∪ done := by
        ext x; simp [or_comm, or_left_comm]
      rw [← e₁]; exact h₂

/-- At the end of an edge, all its colours are matched. -/
theorem inv_next (Bnd : Bounds7 c m P A hc) {e : ℕ} {O : List GOp}
    {Del : Finset (Fin m × ℕ)} {U : Finset (ℕ × ℕ)}
    (hI : Inv B β Bnd e (extR B e ∩ extR B (e + 1)) O Del U) : Inv B β Bnd (e + 1) ∅ O Del U := by
  refine ⟨⟨fun e' he' c' hc' => ?_, fun c' hc' => by simp at hc', hI.facts.stat, hI.facts.del,
    hI.facts.units⟩, hI.small, hI.count⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp he' with h | rfl
  · exact hI.facts.past e' h c' hc'
  · exact (hI.facts.cur c' hc').2

include hA hB hβ hP hR in
/-- **The invariant along the whole process.** -/
theorem inv_proc (Bnd : Bounds7 c m P A hc)
    (hN : NewMis (extR A) (extR B) (tilde (extR A) (extR B) β)) :
    ∀ n, ∃ Del U, Inv B β Bnd n ∅ (proc (extR A) (extR B) (tilde (extR A) (extR B) β) n) Del U := by
  intro n
  induction n with
  | zero =>
      refine ⟨∅, ∅, ⟨⟨fun e' he' => by omega, fun c' hc' => by simp at hc',
        fun e' c' _ hst => ?_, fun p hp => by simp at hp, fun u hu => by simp at hu⟩,
        fun o ho => by simp [proc] at ho, by simp [proc]⟩⟩
      unfold Matched; simp only [proc, curL, actOn, List.filter_nil, List.map_nil, compA_nil]
      exact hst
  | succ n ih =>
      obtain ⟨Del, U, hI⟩ := ih
      obtain ⟨Del', U', h⟩ := inv_fold hA hB hβ hP hR Bnd hN n (ordE (extR B) n) ∅ _ Del U hI
        (fun cc hc => (mem_sort _).mp hc)
      refine ⟨Del', U', inv_next Bnd ?_⟩
      have e₁ : (ordE (extR B) n).toFinset ∪ ∅ = extR B n ∩ extR B (n + 1) := by
        ext x; simp [ordE, mem_sort]
      rw [e₁] at h
      exact h

include hc in
/-- Deleting one more star only adds solutions. -/
theorem Z_cov_insert_le (O : List GOp) (D : Finset (Fin m × ℕ)) (p : Fin m × ℕ) :
    Z c m 7 P A (cov 7 β O D) ≤ Z c m 7 P A (cov 7 β O (insert p D)) := by
  rw [cov_insert]; unfold Z
  rw [card_unpair (k := 7) (P := P) (A := A) _ hc p.1 p.2 _ rfl]
  exact Nat.le_add_right _ _

include hc in
/-- Deleting more stars only adds solutions. -/
theorem Z_cov_mono (O : List GOp) {D S : Finset (Fin m × ℕ)} (h : D ⊆ S) :
    Z c m 7 P A (cov 7 β O D) ≤ Z c m 7 P A (cov 7 β O S) := by
  have key : ∀ T : Finset (Fin m × ℕ), Z c m 7 P A (cov 7 β O D) ≤
      Z c m 7 P A (cov 7 β O (T ∪ D)) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | insert p T _ ih =>
        rw [insert_union]
        exact ih.trans (Z_cov_insert_le (hc := hc) O _ p)
  have := key (S \ D)
  rwa [sdiff_union_of_subset h] at this

include hA hB hβ hP in
/-- **The star and move phase of a seam at `k = 7`.** Processing the new column with the lookahead
process, deleting every star, costs at most a factor `1 - γ_V` per unit of the old column's
vertical difference. -/
theorem seam_moves7 (Bnd : Bounds7 c m P A hc)
    (hvc : ∀ v, ∀ c ∈ extR A v ∩ extR A (v + 1), β (v + 1) c = β v c) :
    (1 - Bnd.γV) ^ Dcol A * (Z c m 7 P A (fun v a => β v.val a) : ℚ) ≤
      Z c m 7 P A (cov 7 β (proc (extR A) (extR B) (tilde (extR A) (extR B) β) m) (stars A B)) := by
  have hcard : ∀ v, (extR A v).card = (extR B v).card := by
    intro v; simp only [extR]; split_ifs with h
    · rw [hA, hB]
    · rfl
  have hβx : ∀ v, Set.InjOn (β v) (extR A v) ∧ ∀ a ∈ extR A v, β v a < 7 := by
    intro v; simp only [extR]; split_ifs with h
    · exact hβ ⟨v, h⟩
    · simp
  have hR : RowLab 7 (extR B) (tilde (extR A) (extR B) β) := rowLab_tilde hcard hβx
  have hN := newMis_tilde (B := B) hvc
  obtain ⟨Del, U, hI⟩ := inv_proc hA hB hβ hP hR Bnd hN m
  -- the charged units are units of the vertical difference
  have hU : U.card ≤ Dcol A := by
    have hsub : U ⊆ (range m).biUnion
        (fun e => (extR A (e + 1) \ extR A e).image (fun a => (e, a))) := by
      intro u hu
      obtain ⟨h1, -, -, -⟩ := hI.facts.units u hu
      have hlt : u.1 + 1 < m := lt_of_mem_extR (mem_sdiff.mp h1).1
      rw [mem_biUnion]
      exact ⟨u.1, mem_range.mpr (by omega), mem_image.mpr ⟨u.2, h1, rfl⟩⟩
    calc U.card ≤ _ := card_le_card hsub
      _ ≤ ∑ e ∈ range m, ((extR A (e + 1) \ extR A e).image (fun a => (e, a))).card :=
          card_biUnion_le
      _ ≤ ∑ e ∈ range m, (extR A (e + 1) \ extR A e).card := sum_le_sum fun e _ => card_image_le
      _ = Dcol A := rfl
  -- the deleted stars are stars
  have hDel : Del ⊆ stars A B := by
    intro p hp
    obtain ⟨cc, hcc, hs, -⟩ := hI.facts.del p hp
    have := (starOf_spec hA hB hβ hcc).1
    rw [← hs, extR_val, extR_val, mem_sdiff] at this
    rw [mem_stars]; exact this
  have hγ0 : 0 ≤ Bnd.γV := le_trans Bnd.hε0 Bnd.hD
  have hpow : (1 - Bnd.γV) ^ Dcol A ≤ (1 - Bnd.γV) ^ U.card :=
    pow_le_pow_of_le_one (by linarith [Bnd.hγV1]) (by linarith) hU
  have hcount := hI.count
  rw [cov_nil] at hcount
  have hZ0 : (0 : ℚ) ≤ Z c m 7 P A (fun v a => β v.val a) := by positivity
  calc (1 - Bnd.γV) ^ Dcol A * (Z c m 7 P A (fun v a => β v.val a) : ℚ)
      ≤ (1 - Bnd.γV) ^ U.card * Z c m 7 P A (fun v a => β v.val a) :=
        mul_le_mul_of_nonneg_right hpow hZ0
    _ ≤ Z c m 7 P A (cov 7 β (proc (extR A) (extR B) (tilde (extR A) (extR B) β) m) Del) :=
        hcount
    _ ≤ _ := by exact_mod_cast Z_cov_mono (hc := hc) _ hDel

end Step

end GridGen.Gauge
