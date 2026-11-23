/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.DissFaces
import Outerplanar.NumTags

/-!
# Polygon dissections with at most six even faces are 3-ECC

**`ecc_three_of_six_even`**: a polygon dissection (`IsDissection`, the 2-connected outerplanar
graphs drawn with their Hamiltonian cycle as the outer face) with at most six even faces
(`IsFace`, `Outerplanar/DissFaces.lean`) is 3-ECC.

The graph is built from a base edge by ears (`TagBuilt`, `Outerplanar/TagBuilt.lean`) following
the numeric face rule of `Outerplanar/NumTags.lean`.

* `tagOf H a b` — the tag demanded on a chord `(a, b)` from the side `[a, b]`: by the number of
  even faces inside (`marks`): none, one (a square or a longer even face), two, more.
* `rule_of_enum` — the face rule holds at the root face of `[a, b]` when `[a, b]` is good
  (`GoodP`: no even face has a side with three or more even faces beyond it).
* `extend` — the side `[a, b]` of an edge already built is built by ears, by induction on the
  width of the interval.
* The base edge: a narrowest chord with at least three even faces inside (if any); its inside is
  good by minimality, its outside has at most three even faces, so it is good too. The outside
  is built in rotated coordinates.

This is the six-even-face theorem of the research note
`ai_research_notes/OUTERPLANAR_SIX_EVEN_2026-11-23.md` (proof by a ChatGPT session; audited and
extended by Claude), formalized.
-/

namespace Outerplanar

open Finset

variable {n : ℕ}

/-! ### The tags -/

open Classical in
/-- The tag demanded on `(a, b)` from the side `[a, b]`. -/
noncomputable def tagOf (H : SimpleGraph (Fin n)) (a b : Fin n) : NTag :=
  if marks H a b = 0 then NTag.plain
  else if marks H a b = 1 then (if sqIn H a b then tSq else tLong)
  else if marks H a b = 2 then tTwo else tHex

section Tags

variable {H : SimpleGraph (Fin n)} {a b : Fin n}

theorem tagOf_zero (h : marks H a b = 0) : tagOf H a b = NTag.plain := by
  unfold tagOf; simp [h]

open Classical in
theorem tagOf_one (h : marks H a b = 1) :
    tagOf H a b = (if sqIn H a b then tSq else tLong) := by
  classical
  unfold tagOf; simp [h]

theorem tagOf_two (h : marks H a b = 2) : tagOf H a b = tTwo := by
  unfold tagOf; simp [h]

theorem tagOf_three (h : 3 ≤ marks H a b) : tagOf H a b = tHex := by
  unfold tagOf
  simp [show marks H a b ≠ 0 by omega, show marks H a b ≠ 1 by omega,
    show marks H a b ≠ 2 by omega]

/-- A tag of one mark: the matching bound, the four-cell constant `3/4`. -/
theorem tagOf_one_facts (h : marks H a b = 1) :
    (tagOf H a b).mb = true ∧ (tagOf H a b).tv = 3 / 4 ∧ 10 / 11 ≤ (tagOf H a b).fl ∨
      tagOf H a b = tSq := by
  classical
  rw [tagOf_one h]
  split_ifs
  · exact Or.inr rfl
  · left
    refine ⟨rfl, rfl, ?_⟩
    show (10 / 11 : ℝ) ≤ 10 / 11
    exact le_rfl

theorem tagOf_one_mb (h : marks H a b = 1) : (tagOf H a b).mb = true := by
  classical
  rw [tagOf_one h]; split_ifs <;> rfl

theorem tagOf_one_tv (h : marks H a b = 1) : (tagOf H a b).tv = 3 / 4 := by
  classical
  rw [tagOf_one h]; split_ifs <;> rfl

theorem tagOf_mb (h : marks H a b ≤ 2) : (tagOf H a b).mb = true := by
  rcases Nat.lt_or_ge (marks H a b) 1 with h0 | h1
  · rw [tagOf_zero (by omega)]; rfl
  · rcases (by omega : marks H a b = 1 ∨ marks H a b = 2) with h1 | h2
    · exact tagOf_one_mb h1
    · rw [tagOf_two h2]; rfl

end Tags

/-! ### At most two marks among the children -/

theorem sum_le_two_cases {k : ℕ} (f : Fin k → ℕ) (h : ∑ i, f i ≤ 2) :
    (∀ i, f i = 0) ∨ (∃ j, f j = 1 ∧ ∀ i, i ≠ j → f i = 0) ∨
      (∃ j, f j = 2 ∧ ∀ i, i ≠ j → f i = 0) ∨
      (∃ j₁ j₂, j₁ < j₂ ∧ f j₁ = 1 ∧ f j₂ = 1 ∧ ∀ i, i ≠ j₁ → i ≠ j₂ → f i = 0) := by
  classical
  by_cases hall : ∀ i, f i = 0
  · exact Or.inl hall
  push Not at hall
  obtain ⟨j, hj⟩ := hall
  have hsplit := Finset.add_sum_erase univ f (mem_univ j)
  by_cases hrest : ∑ i ∈ univ.erase j, f i = 0
  · have hz : ∀ i, i ≠ j → f i = 0 := fun i hi =>
      (Finset.sum_eq_zero_iff.mp hrest) i (mem_erase.mpr ⟨hi, mem_univ i⟩)
    rcases (by omega : f j = 1 ∨ f j = 2) with h1 | h2
    · exact Or.inr (Or.inl ⟨j, h1, hz⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨j, h2, hz⟩))
  · obtain ⟨j', hj'mem, hj'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hrest
    have hj'j := (mem_erase.mp hj'mem).1
    have hsplit2 := Finset.add_sum_erase (univ.erase j) f hj'mem
    have hz : ∀ i, i ≠ j → i ≠ j' → f i = 0 := fun i hi hi' => by
      have hrest2 : ∑ i ∈ (univ.erase j).erase j', f i = 0 := by omega
      exact (Finset.sum_eq_zero_iff.mp hrest2) i
        (mem_erase.mpr ⟨hi', mem_erase.mpr ⟨hi, mem_univ i⟩⟩)
    have h1 : f j = 1 := by omega
    have h1' : f j' = 1 := by omega
    rcases lt_or_gt_of_ne hj'j with hlt | hgt
    · exact Or.inr (Or.inr (Or.inr ⟨j', j, hlt, h1', h1, fun i a b => hz i b a⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨j, j', hgt, h1, h1', hz⟩))

/-! ### The face rule at a root face -/

section Rule

variable {H : SimpleGraph (Fin n)} {a b : Fin n} {m : ℕ} {r : Fin (m + 2) → Fin n}

theorem marks_pos_of_mem {c d : Fin n} {F : Finset (Fin n)} (hF : F ∈ facesIn H c d)
    (hev : Even F.card) : 1 ≤ marks H c d := by
  classical
  unfold marks
  exact card_pos.mpr ⟨F, mem_filter.mpr ⟨hF, hev⟩⟩

/-- With no even face in the children, a square inside is the root face. -/
theorem sqIn_iff_root (hH : IsDissection H) (hadj : H.Adj a b) (he : RootEnum H a b m r)
    (hab : a < b) (h0 : ∀ i : Fin (m + 1), marks H (r i.castSucc) (r i.succ) = 0) :
    sqIn H a b ↔ m = 2 := by
  constructor
  · rintro ⟨F, hF, h4⟩
    rcases he.cover hH hadj hab hF with rfl | ⟨i, hi⟩
    · have := he.card; omega
    · have := marks_pos_of_mem hi (by rw [h4]; decide)
      rw [h0 i] at this
      omega
  · intro hm
    have h2 : a.val + 2 ≤ b.val := by
      have := he.card; have := he.one_le
      by_contra h
      have := card_le_two_of_gap (rootFace_sub (H := H) (a := a) (b := b)) fun z _ ⟨h1, h2⟩ => by
        have : a.val < z.val := h1
        have : z.val < b.val := h2
        omega
      omega
    exact ⟨_, mem_facesIn.mpr ⟨rootFace_isFace hH hadj h2, rootFace_sub⟩, by rw [he.card, hm]⟩

/-- With an odd root face and one child carrying the even faces, a square inside is in that
child. -/
theorem sqIn_iff_child (hH : IsDissection H) (hadj : H.Adj a b) (he : RootEnum H a b m r)
    (hab : a < b) (hodd : ¬ Even (m + 2)) (j : Fin (m + 1))
    (hz : ∀ i, i ≠ j → marks H (r i.castSucc) (r i.succ) = 0) :
    sqIn H a b ↔ sqIn H (r j.castSucc) (r j.succ) := by
  constructor
  · rintro ⟨F, hF, h4⟩
    rcases he.cover hH hadj hab hF with rfl | ⟨i, hi⟩
    · exact absurd (he.card ▸ (h4 ▸ (by decide : Even 4))) hodd
    · by_cases hij : i = j
      · exact ⟨F, hij ▸ hi, h4⟩
      · have := marks_pos_of_mem hi (by rw [h4]; decide)
        rw [hz i hij] at this
        omega
  · rintro ⟨F, hF, h4⟩
    exact ⟨F, he.child_sub j hF, h4⟩

/-- In a good interval with three marks and an even root face, the children of the root face
carry at most two marks. -/
theorem GoodP.root (hH : IsDissection H) (hadj : H.Adj a b) (he : RootEnum H a b m r)
    (hg : GoodP H a b) :
    3 ≤ marks H a b → Even m → ∀ j : Fin (m + 1), marks H (r j.castSucc) (r j.succ) ≤ 2 := by
  intro _ hev j
  have hm1 := he.one_le
  have hevm : Even (m + 2) ↔ Even m := by
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
    · rintro ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
  have h2 : a.val + 2 ≤ b.val := by
    have := he.card
    by_contra h
    have := card_le_two_of_gap (rootFace_sub (H := H) (a := a) (b := b)) fun z _ ⟨h1, h2⟩ => by
      have : a.val < z.val := h1
      have : z.val < b.val := h2
      omega
    omega
  exact hg (rootFace H a b) (mem_facesIn.mpr ⟨rootFace_isFace hH hadj h2, rootFace_sub⟩)
    (by rw [he.card]; exact hevm.mpr hev) _ (he.mem _) _ (he.mem _) (he.lt j) (he.gap j)

/-- **The face rule at the root face of an interval** whose root face, when even and over at
least three marks, has children with at most two marks each. -/
theorem rule_of_enum' (hH : IsDissection H) (hadj : H.Adj a b) (he : RootEnum H a b m r)
    (hab : a < b)
    (hg : 3 ≤ marks H a b → Even m → ∀ j : Fin (m + 1), marks H (r j.castSucc) (r j.succ) ≤ 2) :
    numRule (tagOf H a b) m (fun i => tagOf H (r i.castSucc) (r i.succ)) := by
  classical
  have hM := he.marks_eq hH hadj hab
  set τ : Fin (m + 1) → NTag := fun i => tagOf H (r i.castSucc) (r i.succ) with hτ
  set f : Fin (m + 1) → ℕ := fun i => marks H (r i.castSucc) (r i.succ) with hf
  have hm1 := he.one_le
  have hevm : Even (m + 2) ↔ Even m := by
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
    · rintro ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
  have h2 : a.val + 2 ≤ b.val := by
    have := he.card
    by_contra h
    have := card_le_two_of_gap (rootFace_sub (H := H) (a := a) (b := b)) fun z _ ⟨h1, h2⟩ => by
      have : a.val < z.val := h1
      have : z.val < b.val := h2
      omega
    omega
  by_cases h3 : 3 ≤ marks H a b
  · rw [tagOf_three h3]
    rcases Nat.even_or_odd m with hev | hodd
    · refine numRule_hex_even (by obtain ⟨k, hk⟩ := hev; omega) fun j => ?_
      exact tagOf_mb (hg h3 hev j)
    · exact numRule_hex_odd hodd
  have hsum : univ.sum f ≤ 2 := by
    have : univ.sum f ≤ marks H a b := by rw [hM]; split_ifs <;> omega
    omega
  rcases sum_le_two_cases f hsum with h0 | ⟨j, hj, hz⟩ | ⟨j, hj, hz⟩ |
      ⟨j₁, j₂, h12, hj₁, hj₂, hz⟩
  · -- no marks in the children
    have hs : univ.sum f = 0 := Finset.sum_eq_zero fun i _ => h0 i
    have hτp : ∀ i, τ i = NTag.plain := fun i => tagOf_zero (h0 i)
    by_cases hev : Even (m + 2)
    · have hM1 : marks H a b = 1 := by rw [hM]; simp only [hev, ↓reduceIte]; rw [hs]
      rw [tagOf_one hM1]
      have hτ' : τ = fun _ => NTag.plain := funext hτp
      have hevm' := hevm.mp hev
      by_cases hm2 : m = 2
      · subst hm2
        simp only [(sqIn_iff_root hH hadj he hab h0).mpr rfl, ↓reduceIte]
        rw [hτ']
        exact numRule_bare_square
      · simp only [show ¬ sqIn H a b from fun h => hm2 ((sqIn_iff_root hH hadj he hab h0).mp h),
          ↓reduceIte]
        rw [hτ']
        exact numRule_bare_long hevm' (by obtain ⟨k, hk⟩ := hevm'; omega)
    · have hM0 : marks H a b = 0 := by rw [hM]; simp only [hev, ↓reduceIte]; rw [hs]
      rw [tagOf_zero hM0]
      have hodd : Odd m := Nat.not_even_iff_odd.mp fun h => hev (hevm.mpr h)
      have := numRule_odd_one (τ := τ) hodd 0 (fun i _ => hτp i)
        (fun _ => Or.inr (by rw [hτp 0]; norm_num [NTag.plain]))
      rwa [hτp 0] at this
  · -- one child with one mark
    have hs : univ.sum f = 1 := by
      rw [Finset.sum_eq_single j (fun i _ hi => hz i hi) (fun h => absurd (mem_univ j) h)]
      exact hj
    have hτp : ∀ i, i ≠ j → τ i = NTag.plain := fun i hi => tagOf_zero (hz i hi)
    by_cases hev : Even (m + 2)
    · have hM2 : marks H a b = 2 := by rw [hM]; simp only [hev, ↓reduceIte]; rw [hs]
      rw [tagOf_two hM2]
      have hevm' := hevm.mp hev
      by_cases hm2 : m = 2
      · subst hm2
        by_cases hsq : sqIn H (r j.castSucc) (r j.succ)
        · have htj : τ j = tSq := by
            show tagOf H _ _ = tSq; rw [tagOf_one hj]; simp only [hsq, ↓reduceIte]
          exact numRule_square_hull j hτp (by rw [htj]; rfl) (by rw [htj]; rfl)
        · have htj : τ j = tLong := by
            show tagOf H _ _ = tLong; rw [tagOf_one hj]; simp only [hsq, ↓reduceIte]
          exact numRule_square_long j hτp (by rw [htj]; rfl)
            (by rw [htj]; show (10 / 11 : ℝ) ≤ 10 / 11; exact le_rfl)
      · exact numRule_even_one hevm' (by obtain ⟨k, hk⟩ := hevm'; omega) j hτp
          (tagOf_one_mb hj) (by rw [show τ j = tagOf H _ _ from rfl, tagOf_one_tv hj])
    · have hM1 : marks H a b = 1 := by rw [hM]; simp only [hev, ↓reduceIte]; rw [hs]
      have hodd : Odd m := Nat.not_even_iff_odd.mp fun h => hev (hevm.mpr h)
      have htag : tagOf H a b = τ j := by
        show tagOf H a b = tagOf H (r j.castSucc) (r j.succ)
        rw [tagOf_one hM1, tagOf_one hj]
        simp only [sqIn_iff_child hH hadj he hab hev j hz]
      rw [htag]
      exact numRule_odd_one hodd j hτp fun _ => Or.inr (by
        rw [show τ j = tagOf H _ _ from rfl, tagOf_one_tv hj]; norm_num)
  · -- one child with two marks
    have hs : univ.sum f = 2 := by
      rw [Finset.sum_eq_single j (fun i _ hi => hz i hi) (fun h => absurd (mem_univ j) h)]
      exact hj
    have hτp : ∀ i, i ≠ j → τ i = NTag.plain := fun i hi => tagOf_zero (hz i hi)
    have hev : ¬ Even (m + 2) := fun hev => by
      have : marks H a b = 3 := by rw [hM]; simp only [hev, ↓reduceIte]; rw [hs]
      omega
    have hM2 : marks H a b = 2 := by rw [hM]; simp only [hev, ↓reduceIte]; rw [hs]
    have hodd : Odd m := Nat.not_even_iff_odd.mp fun h => hev (hevm.mpr h)
    have htj : τ j = tTwo := tagOf_two hj
    rw [tagOf_two hM2, ← htj]
    exact numRule_odd_one hodd j hτp fun _ => Or.inr (by rw [htj]; norm_num [tTwo])
  · -- two children with one mark each
    have hs : univ.sum f = 2 := by
      rw [← Finset.add_sum_erase univ f (mem_univ j₁),
        ← Finset.add_sum_erase (univ.erase j₁) f (mem_erase.mpr ⟨ne_of_gt h12, mem_univ j₂⟩)]
      rw [Finset.sum_eq_zero fun i hi => hz i (mem_erase.mp (mem_erase.mp hi).2).1
        (mem_erase.mp hi).1]
      show f j₁ + (f j₂ + 0) = 2
      rw [hj₁, hj₂]
    have hev : ¬ Even (m + 2) := fun hev => by
      have : marks H a b = 3 := by rw [hM]; simp only [hev, ↓reduceIte]; rw [hs]
      omega
    have hM2 : marks H a b = 2 := by rw [hM]; simp only [hev, ↓reduceIte]; rw [hs]
    have hodd : Odd m := Nat.not_even_iff_odd.mp fun h => hev (hevm.mpr h)
    rw [tagOf_two hM2]
    have hv1 : (τ j₁).tv = 3 / 4 := tagOf_one_tv hj₁
    have hv2 : (τ j₂).tv = 3 / 4 := tagOf_one_tv hj₂
    have hb1 : (τ j₁).mb = true := tagOf_one_mb hj₁
    have hb2 : (τ j₂).mb = true := tagOf_one_mb hj₂
    rcases Nat.lt_or_ge m 3 with hlt | h3m
    · obtain rfl : m = 1 := by obtain ⟨k, hk⟩ := hodd; omega
      have e1 : j₁ = 0 := by
        have : j₁.val < j₂.val := h12; have := j₂.isLt; exact Fin.ext (by simp; omega)
      have e2 : j₂ = 1 := by
        have : j₁.val < j₂.val := h12; have := j₂.isLt; exact Fin.ext (by simp; omega)
      subst e1 e2
      refine numRule_tri tTwo (fun _ => ⟨hb1, hb2, by rw [hv1, hv2]; norm_num⟩)
        (by rw [hv1, hv2]; norm_num [tTwo]) ?_ rfl
      exact mul_nonneg (τ 0).fl0 (τ 1).fl0
    · exact numRule_odd_two hodd h3m tTwo j₁ j₂ h12 (fun i h1 h2 => tagOf_zero (hz i h1 h2))
        (fun _ => ⟨hb1, hb2⟩) (by rw [hv1, hv2]; norm_num [tTwo])
        (mul_nonneg (τ j₁).fl0 (τ j₂).fl0) rfl

/-- **The face rule holds at the root face of a good interval.** -/
theorem rule_of_enum (hH : IsDissection H) (hadj : H.Adj a b) (he : RootEnum H a b m r)
    (hab : a < b) (hg : GoodP H a b) :
    numRule (tagOf H a b) m (fun i => tagOf H (r i.castSucc) (r i.succ)) :=
  rule_of_enum' hH hadj he hab (hg.root hH hadj he)

end Rule

/-! ### Building one side of an edge -/

section Extend

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {N : ℕ} {H : SimpleGraph (Fin N)}

/-- The interior vertices of the root face, as the path of an ear. -/
def earVerts {m : ℕ} (ψ : Fin N → V) (r : Fin (m + 2) → Fin N) : Fin m → V :=
  fun j => ψ (r ⟨j.val + 1, by omega⟩)

theorem earPath_eq {a b : Fin N} {m : ℕ} {r : Fin (m + 2) → Fin N} (ψ : Fin N → V)
    (he : RootEnum H a b m r) (j : Fin (m + 2)) :
    earPath (ψ a) (ψ b) (earVerts ψ r) j = ψ (r j) := by
  rcases earPath_cases (ψ a) (ψ b) (earVerts ψ r) j with ⟨h, e⟩ | ⟨h, e⟩ | ⟨j', h, e⟩
  · rw [e, ← he.first]; congr 2; exact (Fin.ext h).symm
  · rw [e, ← he.last]; congr 2; exact Fin.ext (by simp [h])
  · rw [e]; unfold earVerts; congr 2; exact Fin.ext h.symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- **The root face is an ear** on the edge `(a, b)` of a set meeting `[a, b]` in its ends. -/
theorem isEar_root (hH : IsDissection H) (ψ : Fin N → V) (hψ : Function.Bijective ψ)
    (hGH : ∀ i j, G.Adj (ψ i) (ψ j) ↔ H.Adj i j) {a b : Fin N} (hadj : H.Adj a b) (hab : a < b)
    {m : ℕ} {r : Fin (m + 2) → Fin N} (he : RootEnum H a b m r) {T : Finset V} (ha : ψ a ∈ T)
    (hb : ψ b ∈ T) (hT : ∀ i, a < i → i < b → ψ i ∉ T) :
    IsEar G T (ψ a) (ψ b) (earVerts ψ r) := by
  have hm1 := he.one_le
  -- the interior vertices of the root face are strictly inside `(a, b)`
  have hin : ∀ j : Fin m, a < r ⟨j.val + 1, by omega⟩ ∧ r ⟨j.val + 1, by omega⟩ < b := fun j => by
    constructor
    · rw [← he.first]; exact he.mono (show (0 : ℕ) < j.val + 1 by omega)
    · rw [← he.last]; exact he.mono (show j.val + 1 < m + 1 by omega)
  -- adjacency on the root face by index
  have hidx : ∀ k l : Fin (m + 2), k < l → (H.Adj (r k) (r l) ↔ l.val = k.val + 1 ∨
      (k = 0 ∧ l = Fin.last (m + 1))) := by
    intro k l hkl
    rw [rootFace_adj hH hab hadj (he.mem k) (he.mem l) (he.mono hkl)]
    constructor
    · rintro (h | h)
      · left
        by_contra hne
        have hk1 : k.val + 1 < m + 2 := by have := l.isLt; have : k.val < l.val := hkl; omega
        exact h _ (he.mem ⟨k.val + 1, hk1⟩) ⟨he.mono (show k.val < k.val + 1 by omega),
          he.mono (show k.val + 1 < l.val by have : k.val < l.val := hkl; omega)⟩
      · right
        have h1 := (h a (left_mem_rootFace hab.le)).1
        have h2 := (h b (right_mem_rootFace hab.le)).2
        rw [← he.first] at h1; rw [← he.last] at h2
        exact ⟨he.mono.injective (le_antisymm h1 (he.mono.monotone (Fin.zero_le _))),
          he.mono.injective (le_antisymm (he.mono.monotone (Fin.le_last _)) h2)⟩
    · rintro (h | ⟨rfl, rfl⟩)
      · left
        intro z hz ⟨h1, h2⟩
        obtain ⟨i, rfl⟩ := he.surj z hz
        have := he.mono.lt_iff_lt.mp h1
        have := he.mono.lt_iff_lt.mp h2
        have : k.val < i.val := by assumption
        have : i.val < l.val := by assumption
        omega
      · right
        intro z hz
        rw [he.first, he.last]
        exact ⟨(mem_rootFace.mp hz).1, (mem_rootFace.mp hz).2.1⟩
  refine ⟨hm1, ha, hb, (hGH a b).mpr hadj, fun j j' e => ?_, fun j => hT _ (hin j).1 (hin j).2,
    fun j y hy => ?_, fun j j' => ?_⟩
  · have := he.mono.injective (hψ.1 e)
    exact Fin.ext (by have := congrArg Fin.val this; simp at this; omega)
  · obtain ⟨i, rfl⟩ := hψ.2 y
    unfold earVerts
    rw [hGH]
    set k : Fin (m + 2) := ⟨j.val + 1, by omega⟩
    constructor
    · intro hA
      obtain ⟨h1, h2⟩ := nc_inside hH (hin j).1 (hin j).2 hadj hA
      have hiab : i = a ∨ i = b := by
        by_contra h
        push Not at h
        exact hT i (lt_of_le_of_ne h1 (Ne.symm h.1)) (lt_of_le_of_ne h2 h.2) hy
      rcases hiab with rfl | rfl
      · have hA' : H.Adj (r 0) (r k) := by rw [he.first]; exact hA.symm
        rcases (hidx 0 k (show (0 : ℕ) < j.val + 1 by omega)).mp hA' with h | ⟨-, h⟩
        · left; exact ⟨by simp [k] at h; omega, rfl⟩
        · exact absurd (congrArg Fin.val h) (by simp [k]; omega)
      · have hA' : H.Adj (r k) (r (Fin.last (m + 1))) := by rw [he.last]; exact hA
        rcases (hidx k _ (show j.val + 1 < m + 1 by omega)).mp hA' with h | ⟨h, -⟩
        · right; exact ⟨by simp [k] at h; omega, rfl⟩
        · exact absurd (congrArg Fin.val h) (by simp [k])
    · rintro (⟨hj0, hy'⟩ | ⟨hjm, hy'⟩)
      · obtain rfl := hψ.1 hy'
        rw [← he.first]
        exact ((hidx 0 k (show (0 : ℕ) < j.val + 1 by omega)).mpr
          (Or.inl (by simp [k]; omega))).symm
      · obtain rfl := hψ.1 hy'
        rw [← he.last]
        exact (hidx k _ (show j.val + 1 < m + 1 by omega)).mpr (Or.inl (by simp [k]; omega))
  · unfold earVerts
    rw [hGH]
    rcases lt_trichotomy j j' with hlt | rfl | hgt
    · rw [hidx _ _ (show j.val + 1 < j'.val + 1 by have : j.val < j'.val := hlt; omega)]
      constructor
      · rintro (h | ⟨h, -⟩)
        · left; simp at h; omega
        · exact absurd (congrArg Fin.val h) (by simp)
      · rintro (h | h)
        · left; simp; omega
        · have : j.val < j'.val := hlt; omega
    · simp
    · rw [H.adj_comm, hidx _ _ (show j'.val + 1 < j.val + 1 by have : j'.val < j.val := hgt; omega)]
      constructor
      · rintro (h | ⟨h, -⟩)
        · right; simp at h; omega
        · exact absurd (congrArg Fin.val h) (by simp)
      · rintro (h | h)
        · have : j'.val < j.val := hgt; omega
        · left; simp; omega

/-- The intervals of the children cover `[a, b]`. -/
theorem RootEnum.cover_Icc {a b : Fin N} {m : ℕ} {r : Fin (m + 2) → Fin N}
    (he : RootEnum H a b m r) {z : Fin N} (haz : a ≤ z) (hzb : z ≤ b) :
    ∃ i : Fin (m + 1), r i.castSucc ≤ z ∧ z ≤ r i.succ := by
  classical
  set S := univ.filter fun l : Fin (m + 2) => r l ≤ z
  have hSne : S.Nonempty := ⟨0, mem_filter.mpr ⟨mem_univ _, he.first ▸ haz⟩⟩
  have hl := mem_filter.mp (S.max'_mem hSne)
  set l := S.max' hSne
  by_cases hlast : l.val = m + 1
  · refine ⟨⟨m, by omega⟩, ?_, ?_⟩
    · exact (he.mono.monotone (show (m : ℕ) ≤ l.val by omega)).trans hl.2
    · have : (⟨m, by omega⟩ : Fin (m + 1)).succ = Fin.last (m + 1) := Fin.ext (by simp)
      rw [this, he.last]; exact hzb
  · have hlt : l.val < m + 1 := by have := l.isLt; omega
    refine ⟨⟨l.val, hlt⟩, hl.2, ?_⟩
    by_contra h
    push Not at h
    have hmem : (⟨l.val, hlt⟩ : Fin (m + 1)).succ ∈ S := mem_filter.mpr ⟨mem_univ _, h.le⟩
    have := S.le_max' _ hmem
    have h' : ((⟨l.val, hlt⟩ : Fin (m + 1)).succ).val ≤ l.val := this
    simp at h'

/-- **Building the side `[a, b]` of an edge**, by induction on the width. -/
theorem extend {R : ClassSys} {rule : R.Tag → (m : ℕ) → (Fin (m + 1) → R.Tag) → Prop}
    (hH : IsDissection H) (ψ : Fin N → V) (hψ : Function.Bijective ψ)
    (hGH : ∀ i j, G.Adj (ψ i) (ψ j) ↔ H.Adj i j) (tag : Fin N → Fin N → R.Tag)
    (Good : Fin N → Fin N → Prop)
    (hrule : ∀ (a b : Fin N) (m : ℕ) (r : Fin (m + 2) → Fin N), H.Adj a b → a < b →
      RootEnum H a b m r → Good a b → rule (tag a b) m fun i => tag (r i.castSucc) (r i.succ))
    (hmono : ∀ (a b : Fin N) (m : ℕ) (r : Fin (m + 2) → Fin N), RootEnum H a b m r → Good a b →
      ∀ i : Fin (m + 1), Good (r i.castSucc) (r i.succ)) :
    ∀ (d : ℕ) (a b : Fin N), b.val - a.val ≤ d → a < b → H.Adj a b → Good a b →
    ∀ (T : Finset V) (tg : V → V → R.Tag), TagBuilt G R rule (fun _ _ => True) T tg →
      ψ a ∈ T → ψ b ∈ T → (∀ i, a < i → i < b → ψ i ∉ T) → tg (ψ a) (ψ b) = tag a b →
      ∃ tg', TagBuilt G R rule (fun _ _ => True) (T ∪ (Icc a b).image ψ) tg' ∧
        ∀ p ∈ T, ∀ q ∈ T, ¬ (p = ψ a ∧ q = ψ b) → tg' p q = tg p q := by
  intro d
  induction d with
  | zero =>
    intro a b hd hab
    exact absurd hd (by have : a.val < b.val := hab; omega)
  | succ d ih =>
  intro a b hd hab hadj hg T tg hT ha hb hint hdem
  by_cases hedge : b.val ≤ a.val + 1
  · -- a single edge: nothing to build
    have hsub : (Icc a b).image ψ ⊆ T := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hy
      obtain ⟨h1, h2⟩ := mem_Icc.mp hi
      rcases h1.lt_or_eq with h1 | rfl
      · rcases h2.lt_or_eq with h2 | rfl
        · exact absurd hedge (by
            have : a.val < i.val := h1; have : i.val < b.val := h2; omega)
        · exact hb
      · exact ha
    exact ⟨tg, by rw [union_eq_left.mpr hsub]; exact hT, fun _ _ _ _ _ => rfl⟩
  have h2 : a.val + 2 ≤ b.val := by omega
  obtain ⟨m, r, he⟩ := exists_rootEnum hH hadj h2
  have hm1 := he.one_le
  set x := earVerts ψ r with hx
  have hear : IsEar G T (ψ a) (ψ b) x := isEar_root hH ψ hψ hGH hadj hab he ha hb hint
  have hpath : ∀ j, earPath (ψ a) (ψ b) x j = ψ (r j) := fun j => by
    rw [hx]; exact earPath_eq ψ he j
  set τ : Fin (m + 1) → R.Tag := fun i => tag (r i.castSucc) (r i.succ) with hτ
  have hrule : rule (tg (ψ a) (ψ b)) m τ := by
    rw [hdem]; exact hrule a b m r hadj hab he hg
  set T₁ := T ∪ univ.image x with hT₁
  set tg₁ := earTags R T tg (ψ a) (ψ b) x τ with htg₁
  have hT1 : TagBuilt G R rule (fun _ _ => True) T₁ tg₁ :=
    TagBuilt.face (R := R) (rule := rule) (glue := fun _ _ => True) T tg m (ψ a) (ψ b) x
      hear τ hrule hT
  -- the vertices of the root face are in `T₁`
  have hRT : ∀ j : Fin (m + 2), ψ (r j) ∈ T₁ := by
    intro j
    rw [← hpath j]
    rcases earPath_cases (ψ a) (ψ b) x j with ⟨-, e⟩ | ⟨-, e⟩ | ⟨j', -, e⟩
    · rw [e]; exact mem_union_left _ ha
    · rw [e]; exact mem_union_left _ hb
    · rw [e]; exact mem_union_right _ (mem_image_of_mem _ (mem_univ _))
  -- the children, one by one
  have hloop : ∀ k, k ≤ m + 1 → ∃ tgk, TagBuilt G R rule (fun _ _ => True)
      (T₁ ∪ (univ.filter fun i : Fin (m + 1) => i.val < k).biUnion
        fun i => (Icc (r i.castSucc) (r i.succ)).image ψ) tgk ∧
      ∀ p ∈ T₁, ∀ q ∈ T₁, (∀ i : Fin (m + 1), i.val < k →
        ¬ (p = ψ (r i.castSucc) ∧ q = ψ (r i.succ))) → tgk p q = tg₁ p q := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨tg₁, ?_, fun _ _ _ _ _ => rfl⟩
      have : (univ.filter fun i : Fin (m + 1) => i.val < 0) = ∅ := by
        ext i; simp
      rw [this, biUnion_empty, union_empty]
      exact hT1
    | succ k ihk =>
      intro hk
      obtain ⟨tgk, hTk, hpres⟩ := ihk (by omega)
      set i : Fin (m + 1) := ⟨k, by omega⟩ with hi
      set Tk := T₁ ∪ (univ.filter fun i : Fin (m + 1) => i.val < k).biUnion
        fun i => (Icc (r i.castSucc) (r i.succ)).image ψ with hTkdef
      have hw := he.width i
      have hlti := he.lt i
      -- the conditions for the child
      have hc1 : ψ (r i.castSucc) ∈ Tk := mem_union_left _ (hRT _)
      have hc2 : ψ (r i.succ) ∈ Tk := mem_union_left _ (hRT _)
      have hc3 : ∀ z, r i.castSucc < z → z < r i.succ → ψ z ∉ Tk := by
        intro z hz1 hz2 hzT
        have hza : a < z := lt_of_le_of_lt (he.ge _) hz1
        have hzb : z < b := lt_of_lt_of_le hz2 (he.le _)
        rcases mem_union.mp hzT with h | h
        · rcases mem_union.mp h with h | h
          · exact hint z hza hzb h
          · obtain ⟨j, -, hj⟩ := mem_image.mp h
            have hzr := hψ.1 hj
            exact he.gap i _ (he.mem _) ⟨hzr ▸ hz1, hzr ▸ hz2⟩
        · obtain ⟨l, hl, hlz⟩ := mem_biUnion.mp h
          have hlk := (mem_filter.mp hl).2
          obtain ⟨z', hz', hz'z⟩ := mem_image.mp hlz
          obtain rfl := hψ.1 hz'z
          have hle : r l.succ ≤ r i.castSucc := he.mono.monotone (by
            show l.val + 1 ≤ k; omega)
          exact absurd ((mem_Icc.mp hz').2.trans hle) (not_le.mpr hz1)
      have hc4 : tgk (ψ (r i.castSucc)) (ψ (r i.succ)) = tag (r i.castSucc) (r i.succ) := by
        rw [hpres _ (hRT _) _ (hRT _) fun l hl he' => by
          have := he.mono.injective (hψ.1 he'.1)
          have := congrArg Fin.val this
          simp [hi] at this
          omega]
        rw [htg₁, ← hpath i.castSucc, ← hpath i.succ, earTags_fwd (R := R) (tg := tg) (τ := τ) hear i]
      obtain ⟨tg', hT', hpres'⟩ := ih (r i.castSucc) (r i.succ) (by omega) hlti
        (he.adj hH hadj hab i) (hmono a b m r he hg i) Tk tgk hTk hc1 hc2 hc3 hc4
      refine ⟨tg', ?_, fun p hp q hq hnot => ?_⟩
      · have hset : Tk ∪ (Icc (r i.castSucc) (r i.succ)).image ψ = T₁ ∪
            (univ.filter fun i : Fin (m + 1) => i.val < k + 1).biUnion
              fun i => (Icc (r i.castSucc) (r i.succ)).image ψ := by
          ext y
          simp only [hTkdef, mem_union, mem_biUnion, mem_filter, mem_univ, true_and]
          constructor
          · rintro ((h | ⟨l, hl, h⟩) | h)
            · exact Or.inl h
            · exact Or.inr ⟨l, by omega, h⟩
            · exact Or.inr ⟨i, by simp [hi], h⟩
          · rintro (h | ⟨l, hl, h⟩)
            · exact Or.inl (Or.inl h)
            · by_cases hlk : l.val < k
              · exact Or.inl (Or.inr ⟨l, hlk, h⟩)
              · have : l = i := Fin.ext (by simp [hi]; omega)
                exact Or.inr (this ▸ h)
        rw [← hset]; exact hT'
      · rw [hpres' p (mem_union_left _ hp) q (mem_union_left _ hq) (hnot i (by simp [hi])),
          hpres p hp q hq fun l hl => hnot l (by omega)]
  obtain ⟨tgf, hTf, hpresf⟩ := hloop (m + 1) le_rfl
  refine ⟨tgf, ?_, fun p hp q hq hnot => ?_⟩
  · have hset : T₁ ∪ (univ.filter fun i : Fin (m + 1) => i.val < m + 1).biUnion
        (fun i => (Icc (r i.castSucc) (r i.succ)).image ψ) = T ∪ (Icc a b).image ψ := by
      ext y
      simp only [hT₁, mem_union, mem_biUnion, mem_filter, mem_univ, true_and, mem_image]
      constructor
      · rintro ((h | ⟨j, -, rfl⟩) | ⟨i, -, z, hz, rfl⟩)
        · exact Or.inl h
        · right
          refine ⟨r ⟨j.val + 1, by omega⟩, mem_Icc.mpr ⟨he.ge _, he.le _⟩, rfl⟩
        · right
          obtain ⟨h1, h2⟩ := mem_Icc.mp hz
          exact ⟨z, mem_Icc.mpr ⟨(he.ge _).trans h1, h2.trans (he.le _)⟩, rfl⟩
      · rintro (h | ⟨z, hz, rfl⟩)
        · exact Or.inl (Or.inl h)
        · obtain ⟨h1, h2⟩ := mem_Icc.mp hz
          obtain ⟨i, hi1, hi2⟩ := he.cover_Icc h1 h2
          exact Or.inr ⟨i, i.isLt, z, mem_Icc.mpr ⟨hi1, hi2⟩, rfl⟩
    rw [← hset]; exact hTf
  · have hp1 : p ∈ T₁ := mem_union_left _ hp
    have hq1 : q ∈ T₁ := mem_union_left _ hq
    rw [hpresf p hp1 q hq1 fun i _ ⟨e1, e2⟩ => ?_, htg₁, earTags_old (R := R) (tg := tg) (τ := τ) hear hp hq hnot]
    -- a child's ends are not both in `T`
    have hw := he.width i
    have k1 : r i.castSucc = a := by
      by_contra h
      have hlt : a < r i.castSucc := lt_of_le_of_ne (he.ge _) (Ne.symm h)
      exact hint _ hlt ((he.lt i).trans_le (he.le _)) (e1 ▸ hp)
    have k2 : r i.succ = b := by
      by_contra h
      have hlt : r i.succ < b := lt_of_le_of_ne (he.le _) h
      exact hint _ ((he.ge _).trans_lt (he.lt i)) hlt (e2 ▸ hq)
    rw [k1, k2] at hw
    omega

end Extend

/-! ### The two sides of a chord -/

open Classical in
/-- The number of even faces of a polygon dissection. -/
noncomputable def numEvenFaces (G : SimpleGraph (Fin n)) : ℕ :=
  (univ.filter fun F : Finset (Fin n) => IsFace G F ∧ Even F.card).card

section Sides

variable [NeZero n] {G : SimpleGraph (Fin n)}

theorem rot_bijective (r : Fin n) : Function.Bijective (rot r) :=
  ⟨rot_injective r, fun x => ⟨x - r, by simp [rot]⟩⟩

omit [NeZero n] in
/-- The other side of the chord `(a, b)`, read from `b`. -/
theorem sub_le_iff {a b x : Fin n} (hab : a < b) : x - b ≤ a - b ↔ ¬ (a < x ∧ x < b) := by
  have hab' : a.val < b.val := hab
  have hx := x.isLt
  show (x - b).val ≤ (a - b).val ↔ ¬ (a.val < x.val ∧ x.val < b.val)
  rw [sub_val_lt hab]
  by_cases hbx : b ≤ x
  · rw [sub_val_le hbx]
    have : b.val ≤ x.val := hbx
    omega
  · rw [sub_val_lt (not_le.mp hbx)]
    have : x.val < b.val := not_le.mp hbx
    omega

open Classical in
/-- **The even faces of `G` are those inside the chord `(a, b)` and those on its other side.** -/
theorem marks_add_rot (hG : IsDissection G) {a b : Fin n} (hab : a < b) (hadj : G.Adj a b) :
    marks G a b + marks (G.comap (rot b)) 0 (a - b) = numEvenFaces G := by
  unfold numEvenFaces
  set E := univ.filter fun F : Finset (Fin n) => IsFace G F ∧ Even F.card with hE
  have hA : marks G a b = (E.filter fun F => F ⊆ Icc a b).card := by
    unfold marks facesIn
    congr 1
    ext F
    simp only [hE, mem_filter, mem_univ, true_and]
    tauto
  -- a face not inside the chord has no vertex strictly inside it
  have hout : ∀ F, IsFace G F → (¬ F ⊆ Icc a b ↔ ∀ x ∈ F, ¬ (a < x ∧ x < b)) := by
    intro F hF
    constructor
    · intro h x hx ⟨h1, h2⟩
      exact h fun y hy => mem_Icc.mpr (face_sep hG hF hab hadj hx h1 h2 y hy)
    · intro h hsub
      have := card_le_two_of_gap hsub h
      have := hF.1
      omega
  have hB : marks (G.comap (rot b)) 0 (a - b) = (E.filter fun F => ¬ F ⊆ Icc a b).card := by
    unfold marks
    rw [← card_image_of_injective _ (image_injective (rot_injective b))]
    congr 1
    ext F'
    simp only [mem_image, mem_filter, hE, mem_univ, true_and]
    constructor
    · rintro ⟨F, ⟨hF, hev⟩, rfl⟩
      obtain ⟨hF, hsub⟩ := mem_facesIn.mp hF
      have hF' := (isFace_rot G b F).mp hF
      refine ⟨⟨hF', by rwa [card_image_of_injective _ (rot_injective b)]⟩, ?_⟩
      rw [hout _ hF']
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      have hyc : y ≤ a - b := (mem_Icc.mp (hsub hy)).2
      rw [← sub_le_iff hab]
      simpa [rot] using hyc
    · rintro ⟨⟨hF', hev⟩, hnot⟩
      rw [hout _ hF'] at hnot
      refine ⟨F'.image (rot (-b)), ⟨mem_facesIn.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
      · rw [isFace_rot, image_image]
        convert hF'
        ext y; simp [rot]
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
        refine mem_Icc.mpr ⟨Fin.zero_le _, ?_⟩
        have := (sub_le_iff hab).mpr (hnot y hy)
        simpa [rot, sub_eq_add_neg] using this
      · rwa [card_image_of_injective _ (rot_injective _)]
      · rw [image_image]
        ext y; simp [rot]
  rw [hA, hB, Finset.card_filter_add_card_filter_not]

end Sides

/-! ### Building the whole graph from a base edge -/

/-- **The whole graph from a base edge** `(a, b)` (a chord or an edge of the polygon), for any
family of tags and of good intervals with sound face rules, if both sides of the base edge are
good: the inside `[a, b]`, and the outside, read in coordinates rotated by `b`. -/
theorem exists_build {n : ℕ} [NeZero n] {R : ClassSys}
    {rule : R.Tag → (m : ℕ) → (Fin (m + 1) → R.Tag) → Prop} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : IsDissection G) (tag : SimpleGraph (Fin n) → Fin n → Fin n → R.Tag)
    (Good : SimpleGraph (Fin n) → Fin n → Fin n → Prop)
    (hrule : ∀ H : SimpleGraph (Fin n), IsDissection H → ∀ (a b : Fin n) (m : ℕ)
      (r : Fin (m + 2) → Fin n), H.Adj a b → a < b → RootEnum H a b m r → Good H a b →
        rule (tag H a b) m fun i => tag H (r i.castSucc) (r i.succ))
    (hmono : ∀ (H : SimpleGraph (Fin n)) (a b : Fin n) (m : ℕ) (r : Fin (m + 2) → Fin n),
      RootEnum H a b m r → Good H a b → ∀ i : Fin (m + 1), Good H (r i.castSucc) (r i.succ))
    (a b : Fin n) (hab : a < b) (hadj : G.Adj a b) (hg₁ : Good G a b)
    (hg₂ : Good (G.comap (rot b)) 0 (a - b)) :
    ∃ tg, TagBuilt G R rule (fun _ _ => True) univ tg := by
  have hext := extend (G := G) (H := G) hG id Function.bijective_id (fun _ _ => Iff.rfl) (tag G)
    (Good G) (hrule G hG) (hmono G)
  have hne : a ≠ b := ne_of_lt hab
  set c : Fin n := a - b with hc
  set H₂ := G.comap (rot b) with hH₂
  have hT0 := TagBuilt.edge (G := G) (R := R) (rule := rule) (glue := fun _ _ => True)
    a b hadj (tag G a b) (tag H₂ 0 c) trivial
  -- the inside of the base edge
  obtain ⟨tg₁, hT₁, hpres₁⟩ := hext (b.val - a.val) a b le_rfl hab hadj hg₁ {a, b} _ hT0
    (by simp) (by simp) (fun i h1 h2 hi => by
      simp only [id, mem_insert, mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact lt_irrefl _ h1
      · exact lt_irrefl _ h2)
    (by simp [edgeTags])
  -- the outside, in coordinates rotated by `b`
  have hH₂d := isDissection_rot hG b
  have hext₂ := extend (G := G) (H := H₂) hH₂d (rot b) (rot_bijective b)
    (fun _ _ => Iff.rfl) (tag H₂) (Good H₂) (hrule H₂ hH₂d) (hmono H₂)
  have hr0 : rot b (0 : Fin n) = b := by simp [rot]
  have hrc : rot b c = a := by simp [rot, hc]
  have hcpos : (0 : Fin n) < c := by
    rw [Fin.pos_iff_ne_zero, hc]
    exact sub_ne_zero.mpr hne
  have hadj₂ : H₂.Adj 0 c := by
    show G.Adj (rot b 0) (rot b c)
    rw [hr0, hrc]; exact hadj.symm
  set T₁ := ({a, b} : Finset (Fin n)) ∪ (Icc a b).image id with hT₁def
  obtain ⟨tg₂, hT₂, -⟩ := hext₂ c.val 0 c (by simp) hcpos hadj₂ hg₂ T₁ tg₁
    hT₁ (by rw [hr0]; simp [hT₁def]) (by rw [hrc]; simp [hT₁def])
    (fun i h1 h2 hi => by
      have hi' : rot b i ∈ Icc a b := by
        simp only [hT₁def, mem_union, mem_insert, mem_singleton, mem_image, id] at hi
        rcases hi with (h | h) | ⟨y, hy, rfl⟩
        · rw [h]; exact mem_Icc.mpr ⟨le_rfl, hab.le⟩
        · rw [h]; exact mem_Icc.mpr ⟨hab.le, le_rfl⟩
        · exact hy
      obtain ⟨h3, h4⟩ := mem_Icc.mp hi'
      have hle : rot b i - b ≤ a - b := by simpa [rot] using h2.le
      rw [sub_le_iff hab] at hle
      rcases h3.lt_or_eq with h3 | h3
      · rcases h4.lt_or_eq with h4 | h4
        · exact hle ⟨h3, h4⟩
        · have : i = 0 := by
            have := congrArg (· - b) h4
            simpa [rot] using this
          exact lt_irrefl _ (this ▸ h1)
      · have : i = c := by
          have := congrArg (· - b) h3
          simpa [rot, hc] using this.symm
        exact lt_irrefl _ (this ▸ h2))
    (by
      rw [hr0, hrc, hpres₁ b (by simp) a (by simp) fun h => hne h.2]
      simp [edgeTags, hne, Ne.symm hne])
  refine ⟨tg₂, ?_⟩
  have hset : T₁ ∪ (Icc 0 c).image (rot b) = univ := by
    ext x
    simp only [mem_univ, iff_true, hT₁def, mem_union, mem_image, mem_Icc, id]
    by_cases hx : a ≤ x ∧ x ≤ b
    · exact Or.inl (Or.inr ⟨x, hx, rfl⟩)
    · right
      refine ⟨x - b, ⟨Fin.zero_le _, ?_⟩, by simp [rot]⟩
      rw [hc, sub_le_iff hab]
      rintro ⟨h1, h2⟩
      exact hx ⟨h1.le, h2.le⟩
  rw [← hset]
  exact hT₂

/-- The outer edge `(0, n - 1)`, and the outside of it in rotated coordinates: a single edge. -/
theorem outer_edge {n : ℕ} [NeZero n] (hn : 2 ≤ n) {G : SimpleGraph (Fin n)}
    (hG : IsDissection G) :
    ∃ l : Fin n, (0 : Fin n) < l ∧ G.Adj 0 l ∧ (∀ x : Fin n, x ≤ l) ∧ ((0 : Fin n) - l).val = 1 := by
  refine ⟨⟨n - 1, by omega⟩, by show 0 < n - 1; omega,
    hG.2.1 0 _ rfl (by show n - 1 + 1 = n; omega) (ne_of_lt (by show 0 < n - 1; omega)),
    fun x => by show x.val ≤ n - 1; have := x.isLt; omega, ?_⟩
  rw [sub_val_lt (show (0 : Fin n) < ⟨n - 1, by omega⟩ by show 0 < n - 1; omega)]
  simp only [Fin.val_zero]
  omega

/-! ### The theorem -/

open Classical in
/-- **A polygon dissection with at most six even faces is 3-ECC**: every assignment of lists of
three colours has at least as many proper colourings as there are `3`-colourings. -/
theorem ecc_three_of_six_even {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : IsDissection G) (hn : 3 ≤ n)
    (h6 : (univ.filter fun F : Finset (Fin n) => IsFace G F ∧ Even F.card).card ≤ 6) :
    G.ECCAt 3 := by
  have h6' : numEvenFaces G ≤ 6 := h6
  have : NeZero n := ⟨by omega⟩
  suffices h : ∃ tg, TagBuilt G numSys numRule (fun _ _ => True) univ tg by
    obtain ⟨tg, h⟩ := h
    exact ecc_three_of_numBuilt G h
  have hbuild := exists_build (R := numSys) (rule := numRule) G hG (fun H => tagOf H)
    (fun H => GoodP H)
    (fun H hH _ _ _ _ hadj hab he hg => rule_of_enum hH hadj he hab hg)
    (fun _ _ _ _ _ he hg _ => hg.mono (he.ge _) (he.le _))
  -- good from a narrowest heavy chord
  have hgood_of : ∀ a b : Fin n, a < b → (∀ a' b' : Fin n, a' < b' → G.Adj a' b' →
      b'.val - a'.val < b.val - a.val → marks G a' b' ≤ 2) → GoodP G a b := by
    intro a b hab hmin F hF hev f hf f' hf' hff hgap
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
  by_cases hheavy : ∃ a b : Fin n, a < b ∧ G.Adj a b ∧ 3 ≤ marks G a b
  · -- a narrowest chord with at least three even faces inside
    have hex : ∃ d, ∃ a b : Fin n, a < b ∧ G.Adj a b ∧ 3 ≤ marks G a b ∧ b.val - a.val = d := by
      obtain ⟨a, b, h1, h2, h3⟩ := hheavy
      exact ⟨_, a, b, h1, h2, h3, rfl⟩
    obtain ⟨a, b, hab, hadj, h3, hd⟩ := Nat.find_spec hex
    have hmin : ∀ a' b' : Fin n, a' < b' → G.Adj a' b' → b'.val - a'.val < b.val - a.val →
        marks G a' b' ≤ 2 := by
      intro a' b' h1 h2 hw
      by_contra h
      exact Nat.find_min hex (hd ▸ hw) ⟨a', b', h1, h2, by omega, rfl⟩
    have hm₂ : marks (G.comap (rot b)) 0 (a - b) ≤ 3 := by
      have := marks_add_rot hG hab hadj
      omega
    exact hbuild a b hab hadj (hgood_of a b hab hmin) (goodP_of_marks_le hm₂)
  · -- no heavy chord: build everything from the outer edge `(0, n - 1)`
    push Not at hheavy
    obtain ⟨l, h0l, hadj, -, hl1⟩ := outer_edge (by omega) hG
    have hgood := hgood_of 0 l h0l fun a' b' h1 h2 _ => by
      have := hheavy a' b' h1 h2; omega
    refine hbuild 0 l h0l hadj hgood (goodP_of_marks_le ?_)
    rw [marks_edge (by rw [hl1]; simp)]
    omega

end Outerplanar
