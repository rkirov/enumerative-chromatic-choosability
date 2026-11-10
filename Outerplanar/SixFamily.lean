/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Analytic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi

/-!
# Six colourings matched on an edge

The combinatorial core of the bound for 2-trees with three colours (a result of this
repository's 2026-11 AI research collaboration; paper proof in the section "Fourth pass" of
`ai_research_notes/OUTERPLANAR_K3_TRIANGLES_2026-11-10.md`).

Six colourings, seen on an edge `uw` as two maps `p q : Fin 6 → ℕ`, are *matched*
(`Matched (L u) (L w) p q`) when the two lists can be enumerated as `α, β : Fin 3 → ℕ` so that
every pair `(α a, β b)` with `a ≠ b` is the pair of one of the six colourings. The six pairs are
then exactly the pairs off a bijection `α a ↦ β a` between the lists; in particular they are
distinct, and every colour of either list is used by exactly two of the six colourings
(`Matched.injective`, `Matched.prod_left`).

* `exists_matched` — two lists of three colours carry six matched pairs of distinct colours;
* `Matched.extend` — given six matched pairs of distinct colours on `uw` and a third list
  `L v`, the six colourings extend to `v`, with a colour different from both ends, so that they
  are matched on `vu` and on `vw`.

The extension enumerates `L v` twice, as `γ` aligned with `α` (a common colour has the same
index) and as `δ` aligned with `β`, so that `γ` and `δ` agree at some index
(`exists_aligned_pair`): the permutation `r` with `γ ∘ r = δ` then has a fixed point, which is
what makes the choice of the six new colours (`newIdx`) possible. What remains are checks on
three indices, done by `decide`.
-/

namespace Outerplanar

open Finset

/-! ### Finite checks on three indices -/

/-- The six ordered pairs of distinct indices. -/
def offPair : Fin 6 → Fin 3 × Fin 3 := ![(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)]

theorem offPair_ne : ∀ j, (offPair j).1 ≠ (offPair j).2 := by decide

theorem offPair_injective : ∀ j j', offPair j = offPair j' → j = j' := by decide

theorem offPair_surj : ∀ a b : Fin 3, a ≠ b → ∃ j, offPair j = (a, b) := by decide

/-- The colour index given to the new vertex. -/
def newIdx (r : Fin 3 → Fin 3) (k a b : Fin 3) : Fin 3 := if a = r b then k else -(a + r b)

theorem newIdx_spec : ∀ r : Fin 3 → Fin 3, (∀ x y, r x = r y → x = y) → ∀ k, r k = k →
    (∀ a b, a ≠ b → newIdx r k a b ≠ a ∧ newIdx r k a b ≠ r b) ∧
    (∀ c a, c ≠ a → ∃ b, b ≠ a ∧ newIdx r k a b = c) ∧
    (∀ b b', b ≠ b' → ∃ a, a ≠ b' ∧ newIdx r k a b' = r b) := by
  decide

set_option synthInstance.maxHeartbeats 200000 in
set_option synthInstance.maxSize 2000 in
theorem align_pick : ∀ A B : Fin 3 → Option (Fin 3),
    (∀ j j' a, A j = some a → A j' = some a → j = j') →
    (∀ j j' a, B j = some a → B j' = some a → j = j') →
    (∀ j a b, A j = some a → B j = some b → a = b) →
    ∃ j k, (∀ a, A j = some a → a = k) ∧ (∀ j', A j' = some k → j' = j) ∧
      (∀ a, B j = some a → a = k) ∧ (∀ j', B j' = some k → j' = j) := by
  decide +kernel

theorem align_ext : ∀ A : Fin 3 → Option (Fin 3),
    (∀ j j' a, A j = some a → A j' = some a → j = j') →
    ∀ j k, (∀ a, A j = some a → a = k) → (∀ j', A j' = some k → j' = j) →
    ∃ g : Fin 3 → Fin 3, (∀ x y, g x = g y → x = y) ∧ g k = j ∧
      (∀ c a, A (g c) = some a → a = c) := by
  decide

/-! ### Enumerations of a list of three colours -/

theorem exists_enum {L : Finset ℕ} (h : L.card = 3) :
    ∃ ζ : Fin 3 → ℕ, Function.Injective ζ ∧ ∀ j, ζ j ∈ L :=
  ⟨L.orderEmbOfFin h, (L.orderEmbOfFin h).injective, fun j => L.orderEmbOfFin_mem h j⟩

theorem image_enum {L : Finset ℕ} (h : L.card = 3) {γ : Fin 3 → ℕ} (hγ : Function.Injective γ)
    (hm : ∀ j, γ j ∈ L) : univ.image γ = L :=
  Finset.eq_of_subset_of_card_le
    (fun c hc => by obtain ⟨j, -, rfl⟩ := mem_image.mp hc; exact hm j)
    (by rw [card_image_of_injective _ hγ, h]; simp)

/-- The index, in the enumeration `α`, of each colour `ζ j`. -/
theorem exists_pos (α ζ : Fin 3 → ℕ) (hα : Function.Injective α) :
    ∃ A : Fin 3 → Option (Fin 3), ∀ j a, A j = some a ↔ ζ j = α a := by
  classical
  refine ⟨fun j => if h : ∃ a, ζ j = α a then some h.choose else none, fun j a => ?_⟩
  by_cases h : ∃ a, ζ j = α a
  · simp only [dite_eq_left h, Option.some.injEq]
    constructor
    · rintro rfl
      exact h.choose_spec
    · intro h'
      exact hα (h.choose_spec.symm.trans h')
  · simp only [dite_eq_right h]
    constructor
    · intro h'
      cases h'
    · intro h'
      exact absurd ⟨a, h'⟩ h

/-- Two enumerations of a third list, aligned with compatible enumerations `α` and `β` of two
lists, that agree at some index. -/
theorem exists_aligned_pair {Lv : Finset ℕ} (hv : Lv.card = 3) {α β : Fin 3 → ℕ}
    (hα : Function.Injective α) (hβ : Function.Injective β) (hαβ : ∀ a b, α a = β b → a = b) :
    ∃ γ δ : Fin 3 → ℕ, Function.Injective γ ∧ Function.Injective δ ∧ (∀ c, γ c ∈ Lv) ∧
      (∀ c, δ c ∈ Lv) ∧ (∀ c a, γ c = α a → a = c) ∧ (∀ c b, δ c = β b → b = c) ∧
      ∃ k, γ k = δ k := by
  obtain ⟨ζ, hζ, hζm⟩ := exists_enum hv
  obtain ⟨A, hA⟩ := exists_pos α ζ hα
  obtain ⟨B, hB⟩ := exists_pos β ζ hβ
  have hAinj : ∀ j j' a, A j = some a → A j' = some a → j = j' := fun j j' a h h' =>
    hζ (((hA j a).mp h).trans ((hA j' a).mp h').symm)
  have hBinj : ∀ j j' a, B j = some a → B j' = some a → j = j' := fun j j' a h h' =>
    hζ (((hB j a).mp h).trans ((hB j' a).mp h').symm)
  obtain ⟨j, k, h1, h2, h3, h4⟩ := align_pick A B hAinj hBinj fun j a b h h' =>
    hαβ a b (((hA j a).mp h).symm.trans ((hB j b).mp h'))
  obtain ⟨g, hg, hgk, hgA⟩ := align_ext A hAinj j k h1 h2
  obtain ⟨h, hh, hhk, hhB⟩ := align_ext B hBinj j k h3 h4
  exact ⟨fun c => ζ (g c), fun c => ζ (h c), fun x y e => hg x y (hζ e),
    fun x y e => hh x y (hζ e), fun c => hζm _, fun c => hζm _,
    fun c a e => hgA c a ((hA _ a).mpr e), fun c b e => hhB c b ((hB _ b).mpr e),
    k, by show ζ (g k) = ζ (h k); rw [hgk, hhk]⟩

/-! ### Matched families -/

/-- The six pairs `(p i, q i)` are the pairs `(α a, β b)`, `a ≠ b`, for enumerations `α` and
`β` of (three colours of) the two lists. -/
def Matched (Lu Lw : Finset ℕ) (p q : Fin 6 → ℕ) : Prop :=
  ∃ α β : Fin 3 → ℕ, Function.Injective α ∧ Function.Injective β ∧ (∀ a, α a ∈ Lu) ∧
    (∀ b, β b ∈ Lw) ∧ ∀ a b, a ≠ b → ∃ i, p i = α a ∧ q i = β b

theorem Matched.symm {Lu Lw : Finset ℕ} {p q : Fin 6 → ℕ} (h : Matched Lu Lw p q) :
    Matched Lw Lu q p := by
  obtain ⟨α, β, hα, hβ, hαm, hβm, hab⟩ := h
  refine ⟨β, α, hβ, hα, hβm, hαm, fun b a hba => ?_⟩
  obtain ⟨i, h1, h2⟩ := hab a b (Ne.symm hba)
  exact ⟨i, h2, h1⟩

/-- The six colourings, renumbered along `offPair`. -/
theorem matched_reindex {α β : Fin 3 → ℕ} {p q : Fin 6 → ℕ} (hα : Function.Injective α)
    (hβ : Function.Injective β) (hab : ∀ a b, a ≠ b → ∃ i, p i = α a ∧ q i = β b) :
    ∃ κ : Fin 6 → Fin 6, Function.Bijective κ ∧
      ∀ j, p (κ j) = α (offPair j).1 ∧ q (κ j) = β (offPair j).2 := by
  choose κ hκ using fun j => hab _ _ (offPair_ne j)
  have hinj : Function.Injective κ := by
    intro j j' hjj
    apply offPair_injective
    have h1 := (hκ j).1
    have h2 := (hκ j).2
    rw [hjj] at h1 h2
    exact Prod.ext (hα (h1.symm.trans (hκ j').1)) (hβ (h2.symm.trans (hκ j').2))
  exact ⟨κ, ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩, hκ⟩

/-- The six pairs are distinct. -/
theorem Matched.injective {Lu Lw : Finset ℕ} {p q : Fin 6 → ℕ} (h : Matched Lu Lw p q)
    {i i' : Fin 6} (hp : p i = p i') (hq : q i = q i') : i = i' := by
  obtain ⟨α, β, hα, hβ, -, -, hab⟩ := h
  obtain ⟨κ, hκb, hκ⟩ := matched_reindex hα hβ hab
  obtain ⟨j, rfl⟩ := hκb.2 i
  obtain ⟨j', rfl⟩ := hκb.2 i'
  rw [(hκ j).1, (hκ j').1] at hp
  rw [(hκ j).2, (hκ j').2] at hq
  rw [offPair_injective j j' (Prod.ext (hα hp) (hβ hq))]

/-- Every colour of the first list is used by exactly two of the six colourings. -/
theorem Matched.prod_left {Lu Lw : Finset ℕ} {p q : Fin 6 → ℕ} (hu : Lu.card = 3)
    (h : Matched Lu Lw p q) (F : ℕ → ℝ) : ∏ i, F (p i) = (∏ c ∈ Lu, F c) ^ 2 := by
  obtain ⟨α, β, hα, hβ, hαm, -, hab⟩ := h
  obtain ⟨κ, hκb, hκ⟩ := matched_reindex hα hβ hab
  rw [← image_enum hu hα hαm, Finset.prod_image (fun x _ y _ e => hα e),
    ← hκb.prod_comp fun i => F (p i)]
  simp only [(hκ _).1]
  rw [Fin.prod_univ_six, Fin.prod_univ_three]
  simp only [offPair]
  simp only [Matrix.cons_val]
  ring

/-- Two lists of three colours carry six matched pairs of distinct colours. -/
theorem exists_matched {Lu Lw : Finset ℕ} (hu : Lu.card = 3) (hw : Lw.card = 3) :
    ∃ p q : Fin 6 → ℕ, (∀ i, p i ∈ Lu) ∧ (∀ i, q i ∈ Lw) ∧ (∀ i, p i ≠ q i) ∧
      Matched Lu Lw p q := by
  obtain ⟨α, hα, hαm⟩ := exists_enum hu
  obtain ⟨β, -, hβ, -, hβm, -, hβα, -, -⟩ :=
    exists_aligned_pair hw hα hα fun a b e => hα e
  refine ⟨fun i => α (offPair i).1, fun i => β (offPair i).2, fun i => hαm _, fun i => hβm _,
    fun i e => offPair_ne i (hβα _ _ e.symm), α, β, hα, hβ, hαm, hβm, fun a b hne => ?_⟩
  obtain ⟨j, hj⟩ := offPair_surj a b hne
  exact ⟨j, by show α (offPair j).1 = α a; rw [hj], by show β (offPair j).2 = β b; rw [hj]⟩

/-- **The extension step.** Six matched pairs of distinct colours on `uw` extend to a vertex
`v` with a list of three colours: the new colour differs from both old ones, and the six
colourings are matched on `vu` and on `vw`. -/
theorem Matched.extend {Lu Lw Lv : Finset ℕ} (hv : Lv.card = 3) {p q : Fin 6 → ℕ}
    (hpq : ∀ i, p i ≠ q i) (h : Matched Lu Lw p q) :
    ∃ g : Fin 6 → ℕ, (∀ i, g i ∈ Lv) ∧ (∀ i, g i ≠ p i) ∧ (∀ i, g i ≠ q i) ∧
      Matched Lv Lu g p ∧ Matched Lv Lw g q := by
  obtain ⟨α, β, hα, hβ, hαm, hβm, hab⟩ := h
  have hαβ : ∀ a b, α a = β b → a = b := by
    intro a b e
    by_contra hne
    obtain ⟨i, h1, h2⟩ := hab a b hne
    exact hpq i (h1.trans (e.trans h2.symm))
  obtain ⟨γ, δ, hγ, hδ, hγm, hδm, hγα, hδβ, k, hk⟩ := exists_aligned_pair hv hα hβ hαβ
  -- the permutation `r` with `γ ∘ r = δ`
  have hγs : ∀ b, ∃ c, γ c = δ b := by
    intro b
    have hb : δ b ∈ univ.image γ := by rw [image_enum hv hγ hγm]; exact hδm b
    obtain ⟨c, -, hc⟩ := mem_image.mp hb
    exact ⟨c, hc⟩
  choose r hr using hγs
  have hrinj : ∀ x y, r x = r y → x = y := fun x y e => hδ (by rw [← hr x, ← hr y, e])
  have hrk : r k = k := hγ ((hr k).trans hk.symm)
  have hrsurj : Function.Surjective r :=
    Finite.injective_iff_surjective.mp fun x y e => hrinj x y e
  obtain ⟨h1, h2, h3⟩ := newIdx_spec r hrinj k hrk
  -- the indices of the six old pairs
  obtain ⟨κ, hκb, hκ⟩ := matched_reindex hα hβ hab
  have hcov : ∀ i, ∃ a b, a ≠ b ∧ p i = α a ∧ q i = β b := by
    intro i
    obtain ⟨j, rfl⟩ := hκb.2 i
    exact ⟨_, _, offPair_ne j, (hκ j).1, (hκ j).2⟩
  choose a b hne hpa hqb using hcov
  refine ⟨fun i => γ (newIdx r k (a i) (b i)), fun i => hγm _, ?_, ?_, ?_, ?_⟩
  · intro i e
    exact (h1 _ _ (hne i)).1 (hγα _ _ (e.trans (hpa i))).symm
  · intro i e
    obtain ⟨b'', hb''⟩ := hrsurj (newIdx r k (a i) (b i))
    have h4 : δ b'' = β (b i) := by rw [← hr b'', hb'']; exact e.trans (hqb i)
    exact (h1 _ _ (hne i)).2 ((congrArg r (hδβ _ _ h4)).trans hb'').symm
  · refine ⟨γ, α, hγ, hα, hγm, hαm, fun c a' hca => ?_⟩
    obtain ⟨b', hb', hG⟩ := h2 c a' hca
    obtain ⟨i, hi1, hi2⟩ := hab a' b' (Ne.symm hb')
    have ea : a i = a' := hα ((hpa i).symm.trans hi1)
    have eb : b i = b' := hβ ((hqb i).symm.trans hi2)
    exact ⟨i, by show γ (newIdx r k (a i) (b i)) = γ c; rw [ea, eb, hG], hi1⟩
  · refine ⟨δ, β, hδ, hβ, hδm, hβm, fun b₀ b' hbb => ?_⟩
    obtain ⟨a', ha', hG⟩ := h3 b₀ b' hbb
    obtain ⟨i, hi1, hi2⟩ := hab a' b' ha'
    have ea : a i = a' := hα ((hpa i).symm.trans hi1)
    have eb : b i = b' := hβ ((hqb i).symm.trans hi2)
    exact ⟨i, by show γ (newIdx r k (a i) (b i)) = δ b₀; rw [ea, eb, hG, hr], hi2⟩

end Outerplanar
