/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Nine.Box9

/-!
# The refined box bound at `k = 7`: the star constant `γ₇ = 432/69101`

The scheme of `Nine/Box9.lean`, with the fibre split by the centre values `(a, b)` and the value
`a = a₀` of the unpaired star colour treated on its own (`ai_research_notes/
GRID_K7_ABSORPTION_2026-10-20.md`, §6).

* **The split.** For centre values `(a, b)` the dominoes keep the pairs whose seam colour avoids
  `a` and whose label avoids `b` (`card_cls_le_sum7`): these are the options `optU' … a b` of the
  lower bound, at other centre values.
* **A domino, exactly.** On a domino with seam colours `S₂` and labels `S₃`, the compatible pairs
  inside `X × Y` number `|X| · |Y|` less the colours of `X` whose key lies in `Y`
  (`pairCount_add`). Keys are injective on the labels they hit.
* **The per-label ratios** to the hit count `s` (seam colour `≠ a₀`, label `≠ x₀`), for `|S₂|, |S₃|
  ≥ 5`:
  - any `a`: `17/12` for a label `b ∈ S₃`, `7/4` for `b ∉ S₃`, `4/3` for `b = x₀`
    (`dom_ratio_any`);
  - `a = a₀`: `13/12` for `b ∈ S₃`, `4/3` for `b ∉ S₃`, `1` for `b = x₀` (`dom_ratio_star`);
  - `y₆`: `4/3` for a label off `S₆` and `1` on it; `y₁`: `|S₁| ≤ 4/3 · |S₁ \ {a₀}|`.
* **Nesting.** At most `3, 2, 2` labels lie off `S₆` and the two future domino cells. Summing over
  the six labels `b ≠ x₀` gives at most `7285/432` (any `a`) and `4245/432` (`a = a₀`), plus
  `768/432` and `432/432` at `b = x₀`. So `1/P ≤ 8 · 8053/432 + 4677/432 = 69101/432`
  (`box_bound_seven`).
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m k : ℕ} {P A : Fin m → Finset ℕ} {N : Fin m → ℕ → ℕ}

/-! ### The fibre, split by both centre values -/

section Split7

/-- **The fibre over fixed centre values**, with the domino seam colours avoiding `a`. -/
theorem card_cls_ab_le7 (hc : 1 ≤ c) (v : Fin m) (g : Cell c m → ℕ) (a b : ℕ) :
    (((slab c m k P A N).cls (boxB c v) g).filter
        (fun f => f (z₁ v) = a ∧ f (z₂ hc v) = b)).card ≤
      (((slab c m k P A N).avail (boxB c v) g (y₁ v)).erase a).card *
        (opt6b c k P A N v g b).card * (optU' c k P A N hc v a b g).card *
          (optD' c k P A N hc v a b g).card := by
  set C := slab c m k P A N
  have h1v : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  have hT : ({a} ×ˢ {b} ×ˢ (C.avail (boxB c v) g (y₁ v)).erase a ×ˢ opt6b c k P A N v g b ×ˢ
      optU' c k P A N hc v a b g ×ˢ optD' c k P A N hc v a b g).card =
        ((C.avail (boxB c v) g (y₁ v)).erase a).card * (opt6b c k P A N v g b).card *
          (optU' c k P A N hc v a b g).card * (optD' c k P A N hc v a b g).card := by
    simp only [card_product, card_singleton]; ring
  rw [← hT]
  refine card_le_card_of_injOn (boxVals hc v) ?_ (fun f hf f' hf' he =>
    boxVals_injOn hc v g (mem_filter.mp hf).1 (mem_filter.mp hf').1 he)
  intro f hf
  rw [mem_coe, mem_filter] at hf
  obtain ⟨hf, ha, hb⟩ := hf
  have hv := ((CSP.mem_cls _).mp hf).1
  simp only [coe_product, Set.mem_prod, mem_coe, boxVals, mem_singleton]
  refine ⟨ha, hb, ?_, ?_, ?_, ?_⟩
  · rw [mem_erase]
    refine ⟨fun e => ?_, CSP.mem_avail_of_mem_cls _ hf (mem_boxB.mpr (y₁_inY v).1)⟩
    refine ne_of_eq_adj hv (x := y₁ v) (y := z₁ v) (Or.inr ⟨rfl, Or.inl ?_⟩) ?_ ?_ (e.trans ha.symm)
    · show (0 : Fin (c + 2)).val + 1 = (1 : Fin (c + 2)).val; rw [h1v]; rfl
    · show ¬ ((0 : Fin (c + 2)).val = 1 ∧ _); simp
    · show ¬ ((0 : Fin (c + 2)).val = 2 ∧ _); simp
  · unfold opt6b
    split_ifs with h
    · refine mem_map_of_mem _ (mem_erase.mpr ⟨fun e => ?_,
        CSP.mem_avail_of_mem_cls _ hf (mem_boxB.mpr (y₆_inY h v).1)⟩)
      refine ne_of_eq_adj hv (x := y₆ h v) (y := z₂ hc v) (Or.inr ⟨rfl, Or.inr ?_⟩) ?_ ?_
        (e.trans hb.symm)
      · show (2 : ℕ) + 1 = 3; rfl
      · show ¬ ((3 : ℕ) = 1 ∧ _); simp
      · show ¬ ((3 : ℕ) = 2 ∧ _); simp
    · exact mem_singleton_self _
  · unfold optU'
    split_ifs with h
    · refine mem_map_of_mem _ (mem_filter.mpr ⟨mem_dom_of_valid hf (mem_boxB.mpr (yU₁_inY h).1)
        (mem_boxB.mpr (yU₂_inY hc h).1) (slabAdj_dom₁ hc h), fun e => ?_, fun e => ?_⟩)
      · refine ne_of_eq_adj hv (x := yU₁ h) (y := z₁ v) (Or.inl ⟨rfl, Or.inl ?_⟩) ?_ ?_
          (e.trans ha.symm)
        · show v.val - 1 + 1 = v.val; omega
        · show ¬ ((1 : Fin (c + 2)).val = 1 ∧ (1 : Fin (c + 2)).val = 2); rw [h1v]; omega
        · show ¬ ((1 : Fin (c + 2)).val = 2 ∧ _); rw [h1v]; omega
      · refine ne_of_eq_adj hv (x := yU₂ hc h) (y := z₂ hc v) (Or.inl ⟨rfl, Or.inl ?_⟩) ?_ ?_
          (e.trans hb.symm)
        · show v.val - 1 + 1 = v.val; omega
        · show ¬ ((2 : ℕ) = 1 ∧ _); simp
        · show ¬ (_ ∧ (2 : ℕ) = 1); simp
    · exact mem_singleton_self _
  · unfold optD'
    split_ifs with h
    · refine mem_map_of_mem _ (mem_filter.mpr ⟨mem_dom_of_valid hf (mem_boxB.mpr (yD₁_inY h).1)
        (mem_boxB.mpr (yD₂_inY hc h).1) (slabAdj_dom₂ hc h), fun e => ?_, fun e => ?_⟩)
      · refine ne_of_eq_adj hv (x := yD₁ h) (y := z₁ v) (Or.inl ⟨rfl, Or.inr ?_⟩) ?_ ?_
          (e.trans ha.symm)
        · show v.val + 1 = v.val + 1; rfl
        · show ¬ ((1 : Fin (c + 2)).val = 1 ∧ (1 : Fin (c + 2)).val = 2); rw [h1v]; omega
        · show ¬ ((1 : Fin (c + 2)).val = 2 ∧ _); rw [h1v]; omega
      · refine ne_of_eq_adj hv (x := yD₂ hc h) (y := z₂ hc v) (Or.inl ⟨rfl, Or.inr ?_⟩) ?_ ?_
          (e.trans hb.symm)
        · show v.val + 1 = v.val + 1; rfl
        · show ¬ ((2 : ℕ) = 1 ∧ _); simp
        · show ¬ (_ ∧ (2 : ℕ) = 1); simp
    · exact mem_singleton_self _

/-- **The fibre, summed over both centre values.** -/
theorem card_cls_le_sum7 (hc : 1 ≤ c) (v : Fin m) (g : Cell c m → ℕ) :
    ((slab c m k P A N).cls (boxB c v) g).card ≤ ∑ a ∈ A v, ∑ b ∈ range k,
      (((slab c m k P A N).avail (boxB c v) g (y₁ v)).erase a).card *
        (opt6b c k P A N v g b).card * (optU' c k P A N hc v a b g).card *
          (optD' c k P A N hc v a b g).card := by
  rw [card_eq_sum_card_fiberwise (f := fun f => (f (z₁ v), f (z₂ hc v))) (t := A v ×ˢ range k)]
  · rw [sum_product]
    refine sum_le_sum fun a _ => sum_le_sum fun b _ => le_trans (le_of_eq ?_)
      (card_cls_ab_le7 hc v g a b)
    congr 1
  · intro f hf
    have hv := ((CSP.mem_cls _).mp hf).1
    rw [mem_coe, mem_product]
    refine ⟨?_, ?_⟩
    · have := hv.1 (z₁ v); rwa [slab_D_one (z₁_fst v)] at this
    · have := hv.1 (z₂ hc v); rwa [slab_D_fut (by rw [z₂_fst])] at this

end Split7

/-! ### Counting the pairs of a domino -/

section PairCount

/-- The pairs of `X × Y` whose label is not the key of their colour. -/
noncomputable def pairCount (κ : ℕ → ℕ) (X Y : Finset ℕ) : ℕ :=
  ((X ×ˢ Y).filter (fun pq => κ pq.1 ≠ pq.2)).card

/-- The colours of `X` whose key lies in `Y`. -/
noncomputable def keyHits (κ : ℕ → ℕ) (X Y : Finset ℕ) : ℕ :=
  (X.filter (fun p => κ p ∈ Y)).card

/-- **Pairs, exactly.** -/
theorem pairCount_add (κ : ℕ → ℕ) (X Y : Finset ℕ) :
    pairCount κ X Y + keyHits κ X Y = X.card * Y.card := by
  unfold pairCount keyHits
  rw [card_filter, sum_product, card_filter, ← sum_add_distrib, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun p _ => ?_
  rw [← card_filter]
  have e : Y.filter (fun q => κ p ≠ q) = Y.erase (κ p) := by
    ext q; simp only [mem_filter, mem_erase]; exact ⟨fun h => ⟨fun e => h.2 e.symm, h.1⟩,
      fun h => ⟨h.2, fun e => h.1 e.symm⟩⟩
  rw [e]
  by_cases h : κ p ∈ Y
  · rw [ite_eq_left h, card_erase_of_mem h]
    have := card_pos.mpr ⟨_, h⟩
    omega
  · rw [ite_eq_right h, erase_eq_of_notMem h, add_zero]

theorem pairCount_mono (κ : ℕ → ℕ) {X X' Y Y' : Finset ℕ} (hX : X' ⊆ X) (hY : Y' ⊆ Y) :
    pairCount κ X' Y' ≤ pairCount κ X Y :=
  card_le_card (filter_subset_filter _ (product_subset_product hX hY))

theorem keyHits_mono (κ : ℕ → ℕ) {X X' Y Y' : Finset ℕ} (hX : X' ⊆ X) (hY : Y' ⊆ Y) :
    keyHits κ X' Y' ≤ keyHits κ X Y := by
  refine card_le_card fun p hp => ?_
  rw [mem_filter] at hp ⊢
  exact ⟨hX hp.1, hY hp.2⟩

theorem keyHits_le_left (κ : ℕ → ℕ) (X Y : Finset ℕ) : keyHits κ X Y ≤ X.card :=
  card_filter_le _ _

/-- Keys are injective on the labels they hit. -/
def HitInj (κ : ℕ → ℕ) (X Y : Finset ℕ) : Prop :=
  ∀ p ∈ X, ∀ p' ∈ X, κ p ∈ Y → κ p = κ p' → p = p'

theorem keyHits_le_right {κ : ℕ → ℕ} {X Y Y' : Finset ℕ} (hi : HitInj κ X Y) (hY : Y' ⊆ Y) :
    keyHits κ X Y' ≤ Y'.card := by
  refine card_le_card_of_injOn κ (fun p hp => ?_) (fun p hp p' hp' e => ?_)
  · rw [mem_coe, mem_filter] at hp; exact hp.2
  · rw [mem_coe, mem_filter] at hp hp'
    exact hi p hp.1 p' hp'.1 (hY hp.2) e

theorem keyHits_erase {κ : ℕ → ℕ} {X X' Y : Finset ℕ} (hi : HitInj κ X Y) (hX : X' ⊆ X) (b : ℕ) :
    keyHits κ X' Y ≤ keyHits κ X' (Y.erase b) + 1 := by
  unfold keyHits
  have hsub : X'.filter (fun p => κ p ∈ Y) ⊆ X'.filter (fun p => κ p ∈ Y.erase b) ∪
      X'.filter (fun p => κ p ∈ Y ∧ κ p = b) := by
    intro p hp
    rw [mem_filter] at hp
    rw [mem_union, mem_filter, mem_filter, mem_erase]
    by_cases e : κ p = b
    · exact Or.inr ⟨hp.1, hp.2, e⟩
    · exact Or.inl ⟨hp.1, e, hp.2⟩
  have h1 : (X'.filter (fun p => κ p ∈ Y ∧ κ p = b)).card ≤ 1 := by
    refine card_le_one.mpr fun p hp p' hp' => ?_
    rw [mem_filter] at hp hp'
    exact hi p (hX hp.1) p' (hX hp'.1) hp.2.1 (hp.2.2.trans hp'.2.2.symm)
  exact le_trans (card_le_card hsub) (le_trans (card_union_le _ _) (by omega))

end PairCount

/-! ### The domino ratios -/

section Ratios

theorem ain_arith {s2 t3 e2 f3 mU mp mb τ s fb : ℕ} (h3 : 5 ≤ t3) (he4 : 4 ≤ e2)
    (he : s2 ≤ e2 + 1) (hf : t3 ≤ f3 + 1) (hfb : fb + 1 = t3) (hmp1 : mp ≤ mU) (hmp3 : mp ≤ f3)
    (hτ : τ + mb = s2 * fb) (hmb : mU ≤ mb + 1) (hs : s + mp = e2 * f3) : 12 * τ ≤ 17 * s := by
  have h1 : s2 * fb ≤ e2 * f3 + f3 := by nlinarith
  have h2 : 3 * f3 ≤ s := by nlinarith
  omega

theorem aout_arith {s2 t3 e2 f3 mU mp τ s : ℕ} (he4 : 4 ≤ e2) (hf4 : 4 ≤ f3)
    (he : s2 ≤ e2 + 1) (hf : t3 ≤ f3 + 1) (hmp1 : mp ≤ mU) (hmp2 : mp ≤ e2)
    (hτ : τ + mU = s2 * t3) (hs : s + mp = e2 * f3) : 4 * τ ≤ 7 * s := by
  have h1 : s2 * t3 ≤ e2 * f3 + e2 + f3 + 1 := by nlinarith
  have h2 : 4 * (e2 + f3 + 1) ≤ 3 * s := by
    rcases le_total e2 f3 with h | h
    · nlinarith
    · nlinarith
  omega

theorem ax_arith {s2 e2 f3 mx mp τ s : ℕ} (he4 : 4 ≤ e2) (he : s2 ≤ e2 + 1) (hmp : mp ≤ mx)
    (hmp3 : mp ≤ f3) (hτ : τ + mx = s2 * f3) (hs : s + mp = e2 * f3) : 3 * τ ≤ 4 * s := by
  have h1 : s2 * f3 ≤ e2 * f3 + f3 := by nlinarith
  have h2 : 3 * f3 ≤ s := by nlinarith
  omega

theorem cin_arith {e2 f3 mc mp mcb τ s fb : ℕ} (he4 : 4 ≤ e2) (hf4 : 4 ≤ f3) (hfb : fb ≤ f3)
    (hmp1 : mp ≤ mc) (hmp2 : mp ≤ e2) (hτ : τ + mcb = e2 * fb) (hmc : mc ≤ mcb + 1)
    (hs : s + mp = e2 * f3) : 12 * τ ≤ 13 * s := by
  have h1 : e2 * fb ≤ e2 * f3 := Nat.mul_le_mul_left _ hfb
  have h2 : 12 ≤ s := by nlinarith
  omega

theorem cout_arith {e2 t3 f3 mc mp τ s : ℕ} (hf4 : 4 ≤ f3) (hf : t3 ≤ f3 + 1)
    (hmp1 : mp ≤ mc) (hmp2 : mp ≤ e2) (hτ : τ + mc = e2 * t3) (hs : s + mp = e2 * f3) :
    3 * τ ≤ 4 * s := by
  have h1 : e2 * t3 ≤ e2 * f3 + e2 := by nlinarith
  have h2 : 3 * e2 ≤ s := by nlinarith
  omega

variable {S2 S3 : Finset ℕ} {κ : ℕ → ℕ}

/-- **The domino ratio at any seam value `a`.** -/
theorem dom_ratio_any (h2 : 5 ≤ S2.card) (h3 : 5 ≤ S3.card) (hi : HitInj κ S2 S3)
    (a b a₀ x₀ : ℕ) :
    (pairCount κ (S2.erase a) (S3.erase b) : ℚ) ≤
      (if b = x₀ then 4 / 3 else if b ∉ S3 then 17 / 12 + 1 / 3 else 17 / 12) *
        pairCount κ (S2.erase a₀) (S3.erase x₀) := by
  have hτ0 := pairCount_mono κ (erase_subset a S2) (subset_refl (S3.erase b))
  have hs := pairCount_add κ (S2.erase a₀) (S3.erase x₀)
  have he := pred_card_le_card_erase (s := S2) (a := a₀)
  have hf := pred_card_le_card_erase (s := S3) (a := x₀)
  have hmp1 := keyHits_mono κ (erase_subset a₀ S2) (erase_subset x₀ S3)
  have hmp2 := keyHits_le_left κ (S2.erase a₀) (S3.erase x₀)
  have hmp3 := keyHits_le_right (X := S2.erase a₀) (fun p hp p' hp' => hi p (mem_of_mem_erase hp)
    p' (mem_of_mem_erase hp')) (erase_subset x₀ S3)
  by_cases hbx : b = x₀
  · rw [ite_eq_left hbx]
    rw [hbx] at hτ0 ⊢
    have hτ := pairCount_add κ S2 (S3.erase x₀)
    have hmx := keyHits_mono κ (erase_subset a₀ S2) (subset_refl (S3.erase x₀))
    have := ax_arith (τ := pairCount κ S2 (S3.erase x₀)) (by omega) (by omega) hmx hmp3 hτ hs
    have := (Nat.cast_le (α := ℚ)).mpr (le_trans (Nat.mul_le_mul_left 3 hτ0) this)
    push_cast at this
    linarith
  rw [ite_eq_right hbx]
  by_cases hb : b ∈ S3
  · rw [ite_eq_right (not_not.mpr hb)]
    have hτ := pairCount_add κ S2 (S3.erase b)
    have hmb := keyHits_erase hi (subset_refl S2) b
    have hfb := card_erase_add_one hb
    have := ain_arith (τ := pairCount κ S2 (S3.erase b)) (s2 := S2.card) (t3 := S3.card)
      (by omega) (by omega) (by omega) (by omega) hfb hmp1 hmp3 hτ hmb hs
    have := (Nat.cast_le (α := ℚ)).mpr (le_trans (Nat.mul_le_mul_left 12 hτ0) this)
    push_cast at this
    linarith
  · rw [ite_eq_left hb]
    have hτ := pairCount_add κ S2 S3
    rw [erase_eq_of_notMem hb] at hτ0 ⊢
    have := aout_arith (τ := pairCount κ S2 S3) (s2 := S2.card) (t3 := S3.card) (by omega)
      (by omega) (by omega) (by omega) hmp1 hmp2 hτ hs
    have := (Nat.cast_le (α := ℚ)).mpr (le_trans (Nat.mul_le_mul_left 4 hτ0) this)
    push_cast at this
    linarith

/-- **The domino ratio at the star value `a₀`.** -/
theorem dom_ratio_star (h2 : 5 ≤ S2.card) (h3 : 5 ≤ S3.card) (hi : HitInj κ S2 S3)
    (b a₀ x₀ : ℕ) :
    (pairCount κ (S2.erase a₀) (S3.erase b) : ℚ) ≤
      (if b = x₀ then 1 else if b ∉ S3 then 13 / 12 + 1 / 4 else 13 / 12) *
        pairCount κ (S2.erase a₀) (S3.erase x₀) := by
  have hs := pairCount_add κ (S2.erase a₀) (S3.erase x₀)
  have he := pred_card_le_card_erase (s := S2) (a := a₀)
  have hf := pred_card_le_card_erase (s := S3) (a := x₀)
  have hi' : HitInj κ (S2.erase a₀) S3 := fun p hp p' hp' => hi p (mem_of_mem_erase hp)
    p' (mem_of_mem_erase hp')
  have hmp1 := keyHits_mono κ (subset_refl (S2.erase a₀)) (erase_subset x₀ S3)
  have hmp2 := keyHits_le_left κ (S2.erase a₀) (S3.erase x₀)
  have hmc := keyHits_le_left κ (S2.erase a₀) S3
  by_cases hbx : b = x₀
  · rw [ite_eq_left hbx, hbx, one_mul]
  rw [ite_eq_right hbx]
  by_cases hb : b ∈ S3
  · rw [ite_eq_right (not_not.mpr hb)]
    have hτ := pairCount_add κ (S2.erase a₀) (S3.erase b)
    have hmb := keyHits_erase hi' (subset_refl _) b
    have hfb := card_erase_le (s := S3) (a := b)
    have hfb' := card_erase_add_one hb
    have := cin_arith (τ := pairCount κ (S2.erase a₀) (S3.erase b)) (by omega) (by omega)
      (show (S3.erase b).card ≤ (S3.erase x₀).card by omega) hmp1 hmp2 hτ hmb hs
    have := (Nat.cast_le (α := ℚ)).mpr this
    push_cast at this
    linarith
  · rw [ite_eq_left hb]
    have hτ := pairCount_add κ (S2.erase a₀) S3
    rw [erase_eq_of_notMem hb]
    have := cout_arith (τ := pairCount κ (S2.erase a₀) S3) (t3 := S3.card) (by omega)
      (by omega) hmp1 hmp2 hτ hs
    have := (Nat.cast_le (α := ℚ)).mpr this
    push_cast at this
    linarith

end Ratios

/-! ### The domino factors in the slab -/

section SlabDom

/-- On a seam domino, the pairs avoiding `a` and `b` are counted by `pairCount`. -/
theorem dom_filter_eq {U : Finset (Cell c m)} {g : Cell c m → ℕ} {y y' : Cell c m}
    (h1 : y.1.val = 1) (h2 : y'.1.val = 2) (a b : ℕ) :
    ((dom c k P A N U g y y').filter (fun pq => pq.1 ≠ a ∧ pq.2 ≠ b)).card =
      pairCount (N y.2) (((slab c m k P A N).avail U g y).erase a)
        (((slab c m k P A N).avail U g y').erase b) := by
  unfold pairCount
  congr 1
  ext ⟨p, q⟩
  rw [mem_filter, mem_filter, mem_dom_iff, mem_product, mem_erase, mem_erase,
    slab_conf_seam h1 h2, slab_conf_seam' h2 h1]
  dsimp only
  constructor
  · rintro ⟨⟨⟨hp, hq⟩, hn, -⟩, ha, hb⟩
    exact ⟨⟨⟨ha, hp⟩, hb, hq⟩, hn⟩
  · rintro ⟨⟨⟨ha, hp⟩, hb, hq⟩, hn⟩
    exact ⟨⟨⟨hp, hq⟩, hn, fun e => hn e.symm⟩, ha, hb⟩

/-- Keys are injective on the labels they hit. -/
theorem hitInj_of_keyInj (hK : KeyInj 7 A N) {U : Finset (Cell c m)} {g : Cell c m → ℕ}
    {y y' : Cell c m} (h1 : y.1.val = 1) (h2 : 2 ≤ y'.1.val) :
    HitInj (N y.2) ((slab c m 7 P A N).avail U g y) ((slab c m 7 P A N).avail U g y') := by
  intro p hp p' hp' hκ e
  have hpA := ((slab c m 7 P A N).mem_avail.mp hp).1
  have hpA' := ((slab c m 7 P A N).mem_avail.mp hp').1
  have hκ7 := ((slab c m 7 P A N).mem_avail.mp hκ).1
  rw [slab_D_one h1] at hpA hpA'
  rw [slab_D_fut h2, mem_range] at hκ7
  exact hK y.2 p p' hpA hpA' e hκ7

/-- A domino factor at `k = 7`, at any seam value `a`. -/
theorem dom_any7 (hK : KeyInj 7 A N) {v : Fin m} {g : Cell c m → ℕ} {y y' : Cell c m}
    (h1 : y.1.val = 1) (h2 : y'.1.val = 2)
    (hs2 : 5 ≤ ((slab c m 7 P A N).avail (boxB c v) g y).card)
    (hs3 : 5 ≤ ((slab c m 7 P A N).avail (boxB c v) g y').card) (a b a₀ x₀ : ℕ) :
    (((dom c 7 P A N (boxB c v) g y y').filter (fun pq => pq.1 ≠ a ∧ pq.2 ≠ b)).card : ℚ) ≤
      (if b = x₀ then 4 / 3 else
        if b ∉ (slab c m 7 P A N).avail (boxB c v) g y' then 17 / 12 + 1 / 3 else 17 / 12) *
        ((dom c 7 P A N (boxB c v) g y y').filter (fun pq => pq.1 ≠ a₀ ∧ pq.2 ≠ x₀)).card := by
  rw [dom_filter_eq h1 h2, dom_filter_eq h1 h2]
  exact dom_ratio_any hs2 hs3 (hitInj_of_keyInj hK h1 (by omega)) a b a₀ x₀

/-- A domino factor at `k = 7`, at the star value `a₀`. -/
theorem dom_star7 (hK : KeyInj 7 A N) {v : Fin m} {g : Cell c m → ℕ} {y y' : Cell c m}
    (h1 : y.1.val = 1) (h2 : y'.1.val = 2)
    (hs2 : 5 ≤ ((slab c m 7 P A N).avail (boxB c v) g y).card)
    (hs3 : 5 ≤ ((slab c m 7 P A N).avail (boxB c v) g y').card) (b a₀ x₀ : ℕ) :
    (((dom c 7 P A N (boxB c v) g y y').filter (fun pq => pq.1 ≠ a₀ ∧ pq.2 ≠ b)).card : ℚ) ≤
      (if b = x₀ then 1 else
        if b ∉ (slab c m 7 P A N).avail (boxB c v) g y' then 13 / 12 + 1 / 4 else 13 / 12) *
        ((dom c 7 P A N (boxB c v) g y y').filter (fun pq => pq.1 ≠ a₀ ∧ pq.2 ≠ x₀)).card := by
  rw [dom_filter_eq h1 h2, dom_filter_eq h1 h2]
  exact dom_ratio_star hs2 hs3 (hitInj_of_keyInj hK h1 (by omega)) b a₀ x₀

theorem dom_avail_U7 (hK : KeyInj 7 A N) (hA : ∀ v, (A v).card = 7) (hc : 1 ≤ c) {v : Fin m}
    (h : 1 ≤ v.val) {g : Cell c m → ℕ} (hg : (slab c m 7 P A N).Valid g) :
    5 ≤ ((slab c m 7 P A N).avail (boxB c v) g (yU₁ h)).card ∧
      5 ≤ ((slab c m 7 P A N).avail (boxB c v) g (yU₂ hc h)).card := by
  have hM := slab_match (c := c) (P := P) hK
  have hI : (slab c m 7 P A N : CSP (Cell c m)).Irrefl := slab_irrefl
  constructor
  · have hav := (slab c m 7 P A N).card_avail_ge hM hI (mem_boxB.mpr (yU₁_inY (c := c) h).1)
      (fun x _ => hg.1 x)
    rw [slab_D_one (show (yU₁ (c := c) h).1.val = 1 from Fin.val_one _), hA] at hav
    have hn := nbrsOut_yU₁ (c := c) (k := 7) (P := P) (A := A) (N := N) h
    omega
  · have hav := card_avail_fut_ge hK hg (yU₂_inY hc h).1 (show 2 ≤ (yU₂ hc h).1.val from le_rfl)
    have hn := nbrsOut_yU₂ (k := 7) (P := P) (A := A) (N := N) hc h
    omega

theorem dom_avail_D7 (hK : KeyInj 7 A N) (hA : ∀ v, (A v).card = 7) (hc : 1 ≤ c) {v : Fin m}
    (h : v.val + 1 < m) {g : Cell c m → ℕ} (hg : (slab c m 7 P A N).Valid g) :
    5 ≤ ((slab c m 7 P A N).avail (boxB c v) g (yD₁ h)).card ∧
      5 ≤ ((slab c m 7 P A N).avail (boxB c v) g (yD₂ hc h)).card := by
  have hM := slab_match (c := c) (P := P) hK
  have hI : (slab c m 7 P A N : CSP (Cell c m)).Irrefl := slab_irrefl
  constructor
  · have hav := (slab c m 7 P A N).card_avail_ge hM hI (mem_boxB.mpr (yD₁_inY (c := c) h).1)
      (fun x _ => hg.1 x)
    rw [slab_D_one (show (yD₁ (c := c) h).1.val = 1 from Fin.val_one _), hA] at hav
    have hn := nbrsOut_yD₁ (c := c) (k := 7) (P := P) (A := A) (N := N) h
    omega
  · have hav := card_avail_fut_ge hK hg (yD₂_inY hc h).1 (show 2 ≤ (yD₂ hc h).1.val from le_rfl)
    have hn := nbrsOut_yD₂ (k := 7) (P := P) (A := A) (N := N) hc h
    omega

/-- Labels unavailable at `y₆`. -/
def o6s (v : Fin m) (g : Cell c m → ℕ) (b : ℕ) : Prop :=
  if h : 2 ≤ c then b ∉ (slab c m 7 P A N).avail (boxB c v) g (y₆ h v) else False

/-- Labels unavailable at the future cell of the upper domino. -/
def oUs (hc : 1 ≤ c) (v : Fin m) (g : Cell c m → ℕ) (b : ℕ) : Prop :=
  if h : 1 ≤ v.val then b ∉ (slab c m 7 P A N).avail (boxB c v) g (yU₂ hc h) else False

/-- Labels unavailable at the future cell of the lower domino. -/
def oDs (hc : 1 ≤ c) (v : Fin m) (g : Cell c m → ℕ) (b : ℕ) : Prop :=
  if h : v.val + 1 < m then b ∉ (slab c m 7 P A N).avail (boxB c v) g (yD₂ hc h) else False

/-- The upper domino factor, at any seam value `a`. -/
theorem U_any7 (hK : KeyInj 7 A N) (hA : ∀ v, (A v).card = 7) (hc : 1 ≤ c) (v : Fin m)
    {g : Cell c m → ℕ} (hg : (slab c m 7 P A N).Valid g) (a b a₀ x₀ : ℕ) :
    ((optU' c 7 P A N hc v a b g).card : ℚ) ≤
      (if b = x₀ then 4 / 3 else
        if oUs (P := P) (A := A) (N := N) hc v g b then 17 / 12 + 1 / 3 else 17 / 12) *
        (optU' c 7 P A N hc v a₀ x₀ g).card := by
  by_cases h : 1 ≤ v.val
  · have ho : oUs (P := P) (A := A) (N := N) hc v g b ↔
        b ∉ (slab c m 7 P A N).avail (boxB c v) g (yU₂ hc h) := by simp [oUs, h]
    simp only [optU', dite_eq_left h, card_map]
    obtain ⟨h2, h3⟩ := dom_avail_U7 hK hA hc h hg
    have := dom_any7 hK (show (yU₁ (c := c) h).1.val = 1 from Fin.val_one _)
      (show (yU₂ hc h).1.val = 2 from rfl) h2 h3 a b a₀ x₀
    by_cases hbx : b = x₀
    · rw [ite_eq_left hbx] at this ⊢; exact this
    rw [ite_eq_right hbx] at this ⊢
    by_cases hb : oUs (P := P) (A := A) (N := N) hc v g b
    · rw [ite_eq_left hb]; rw [ite_eq_left (ho.mp hb)] at this; exact this
    · rw [ite_eq_right hb]; rw [ite_eq_right (fun h' => hb (ho.mpr h'))] at this; exact this
  · simp only [optU', oUs, dite_eq_right h, card_singleton, Nat.cast_one]
    split_ifs <;> norm_num

/-- The lower domino factor, at any seam value `a`. -/
theorem D_any7 (hK : KeyInj 7 A N) (hA : ∀ v, (A v).card = 7) (hc : 1 ≤ c) (v : Fin m)
    {g : Cell c m → ℕ} (hg : (slab c m 7 P A N).Valid g) (a b a₀ x₀ : ℕ) :
    ((optD' c 7 P A N hc v a b g).card : ℚ) ≤
      (if b = x₀ then 4 / 3 else
        if oDs (P := P) (A := A) (N := N) hc v g b then 17 / 12 + 1 / 3 else 17 / 12) *
        (optD' c 7 P A N hc v a₀ x₀ g).card := by
  by_cases h : v.val + 1 < m
  · have ho : oDs (P := P) (A := A) (N := N) hc v g b ↔
        b ∉ (slab c m 7 P A N).avail (boxB c v) g (yD₂ hc h) := by simp [oDs, h]
    simp only [optD', dite_eq_left h, card_map]
    obtain ⟨h2, h3⟩ := dom_avail_D7 hK hA hc h hg
    have := dom_any7 hK (show (yD₁ (c := c) h).1.val = 1 from Fin.val_one _)
      (show (yD₂ hc h).1.val = 2 from rfl) h2 h3 a b a₀ x₀
    by_cases hbx : b = x₀
    · rw [ite_eq_left hbx] at this ⊢; exact this
    rw [ite_eq_right hbx] at this ⊢
    by_cases hb : oDs (P := P) (A := A) (N := N) hc v g b
    · rw [ite_eq_left hb]; rw [ite_eq_left (ho.mp hb)] at this; exact this
    · rw [ite_eq_right hb]; rw [ite_eq_right (fun h' => hb (ho.mpr h'))] at this; exact this
  · simp only [optD', oDs, dite_eq_right h, card_singleton, Nat.cast_one]
    split_ifs <;> norm_num

/-- The upper domino factor, at the star value `a₀`. -/
theorem U_star7 (hK : KeyInj 7 A N) (hA : ∀ v, (A v).card = 7) (hc : 1 ≤ c) (v : Fin m)
    {g : Cell c m → ℕ} (hg : (slab c m 7 P A N).Valid g) (b a₀ x₀ : ℕ) :
    ((optU' c 7 P A N hc v a₀ b g).card : ℚ) ≤
      (if b = x₀ then 1 else
        if oUs (P := P) (A := A) (N := N) hc v g b then 13 / 12 + 1 / 4 else 13 / 12) *
        (optU' c 7 P A N hc v a₀ x₀ g).card := by
  by_cases h : 1 ≤ v.val
  · have ho : oUs (P := P) (A := A) (N := N) hc v g b ↔
        b ∉ (slab c m 7 P A N).avail (boxB c v) g (yU₂ hc h) := by simp [oUs, h]
    simp only [optU', dite_eq_left h, card_map]
    obtain ⟨h2, h3⟩ := dom_avail_U7 hK hA hc h hg
    have := dom_star7 hK (show (yU₁ (c := c) h).1.val = 1 from Fin.val_one _)
      (show (yU₂ hc h).1.val = 2 from rfl) h2 h3 b a₀ x₀
    by_cases hbx : b = x₀
    · rw [ite_eq_left hbx] at this ⊢; exact this
    rw [ite_eq_right hbx] at this ⊢
    by_cases hb : oUs (P := P) (A := A) (N := N) hc v g b
    · rw [ite_eq_left hb]; rw [ite_eq_left (ho.mp hb)] at this; exact this
    · rw [ite_eq_right hb]; rw [ite_eq_right (fun h' => hb (ho.mpr h'))] at this; exact this
  · simp only [optU', oUs, dite_eq_right h, card_singleton, Nat.cast_one]
    split_ifs <;> norm_num

/-- The lower domino factor, at the star value `a₀`. -/
theorem D_star7 (hK : KeyInj 7 A N) (hA : ∀ v, (A v).card = 7) (hc : 1 ≤ c) (v : Fin m)
    {g : Cell c m → ℕ} (hg : (slab c m 7 P A N).Valid g) (b a₀ x₀ : ℕ) :
    ((optD' c 7 P A N hc v a₀ b g).card : ℚ) ≤
      (if b = x₀ then 1 else
        if oDs (P := P) (A := A) (N := N) hc v g b then 13 / 12 + 1 / 4 else 13 / 12) *
        (optD' c 7 P A N hc v a₀ x₀ g).card := by
  by_cases h : v.val + 1 < m
  · have ho : oDs (P := P) (A := A) (N := N) hc v g b ↔
        b ∉ (slab c m 7 P A N).avail (boxB c v) g (yD₂ hc h) := by simp [oDs, h]
    simp only [optD', dite_eq_left h, card_map]
    obtain ⟨h2, h3⟩ := dom_avail_D7 hK hA hc h hg
    have := dom_star7 hK (show (yD₁ (c := c) h).1.val = 1 from Fin.val_one _)
      (show (yD₂ hc h).1.val = 2 from rfl) h2 h3 b a₀ x₀
    by_cases hbx : b = x₀
    · rw [ite_eq_left hbx] at this ⊢; exact this
    rw [ite_eq_right hbx] at this ⊢
    by_cases hb : oDs (P := P) (A := A) (N := N) hc v g b
    · rw [ite_eq_left hb]; rw [ite_eq_left (ho.mp hb)] at this; exact this
    · rw [ite_eq_right hb]; rw [ite_eq_right (fun h' => hb (ho.mpr h'))] at this; exact this
  · simp only [optD', oDs, dite_eq_right h, card_singleton, Nat.cast_one]
    split_ifs <;> norm_num

end SlabDom

/-! ### The single cells and the nesting -/

section Seven

/-- Few labels are unavailable at a future cell of the box. -/
theorem card_unavail_le7 (hK : KeyInj 7 A N) {v : Fin m} {g : Cell c m → ℕ}
    (hg : (slab c m 7 P A N).Valid g) {y : Cell c m} (hy : inB v y) (hy2 : 2 ≤ y.1.val) {r : ℕ}
    (hr : ((slab c m 7 P A N).nbrsOut y (boxB c v)).card ≤ r) :
    ((range 7).filter (fun b => b ∉ (slab c m 7 P A N).avail (boxB c v) g y)).card ≤ r := by
  have hav := card_avail_fut_ge hK hg hy hy2
  have hsub : (slab c m 7 P A N).avail (boxB c v) g y ⊆ range 7 := by
    intro a ha; have := ((slab c m 7 P A N).mem_avail.mp ha).1; rwa [slab_D_fut hy2] at this
  have e : (range 7).filter (fun b => b ∉ (slab c m 7 P A N).avail (boxB c v) g y) =
      range 7 \ (slab c m 7 P A N).avail (boxB c v) g y := by
    ext b; simp [mem_sdiff]
  rw [e, card_sdiff_of_subset hsub, card_range]
  omega

/-- The `y₁` factor at `k = 7`. -/
theorem y1_seven (hK : KeyInj 7 A N) (v : Fin m) {a₀ : ℕ} (hPv : 6 ≤ (P v).card ∨ a₀ ∉ P v)
    {g : Cell c m → ℕ} (hg : (slab c m 7 P A N).Valid g) :
    3 * ((slab c m 7 P A N).avail (boxB c v) g (y₁ v)).card ≤
      4 * (((slab c m 7 P A N).avail (boxB c v) g (y₁ v)).erase a₀).card := by
  have hM := slab_match (c := c) (P := P) hK
  have hI : (slab c m 7 P A N : CSP (Cell c m)).Irrefl := slab_irrefl
  by_cases hm : a₀ ∈ (slab c m 7 P A N).avail (boxB c v) g (y₁ v)
  · have hP : a₀ ∈ P v := by
      have := ((slab c m 7 P A N).mem_avail.mp hm).1; rwa [slab_D_zero rfl] at this
    have hPc : 6 ≤ (P v).card := hPv.resolve_right (not_not.mpr hP)
    have hav := (slab c m 7 P A N).card_avail_ge hM hI (mem_boxB.mpr (y₁_inY (c := c) v).1)
      (fun x _ => hg.1 x)
    rw [slab_D_zero rfl] at hav
    change (P v).card - _ ≤ _ at hav
    have hn := nbrsOut_y₁ (c := c) (k := 7) (P := P) (A := A) (N := N) v
    rw [card_erase_of_mem hm]
    omega
  · rw [erase_eq_of_notMem hm]; omega

/-- The `y₆` factor at `k = 7`. -/
theorem y6_seven (hK : KeyInj 7 A N) (v : Fin m) {x₀ : ℕ} {g : Cell c m → ℕ}
    (hg : (slab c m 7 P A N).Valid g) (b : ℕ) :
    ((opt6b c 7 P A N v g b).card : ℚ) ≤
      (if o6s (P := P) (A := A) (N := N) v g b then 1 + 1 / 3 else 1) *
        (opt6' c 7 P A N v x₀ g).card := by
  by_cases h : 2 ≤ c
  · have ho : o6s (P := P) (A := A) (N := N) v g b ↔
        b ∉ (slab c m 7 P A N).avail (boxB c v) g (y₆ h v) := by simp [o6s, h]
    simp only [opt6b, opt6', dite_eq_left h, card_map]
    have hav := card_avail_fut_ge hK hg (y₆_inY h v).1 (show 2 ≤ (y₆ h v).1.val by
      show 2 ≤ 3; omega)
    have hn := nbrsOut_y₆ (k := 7) (P := P) (A := A) (N := N) h v
    have hlow := pred_card_le_card_erase (s := (slab c m 7 P A N).avail (boxB c v) g (y₆ h v))
      (a := x₀)
    by_cases hb : b ∈ (slab c m 7 P A N).avail (boxB c v) g (y₆ h v)
    · rw [ite_eq_right (by rw [ho]; exact not_not.mpr hb), one_mul, card_erase_of_mem hb]
      exact_mod_cast hlow
    · rw [ite_eq_left (by rw [ho]; exact hb), erase_eq_of_notMem hb]
      have h3 : 3 * ((slab c m 7 P A N).avail (boxB c v) g (y₆ h v)).card ≤
          4 * (((slab c m 7 P A N).avail (boxB c v) g (y₆ h v)).erase x₀).card := by omega
      have := (Nat.cast_le (α := ℚ)).mpr h3
      push_cast at this
      linarith
  · simp only [opt6b, opt6', o6s, dite_eq_right h, card_singleton, Nat.cast_one]; norm_num

/-- **The nested outsider sum**, for ratio factors `1 + α`, `β + γ` off and `1`, `β` on. -/
theorem nested_gen (T : Finset ℕ) (hT : T.card ≤ 6) (o6 oU oD : ℕ → Prop) [DecidablePred o6]
    [DecidablePred oU] [DecidablePred oD] (h6 : (T.filter o6).card ≤ 3)
    (hU : (T.filter oU).card ≤ 2) (hD : (T.filter oD).card ≤ 2) {α β γ : ℚ} (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) :
    ∑ b ∈ T, (if o6 b then 1 + α else 1) * (if oU b then β + γ else β) *
      (if oD b then β + γ else β) ≤
        6 * β ^ 2 + 3 * (α * β ^ 2) + 4 * (β * γ) + 4 * (α * β * γ) + 2 * γ ^ 2 +
          2 * (α * γ ^ 2) := by
  set I6 : ℕ → ℚ := fun b => if o6 b then 1 else 0
  set IU : ℕ → ℚ := fun b => if oU b then 1 else 0
  set ID : ℕ → ℚ := fun b => if oD b then 1 else 0
  have e : ∀ b, (if o6 b then 1 + α else 1) * (if oU b then β + γ else β) *
      (if oD b then β + γ else β) = β ^ 2 + α * β ^ 2 * I6 b + β * γ * IU b + β * γ * ID b +
        α * β * γ * (I6 b * IU b) + α * β * γ * (I6 b * ID b) + γ ^ 2 * (IU b * ID b) +
          α * γ ^ 2 * (I6 b * (IU b * ID b)) := by
    intro b; simp only [I6, IU, ID]; split_ifs <;> ring
  have hI : ∀ (o : ℕ → Prop) [DecidablePred o], ∑ b ∈ T, (if o b then (1 : ℚ) else 0) =
      (T.filter o).card := by
    intro o _; rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
  have s6 : ∑ b ∈ T, I6 b ≤ 3 := by rw [hI o6]; exact_mod_cast h6
  have sU : ∑ b ∈ T, IU b ≤ 2 := by rw [hI oU]; exact_mod_cast hU
  have sD : ∑ b ∈ T, ID b ≤ 2 := by rw [hI oD]; exact_mod_cast hD
  have b01 : ∀ (I : ℕ → ℚ), (∀ b, I b = 0 ∨ I b = 1) → ∀ b, 0 ≤ I b ∧ I b ≤ 1 := by
    intro I h b; rcases h b with h | h <;> rw [h] <;> norm_num
  have i6 := b01 I6 (fun b => by simp only [I6]; split_ifs <;> simp)
  have iU := b01 IU (fun b => by simp only [IU]; split_ifs <;> simp)
  have iD := b01 ID (fun b => by simp only [ID]; split_ifs <;> simp)
  have p1 : ∑ b ∈ T, I6 b * IU b ≤ 2 := le_trans (sum_le_sum fun b _ =>
    mul_le_of_le_one_left (iU b).1 (i6 b).2) sU
  have p2 : ∑ b ∈ T, I6 b * ID b ≤ 2 := le_trans (sum_le_sum fun b _ =>
    mul_le_of_le_one_left (iD b).1 (i6 b).2) sD
  have p3 : ∑ b ∈ T, IU b * ID b ≤ 2 := le_trans (sum_le_sum fun b _ =>
    mul_le_of_le_one_left (iD b).1 (iU b).2) sD
  have p4 : ∑ b ∈ T, I6 b * (IU b * ID b) ≤ 2 := le_trans (sum_le_sum fun b _ =>
    mul_le_of_le_one_left (mul_nonneg (iU b).1 (iD b).1) (i6 b).2) p3
  have hTq : (T.card : ℚ) ≤ 6 := by exact_mod_cast hT
  rw [sum_congr rfl fun b _ => e b]
  simp only [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
  have k0 := mul_le_mul_of_nonneg_left hTq (sq_nonneg β)
  have k1 := mul_le_mul_of_nonneg_left s6 (by positivity : 0 ≤ α * β ^ 2)
  have k2 := mul_le_mul_of_nonneg_left sU (by positivity : 0 ≤ β * γ)
  have k3 := mul_le_mul_of_nonneg_left sD (by positivity : 0 ≤ β * γ)
  have k4 := mul_le_mul_of_nonneg_left p1 (by positivity : 0 ≤ α * β * γ)
  have k5 := mul_le_mul_of_nonneg_left p2 (by positivity : 0 ≤ α * β * γ)
  have k6 := mul_le_mul_of_nonneg_left p3 (by positivity : 0 ≤ γ ^ 2)
  have k7 := mul_le_mul_of_nonneg_left p4 (by positivity : 0 ≤ α * γ ^ 2)
  linarith

end Seven

/-! ### The box bound -/

section SevenFibre

theorem card_o6s_le (hK : KeyInj 7 A N) (v : Fin m) {g : Cell c m → ℕ}
    (hg : (slab c m 7 P A N).Valid g) :
    ((range 7).filter (o6s (P := P) (A := A) (N := N) v g)).card ≤ 3 := by
  by_cases h : 2 ≤ c
  · have e : (range 7).filter (o6s (P := P) (A := A) (N := N) v g) =
        (range 7).filter (fun b => b ∉ (slab c m 7 P A N).avail (boxB c v) g (y₆ h v)) := by
      ext b; simp only [mem_filter, o6s, dite_eq_left h]
    rw [e]
    exact card_unavail_le7 hK hg (y₆_inY h v).1 (show 2 ≤ (y₆ h v).1.val by show 2 ≤ 3; omega)
      (nbrsOut_y₆ h v)
  · have e : (range 7).filter (o6s (P := P) (A := A) (N := N) v g) = ∅ := by
      ext b; simp [o6s, h]
    rw [e]; simp

theorem card_oUs_le (hK : KeyInj 7 A N) (hc : 1 ≤ c) (v : Fin m) {g : Cell c m → ℕ}
    (hg : (slab c m 7 P A N).Valid g) :
    ((range 7).filter (oUs (P := P) (A := A) (N := N) hc v g)).card ≤ 2 := by
  by_cases h : 1 ≤ v.val
  · have e : (range 7).filter (oUs (P := P) (A := A) (N := N) hc v g) =
        (range 7).filter (fun b => b ∉ (slab c m 7 P A N).avail (boxB c v) g (yU₂ hc h)) := by
      ext b; simp only [mem_filter, oUs, dite_eq_left h]
    rw [e]
    exact card_unavail_le7 hK hg (yU₂_inY hc h).1 le_rfl (nbrsOut_yU₂ hc h)
  · have e : (range 7).filter (oUs (P := P) (A := A) (N := N) hc v g) = ∅ := by
      ext b; simp [oUs, h]
    rw [e]; simp

theorem card_oDs_le (hK : KeyInj 7 A N) (hc : 1 ≤ c) (v : Fin m) {g : Cell c m → ℕ}
    (hg : (slab c m 7 P A N).Valid g) :
    ((range 7).filter (oDs (P := P) (A := A) (N := N) hc v g)).card ≤ 2 := by
  by_cases h : v.val + 1 < m
  · have e : (range 7).filter (oDs (P := P) (A := A) (N := N) hc v g) =
        (range 7).filter (fun b => b ∉ (slab c m 7 P A N).avail (boxB c v) g (yD₂ hc h)) := by
      ext b; simp only [mem_filter, oDs, dite_eq_left h]
    rw [e]
    exact card_unavail_le7 hK hg (yD₂_inY hc h).1 le_rfl (nbrsOut_yD₂ hc h)
  · have e : (range 7).filter (oDs (P := P) (A := A) (N := N) hc v g) = ∅ := by
      ext b; simp [oDs, h]
    rw [e]; simp

/-- **The label sum at any seam value `a`**: `768/432` at `b = x₀` and `7285/432` off it. -/
theorem inner_any7 (hK : KeyInj 7 A N) (hA : ∀ v, (A v).card = 7) (hc : 1 ≤ c) (v : Fin m)
    {x₀ : ℕ} (hx : x₀ < 7) {g : Cell c m → ℕ} (hg : (slab c m 7 P A N).Valid g) (a a₀ : ℕ) :
    ∑ b ∈ range 7, ((opt6b c 7 P A N v g b).card : ℚ) * (optU' c 7 P A N hc v a b g).card *
        (optD' c 7 P A N hc v a b g).card ≤
      8053 / 432 * (((opt6' c 7 P A N v x₀ g).card : ℚ) *
        (optU' c 7 P A N hc v a₀ x₀ g).card * (optD' c 7 P A N hc v a₀ x₀ g).card) := by
  set s₆ : ℚ := ((opt6' c 7 P A N v x₀ g).card : ℚ)
  set sU : ℚ := ((optU' c 7 P A N hc v a₀ x₀ g).card : ℚ)
  set sD : ℚ := ((optD' c 7 P A N hc v a₀ x₀ g).card : ℚ)
  have hs6 : (0 : ℚ) ≤ s₆ := by positivity
  have hsU : (0 : ℚ) ≤ sU := by positivity
  have hsD : (0 : ℚ) ≤ sD := by positivity
  set T := (range 7).erase x₀
  have hT : T.card ≤ 6 := by rw [card_erase_of_mem (mem_range.mpr hx), card_range]
  have h6 := le_trans (card_le_card (filter_subset_filter (o6s (P := P) (A := A) (N := N) v g)
    (erase_subset x₀ (range 7)))) (card_o6s_le hK v hg)
  have hU := le_trans (card_le_card (filter_subset_filter (oUs (P := P) (A := A) (N := N) hc v g)
    (erase_subset x₀ (range 7)))) (card_oUs_le hK hc v hg)
  have hD := le_trans (card_le_card (filter_subset_filter (oDs (P := P) (A := A) (N := N) hc v g)
    (erase_subset x₀ (range 7)))) (card_oDs_le hK hc v hg)
  have hnest := le_trans (nested_gen T hT _ _ _ h6 hU hD (α := 1 / 3) (β := 17 / 12)
    (γ := 1 / 3) (by norm_num) (by norm_num) (by norm_num)) (show _ ≤ (7285 / 432 : ℚ) by norm_num)
  rw [← add_sum_erase _ _ (mem_range.mpr hx)]
  have hx₀ : ((opt6b c 7 P A N v g x₀).card : ℚ) * (optU' c 7 P A N hc v a x₀ g).card *
      (optD' c 7 P A N hc v a x₀ g).card ≤ 16 / 9 * (s₆ * sU * sD) := by
    have e2 := U_any7 hK hA hc v hg a x₀ a₀ x₀
    have e3 := D_any7 hK hA hc v hg a x₀ a₀ x₀
    rw [ite_eq_left rfl] at e2 e3
    have e6 : opt6b c 7 P A N v g x₀ = opt6' c 7 P A N v x₀ g := rfl
    rw [e6]
    calc _ ≤ s₆ * (4 / 3 * sU) * (4 / 3 * sD) := by gcongr
      _ = _ := by ring
  have hrest : ∑ b ∈ T, ((opt6b c 7 P A N v g b).card : ℚ) * (optU' c 7 P A N hc v a b g).card *
      (optD' c 7 P A N hc v a b g).card ≤
        (∑ b ∈ T, (if o6s (P := P) (A := A) (N := N) v g b then 1 + 1 / 3 else 1) *
          (if oUs (P := P) (A := A) (N := N) hc v g b then 17 / 12 + 1 / 3 else 17 / 12) *
          (if oDs (P := P) (A := A) (N := N) hc v g b then 17 / 12 + 1 / 3 else 17 / 12)) *
            (s₆ * sU * sD) := by
    rw [sum_mul]
    refine sum_le_sum fun b hb => ?_
    have hbx : b ≠ x₀ := ne_of_mem_erase hb
    have e1 := y6_seven hK v (x₀ := x₀) hg b
    have e2 := U_any7 hK hA hc v hg a b a₀ x₀
    have e3 := D_any7 hK hA hc v hg a b a₀ x₀
    rw [ite_eq_right hbx] at e2 e3
    calc _ ≤ ((if o6s (P := P) (A := A) (N := N) v g b then 1 + 1 / 3 else 1) * s₆) *
          ((if oUs (P := P) (A := A) (N := N) hc v g b then 17 / 12 + 1 / 3 else 17 / 12) * sU) *
          ((if oDs (P := P) (A := A) (N := N) hc v g b then 17 / 12 + 1 / 3 else 17 / 12) * sD) := by
          gcongr
      _ = _ := by ring
  have hP : (0 : ℚ) ≤ s₆ * sU * sD := by positivity
  have := mul_le_mul_of_nonneg_right hnest hP
  linarith

/-- **The label sum at the star value `a₀`**: `432/432` at `b = x₀` and `4245/432` off it. -/
theorem inner_star7 (hK : KeyInj 7 A N) (hA : ∀ v, (A v).card = 7) (hc : 1 ≤ c) (v : Fin m)
    {x₀ : ℕ} (hx : x₀ < 7) {g : Cell c m → ℕ} (hg : (slab c m 7 P A N).Valid g) (a₀ : ℕ) :
    ∑ b ∈ range 7, ((opt6b c 7 P A N v g b).card : ℚ) * (optU' c 7 P A N hc v a₀ b g).card *
        (optD' c 7 P A N hc v a₀ b g).card ≤
      4677 / 432 * (((opt6' c 7 P A N v x₀ g).card : ℚ) *
        (optU' c 7 P A N hc v a₀ x₀ g).card * (optD' c 7 P A N hc v a₀ x₀ g).card) := by
  set s₆ : ℚ := ((opt6' c 7 P A N v x₀ g).card : ℚ)
  set sU : ℚ := ((optU' c 7 P A N hc v a₀ x₀ g).card : ℚ)
  set sD : ℚ := ((optD' c 7 P A N hc v a₀ x₀ g).card : ℚ)
  have hs6 : (0 : ℚ) ≤ s₆ := by positivity
  have hsU : (0 : ℚ) ≤ sU := by positivity
  have hsD : (0 : ℚ) ≤ sD := by positivity
  set T := (range 7).erase x₀
  have hT : T.card ≤ 6 := by rw [card_erase_of_mem (mem_range.mpr hx), card_range]
  have h6 := le_trans (card_le_card (filter_subset_filter (o6s (P := P) (A := A) (N := N) v g)
    (erase_subset x₀ (range 7)))) (card_o6s_le hK v hg)
  have hU := le_trans (card_le_card (filter_subset_filter (oUs (P := P) (A := A) (N := N) hc v g)
    (erase_subset x₀ (range 7)))) (card_oUs_le hK hc v hg)
  have hD := le_trans (card_le_card (filter_subset_filter (oDs (P := P) (A := A) (N := N) hc v g)
    (erase_subset x₀ (range 7)))) (card_oDs_le hK hc v hg)
  have hnest := le_trans (nested_gen T hT _ _ _ h6 hU hD (α := 1 / 3) (β := 13 / 12)
    (γ := 1 / 4) (by norm_num) (by norm_num) (by norm_num)) (show _ ≤ (4245 / 432 : ℚ) by norm_num)
  rw [← add_sum_erase _ _ (mem_range.mpr hx)]
  have hx₀ : ((opt6b c 7 P A N v g x₀).card : ℚ) * (optU' c 7 P A N hc v a₀ x₀ g).card *
      (optD' c 7 P A N hc v a₀ x₀ g).card = s₆ * sU * sD := rfl
  have hrest : ∑ b ∈ T, ((opt6b c 7 P A N v g b).card : ℚ) * (optU' c 7 P A N hc v a₀ b g).card *
      (optD' c 7 P A N hc v a₀ b g).card ≤
        (∑ b ∈ T, (if o6s (P := P) (A := A) (N := N) v g b then 1 + 1 / 3 else 1) *
          (if oUs (P := P) (A := A) (N := N) hc v g b then 13 / 12 + 1 / 4 else 13 / 12) *
          (if oDs (P := P) (A := A) (N := N) hc v g b then 13 / 12 + 1 / 4 else 13 / 12)) *
            (s₆ * sU * sD) := by
    rw [sum_mul]
    refine sum_le_sum fun b hb => ?_
    have hbx : b ≠ x₀ := ne_of_mem_erase hb
    have e1 := y6_seven hK v (x₀ := x₀) hg b
    have e2 := U_star7 hK hA hc v hg b a₀ x₀
    have e3 := D_star7 hK hA hc v hg b a₀ x₀
    rw [ite_eq_right hbx] at e2 e3
    calc _ ≤ ((if o6s (P := P) (A := A) (N := N) v g b then 1 + 1 / 3 else 1) * s₆) *
          ((if oUs (P := P) (A := A) (N := N) hc v g b then 13 / 12 + 1 / 4 else 13 / 12) * sU) *
          ((if oDs (P := P) (A := A) (N := N) hc v g b then 13 / 12 + 1 / 4 else 13 / 12) * sD) := by
          gcongr
      _ = _ := by ring
  have hP : (0 : ℚ) ≤ s₆ * sU * sD := by positivity
  have := mul_le_mul_of_nonneg_right hnest hP
  linarith

/-- **The refined box inequality on one fibre** (`k = 7`). -/
theorem box_fibre_seven (hK : KeyInj 7 A N) (hA : ∀ v, (A v).card = 7) (hc : 1 ≤ c)
    (v : Fin m) {a₀ x₀ : ℕ} (ha : a₀ ∈ A v) (hx : x₀ < 7) (hN : 7 ≤ N v a₀)
    (hPv : 6 ≤ (P v).card ∨ a₀ ∉ P v) {g : Cell c m → ℕ}
    (hg : (slab c m 7 P A N).Valid g) :
    (((slab c m 7 P A N).cls (boxB c v) g).card : ℚ) * 432 ≤
      ((((slab c m 7 P A N).cls (boxB c v) g).filter (Hit hc v a₀ x₀)).card : ℚ) * 69101 := by
  set C := slab c m 7 P A N
  have h₁ := y1_seven (P := P) hK v hPv hg
  set s₁ := ((C.avail (boxB c v) g (y₁ v)).erase a₀).card
  set s₆ := (opt6' c 7 P A N v x₀ g).card
  set sU := (optU' c 7 P A N hc v a₀ x₀ g).card
  set sD := (optD' c 7 P A N hc v a₀ x₀ g).card
  have hup := card_cls_le_sum7 (k := 7) (P := P) (A := A) (N := N) hc v g
  have hlo := card_hit_ge (P := P) hc v hg ha hx hN
  have hcls : (((slab c m 7 P A N).cls (boxB c v) g).card : ℚ) ≤
      ∑ a ∈ A v, (((C.avail (boxB c v) g (y₁ v)).erase a).card : ℚ) *
        ∑ b ∈ range 7, ((opt6b c 7 P A N v g b).card : ℚ) * (optU' c 7 P A N hc v a b g).card *
          (optD' c 7 P A N hc v a b g).card := by
    have := (Nat.cast_le (α := ℚ)).mpr hup
    push_cast at this
    refine le_trans this (le_of_eq (sum_congr rfl fun a _ => ?_))
    rw [mul_sum]
    exact sum_congr rfl fun b _ => by ring
  rw [← add_sum_erase _ _ ha] at hcls
  have hP : (0 : ℚ) ≤ (s₆ : ℚ) * sU * sD := by positivity
  have hstar : (s₁ : ℚ) * ∑ b ∈ range 7, ((opt6b c 7 P A N v g b).card : ℚ) *
      (optU' c 7 P A N hc v a₀ b g).card * (optD' c 7 P A N hc v a₀ b g).card ≤
        (s₁ : ℚ) * (4677 / 432 * ((s₆ : ℚ) * sU * sD)) :=
    mul_le_mul_of_nonneg_left (inner_star7 hK hA hc v hx hg a₀) (by positivity)
  have hy1 : ∀ a, (((C.avail (boxB c v) g (y₁ v)).erase a).card : ℚ) ≤ 4 / 3 * s₁ := by
    intro a
    have h1 := (Nat.cast_le (α := ℚ)).mpr (le_trans (Nat.mul_le_mul_left 3
      (card_erase_le (s := C.avail (boxB c v) g (y₁ v)) (a := a))) h₁)
    push_cast at h1
    linarith
  have hothers : ∑ a ∈ (A v).erase a₀, (((C.avail (boxB c v) g (y₁ v)).erase a).card : ℚ) *
      ∑ b ∈ range 7, ((opt6b c 7 P A N v g b).card : ℚ) * (optU' c 7 P A N hc v a b g).card *
        (optD' c 7 P A N hc v a b g).card ≤
          ∑ _a ∈ (A v).erase a₀, (4 / 3 * (s₁ : ℚ)) * (8053 / 432 * ((s₆ : ℚ) * sU * sD)) :=
    sum_le_sum fun a _ => mul_le_mul (hy1 a) (inner_any7 hK hA hc v hx hg a a₀)
      (sum_nonneg fun b _ => by positivity) (by positivity)
  have hcard : ((A v).erase a₀).card = 6 := by rw [card_erase_of_mem ha, hA]
  rw [sum_const, hcard, nsmul_eq_mul] at hothers
  have hlo' : (s₁ : ℚ) * s₆ * sU * sD ≤
      ((((slab c m 7 P A N).cls (boxB c v) g).filter (Hit hc v a₀ x₀)).card : ℚ) := by
    exact_mod_cast hlo
  push_cast at hothers
  linarith

/-- **The refined box bound** (`k = 7`): a `432/69101` fraction of the slab solutions puts the
unpaired colour `a₀` at `(1, v)` and `x₀` at `(2, v)`. -/
theorem box_bound_seven (hK : KeyInj 7 A N) (hA : ∀ v, (A v).card = 7) (hc : 1 ≤ c)
    (v : Fin m) {a₀ x₀ : ℕ} (ha : a₀ ∈ A v) (hx : x₀ < 7) (hN : 7 ≤ N v a₀)
    (hPv : 6 ≤ (P v).card ∨ a₀ ∉ P v) :
    (slab c m 7 P A N).Ω.card * 432 ≤
      ((slab c m 7 P A N).Ω.filter (Hit hc v a₀ x₀)).card * 69101 :=
  (slab c m 7 P A N).fibre_sum_ge (boxB c v) _ _ _ fun _ hg => by
    have := box_fibre_seven hK hA hc v ha hx hN hPv ((CSP.mem_Ω _).mp hg)
    exact_mod_cast this

end SevenFibre

end GridGen.Gauge
