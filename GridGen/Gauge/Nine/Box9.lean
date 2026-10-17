/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Seam

/-!
# The refined box bound at `k = 9`

`GridGen.Gauge.box_bound` gives every pair `(a, b)` of centre values the worst factor. Here the
fibre is split by the centre values, and each factor is bounded by what the pair allows:

* `y₁`: `|avail₁ \ {a}|`, which is the lower-bound factor itself for `a = a₀`;
* `y₆`: `α₆ - 1` when `b` is available at `y₆` (ratio `1`), `α₆` otherwise (ratio `6/5`);
* a domino: `τ - (α₂ - 1)` when `b` is available at its future cell (ratio `9/7`), `τ` otherwise
  (ratio `3/2`).

At most `3, 2, 2` labels are unavailable at `y₆` and at the two dominoes. Expanding the product
of the three ratio factors and summing over the nine labels gives at most `8478/490`. The `y₁`
factors sum to at most `1 + 8 · 6/5 = 53/5`. Hence a `2450/449334` fraction of the solutions is
hit (`box_bound_nine`), against `400/104976` for the uniform bound.
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m k : ℕ} {P A : Fin m → Finset ℕ} {N : Fin m → ℕ → ℕ}

/-! ### The fibre, split by the centre values -/

theorem boxVals_injOn (hc : 1 ≤ c) (v : Fin m) (g : Cell c m → ℕ) :
    Set.InjOn (boxVals hc v) ((slab c m k P A N).cls (boxB c v) g) := by
  intro f hf f' hf' he
  simp only [boxVals, Prod.mk.injEq] at he
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := he
  have hf1 := (CSP.mem_cls _).mp hf
  have hf1' := (CSP.mem_cls _).mp hf'
  funext y
  by_cases hB : y ∈ boxB c v
  · rcases (inB_iff hc).mp (mem_boxB.mp hB) with hY | rfl | rfl
    · rcases inY_cases hc hY with rfl | ⟨h, rfl⟩ | ⟨h, rfl | rfl⟩ | ⟨h, rfl | rfl⟩
      · exact e3
      · simp only [dite_eq_left h, Option.some.injEq] at e4; exact e4
      · simp only [dite_eq_left h, Option.some.injEq, Prod.mk.injEq] at e5; exact e5.1
      · simp only [dite_eq_left h, Option.some.injEq, Prod.mk.injEq] at e5; exact e5.2
      · simp only [dite_eq_left h, Option.some.injEq, Prod.mk.injEq] at e6; exact e6.1
      · simp only [dite_eq_left h, Option.some.injEq, Prod.mk.injEq] at e6; exact e6.2
    · exact e1
    · exact e2
  · rw [hf1.2 y hB, hf1'.2 y hB]

section Split

variable (c k P A N) in
/-- Options at `y₆` avoiding the label `b` of `z₂`. -/
noncomputable def opt6b (v : Fin m) (g : Cell c m → ℕ) (b : ℕ) : Finset (Option ℕ) :=
  if h : 2 ≤ c then (((slab c m k P A N).avail (boxB c v) g (y₆ h v)).erase b).map
    Function.Embedding.some else {none}

variable (c k P A N) in
/-- Options on the upper domino whose future cell avoids `b`. -/
noncomputable def optUb (hc : 1 ≤ c) (v : Fin m) (g : Cell c m → ℕ) (b : ℕ) :
    Finset (Option (ℕ × ℕ)) :=
  if h : 1 ≤ v.val then ((dom c k P A N (boxB c v) g (yU₁ h) (yU₂ hc h)).filter
    (fun pq => pq.2 ≠ b)).map Function.Embedding.some else {none}

variable (c k P A N) in
/-- Options on the lower domino whose future cell avoids `b`. -/
noncomputable def optDb (hc : 1 ≤ c) (v : Fin m) (g : Cell c m → ℕ) (b : ℕ) :
    Finset (Option (ℕ × ℕ)) :=
  if h : v.val + 1 < m then ((dom c k P A N (boxB c v) g (yD₁ h) (yD₂ hc h)).filter
    (fun pq => pq.2 ≠ b)).map Function.Embedding.some else {none}

theorem ne_of_eq_adj {f : Cell c m → ℕ} (hf : (slab c m k P A N).Valid f)
    {x y : Cell c m} (h : slabAdj x y) (h1 : ¬ (x.1.val = 1 ∧ y.1.val = 2))
    (h2 : ¬ (x.1.val = 2 ∧ y.1.val = 1)) : f x ≠ f y := by
  have := hf.2 x y h
  rwa [slab_conf_eq h1 h2] at this

/-- **The fibre over fixed centre values.** -/
theorem card_cls_ab_le (hc : 1 ≤ c) (v : Fin m) (g : Cell c m → ℕ) (a b : ℕ) :
    (((slab c m k P A N).cls (boxB c v) g).filter
        (fun f => f (z₁ v) = a ∧ f (z₂ hc v) = b)).card ≤
      (((slab c m k P A N).avail (boxB c v) g (y₁ v)).erase a).card *
        (opt6b c k P A N v g b).card * (optUb c k P A N hc v g b).card *
          (optDb c k P A N hc v g b).card := by
  set C := slab c m k P A N
  have h1v : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  have hT : ({a} ×ˢ {b} ×ˢ (C.avail (boxB c v) g (y₁ v)).erase a ×ˢ opt6b c k P A N v g b ×ˢ
      optUb c k P A N hc v g b ×ˢ optDb c k P A N hc v g b).card =
        ((C.avail (boxB c v) g (y₁ v)).erase a).card * (opt6b c k P A N v g b).card *
          (optUb c k P A N hc v g b).card * (optDb c k P A N hc v g b).card := by
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
  · unfold optUb
    split_ifs with h
    · refine mem_map_of_mem _ (mem_filter.mpr ⟨mem_dom_of_valid hf (mem_boxB.mpr (yU₁_inY h).1)
        (mem_boxB.mpr (yU₂_inY hc h).1) (slabAdj_dom₁ hc h), fun e => ?_⟩)
      refine ne_of_eq_adj hv (x := yU₂ hc h) (y := z₂ hc v) (Or.inl ⟨rfl, Or.inl ?_⟩) ?_ ?_
        (e.trans hb.symm)
      · show v.val - 1 + 1 = v.val; omega
      · show ¬ ((2 : ℕ) = 1 ∧ _); simp
      · show ¬ (_ ∧ (2 : ℕ) = 1); simp
    · exact mem_singleton_self _
  · unfold optDb
    split_ifs with h
    · refine mem_map_of_mem _ (mem_filter.mpr ⟨mem_dom_of_valid hf (mem_boxB.mpr (yD₁_inY h).1)
        (mem_boxB.mpr (yD₂_inY hc h).1) (slabAdj_dom₂ hc h), fun e => ?_⟩)
      refine ne_of_eq_adj hv (x := yD₂ hc h) (y := z₂ hc v) (Or.inl ⟨rfl, Or.inr ?_⟩) ?_ ?_
        (e.trans hb.symm)
      · show v.val + 1 = v.val + 1; rfl
      · show ¬ ((2 : ℕ) = 1 ∧ _); simp
      · show ¬ (_ ∧ (2 : ℕ) = 1); simp
    · exact mem_singleton_self _

/-- **The fibre, summed over the centre values.** -/
theorem card_cls_le_sum (hc : 1 ≤ c) (v : Fin m) (g : Cell c m → ℕ) :
    ((slab c m k P A N).cls (boxB c v) g).card ≤ ∑ a ∈ A v, ∑ b ∈ range k,
      (((slab c m k P A N).avail (boxB c v) g (y₁ v)).erase a).card *
        (opt6b c k P A N v g b).card * (optUb c k P A N hc v g b).card *
          (optDb c k P A N hc v g b).card := by
  set C := slab c m k P A N
  rw [card_eq_sum_card_fiberwise (f := fun f => (f (z₁ v), f (z₂ hc v))) (t := A v ×ˢ range k)]
  · rw [sum_product]
    refine sum_le_sum fun a _ => sum_le_sum fun b _ => le_trans (le_of_eq ?_)
      (card_cls_ab_le hc v g a b)
    congr 1
  · intro f hf
    have hv := ((CSP.mem_cls _).mp hf).1
    rw [mem_coe, mem_product]
    refine ⟨?_, ?_⟩
    · have := hv.1 (z₁ v); rwa [slab_D_one (z₁_fst v)] at this
    · have := hv.1 (z₂ hc v); rwa [slab_D_fut (by rw [z₂_fst])] at this

end Split

/-! ### The ratio factors at `k = 9` -/

section Nine

/-- Pairs of a domino whose future cell carries a given available label: all but at most one
colour of the seam cell. -/
theorem card_dom_eq_ge (hK : KeyInj k A N) {U : Finset (Cell c m)} {g : Cell c m → ℕ}
    {y y' : Cell c m} {b : ℕ} (hb : b ∈ (slab c m k P A N).avail U g y') :
    ((slab c m k P A N).avail U g y).card +
        ((dom c k P A N U g y y').filter (fun pq => pq.2 ≠ b)).card ≤
      (dom c k P A N U g y y').card + 1 := by
  set C := slab c m k P A N
  have hbad : ((C.avail U g y).filter (fun p => ¬ (¬ C.conf y y' p b ∧ ¬ C.conf y' y b p))).card
      ≤ 1 := by
    refine card_le_one.mpr fun p hp p' hp' => ?_
    rw [mem_filter] at hp hp'
    have hbD := (C.mem_avail.mp hb).1
    refine slab_match hK y y' b hbD p p' (C.mem_avail.mp hp.1).1 (C.mem_avail.mp hp'.1).1 ?_ ?_
    · by_contra hn; push Not at hn; exact hp.2 ⟨hn.1, hn.2⟩
    · by_contra hn; push Not at hn; exact hp'.2 ⟨hn.1, hn.2⟩
  have hsplit := card_filter_add_card_filter_not (s := C.avail U g y)
    (fun p => ¬ C.conf y y' p b ∧ ¬ C.conf y' y b p)
  have hsplit2 := card_filter_add_card_filter_not (s := dom c k P A N U g y y')
    (fun pq => pq.2 = b)
  have himg : ((C.avail U g y).filter (fun p => ¬ C.conf y y' p b ∧ ¬ C.conf y' y b p)).card ≤
      ((dom c k P A N U g y y').filter (fun pq => pq.2 = b)).card := by
    refine card_le_card_of_injOn (fun p => (p, b)) (fun p hp => ?_) (fun p _ p' _ e => by
      simpa using e)
    rw [mem_coe, mem_filter] at hp
    rw [mem_coe, mem_filter, mem_dom_iff]
    exact ⟨⟨⟨hp.1, hb⟩, hp.2⟩, rfl⟩
  have e : (dom c k P A N U g y y').filter (fun pq => ¬ pq.2 = b) =
      (dom c k P A N U g y y').filter (fun pq => pq.2 ≠ b) := rfl
  rw [e] at hsplit2
  omega

theorem dom_in_arith {α₂ α₃ τ u s : ℕ} (h2 : 7 ≤ α₂) (h3 : 7 ≤ α₃) (hτ : α₂ * (α₃ - 1) ≤ τ)
    (hu : u + α₂ ≤ τ + 1) (hs : τ ≤ s + α₃ + α₂) : 7 * u ≤ 9 * s := by
  obtain ⟨p, rfl⟩ : ∃ p, α₂ = 7 + p := ⟨α₂ - 7, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, α₃ = 7 + q := ⟨α₃ - 7, by omega⟩
  have e : (7 + p) * (7 + q - 1) = 42 + 6 * p + 7 * q + p * q := by
    rw [show 7 + q - 1 = 6 + q by omega]; ring
  rw [e] at hτ
  nlinarith

theorem dom_out_arith {α₂ α₃ τ u s : ℕ} (h2 : 7 ≤ α₂) (h3 : 7 ≤ α₃) (hτ : α₂ * (α₃ - 1) ≤ τ)
    (hu : u ≤ τ) (hs : τ ≤ s + α₃ + α₂) : 2 * u ≤ 3 * s := by
  obtain ⟨p, rfl⟩ : ∃ p, α₂ = 7 + p := ⟨α₂ - 7, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, α₃ = 7 + q := ⟨α₃ - 7, by omega⟩
  have e : (7 + p) * (7 + q - 1) = 42 + 6 * p + 7 * q + p * q := by
    rw [show 7 + q - 1 = 6 + q by omega]; ring
  rw [e] at hτ
  nlinarith

/-- The nested outsider sum. -/
theorem nested_sum (o6 oU oD : ℕ → Prop) [DecidablePred o6] [DecidablePred oU]
    [DecidablePred oD] (h6 : ((range 9).filter o6).card ≤ 3) (hU : ((range 9).filter oU).card ≤ 2)
    (hD : ((range 9).filter oD).card ≤ 2) :
    ∑ b ∈ range 9, (if o6 b then (6 / 5 : ℚ) else 1) * (if oU b then (3 / 2 : ℚ) else 9 / 7) *
      (if oD b then (3 / 2 : ℚ) else 9 / 7) ≤ 8478 / 490 := by
  set I6 : ℕ → ℚ := fun b => if o6 b then 1 else 0
  set IU : ℕ → ℚ := fun b => if oU b then 1 else 0
  set ID : ℕ → ℚ := fun b => if oD b then 1 else 0
  have e : ∀ b, (if o6 b then (6 / 5 : ℚ) else 1) * (if oU b then (3 / 2 : ℚ) else 9 / 7) *
      (if oD b then (3 / 2 : ℚ) else 9 / 7) = 81 / 49 + 81 / 245 * I6 b + 27 / 98 * IU b +
        27 / 98 * ID b + 27 / 490 * (I6 b * IU b) + 27 / 490 * (I6 b * ID b) +
          9 / 196 * (IU b * ID b) + 9 / 980 * (I6 b * (IU b * ID b)) := by
    intro b; simp only [I6, IU, ID]; split_ifs <;> norm_num
  have hI : ∀ (o : ℕ → Prop) [DecidablePred o], ∑ b ∈ range 9, (if o b then (1 : ℚ) else 0) =
      ((range 9).filter o).card := by
    intro o _; rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
  have s6 : ∑ b ∈ range 9, I6 b ≤ 3 := by rw [hI o6]; exact_mod_cast h6
  have sU : ∑ b ∈ range 9, IU b ≤ 2 := by rw [hI oU]; exact_mod_cast hU
  have sD : ∑ b ∈ range 9, ID b ≤ 2 := by rw [hI oD]; exact_mod_cast hD
  have b01 : ∀ (I : ℕ → ℚ), (∀ b, I b = 0 ∨ I b = 1) → ∀ b, 0 ≤ I b ∧ I b ≤ 1 := by
    intro I h b; rcases h b with h | h <;> rw [h] <;> norm_num
  have i6 := b01 I6 (fun b => by simp only [I6]; split_ifs <;> simp)
  have iU := b01 IU (fun b => by simp only [IU]; split_ifs <;> simp)
  have iD := b01 ID (fun b => by simp only [ID]; split_ifs <;> simp)
  have p1 : ∑ b ∈ range 9, I6 b * IU b ≤ 2 := le_trans (sum_le_sum fun b _ =>
    mul_le_of_le_one_left (iU b).1 (i6 b).2) sU
  have p2 : ∑ b ∈ range 9, I6 b * ID b ≤ 2 := le_trans (sum_le_sum fun b _ =>
    mul_le_of_le_one_left (iD b).1 (i6 b).2) sD
  have p3 : ∑ b ∈ range 9, IU b * ID b ≤ 2 := le_trans (sum_le_sum fun b _ =>
    mul_le_of_le_one_left (iD b).1 (iU b).2) sD
  have p4 : ∑ b ∈ range 9, I6 b * (IU b * ID b) ≤ 2 := le_trans (sum_le_sum fun b _ =>
    mul_le_of_le_one_left (mul_nonneg (iU b).1 (iD b).1) (i6 b).2) p3
  rw [sum_congr rfl fun b _ => e b]
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  push_cast
  linarith

end Nine

section NineFibre

/-- Labels unavailable at `y₆`. -/
def o6 (v : Fin m) (g : Cell c m → ℕ) (b : ℕ) : Prop :=
  if h : 2 ≤ c then b ∉ (slab c m 9 P A N).avail (boxB c v) g (y₆ h v) else False

/-- Labels unavailable at the future cell of the upper domino. -/
def oU (hc : 1 ≤ c) (v : Fin m) (g : Cell c m → ℕ) (b : ℕ) : Prop :=
  if h : 1 ≤ v.val then b ∉ (slab c m 9 P A N).avail (boxB c v) g (yU₂ hc h) else False

/-- Labels unavailable at the future cell of the lower domino. -/
def oD (hc : 1 ≤ c) (v : Fin m) (g : Cell c m → ℕ) (b : ℕ) : Prop :=
  if h : v.val + 1 < m then b ∉ (slab c m 9 P A N).avail (boxB c v) g (yD₂ hc h) else False

/-- Few labels are unavailable at a future cell of the box. -/
theorem card_unavail_le (hK : KeyInj 9 A N) {v : Fin m} {g : Cell c m → ℕ}
    (hg : (slab c m 9 P A N).Valid g) {y : Cell c m} (hy : inB v y) (hy2 : 2 ≤ y.1.val) {r : ℕ}
    (hr : ((slab c m 9 P A N).nbrsOut y (boxB c v)).card ≤ r) :
    ((range 9).filter (fun b => b ∉ (slab c m 9 P A N).avail (boxB c v) g y)).card ≤ r := by
  have hav := card_avail_fut_ge hK hg hy hy2
  have hsub : (slab c m 9 P A N).avail (boxB c v) g y ⊆ range 9 := by
    intro a ha; have := ((slab c m 9 P A N).mem_avail.mp ha).1; rwa [slab_D_fut hy2] at this
  have e : (range 9).filter (fun b => b ∉ (slab c m 9 P A N).avail (boxB c v) g y) =
      range 9 \ (slab c m 9 P A N).avail (boxB c v) g y := by
    ext b; simp [mem_sdiff]
  rw [e, card_sdiff_of_subset hsub, card_range]
  omega

/-- The `y₁` factor at `k = 9`. -/
theorem y1_nine (hK : KeyInj 9 A N) (v : Fin m) {a₀ : ℕ} (hPv : 8 ≤ (P v).card ∨ a₀ ∉ P v)
    {g : Cell c m → ℕ} (hg : (slab c m 9 P A N).Valid g) :
    5 * ((slab c m 9 P A N).avail (boxB c v) g (y₁ v)).card ≤
      6 * (((slab c m 9 P A N).avail (boxB c v) g (y₁ v)).erase a₀).card := by
  have hM := slab_match (c := c) (P := P) hK
  have hI : (slab c m 9 P A N : CSP (Cell c m)).Irrefl := slab_irrefl
  by_cases hm : a₀ ∈ (slab c m 9 P A N).avail (boxB c v) g (y₁ v)
  · have hP : a₀ ∈ P v := by
      have := ((slab c m 9 P A N).mem_avail.mp hm).1; rwa [slab_D_zero rfl] at this
    have hPc : 8 ≤ (P v).card := hPv.resolve_right (not_not.mpr hP)
    have hav := (slab c m 9 P A N).card_avail_ge hM hI (mem_boxB.mpr (y₁_inY (c := c) v).1)
      (fun x _ => hg.1 x)
    rw [slab_D_zero rfl] at hav
    change (P v).card - _ ≤ _ at hav
    have hn := nbrsOut_y₁ (c := c) (k := 9) (P := P) (A := A) (N := N) v
    rw [card_erase_of_mem hm]
    omega
  · rw [erase_eq_of_notMem hm]; omega

/-- The `y₆` factor at `k = 9`. -/
theorem y6_nine (hK : KeyInj 9 A N) (v : Fin m) {x₀ : ℕ} {g : Cell c m → ℕ}
    (hg : (slab c m 9 P A N).Valid g) (b : ℕ) :
    ((opt6b c 9 P A N v g b).card : ℚ) ≤
      (if o6 (P := P) (A := A) (N := N) v g b then (6 / 5 : ℚ) else 1) *
        (opt6' c 9 P A N v x₀ g).card := by
  by_cases h : 2 ≤ c
  · have ho : o6 (P := P) (A := A) (N := N) v g b ↔
        b ∉ (slab c m 9 P A N).avail (boxB c v) g (y₆ h v) := by simp [o6, h]
    simp only [opt6b, opt6', dite_eq_left h, card_map]
    have hav := card_avail_fut_ge hK hg (y₆_inY h v).1 (show 2 ≤ (y₆ h v).1.val by
      show 2 ≤ 3; omega)
    have hn := nbrsOut_y₆ (k := 9) (P := P) (A := A) (N := N) h v
    have hlow := pred_card_le_card_erase (s := (slab c m 9 P A N).avail (boxB c v) g (y₆ h v))
      (a := x₀)
    by_cases hb : b ∈ (slab c m 9 P A N).avail (boxB c v) g (y₆ h v)
    · rw [if_neg (by rw [ho]; exact not_not.mpr hb), one_mul, card_erase_of_mem hb]
      exact_mod_cast hlow
    · rw [if_pos (by rw [ho]; exact hb), erase_eq_of_notMem hb]
      have h3 : 5 * ((slab c m 9 P A N).avail (boxB c v) g (y₆ h v)).card ≤
          6 * (((slab c m 9 P A N).avail (boxB c v) g (y₆ h v)).erase x₀).card := by omega
      have := (Nat.cast_le (α := ℚ)).mpr h3
      push_cast at this
      linarith
  · simp only [opt6b, opt6', o6, dite_eq_right h, card_singleton, Nat.cast_one]; norm_num

/-- A domino factor at `k = 9`. -/
theorem dom_nine (hK : KeyInj 9 A N) {v : Fin m} {g : Cell c m → ℕ} {y y' : Cell c m} {a₀ x₀ : ℕ}
    (h2 : 7 ≤ ((slab c m 9 P A N).avail (boxB c v) g y).card)
    (h3 : 7 ≤ ((slab c m 9 P A N).avail (boxB c v) g y').card) (b : ℕ) :
    (((dom c 9 P A N (boxB c v) g y y').filter (fun pq => pq.2 ≠ b)).card : ℚ) ≤
      (if b ∉ (slab c m 9 P A N).avail (boxB c v) g y' then (3 / 2 : ℚ) else 9 / 7) *
        ((dom c 9 P A N (boxB c v) g y y').filter (fun pq => pq.1 ≠ a₀ ∧ pq.2 ≠ x₀)).card := by
  have hτ := card_dom_ge (c := c) (P := P) (A := A) (N := N) (U := boxB c v) (g := g)
    (y := y) (y' := y') hK
  have hs := card_dom_filter_ge (c := c) (k := 9) (P := P) (A := A) (N := N)
    (U := boxB c v) (g := g) (y := y) (y' := y') a₀ x₀
  have hle : ((dom c 9 P A N (boxB c v) g y y').filter (fun pq => pq.2 ≠ b)).card ≤
      (dom c 9 P A N (boxB c v) g y y').card := card_le_card (filter_subset _ _)
  by_cases hb : b ∈ (slab c m 9 P A N).avail (boxB c v) g y'
  · rw [if_neg (not_not.mpr hb)]
    have hge := card_dom_eq_ge hK hb (y := y)
    have := dom_in_arith (u := ((dom c 9 P A N (boxB c v) g y y').filter
      (fun pq => pq.2 ≠ b)).card) h2 h3 hτ (by omega) hs
    have := (Nat.cast_le (α := ℚ)).mpr this
    push_cast at this
    linarith
  · rw [if_pos hb]
    have := dom_out_arith (u := ((dom c 9 P A N (boxB c v) g y y').filter
      (fun pq => pq.2 ≠ b)).card) h2 h3 hτ hle hs
    have := (Nat.cast_le (α := ℚ)).mpr this
    push_cast at this
    linarith

theorem dom_avail_U (hK : KeyInj 9 A N) (hA : ∀ v, (A v).card = 9) (hc : 1 ≤ c) {v : Fin m}
    (h : 1 ≤ v.val) {g : Cell c m → ℕ} (hg : (slab c m 9 P A N).Valid g) :
    7 ≤ ((slab c m 9 P A N).avail (boxB c v) g (yU₁ h)).card ∧
      7 ≤ ((slab c m 9 P A N).avail (boxB c v) g (yU₂ hc h)).card := by
  have hM := slab_match (c := c) (P := P) hK
  have hI : (slab c m 9 P A N : CSP (Cell c m)).Irrefl := slab_irrefl
  constructor
  · have hav := (slab c m 9 P A N).card_avail_ge hM hI (mem_boxB.mpr (yU₁_inY (c := c) h).1)
      (fun x _ => hg.1 x)
    rw [slab_D_one (show (yU₁ (c := c) h).1.val = 1 from Fin.val_one _), hA] at hav
    have hn := nbrsOut_yU₁ (c := c) (k := 9) (P := P) (A := A) (N := N) h
    omega
  · have hav := card_avail_fut_ge hK hg (yU₂_inY hc h).1 (show 2 ≤ (yU₂ hc h).1.val from le_rfl)
    have hn := nbrsOut_yU₂ (k := 9) (P := P) (A := A) (N := N) hc h
    omega

theorem dom_avail_D (hK : KeyInj 9 A N) (hA : ∀ v, (A v).card = 9) (hc : 1 ≤ c) {v : Fin m}
    (h : v.val + 1 < m) {g : Cell c m → ℕ} (hg : (slab c m 9 P A N).Valid g) :
    7 ≤ ((slab c m 9 P A N).avail (boxB c v) g (yD₁ h)).card ∧
      7 ≤ ((slab c m 9 P A N).avail (boxB c v) g (yD₂ hc h)).card := by
  have hM := slab_match (c := c) (P := P) hK
  have hI : (slab c m 9 P A N : CSP (Cell c m)).Irrefl := slab_irrefl
  constructor
  · have hav := (slab c m 9 P A N).card_avail_ge hM hI (mem_boxB.mpr (yD₁_inY (c := c) h).1)
      (fun x _ => hg.1 x)
    rw [slab_D_one (show (yD₁ (c := c) h).1.val = 1 from Fin.val_one _), hA] at hav
    have hn := nbrsOut_yD₁ (c := c) (k := 9) (P := P) (A := A) (N := N) h
    omega
  · have hav := card_avail_fut_ge hK hg (yD₂_inY hc h).1 (show 2 ≤ (yD₂ hc h).1.val from le_rfl)
    have hn := nbrsOut_yD₂ (k := 9) (P := P) (A := A) (N := N) hc h
    omega

theorem U_nine (hK : KeyInj 9 A N) (hA : ∀ v, (A v).card = 9) (hc : 1 ≤ c) (v : Fin m)
    {a₀ x₀ : ℕ} {g : Cell c m → ℕ} (hg : (slab c m 9 P A N).Valid g) (b : ℕ) :
    ((optUb c 9 P A N hc v g b).card : ℚ) ≤
      (if oU (P := P) (A := A) (N := N) hc v g b then (3 / 2 : ℚ) else 9 / 7) *
        (optU' c 9 P A N hc v a₀ x₀ g).card := by
  by_cases h : 1 ≤ v.val
  · have ho : oU (P := P) (A := A) (N := N) hc v g b ↔
        b ∉ (slab c m 9 P A N).avail (boxB c v) g (yU₂ hc h) := by simp [oU, h]
    simp only [optUb, optU', dite_eq_left h, card_map]
    obtain ⟨h2, h3⟩ := dom_avail_U hK hA hc h hg
    have := dom_nine (a₀ := a₀) (x₀ := x₀) hK h2 h3 b
    by_cases hb : oU (P := P) (A := A) (N := N) hc v g b
    · rw [if_pos hb]; rw [if_pos (ho.mp hb)] at this; exact this
    · rw [if_neg hb]; rw [if_neg (fun h' => hb (ho.mpr h'))] at this; exact this
  · simp only [optUb, optU', oU, dite_eq_right h, card_singleton, Nat.cast_one]; norm_num

theorem D_nine (hK : KeyInj 9 A N) (hA : ∀ v, (A v).card = 9) (hc : 1 ≤ c) (v : Fin m)
    {a₀ x₀ : ℕ} {g : Cell c m → ℕ} (hg : (slab c m 9 P A N).Valid g) (b : ℕ) :
    ((optDb c 9 P A N hc v g b).card : ℚ) ≤
      (if oD (P := P) (A := A) (N := N) hc v g b then (3 / 2 : ℚ) else 9 / 7) *
        (optD' c 9 P A N hc v a₀ x₀ g).card := by
  by_cases h : v.val + 1 < m
  · have ho : oD (P := P) (A := A) (N := N) hc v g b ↔
        b ∉ (slab c m 9 P A N).avail (boxB c v) g (yD₂ hc h) := by simp [oD, h]
    simp only [optDb, optD', dite_eq_left h, card_map]
    obtain ⟨h2, h3⟩ := dom_avail_D hK hA hc h hg
    have := dom_nine (a₀ := a₀) (x₀ := x₀) hK h2 h3 b
    by_cases hb : oD (P := P) (A := A) (N := N) hc v g b
    · rw [if_pos hb]; rw [if_pos (ho.mp hb)] at this; exact this
    · rw [if_neg hb]; rw [if_neg (fun h' => hb (ho.mpr h'))] at this; exact this
  · simp only [optDb, optD', oD, dite_eq_right h, card_singleton, Nat.cast_one]; norm_num

/-- **The refined box inequality on one fibre** (`k = 9`). -/
theorem box_fibre_nine (hK : KeyInj 9 A N) (hA : ∀ v, (A v).card = 9) (hc : 1 ≤ c)
    (v : Fin m) {a₀ x₀ : ℕ} (ha : a₀ ∈ A v) (hx : x₀ < 9) (hN : 9 ≤ N v a₀)
    (hPv : 8 ≤ (P v).card ∨ a₀ ∉ P v) {g : Cell c m → ℕ}
    (hg : (slab c m 9 P A N).Valid g) :
    (((slab c m 9 P A N).cls (boxB c v) g).card : ℚ) * 2450 ≤
      ((((slab c m 9 P A N).cls (boxB c v) g).filter (Hit hc v a₀ x₀)).card : ℚ) * 449334 := by
  set C := slab c m 9 P A N
  have h₁ := y1_nine (P := P) hK v hPv hg
  have hsum₁ : ∑ a ∈ A v, ((C.avail (boxB c v) g (y₁ v)).erase a).card ≤
      ((C.avail (boxB c v) g (y₁ v)).erase a₀).card + 8 * (C.avail (boxB c v) g (y₁ v)).card := by
    rw [← add_sum_erase _ _ ha]
    refine Nat.add_le_add_left ?_ _
    calc ∑ a ∈ (A v).erase a₀, ((C.avail (boxB c v) g (y₁ v)).erase a).card
        ≤ ∑ _a ∈ (A v).erase a₀, (C.avail (boxB c v) g (y₁ v)).card :=
          sum_le_sum fun a _ => card_erase_le
      _ = 8 * (C.avail (boxB c v) g (y₁ v)).card := by
          rw [sum_const, card_erase_of_mem ha, hA, smul_eq_mul]
  set s₁ := ((C.avail (boxB c v) g (y₁ v)).erase a₀).card
  set s₆ := (opt6' c 9 P A N v x₀ g).card
  set sU := (optU' c 9 P A N hc v a₀ x₀ g).card
  set sD := (optD' c 9 P A N hc v a₀ x₀ g).card
  have h₆ := y6_nine (P := P) hK v (x₀ := x₀) hg
  have hU := U_nine (P := P) hK hA hc v (a₀ := a₀) (x₀ := x₀) hg
  have hD := D_nine (P := P) hK hA hc v (a₀ := a₀) (x₀ := x₀) hg
  -- outsider counts
  have c6 : ((range 9).filter (o6 (P := P) (A := A) (N := N) v g)).card ≤ 3 := by
    by_cases h : 2 ≤ c
    · have e : (range 9).filter (o6 (P := P) (A := A) (N := N) v g) =
          (range 9).filter (fun b => b ∉ C.avail (boxB c v) g (y₆ h v)) := by
        ext b; simp only [mem_filter, o6, dite_eq_left h]; rfl
      rw [e]
      exact card_unavail_le hK hg (y₆_inY h v).1 (show 2 ≤ (y₆ h v).1.val by show 2 ≤ 3; omega)
        (nbrsOut_y₆ h v)
    · have e : (range 9).filter (o6 (P := P) (A := A) (N := N) v g) = ∅ := by
        ext b; simp [o6, h]
      rw [e]; simp
  have cU : ((range 9).filter (oU (P := P) (A := A) (N := N) hc v g)).card ≤ 2 := by
    by_cases h : 1 ≤ v.val
    · have e : (range 9).filter (oU (P := P) (A := A) (N := N) hc v g) =
          (range 9).filter (fun b => b ∉ C.avail (boxB c v) g (yU₂ hc h)) := by
        ext b; simp only [mem_filter, oU, dite_eq_left h]; rfl
      rw [e]
      exact card_unavail_le hK hg (yU₂_inY hc h).1 le_rfl (nbrsOut_yU₂ hc h)
    · have e : (range 9).filter (oU (P := P) (A := A) (N := N) hc v g) = ∅ := by
        ext b; simp [oU, h]
      rw [e]; simp
  have cD : ((range 9).filter (oD (P := P) (A := A) (N := N) hc v g)).card ≤ 2 := by
    by_cases h : v.val + 1 < m
    · have e : (range 9).filter (oD (P := P) (A := A) (N := N) hc v g) =
          (range 9).filter (fun b => b ∉ C.avail (boxB c v) g (yD₂ hc h)) := by
        ext b; simp only [mem_filter, oD, dite_eq_left h]; rfl
      rw [e]
      exact card_unavail_le hK hg (yD₂_inY hc h).1 le_rfl (nbrsOut_yD₂ hc h)
    · have e : (range 9).filter (oD (P := P) (A := A) (N := N) hc v g) = ∅ := by
        ext b; simp [oD, h]
      rw [e]; simp
  have hnest := nested_sum _ _ _ c6 cU cD
  -- assemble
  have hup := card_cls_le_sum (k := 9) (P := P) (A := A) (N := N) hc v g
  have hlo := card_hit_ge (P := P) hc v hg ha hx hN
  have hs6 : (0 : ℚ) ≤ s₆ := by positivity
  have hsU : (0 : ℚ) ≤ sU := by positivity
  have hsD : (0 : ℚ) ≤ sD := by positivity
  have hb : ∀ b, ((opt6b c 9 P A N v g b).card : ℚ) * (optUb c 9 P A N hc v g b).card *
      (optDb c 9 P A N hc v g b).card ≤ ((if o6 (P := P) (A := A) (N := N) v g b then (6 / 5 : ℚ)
        else 1) * (if oU (P := P) (A := A) (N := N) hc v g b then (3 / 2 : ℚ) else 9 / 7) *
        (if oD (P := P) (A := A) (N := N) hc v g b then (3 / 2 : ℚ) else 9 / 7)) * (s₆ * sU * sD) := by
    intro b
    have e1 := h₆ b
    have e2 := hU b
    have e3 := hD b
    calc ((opt6b c 9 P A N v g b).card : ℚ) * (optUb c 9 P A N hc v g b).card *
          (optDb c 9 P A N hc v g b).card
        ≤ ((if o6 (P := P) (A := A) (N := N) v g b then (6 / 5 : ℚ) else 1) * s₆) *
            ((if oU (P := P) (A := A) (N := N) hc v g b then (3 / 2 : ℚ) else 9 / 7) * sU) *
              ((if oD (P := P) (A := A) (N := N) hc v g b then (3 / 2 : ℚ) else 9 / 7) * sD) := by
          gcongr
      _ = _ := by ring
  have hsumb : (∑ b ∈ range 9, ((opt6b c 9 P A N v g b).card : ℚ) * (optUb c 9 P A N hc v g b).card *
      (optDb c 9 P A N hc v g b).card) ≤ 8478 / 490 * (s₆ * sU * sD) := by
    calc _ ≤ ∑ b ∈ range 9, ((if o6 (P := P) (A := A) (N := N) v g b then (6 / 5 : ℚ) else 1) *
          (if oU (P := P) (A := A) (N := N) hc v g b then (3 / 2 : ℚ) else 9 / 7) *
          (if oD (P := P) (A := A) (N := N) hc v g b then (3 / 2 : ℚ) else 9 / 7)) *
            (s₆ * sU * sD) := sum_le_sum fun b _ => hb b
      _ = (∑ b ∈ range 9, (if o6 (P := P) (A := A) (N := N) v g b then (6 / 5 : ℚ) else 1) *
          (if oU (P := P) (A := A) (N := N) hc v g b then (3 / 2 : ℚ) else 9 / 7) *
          (if oD (P := P) (A := A) (N := N) hc v g b then (3 / 2 : ℚ) else 9 / 7)) *
            (s₆ * sU * sD) := by rw [sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hnest (by positivity)
  have hcls : (((slab c m 9 P A N).cls (boxB c v) g).card : ℚ) ≤
      (∑ a ∈ A v, (((C.avail (boxB c v) g (y₁ v)).erase a).card : ℚ)) *
        ∑ b ∈ range 9, ((opt6b c 9 P A N v g b).card : ℚ) * (optUb c 9 P A N hc v g b).card *
          (optDb c 9 P A N hc v g b).card := by
    rw [sum_mul_sum]
    have := (Nat.cast_le (α := ℚ)).mpr hup
    push_cast at this
    refine le_trans this (le_of_eq (sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring))
  have ha1 : (∑ a ∈ A v, (((C.avail (boxB c v) g (y₁ v)).erase a).card : ℚ)) ≤ 53 / 5 * s₁ := by
    have := (Nat.cast_le (α := ℚ)).mpr hsum₁
    have h1q := (Nat.cast_le (α := ℚ)).mpr h₁
    push_cast at this h1q
    linarith
  have hlo' : (s₁ : ℚ) * s₆ * sU * sD ≤
      ((((slab c m 9 P A N).cls (boxB c v) g).filter (Hit hc v a₀ x₀)).card : ℚ) := by
    exact_mod_cast hlo
  have hs1 : (0 : ℚ) ≤ s₁ := by positivity
  calc (((slab c m 9 P A N).cls (boxB c v) g).card : ℚ) * 2450
      ≤ (53 / 5 * s₁) * (8478 / 490 * (s₆ * sU * sD)) * 2450 := by
        have := mul_le_mul ha1 hsumb (sum_nonneg fun b _ => by positivity) (by positivity)
        nlinarith
    _ = (s₁ * s₆ * sU * sD) * 449334 := by ring
    _ ≤ _ := by nlinarith

/-- **The refined box bound** (`k = 9`). -/
theorem box_bound_nine (hK : KeyInj 9 A N) (hA : ∀ v, (A v).card = 9) (hc : 1 ≤ c)
    (v : Fin m) {a₀ x₀ : ℕ} (ha : a₀ ∈ A v) (hx : x₀ < 9) (hN : 9 ≤ N v a₀)
    (hPv : 8 ≤ (P v).card ∨ a₀ ∉ P v) :
    (slab c m 9 P A N).Ω.card * 2450 ≤
      ((slab c m 9 P A N).Ω.filter (Hit hc v a₀ x₀)).card * 449334 :=
  (slab c m 9 P A N).fibre_sum_ge (boxB c v) _ _ _ fun _ hg => by
    have := box_fibre_nine hK hA hc v ha hx hN hPv ((CSP.mem_Ω _).mp hg)
    exact_mod_cast this

end NineFibre

end GridGen.Gauge
