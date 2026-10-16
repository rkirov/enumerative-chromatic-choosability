/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Paths

/-!
# Vertically consistent labellings and the moves between them

A *labelling* of a column of lists gives each row a bijection from its list onto `{0, …, k-1}`.
It is *vertically consistent* (VC) when a colour shared by adjacent rows gets the same label in
both. The gauge telescope keeps every column labelled VC. Passing to the next column costs:

* one deleted seam pair per colour that leaves a row (`H` stars);
* a product of label transpositions applied to the rows below each row edge (`moves`). There are
  at most `2H` of them.

The transposition count rests on `realize`. Two labellings of a colour set that disagree on `r`
colours differ by a product of at most `r` transpositions. The construction is `glue`: start from
any row-wise labelling `βt`. Going down the column, conjugate row `v + 1` by a product `ρ_v` that
makes it agree with row `v` on the shared colours.
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

/-! ### Products of transpositions -/

/-- The composition `t₁ ∘ t₂ ∘ ⋯` of the transpositions of a list. -/
def comp : List (ℕ × ℕ) → ℕ → ℕ
  | [] => id
  | p :: ts => fun z => Equiv.swap p.1 p.2 (comp ts z)

theorem comp_nil : comp [] = id := rfl

theorem comp_cons (p : ℕ × ℕ) (ts : List (ℕ × ℕ)) (z : ℕ) :
    comp (p :: ts) z = Equiv.swap p.1 p.2 (comp ts z) := rfl

theorem comp_append : ∀ (ts ts' : List (ℕ × ℕ)) (z : ℕ), comp (ts ++ ts') z = comp ts (comp ts' z)
  | [], _, _ => rfl
  | p :: ts, ts', z => by rw [List.cons_append, comp_cons, comp_cons, comp_append]

theorem comp_injective : ∀ ts : List (ℕ × ℕ), Function.Injective (comp ts)
  | [] => fun _ _ h => h
  | p :: ts => fun _ _ h => comp_injective ts ((Equiv.swap p.1 p.2).injective h)

/-- Transpositions of labels below `k` fix everything else and preserve `{0, …, k-1}`. -/
def Small (k : ℕ) (ts : List (ℕ × ℕ)) : Prop := ∀ p ∈ ts, p.1 < k ∧ p.2 < k

theorem comp_lt {k : ℕ} : ∀ {ts : List (ℕ × ℕ)}, Small k ts → ∀ {z : ℕ}, z < k → comp ts z < k
  | [], _, _, hz => hz
  | p :: ts, h, z, hz => by
      rw [comp_cons]
      have hp := h p (by simp)
      have ih : comp ts z < k := comp_lt (ts := ts) (fun q hq => h q (by simp [hq])) hz
      rcases eq_or_ne (comp ts z) p.1 with e | e
      · rw [e, Equiv.swap_apply_left]; exact hp.2
      rcases eq_or_ne (comp ts z) p.2 with e' | e'
      · rw [e', Equiv.swap_apply_right]; exact hp.1
      · rw [Equiv.swap_apply_of_ne_of_ne e e']; exact ih

theorem comp_of_ge {k : ℕ} : ∀ {ts : List (ℕ × ℕ)}, Small k ts → ∀ {z : ℕ}, k ≤ z → comp ts z = z
  | [], _, _, _ => rfl
  | p :: ts, h, z, hz => by
      rw [comp_cons, comp_of_ge (ts := ts) (fun q hq => h q (by simp [hq])) hz]
      have hp := h p (by simp)
      exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)

/-- **Realization.** Two labellings of a colour set that disagree on `r` colours differ by a
product of at most `r` transpositions of labels below `k`. -/
theorem realize (k : ℕ) : ∀ (r : ℕ) (C : Finset ℕ) (g h : ℕ → ℕ), Set.InjOn g C → Set.InjOn h C →
    (∀ c ∈ C, g c < k) → (∀ c ∈ C, h c < k) → (C.filter fun c => g c ≠ h c).card ≤ r →
      ∃ ts : List (ℕ × ℕ), ts.length ≤ (C.filter fun c => g c ≠ h c).card ∧ Small k ts ∧
        ∀ c ∈ C, comp ts (g c) = h c := by
  intro r
  induction r with
  | zero =>
      intro C g h _ _ _ _ hr
      refine ⟨[], by simp, fun _ hp => by simp at hp, fun c hc => ?_⟩
      have : c ∉ C.filter fun c => g c ≠ h c := by
        rw [card_eq_zero.mp (Nat.le_zero.mp hr)]; exact notMem_empty c
      rw [mem_filter] at this
      show g c = h c
      by_contra hne; exact this ⟨hc, hne⟩
  | succ r ih =>
      intro C g h hg hh hgk hhk hr
      by_cases h0 : (C.filter fun c => g c ≠ h c) = ∅
      · refine ⟨[], by simp, fun _ hp => by simp at hp, fun c hc => ?_⟩
        have : c ∉ C.filter fun c => g c ≠ h c := by rw [h0]; exact notMem_empty c
        rw [mem_filter] at this
        show g c = h c
        by_contra hne; exact this ⟨hc, hne⟩
      obtain ⟨c₀, hc₀⟩ := nonempty_iff_ne_empty.mpr h0
      rw [mem_filter] at hc₀
      set a := g c₀
      set b := h c₀
      set h' : ℕ → ℕ := fun c => Equiv.swap a b (h c)
      have hh' : Set.InjOn h' C := fun c hc c' hc' e => hh hc hc' ((Equiv.swap a b).injective e)
      have hhk' : ∀ c ∈ C, h' c < k := by
        intro c hc
        simp only [h']
        rcases eq_or_ne (h c) a with e | e
        · rw [e, Equiv.swap_apply_left]; exact hhk c₀ hc₀.1
        rcases eq_or_ne (h c) b with e' | e'
        · rw [e', Equiv.swap_apply_right]; exact hgk c₀ hc₀.1
        · rw [Equiv.swap_apply_of_ne_of_ne e e']; exact hhk c hc
      -- the disagreements of `g, h'` are those of `g, h` without `c₀`
      have hsub : (C.filter fun c => g c ≠ h' c) ⊆ (C.filter fun c => g c ≠ h c).erase c₀ := by
        intro c hc
        rw [mem_filter] at hc
        rw [mem_erase, mem_filter]
        refine ⟨fun e => ?_, hc.1, fun e => hc.2 ?_⟩
        · subst e; apply hc.2; simp [h', a, b]
        · simp only [h']
          rw [← e]
          have hca : g c ≠ a := fun e' => by
            have := hg hc.1 hc₀.1 e'
            subst this; exact hc₀.2 e
          have hcb : g c ≠ b := fun e' => by
            have := hh hc.1 hc₀.1 (e.symm.trans e')
            subst this; exact hc₀.2 e
          rw [Equiv.swap_apply_of_ne_of_ne hca hcb]
      have hcard : (C.filter fun c => g c ≠ h' c).card ≤ r := by
        have := card_le_card hsub
        rw [card_erase_of_mem (mem_filter.mpr hc₀)] at this
        omega
      obtain ⟨ts, hlen, hsmall, hts⟩ := ih C g h' hg hh' hgk hhk' hcard
      refine ⟨(a, b) :: ts, ?_, ?_, fun c hc => ?_⟩
      · simp only [List.length_cons]
        have := card_le_card hsub
        rw [card_erase_of_mem (mem_filter.mpr hc₀)] at this
        have hpos : 0 < (C.filter fun c => g c ≠ h c).card :=
          card_pos.mpr ⟨c₀, mem_filter.mpr hc₀⟩
        omega
      · intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ⟨hgk c₀ hc₀.1, hhk c₀ hc₀.1⟩
        · exact hsmall p hp
      · rw [comp_cons, hts c hc]
        simp only [h', Equiv.swap_apply_self]

/-! ### Glueing row labellings into a vertically consistent one -/

section Glue

variable (k : ℕ) (Bx : ℕ → Finset ℕ) (βx : ℕ → ℕ → ℕ)

/-- The hypotheses of `realize`, bundled. -/
def RGood (C : Finset ℕ) (g h : ℕ → ℕ) : Prop :=
  Set.InjOn g C ∧ Set.InjOn h C ∧ (∀ c ∈ C, g c < k) ∧ (∀ c ∈ C, h c < k)

/-- The transpositions that make row `v + 1` agree with row `v` on their shared colours, after
the rows above have been conjugated by `comp pl`. -/
noncomputable def rho (v : ℕ) (pl : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  if h : RGood k (Bx v ∩ Bx (v + 1)) (fun c => comp pl (βx (v + 1) c)) (fun c => comp pl (βx v c))
  then Classical.choose (realize k _ (Bx v ∩ Bx (v + 1)) _ _ h.1 h.2.1 h.2.2.1 h.2.2.2 le_rfl)
  else []

/-- The accumulated conjugation of row `v`. -/
noncomputable def piL : ℕ → List (ℕ × ℕ)
  | 0 => []
  | v + 1 => rho k Bx βx v (piL v) ++ piL v

/-- **The glued labelling.** -/
noncomputable def glueLab (v : ℕ) (a : ℕ) : ℕ := comp (piL k Bx βx v) (βx v a)

variable {k Bx βx}

/-- Row labellings are injective with labels below `k`. -/
def RowLab (k : ℕ) (Bx : ℕ → Finset ℕ) (βx : ℕ → ℕ → ℕ) : Prop :=
  ∀ v, Set.InjOn (βx v) (Bx v) ∧ ∀ a ∈ Bx v, βx v a < k

theorem rgood (hR : RowLab k Bx βx) {pl : List (ℕ × ℕ)} (hpl : Small k pl) (v : ℕ) :
    RGood k (Bx v ∩ Bx (v + 1)) (fun c => comp pl (βx (v + 1) c)) (fun c => comp pl (βx v c)) := by
  refine ⟨fun c hc c' hc' e => (hR (v + 1)).1 (mem_inter.mp hc).2 (mem_inter.mp hc').2
      (comp_injective pl e),
    fun c hc c' hc' e => (hR v).1 (mem_inter.mp hc).1 (mem_inter.mp hc').1 (comp_injective pl e),
    fun c hc => comp_lt hpl ((hR (v + 1)).2 c (mem_inter.mp hc).2),
    fun c hc => comp_lt hpl ((hR v).2 c (mem_inter.mp hc).1)⟩

theorem rho_spec (hR : RowLab k Bx βx) {pl : List (ℕ × ℕ)} (hpl : Small k pl) (v : ℕ) :
    (rho k Bx βx v pl).length ≤ ((Bx v ∩ Bx (v + 1)).filter
        fun c => comp pl (βx (v + 1) c) ≠ comp pl (βx v c)).card ∧
      Small k (rho k Bx βx v pl) ∧ ∀ c ∈ Bx v ∩ Bx (v + 1),
        comp (rho k Bx βx v pl) (comp pl (βx (v + 1) c)) = comp pl (βx v c) := by
  have h := rgood hR hpl v
  unfold rho
  rw [dite_eq_left h]
  exact Classical.choose_spec (realize k _ (Bx v ∩ Bx (v + 1)) _ _ h.1 h.2.1 h.2.2.1 h.2.2.2 le_rfl)

theorem small_piL (hR : RowLab k Bx βx) : ∀ v, Small k (piL k Bx βx v)
  | 0 => fun _ hp => by simp [piL] at hp
  | v + 1 => by
      intro p hp
      simp only [piL, List.mem_append] at hp
      rcases hp with hp | hp
      · exact (rho_spec hR (small_piL hR v) v).2.1 p hp
      · exact small_piL hR v p hp

/-- **Vertical consistency of the glued labelling.** -/
theorem glueLab_vc (hR : RowLab k Bx βx) (v : ℕ) {c : ℕ} (hc : c ∈ Bx v ∩ Bx (v + 1)) :
    glueLab k Bx βx (v + 1) c = glueLab k Bx βx v c := by
  unfold glueLab
  simp only [piL]
  rw [comp_append]
  exact (rho_spec hR (small_piL hR v) v).2.2 c hc

theorem glueLab_injOn (hR : RowLab k Bx βx) (v : ℕ) : Set.InjOn (glueLab k Bx βx v) (Bx v) :=
  fun _ ha _ ha' e => (hR v).1 ha ha' (comp_injective _ e)

theorem glueLab_lt (hR : RowLab k Bx βx) (v : ℕ) {a : ℕ} (ha : a ∈ Bx v) :
    glueLab k Bx βx v a < k :=
  comp_lt (small_piL hR v) ((hR v).2 a ha)

/-- The number of transpositions at the edge below row `v`. -/
theorem length_rho_le (hR : RowLab k Bx βx) (v : ℕ) :
    (rho k Bx βx v (piL k Bx βx v)).length ≤
      ((Bx v ∩ Bx (v + 1)).filter fun c => βx (v + 1) c ≠ βx v c).card := by
  refine le_trans (rho_spec hR (small_piL hR v) v).1 (le_of_eq ?_)
  congr 1
  ext c
  simp only [mem_filter]
  exact and_congr_right fun _ =>
    ⟨fun h e => h (by rw [e]), fun h e => h (comp_injective _ e)⟩

/-! ### The moves -/

/-- Apply the transpositions of `ts` to the keys of the rows below `v` (last first). -/
def applyEdge {m : ℕ} (v : ℕ) (ts : List (ℕ × ℕ)) (M : Fin m → ℕ → ℕ) : Fin m → ℕ → ℕ :=
  ts.foldr (fun p M => moveKey M v p.1 p.2) M

theorem applyEdge_eq {m : ℕ} (v : ℕ) : ∀ (ts : List (ℕ × ℕ)) (M : Fin m → ℕ → ℕ),
    applyEdge v ts M = fun u a => if v < u.val then comp ts (M u a) else M u a
  | [], M => by funext u a; simp [applyEdge, comp]
  | p :: ts, M => by
      funext u a
      have ih := applyEdge_eq v ts M
      simp only [applyEdge, List.foldr_cons] at ih ⊢
      rw [moveKey, ih]
      by_cases h : v < u.val
      · simp only [ite_eq_left h, comp_cons]
      · simp only [ite_eq_right h]

/-- Process the row edges `0, …, e - 1` in order. -/
noncomputable def applyAll {m : ℕ} : ℕ → (Fin m → ℕ → ℕ) → Fin m → ℕ → ℕ
  | 0, M => M
  | e + 1, M => applyEdge e (rho k Bx βx e (piL k Bx βx e)) (applyAll e M)

theorem applyAll_eq {m : ℕ} (M : Fin m → ℕ → ℕ) : ∀ e (u : Fin m) (a : ℕ),
    applyAll (k := k) (Bx := Bx) (βx := βx) e M u a = comp (piL k Bx βx (min u.val e)) (M u a)
  | 0, u, a => by simp [applyAll, piL, comp]
  | e + 1, u, a => by
      simp only [applyAll]
      rw [applyEdge_eq]
      simp only
      split_ifs with h
      · rw [applyAll_eq M e u a, show min u.val e = e by omega,
          show min u.val (e + 1) = e + 1 by omega, piL, comp_append]
      · rw [applyAll_eq M e u a, show min u.val e = u.val by omega,
          show min u.val (e + 1) = u.val by omega]

end Glue

/-! ### From the old labelling to row labellings of the new column -/

section Tilde

variable (k : ℕ) (Ax Bx : ℕ → Finset ℕ) (β : ℕ → ℕ → ℕ)

/-- A bijection from the new colours of row `v` onto the labels of its leaving colours. -/
noncomputable def starMap (v : ℕ) : ℕ → ℕ :=
  if h : (Bx v \ Ax v).card = ((Ax v \ Bx v).image (β v)).card then
    fun a => if ha : a ∈ Bx v \ Ax v then
      ((Fintype.equivOfCardEq (by simpa using h) :
        ↥(Bx v \ Ax v) ≃ ↥((Ax v \ Bx v).image (β v))) ⟨a, ha⟩).1 else 0
  else fun _ => 0

/-- The row labellings of the new column: old labels on kept colours, star labels on new ones. -/
noncomputable def tilde (v : ℕ) (a : ℕ) : ℕ := if a ∈ Ax v then β v a else starMap Ax Bx β v a

variable {k Ax Bx β}

theorem card_new_eq (hA : ∀ v, (Ax v).card = (Bx v).card) (hβ : ∀ v, Set.InjOn (β v) (Ax v))
    (v : ℕ) : (Bx v \ Ax v).card = ((Ax v \ Bx v).image (β v)).card := by
  rw [card_image_of_injOn (fun a ha a' ha' e => hβ v (mem_sdiff.mp ha).1 (mem_sdiff.mp ha').1 e)]
  have h1 := card_sdiff_add_card_inter (Bx v) (Ax v)
  have h2 := card_sdiff_add_card_inter (Ax v) (Bx v)
  rw [inter_comm] at h2
  rw [hA v] at h2
  omega

theorem starMap_mem (hA : ∀ v, (Ax v).card = (Bx v).card) (hβ : ∀ v, Set.InjOn (β v) (Ax v))
    {v a : ℕ} (ha : a ∈ Bx v \ Ax v) : starMap Ax Bx β v a ∈ (Ax v \ Bx v).image (β v) := by
  unfold starMap
  rw [dite_eq_left (card_new_eq hA hβ v), dite_eq_left ha]
  exact Subtype.mem _

theorem starMap_injOn (hA : ∀ v, (Ax v).card = (Bx v).card) (hβ : ∀ v, Set.InjOn (β v) (Ax v))
    (v : ℕ) {a a' : ℕ} (ha : a ∈ Bx v \ Ax v) (ha' : a' ∈ Bx v \ Ax v)
    (e : starMap Ax Bx β v a = starMap Ax Bx β v a') : a = a' := by
  unfold starMap at e
  rw [dite_eq_left (card_new_eq hA hβ v), dite_eq_left ha, dite_eq_left ha'] at e
  have := (Fintype.equivOfCardEq _).injective (Subtype.ext e)
  exact congrArg Subtype.val this

/-- **The new row labellings are injective with labels below `k`.** -/
theorem rowLab_tilde (hA : ∀ v, (Ax v).card = (Bx v).card)
    (hβ : ∀ v, Set.InjOn (β v) (Ax v) ∧ ∀ a ∈ Ax v, β v a < k) :
    RowLab k Bx (tilde Ax Bx β) := by
  have hi : ∀ v, Set.InjOn (β v) (Ax v) := fun v => (hβ v).1
  intro v
  refine ⟨fun a ha a' ha' e => ?_, fun a ha => ?_⟩
  · unfold tilde at e
    by_cases h1 : a ∈ Ax v <;> by_cases h2 : a' ∈ Ax v
    · rw [ite_eq_left h1, ite_eq_left h2] at e; exact hi v h1 h2 e
    · rw [ite_eq_left h1, ite_eq_right h2] at e
      obtain ⟨a'', ha'', e'⟩ := mem_image.mp (starMap_mem hA hi (mem_sdiff.mpr ⟨ha', h2⟩))
      have := hi v (mem_sdiff.mp ha'').1 h1 (e'.trans e.symm)
      subst this; exact absurd ha (mem_sdiff.mp ha'').2
    · rw [ite_eq_right h1, ite_eq_left h2] at e
      obtain ⟨a'', ha'', e'⟩ := mem_image.mp (starMap_mem hA hi (mem_sdiff.mpr ⟨ha, h1⟩))
      have := hi v (mem_sdiff.mp ha'').1 h2 (e'.trans e)
      subst this; exact absurd ha' (mem_sdiff.mp ha'').2
    · rw [ite_eq_right h1, ite_eq_right h2] at e
      exact starMap_injOn hA hi v (mem_sdiff.mpr ⟨ha, h1⟩) (mem_sdiff.mpr ⟨ha', h2⟩) e
  · unfold tilde
    split_ifs with h
    · exact (hβ v).2 a h
    · obtain ⟨a'', ha'', e'⟩ := mem_image.mp (starMap_mem hA hi (mem_sdiff.mpr ⟨ha, h⟩))
      rw [← e']; exact (hβ v).2 a'' (mem_sdiff.mp ha'').1

/-- **Mismatches sit at new colours.** -/
theorem card_mismatch_le (hvc : ∀ v, ∀ c ∈ Ax v ∩ Ax (v + 1), β (v + 1) c = β v c) (v : ℕ) :
    ((Bx v ∩ Bx (v + 1)).filter fun c => tilde Ax Bx β (v + 1) c ≠ tilde Ax Bx β v c).card ≤
      (Bx v \ Ax v).card + (Bx (v + 1) \ Ax (v + 1)).card := by
  refine le_trans (card_le_card ?_) (card_union_le _ _)
  intro c hc
  rw [mem_filter, mem_inter] at hc
  rw [mem_union, mem_sdiff, mem_sdiff]
  by_contra hn
  push Not at hn
  have h1 := hn.1 hc.1.1
  have h2 := hn.2 hc.1.2
  apply hc.2
  unfold tilde
  rw [ite_eq_left h1, ite_eq_left h2]
  exact hvc v c (mem_inter.mpr ⟨h1, h2⟩)

end Tilde

end GridGen.Gauge
