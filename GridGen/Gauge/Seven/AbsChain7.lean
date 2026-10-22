/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Seven.SwapSlab7
import GridGen.Gauge.Seven.Chordless

/-!
# Absorbed chains at `k = 7`

Let `z₁ = (1, r)`, `z₂ = (2, r)`, and `a₀` an unpaired colour of row `r`. An event that puts one
prescribed colour on `z₁`, the label `h` on `z₂`, and prescribed values on a chain `rest` away from
`z₁`'s list neighbours, is rarer than the hit event `{z₁ = a₀, z₂ = h}` by
`(64/27) / chainProd rest` (`absorb_core`):

* swapping `z₁` to `a₀` costs at most `64/27` (`swap_seam`);
* given the hit event, prescribing `rest` costs `chainProd rest` (`card_prescribed_cond`).

A chordless crossing path of at least three cells with its head (or last cell) at `(2, r)` gives
such an event, with `chainProd rest ≥ 4^{L-1}·3` (`absorb_chain_head`).
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m : ℕ} {P A : Fin m → Finset ℕ} {M : Fin m → ℕ → ℕ}

/-- **The absorbed event, generically.** -/
theorem absorb_core (hK : KeyInj 7 A M) (hA : ∀ v, (A v).card = 7)
    (hP : ∀ v a, a ∈ A v → 6 ≤ (P v).card ∨ a ∉ P v) (hc : 1 ≤ c) (r : Fin m) {h a₀ : ℕ}
    (ha₀ : a₀ ∈ A r) (h7 : 7 ≤ M r a₀) (T : Finset ℕ) (hT : T.card ≤ 1)
    (rest : List (Cell c m)) (hnd : rest.Nodup) (S : Cell c m → Finset ℕ)
    (hS : ∀ z ∈ rest, (S z).card ≤ 1)
    (hoff : ∀ z ∈ rest, z ∉ boxS (c := c) r ∧ z ≠ (fut0 hc, r))
    (E : (Cell c m → ℕ) → Prop) [DecidablePred E]
    (hE : ∀ f, E f → f ((1 : Fin (c + 2)), r) ∈ T ∧ f (fut0 hc, r) = h ∧ ∀ z ∈ rest, f z ∈ S z) :
    ((slab c m 7 P A M).Ω.filter E).card * 27 * (slab c m 7 P A M).chainProd rest ≤
      64 * ((slab c m 7 P A M).Ω.filter (Hit hc r a₀ h)).card := by
  set C := slab c m 7 P A M
  set z : Cell c m := ((1 : Fin (c + 2)), r)
  -- the event read off the box: the label at `z₂` and the rest of the chain
  set R : (Cell c m → ℕ) → Prop := fun f => f (fut0 hc, r) = h ∧ ∀ w ∈ rest, f w ∈ S w
  have hR : CSP.OffU (boxS (c := c) r) R := by
    intro f g hfg
    have h2 : (fut0 hc, r) ∉ boxS (c := c) r := by
      unfold boxS; rw [mem_insert, mem_nbS, not_or]
      refine ⟨fun e => ?_, ?_⟩
      · have := congrArg (fun w : Cell c m => w.1.val) e; simp [fut0, one_val] at this
      · simp [fut0]
    simp only [R]
    rw [hfg _ h2]
    refine and_congr Iff.rfl (forall₂_congr fun w hw => ?_)
    rw [hfg w (hoff w hw).1]
  -- at most one colour on `z₁`
  have hE₁ : (C.Ω.filter E).card ≤ ∑ a ∈ T, ((C.Ω.filter R).filter (fun f => f z = a)).card := by
    calc (C.Ω.filter E).card ≤ (T.biUnion fun a => (C.Ω.filter R).filter (fun f => f z = a)).card := by
          refine card_le_card fun f hf => ?_
          rw [mem_filter] at hf
          obtain ⟨h1, h2, h3⟩ := hE f hf.2
          rw [mem_biUnion]
          exact ⟨_, h1, mem_filter.mpr ⟨mem_filter.mpr ⟨hf.1, h2, h3⟩, rfl⟩⟩
      _ ≤ _ := card_biUnion_le
  have hswap : ∀ a, ((C.Ω.filter R).filter (fun f => f z = a)).card * 27 ≤
      ((C.Ω.filter R).filter (fun f => f z = a₀)).card * 64 := fun a =>
    swap_seam hK hA hP r ha₀ h7 R hR
  -- given the hit event, the rest of the chain
  have hHit : CSP.OffU rest.toFinset (Hit hc r a₀ h) := by
    intro f g hfg
    have h1 : z ∉ rest.toFinset := fun hz => by
      have := (hoff z (by simpa using hz)).1
      exact this (mem_insert_self _ _)
    have h2 : (fut0 hc, r) ∉ rest.toFinset := fun hz => (hoff _ (by simpa using hz)).2 rfl
    unfold Hit
    rw [hfg _ h1, hfg _ h2]
  have hchain := C.card_prescribed_cond (slab_match (c := c) (P := P) hK) slab_irrefl rest hnd S hS
    (Hit hc r a₀ h) hHit
  have hsub : (C.Ω.filter R).filter (fun f => f z = a₀) ⊆
      (C.Ω.filter (Hit hc r a₀ h)).filter (fun f => ∀ w ∈ rest, f w ∈ S w) := by
    intro f hf
    simp only [mem_filter, R] at hf ⊢
    exact ⟨⟨hf.1.1, hf.2, hf.1.2.1⟩, hf.1.2.2⟩
  have hsub' := card_le_card hsub
  -- combine
  have hT' : (∑ a ∈ T, ((C.Ω.filter R).filter (fun f => f z = a)).card) * 27 ≤
      ((C.Ω.filter R).filter (fun f => f z = a₀)).card * 64 := by
    obtain ⟨a, hTa⟩ := card_le_one_iff_subset_singleton.mp hT
    calc (∑ b ∈ T, ((C.Ω.filter R).filter (fun f => f z = b)).card) * 27
        ≤ (∑ b ∈ ({a} : Finset ℕ), ((C.Ω.filter R).filter (fun f => f z = b)).card) * 27 :=
          Nat.mul_le_mul_right _ (sum_le_sum_of_subset hTa)
      _ = ((C.Ω.filter R).filter (fun f => f z = a)).card * 27 := by rw [sum_singleton]
      _ ≤ _ := hswap a
  calc (C.Ω.filter E).card * 27 * C.chainProd rest
      ≤ (∑ a ∈ T, ((C.Ω.filter R).filter (fun f => f z = a)).card) * 27 * C.chainProd rest :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hE₁)
    _ ≤ ((C.Ω.filter R).filter (fun f => f z = a₀)).card * 64 * C.chainProd rest :=
        Nat.mul_le_mul_right _ hT'
    _ ≤ (((C.Ω.filter (Hit hc r a₀ h)).filter (fun f => ∀ w ∈ rest, f w ∈ S w)).card) * 64 *
          C.chainProd rest := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hsub')
    _ = 64 * ((((C.Ω.filter (Hit hc r a₀ h)).filter (fun f => ∀ w ∈ rest, f w ∈ S w)).card) *
          C.chainProd rest) := by ring
    _ ≤ 64 * (C.Ω.filter (Hit hc r a₀ h)).card := Nat.mul_le_mul_left _ hchain

/-- The prescriptions of an event have at most one value. -/
theorem presc_card_le (hK : KeyInj 7 A M) {x y : ℕ} (hx : x < 7) (hy : y < 7)
    (l : List (Cell c m)) {ℓ₀ : ℕ} (hℓ : ℓ₀ = x ∨ ℓ₀ = y) (z : Cell c m) :
    (presc (A := A) M x y l ℓ₀ z).card ≤ 1 := by
  unfold presc
  have hfil : ∀ t, (t = x ∨ t = y) → ((A z.2).filter (fun a => M z.2 a = t)).card ≤ 1 := by
    intro t ht
    refine card_le_one.mpr fun a ha a' ha' => ?_
    rw [mem_filter] at ha ha'
    exact hK z.2 a a' ha.1 ha'.1 (ha.2.trans ha'.2.symm) (by rcases ht with rfl | rfl <;>
      rw [ha.2] <;> assumption)
  split_ifs
  · exact hfil _ (oth_mem hℓ)
  · exact hfil _ (oth_mem (lab_mem hℓ _))
  · simp

theorem cell_card_seven (hA : ∀ v, (A v).card = 7) {z : Cell c m} (hz : 1 ≤ z.1.val) :
    ((slab c m 7 P A M).D z).card = 7 := by
  by_cases h1 : z.1.val = 1
  · rw [slab_D_one h1, hA]
  · rw [slab_D_fut (by omega), card_range]

/-- In a chordless path of at least three cells, the rows of the first and last cells differ by
at least two when both are in the first future column. -/
theorem ends_far {hc : 1 ≤ c} {l : List (Cell c m)} (hnd : l.Nodup) (hchl : Chordless l)
    (hL : 3 ≤ l.length) {v₁ v₂ : Fin m} (h1 : l.head? = some (fut0 hc, v₁))
    (h2 : l.getLast? = some (fut0 hc, v₂)) :
    v₂ ≠ v₁ ∧ v₂.val + 1 ≠ v₁.val ∧ v₂.val ≠ v₁.val + 1 := by
  have e0 : l[0]'(by omega) = (fut0 hc, v₁) := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h1
    exact Option.some.inj h1
  have eL : l[l.length - 1]'(by omega) = (fut0 hc, v₂) := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h2
    exact Option.some.inj h2
  have hna := hchl 0 (l.length - 1) (by omega) (by omega) (by omega)
  rw [e0, eL] at hna
  refine ⟨fun e => ?_, fun e => hna ?_, fun e => hna ?_⟩
  · have := (List.Nodup.getElem_inj_iff hnd (i := 0) (j := l.length - 1)
      (hi := by omega) (hj := by omega)).mp (by rw [e0, eL, e])
    omega
  · unfold slabAdj; left; exact ⟨rfl, Or.inr (by dsimp only; omega)⟩
  · unfold slabAdj; left; exact ⟨rfl, Or.inl (by dsimp only; omega)⟩

/-- **An absorbed chain, head at the hole row.** -/
theorem absorb_chain_head (hK : KeyInj 7 A M) (hA : ∀ v, (A v).card = 7)
    (hP : ∀ v a, a ∈ A v → 6 ≤ (P v).card ∨ a ∉ P v) (hc : 1 ≤ c) {w x y h : ℕ}
    (hx : x < 7) (hy : y < 7) (hh : h = x ∨ h = y) {r : Fin m} {a₀ : ℕ} (ha₀ : a₀ ∈ A r)
    (h7 : 7 ≤ M r a₀) {l : List (Cell c m)} (hl : CrossPath hc w l) (hchl : Chordless l)
    (hhead : l.head? = some (fut0 hc, r)) (hL : 3 ≤ l.length) :
    ((slab c m 7 P A M).Ω.filter (Event (A := A) M x y l h)).card * 27 *
        (4 ^ (l.length - 1) * 3) ≤
      64 * ((slab c m 7 P A M).Ω.filter (Hit hc r a₀ h)).card := by
  obtain ⟨hne, hcnd, hcch, hclen, hcol⟩ := chainOf_props hl
  obtain ⟨hnd, hch, hfut, -, ⟨v₂, hw₂, h2⟩⟩ := hl
  obtain ⟨hv2r, hv2a, hv2b⟩ := ends_far hnd hchl hL hhead h2
  obtain ⟨t, rfl⟩ : ∃ t, l = (fut0 hc, r) :: t := by
    cases l with
    | nil => simp at hhead
    | cons a t => simp at hhead; exact ⟨t, by rw [hhead]⟩
  have hceq : chainOf ((fut0 hc, r) :: t) = (1, r) :: (fut0 hc, r) :: (t ++ [(1, v₂)]) := by
    rw [chainOf_eq hhead h2]; rfl
  set rest := t ++ [((1 : Fin (c + 2)), v₂)] with hrest
  have hrnd : rest.Nodup := by rw [hceq] at hcnd; exact (List.nodup_cons.mp hcnd).2.of_cons
  have hrch : rest.IsChain slabAdj := by rw [hceq] at hcch; exact hcch.tail.tail
  have hrlen : rest.length = ((fut0 hc, r) :: t).length := by simp [rest]
  have hrne : rest ≠ [] := by simp [rest]
  have hmemc : ∀ z ∈ rest, z ∈ chainOf ((fut0 hc, r) :: t) := fun z hz => by
    rw [hceq]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz)
  have hoff : ∀ z ∈ rest, z ∉ boxS (c := c) r ∧ z ≠ (fut0 hc, r) := by
    intro z hz
    rcases List.mem_append.mp hz with hzt | hzs
    · have h2z := hfut z (List.mem_cons_of_mem _ hzt)
      refine ⟨fun hb => ?_, fun e => (List.nodup_cons.mp hnd).1 (e ▸ hzt)⟩
      unfold boxS at hb; rw [mem_insert, mem_nbS] at hb
      rcases hb with e | ⟨e, -⟩ | ⟨e, -⟩
      · rw [e] at h2z; simp [one_val] at h2z
      · omega
      · omega
    · rw [List.mem_singleton] at hzs
      subst hzs
      refine ⟨fun hb => ?_, fun e => ?_⟩
      · unfold boxS at hb; rw [mem_insert, mem_nbS] at hb
        rcases hb with e | ⟨e, -⟩ | ⟨-, e⟩
        · exact hv2r (congrArg Prod.snd e)
        · simp [one_val] at e
        · dsimp only at e; omega
      · have := congrArg (fun w : Cell c m => w.1.val) e; simp [fut0, one_val] at this
  have hE : ∀ f, Event (A := A) M x y ((fut0 hc, r) :: t) h f →
      f ((1 : Fin (c + 2)), r) ∈ (A r).filter (fun a => M r a = oth x y h) ∧ f (fut0 hc, r) = h ∧
        ∀ z ∈ rest, f z ∈ presc (A := A) M x y ((fut0 hc, r) :: t) h z := by
    intro f he
    refine ⟨?_, ?_, fun z hz => he z (hmemc z hz)⟩
    · have := he (1, r) (by rw [hceq]; exact List.mem_cons_self)
      unfold presc at this
      rw [ite_eq_left one_val, ite_eq_left (by simp)] at this
      exact this
    · have := he (fut0 hc, r) (by rw [hceq]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      unfold presc at this
      rw [ite_eq_right (by simp [fut0]), mem_singleton] at this
      rw [this]; simp [lab]
  have hT : ((A r).filter (fun a => M r a = oth x y h)).card ≤ 1 := by
    have := presc_card_le (A := A) hK hx hy ((fut0 hc, r) :: t) hh ((1 : Fin (c + 2)), r)
    unfold presc at this; rwa [ite_eq_left one_val, ite_eq_left (by simp)] at this
  have hcore := absorb_core hK hA hP hc r ha₀ h7 _ hT rest hrnd _
    (fun z _ => presc_card_le hK hx hy _ hh z) hoff _ hE
  have hge := chainProd_ge (c := c) (P := P) (A := A) (M := M) (k := 7) (by omega) rest hrne hrnd hrch
    (fun z hz => cell_card_seven hA (hcol z (hmemc z hz)))
  rw [hrlen] at hge
  calc ((slab c m 7 P A M).Ω.filter (Event (A := A) M x y ((fut0 hc, r) :: t) h)).card * 27 *
        (4 ^ (((fut0 hc, r) :: t).length - 1) * 3)
      ≤ ((slab c m 7 P A M).Ω.filter (Event (A := A) M x y ((fut0 hc, r) :: t) h)).card * 27 *
          (slab c m 7 P A M).chainProd rest := Nat.mul_le_mul_left _ (by simpa using hge)
    _ ≤ _ := hcore

/-- **An absorbed chain, last cell at the hole row.** -/
theorem absorb_chain_last (hK : KeyInj 7 A M) (hA : ∀ v, (A v).card = 7)
    (hP : ∀ v a, a ∈ A v → 6 ≤ (P v).card ∨ a ∉ P v) (hc : 1 ≤ c) {w x y ℓ₀ h : ℕ}
    (hx : x < 7) (hy : y < 7) (hℓ : ℓ₀ = x ∨ ℓ₀ = y) {r : Fin m} {a₀ : ℕ} (ha₀ : a₀ ∈ A r)
    (h7 : 7 ≤ M r a₀) {l : List (Cell c m)} (hl : CrossPath hc w l) (hchl : Chordless l)
    (hlast : l.getLast? = some (fut0 hc, r)) (hlab : lab x y ℓ₀ (l.length - 1) = h)
    (hL : 3 ≤ l.length) :
    ((slab c m 7 P A M).Ω.filter (Event (A := A) M x y l ℓ₀)).card * 27 *
        (4 ^ (l.length - 1) * 3) ≤
      64 * ((slab c m 7 P A M).Ω.filter (Hit hc r a₀ h)).card := by
  obtain ⟨hne, hcnd, hcch, hclen, hcol⟩ := chainOf_props hl
  obtain ⟨hnd, hch, hfut, ⟨v₁, hw₁, h1⟩, -⟩ := hl
  obtain ⟨hv1r, hv1a, hv1b⟩ := ends_far hnd hchl hL h1 hlast
  have hlne : l ≠ [] := by rintro rfl; simp at hL
  have hgl : l.getLast hlne = (fut0 hc, r) := by
    rw [List.getLast?_eq_some_getLast hlne] at hlast; exact Option.some.inj hlast
  have hl_eq : l = l.dropLast ++ [(fut0 hc, r)] := by
    rw [← hgl]; exact (List.dropLast_append_getLast hlne).symm
  have hceq : chainOf l = ((1 : Fin (c + 2)), v₁) :: (l.dropLast ++ [(fut0 hc, r), (1, r)]) := by
    rw [chainOf_eq h1 hlast]
    conv_lhs => rw [hl_eq]
    simp
  set rest := ((1 : Fin (c + 2)), v₁) :: l.dropLast with hrest
  have hceq' : chainOf l = rest ++ [(fut0 hc, r), (1, r)] := by rw [hceq]; simp [rest]
  have hrnd : rest.Nodup := by rw [hceq'] at hcnd; exact hcnd.sublist (List.sublist_append_left _ _)
  have hrch : rest.IsChain slabAdj := by
    rw [hceq', List.isChain_append] at hcch; exact hcch.1
  have hrlen : rest.length = l.length := by
    simp [rest, List.length_dropLast]; omega
  have hrne : rest ≠ [] := by simp [rest]
  have hmemc : ∀ z ∈ rest, z ∈ chainOf l := fun z hz => by
    rw [hceq']; exact List.mem_append_left _ hz
  have hlastmem : ((fut0 hc, r) : Cell c m) ∉ l.dropLast := by
    intro hm
    rw [hl_eq] at hnd
    exact (List.nodup_append.mp hnd).2.2 _ hm _ (List.mem_singleton_self _) rfl
  have hoff : ∀ z ∈ rest, z ∉ boxS (c := c) r ∧ z ≠ (fut0 hc, r) := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hzt
    · refine ⟨fun hb => ?_, fun e => ?_⟩
      · unfold boxS at hb; rw [mem_insert, mem_nbS] at hb
        rcases hb with e | ⟨e, -⟩ | ⟨-, e⟩
        · exact hv1r (congrArg Prod.snd e).symm
        · simp [one_val] at e
        · dsimp only at e; omega
      · have := congrArg (fun w : Cell c m => w.1.val) e; simp [fut0, one_val] at this
    · have h2z := hfut z (List.dropLast_subset _ hzt)
      refine ⟨fun hb => ?_, fun e => hlastmem (e ▸ hzt)⟩
      unfold boxS at hb; rw [mem_insert, mem_nbS] at hb
      rcases hb with e | ⟨e, -⟩ | ⟨e, -⟩
      · rw [e] at h2z; simp [one_val] at h2z
      · omega
      · omega
  -- the index of the last cell
  have hidx : l.idxOf (fut0 hc, r) = l.length - 1 := by
    conv_lhs => rw [hl_eq]
    rw [List.idxOf_append_of_notMem hlastmem]
    simp [List.length_dropLast]
  have hE : ∀ f, Event (A := A) M x y l ℓ₀ f →
      f ((1 : Fin (c + 2)), r) ∈ (A r).filter (fun a => M r a = oth x y h) ∧ f (fut0 hc, r) = h ∧
        ∀ z ∈ rest, f z ∈ presc (A := A) M x y l ℓ₀ z := by
    intro f he
    refine ⟨?_, ?_, fun z hz => he z (hmemc z hz)⟩
    · have := he (1, r) (by rw [hceq']; simp)
      unfold presc at this
      rw [ite_eq_left one_val, ite_eq_right (by rw [h1]; simp; exact fun e => hv1r e), hlab]
        at this
      exact this
    · have := he (fut0 hc, r) (by rw [hceq']; simp)
      unfold presc at this
      rw [ite_eq_right (by simp [fut0]), mem_singleton, hidx, hlab] at this
      exact this
  have hT : ((A r).filter (fun a => M r a = oth x y h)).card ≤ 1 := by
    have := presc_card_le (A := A) hK hx hy l hℓ ((1 : Fin (c + 2)), r)
    unfold presc at this
    rwa [ite_eq_left one_val, ite_eq_right (by rw [h1]; simp; exact fun e => hv1r e), hlab]
      at this
  have hcore := absorb_core hK hA hP hc r ha₀ h7 _ hT rest hrnd _
    (fun z _ => presc_card_le hK hx hy _ hℓ z) hoff _ hE
  have hge := chainProd_ge (c := c) (P := P) (A := A) (M := M) (k := 7) (by omega) rest hrne hrnd hrch
    (fun z hz => cell_card_seven hA (hcol z (hmemc z hz)))
  rw [hrlen] at hge
  calc ((slab c m 7 P A M).Ω.filter (Event (A := A) M x y l ℓ₀)).card * 27 *
        (4 ^ (l.length - 1) * 3)
      ≤ ((slab c m 7 P A M).Ω.filter (Event (A := A) M x y l ℓ₀)).card * 27 *
          (slab c m 7 P A M).chainProd rest := Nat.mul_le_mul_left _ (by simpa using hge)
    _ ≤ _ := hcore

end GridGen.Gauge
