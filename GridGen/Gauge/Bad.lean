/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Kempe

/-!
# The bad event is rare

A bad solution of a lower-part move has a path of `x/y`-alternating future cells. The path runs
from a first future cell `(2, v₁)`, `v₁ > w`, to one `(2, v₂)`, `v₂ ≤ w`. Both ends sit next to
seam cells whose keys are the other label. Prepending and appending those seam cells gives a
chain of `|path| + 2` cells whose colours are prescribed up to a factor `2` (the first label).
The chain bound of `GridGen.Gauge.CSP` makes each such chain cost `(k-3)^{|path|+1}(k-4)`. A union
bound over the crossing paths gives `card_bad_le`.
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m k : ℕ} {P A : Fin m → Finset ℕ} {M : Fin m → ℕ → ℕ}

/-! ### Chains in the slab -/

/-- Every slab cell has at most four neighbours. -/
theorem card_nbrs_le (z : Cell c m) : ((slab c m k P A M).nbrs z).card ≤ 4 := by
  refine card_le_of_coords _
    [(z.1.val, z.2.val - 1), (z.1.val, z.2.val + 1), (z.1.val - 1, z.2.val), (z.1.val + 1, z.2.val)]
    fun w hw => ?_
  rw [CSP.mem_nbrs] at hw
  have := adj_coords (c := c) (k := k) (P := P) (A := A) (N := M) hw
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  omega

/-- **Chains cost `(k-3)` per cell and `(k-4)` for the last.** -/
theorem chainProd_ge (hk : 4 ≤ k) :
    ∀ ch : List (Cell c m), ch ≠ [] → ch.Nodup → ch.IsChain slabAdj →
      (∀ z ∈ ch, ((slab c m k P A M).D z).card = k) →
        (k - 3) ^ (ch.length - 1) * (k - 4) ≤ (slab c m k P A M).chainProd ch := by
  intro ch
  induction ch with
  | nil => intro h; exact absurd rfl h
  | cons z rest ih =>
      intro _ hnd hch hD
      rw [List.nodup_cons] at hnd
      have hz : ((slab c m k P A M).D z).card = k := hD z (by simp)
      cases rest with
      | nil =>
          simp only [CSP.chainProd, List.length_singleton, Nat.sub_self, pow_zero, one_mul,
            mul_one, hz]
          have : ((slab c m k P A M).nbrsOut z ([] : List (Cell c m)).toFinset).card ≤ 4 :=
            le_trans (card_le_card (filter_subset _ _)) (card_nbrs_le z)
          omega
      | cons z' rest' =>
          rw [List.isChain_cons_cons] at hch
          have hrest := ih (by simp) hnd.2 hch.2 (fun y hy => hD y (by simp [hy]))
          have hout : ((slab c m k P A M).nbrsOut z (z' :: rest').toFinset).card ≤ 3 := by
            have hsub : (slab c m k P A M).nbrsOut z (z' :: rest').toFinset ⊆
                ((slab c m k P A M).nbrs z).erase z' := by
              intro y hy
              rw [CSP.mem_nbrsOut] at hy
              rw [mem_erase, CSP.mem_nbrs]
              exact ⟨fun h => hy.2 (by simp [h]), hy.1⟩
            have hz' : z' ∈ (slab c m k P A M).nbrs z := by
              rw [CSP.mem_nbrs]; exact Or.inl hch.1
            have := card_erase_of_mem hz'
            have := card_nbrs_le (k := k) (P := P) (A := A) (M := M) z
            have := card_le_card hsub
            omega
          simp only [CSP.chainProd, hz, List.length_cons]
          calc (k - 3) ^ (rest'.length + 1 + 1 - 1) * (k - 4)
              = (k - 3) * ((k - 3) ^ ((z' :: rest').length - 1) * (k - 4)) := by
                simp only [List.length_cons]
                rw [show rest'.length + 1 + 1 - 1 = (rest'.length + 1 - 1) + 1 by omega, pow_succ]
                ring
            _ ≤ (k - ((slab c m k P A M).nbrsOut z (z' :: rest').toFinset).card) *
                  (slab c m k P A M).chainProd (z' :: rest') :=
                Nat.mul_le_mul (by omega) hrest

/-! ### Crossing paths -/

/-- Every duplicate-free list, as a finset. -/
noncomputable def allLists (c m : ℕ) : Finset (List (Cell c m)) :=
  (range (Fintype.card (Cell c m) + 1)).biUnion fun L =>
    (univ : Finset (Fin L → Cell c m)).image List.ofFn

theorem mem_allLists {l : List (Cell c m)} (h : l.Nodup) : l ∈ allLists c m := by
  unfold allLists
  rw [mem_biUnion]
  refine ⟨l.length, mem_range.mpr (Nat.lt_succ_of_le h.length_le_card), mem_image.mpr
    ⟨fun i => l.get i, mem_univ _, List.ofFn_get l⟩⟩

/-- A crossing path for the cut below row `w`: duplicate-free, consecutive cells adjacent, all in
the future, from a first future cell below the cut to one above it. -/
def CrossPath (hc : 1 ≤ c) (w : ℕ) (l : List (Cell c m)) : Prop :=
  l.Nodup ∧ l.IsChain slabAdj ∧ (∀ z ∈ l, 2 ≤ z.1.val) ∧
    (∃ v₁ : Fin m, w < v₁.val ∧ l.head? = some (fut0 hc, v₁)) ∧
      (∃ v₂ : Fin m, v₂.val ≤ w ∧ l.getLast? = some (fut0 hc, v₂))

/-- The crossing paths. -/
noncomputable def crossPaths (hc : 1 ≤ c) (w : ℕ) : Finset (List (Cell c m)) :=
  (allLists c m).filter (CrossPath hc w)

/-! ### Alternating labels -/

section Alt

variable (x y : ℕ)

/-- The other label. -/
def oth (ℓ : ℕ) : ℕ := if ℓ = x then y else x

/-- The label at position `j` of a path starting with `ℓ₀`. -/
def lab (ℓ₀ j : ℕ) : ℕ := if j % 2 = 0 then ℓ₀ else oth x y ℓ₀

variable {x y}

theorem oth_mem {ℓ : ℕ} (_h : ℓ = x ∨ ℓ = y) : oth x y ℓ = x ∨ oth x y ℓ = y := by
  unfold oth; split_ifs <;> simp

theorem oth_oth (hxy : x ≠ y) {ℓ : ℕ} (h : ℓ = x ∨ ℓ = y) : oth x y (oth x y ℓ) = ℓ := by
  unfold oth
  rcases h with rfl | rfl
  · simp [Ne.symm hxy]
  · simp [hxy, Ne.symm hxy]

theorem eq_oth (hxy : x ≠ y) {ℓ ℓ' : ℕ} (h : ℓ = x ∨ ℓ = y) (h' : ℓ' = x ∨ ℓ' = y)
    (hne : ℓ' ≠ ℓ) : ℓ' = oth x y ℓ := by
  unfold oth
  rcases h with rfl | rfl <;> rcases h' with rfl | rfl <;> simp_all

theorem lab_mem {ℓ₀ : ℕ} (h : ℓ₀ = x ∨ ℓ₀ = y) (j : ℕ) : lab x y ℓ₀ j = x ∨ lab x y ℓ₀ j = y := by
  unfold lab; split_ifs
  · exact h
  · exact oth_mem h

theorem lab_succ (hxy : x ≠ y) {ℓ₀ : ℕ} (h : ℓ₀ = x ∨ ℓ₀ = y) (j : ℕ) :
    lab x y ℓ₀ (j + 1) = lab x y (oth x y ℓ₀) j := by
  unfold lab
  by_cases hj : j % 2 = 0
  · rw [ite_eq_right (by omega), ite_eq_left hj]
  · rw [ite_eq_left (by omega), ite_eq_right hj, oth_oth hxy h]

end Alt

/-! ### Extracting a crossing path from a bad solution -/

section Extract

variable {hc : 1 ≤ c} {w x y : ℕ}

/-- Adjacent future cells of a solution carry different colours. -/
theorem ne_of_fut_adj {f : Cell c m → ℕ} (hf : (slab c m k P A M).Valid f) {u u' : Cell c m}
    (hu : 2 ≤ u.1.val) (hu' : 2 ≤ u'.1.val) (h : slabAdj u u') : f u ≠ f u' := by
  have := hf.2 u u' h
  rwa [slab_conf_eq (by omega) (by omega)] at this

/-- **Alternation.** Along a path of `{x, y}`-coloured future cells the colours alternate. -/
theorem alt_of_chain (hxy : x ≠ y) {f : Cell c m → ℕ} (hf : (slab c m k P A M).Valid f) :
    ∀ (l : List (Cell c m)) (ℓ₀ : ℕ), l.IsChain (kG x y f).Adj → (∀ a ∈ l.head?, f a = ℓ₀) →
      (ℓ₀ = x ∨ ℓ₀ = y) → ∀ j (hj : j < l.length), f l[j] = lab x y ℓ₀ j := by
  intro l
  induction l with
  | nil => intro _ _ _ _ j hj; simp at hj
  | cons a rest ih =>
      intro ℓ₀ hch hhead hℓ j hj
      have ha : f a = ℓ₀ := hhead a rfl
      cases j with
      | zero => simp [lab, ha]
      | succ j =>
          cases rest with
          | nil => simp at hj
          | cons b rest' =>
              rw [List.isChain_cons_cons] at hch
              have hadj := hch.1
              have hb : f b = oth x y ℓ₀ :=
                eq_oth hxy hℓ hadj.2.2.2 (ha ▸ (ne_of_fut_adj hf hadj.2.1.1 hadj.2.2.1 hadj.1).symm)
              have := ih (oth x y ℓ₀) hch.2 (fun a' ha' => by
                simp at ha'; rw [← ha']; exact hb) (oth_mem hℓ) j (by simpa using hj)
              simp only [List.getElem_cons_succ]
              rw [this, lab_succ hxy hℓ]

end Extract

/-! ### The chain of a crossing path, and its prescribed colours -/

/-- The seam cell of a row. -/
def seamOf (z : Cell c m) : Cell c m := (1, z.2)

/-- The seam cells at both ends, and the path between. -/
def chainOf (l : List (Cell c m)) : List (Cell c m) :=
  l.head?.toList.map seamOf ++ l ++ l.getLast?.toList.map seamOf

section Presc

variable (M) (x y : ℕ)

/-- The prescribed colours: on the path the alternating labels; on the two seam cells, the colours
whose key is the other label of the adjacent path cell. -/
noncomputable def presc (l : List (Cell c m)) (ℓ₀ : ℕ) (z : Cell c m) : Finset ℕ :=
  if z.1.val = 1 then
    (if some z.2 = l.head?.map Prod.snd then (A z.2).filter (fun a => M z.2 a = oth x y ℓ₀)
    else (A z.2).filter (fun a => M z.2 a = oth x y (lab x y ℓ₀ (l.length - 1))))
  else {lab x y ℓ₀ (l.idxOf z)}

/-- The prescribed event. -/
def Event (l : List (Cell c m)) (ℓ₀ : ℕ) (f : Cell c m → ℕ) : Prop :=
  ∀ z ∈ chainOf l, f z ∈ presc (A := A) M x y l ℓ₀ z

end Presc

section Extract2

variable {hc : 1 ≤ c} {w x y : ℕ}

theorem seamOf_fst (z : Cell c m) : (seamOf z).1.val = 1 := Fin.val_one _

theorem slabAdj_seam (z : Cell c m) (hz : z.1.val = 2) : slabAdj (seamOf z) z := by
  unfold slabAdj seamOf
  right; exact ⟨rfl, Or.inl (by rw [Fin.val_one, hz])⟩

/-- **A bad solution realizes a prescribed event on a crossing path.** -/
theorem bad_event (hxy : x ≠ y) {f : Cell c m → ℕ} (hf : (slab c m k P A M).Valid f)
    (hb : Bad hc M w x y f) :
    ∃ l ∈ crossPaths hc w, ∃ ℓ₀ ∈ ({x, y} : Finset ℕ), Event (A := A) M x y l ℓ₀ f := by
  obtain ⟨s, ⟨v₁, hw₁, rfl, hk₁, hxy₁⟩, v₂, hw₂, hk₂, hr⟩ := hb
  obtain ⟨p⟩ := hr
  set q := p.bypass
  have hq : q.IsPath := p.bypass_isPath
  set l := q.support with hl
  have hnd : l.Nodup := hq.support_nodup
  have hch : l.IsChain (kG x y f).Adj := q.isChain_adj_support
  have hxyl : ∀ z ∈ l, XY x y f z := fun z hz =>
    xy_of_reachable hxy₁ ⟨q.takeUntil z hz⟩
  have hhead : l.head? = some (fut0 hc, v₁) := by
    rw [List.head?_eq_some_head (SimpleGraph.Walk.support_ne_nil _), SimpleGraph.Walk.head_support]
  have hlast : l.getLast? = some (fut0 hc, v₂) := by
    rw [List.getLast?_eq_some_getLast (SimpleGraph.Walk.support_ne_nil _),
      SimpleGraph.Walk.getLast_support]
  have hne : l ≠ [] := SimpleGraph.Walk.support_ne_nil _
  have hv : v₁ ≠ v₂ := fun h => by rw [h] at hw₁; omega
  refine ⟨l, ?_, f (fut0 hc, v₁), ?_, ?_⟩
  · unfold crossPaths
    rw [mem_filter]
    refine ⟨mem_allLists hnd, ?_⟩
    unfold CrossPath
    exact ⟨hnd, hch.imp fun _ _ h => h.1, fun z hz => (hxyl z hz).1,
      ⟨v₁, hw₁, hhead⟩, ⟨v₂, hw₂, hlast⟩⟩
  · rcases hxy₁.2 with h | h <;> simp [h]
  · have hℓ := hxy₁.2
    have halt := alt_of_chain hxy hf l (f (fut0 hc, v₁)) hch
      (fun a ha => by rw [hhead] at ha; simp at ha; rw [ha]) hℓ
    have hseam : ∀ v : Fin m, M v (f (1, v)) ≠ f (fut0 hc, v) := fun v => by
      have := hf.2 (1, v) (fut0 hc, v) (slabAdj_seam (fut0 hc, v) rfl)
      rwa [slab_conf_seam (Fin.val_one _) rfl] at this
    have hA1 : ∀ v : Fin m, f (1, v) ∈ A v := fun v => by
      have := hf.1 (1, v); rwa [slab_D_one (Fin.val_one _)] at this
    intro z hz
    unfold chainOf at hz
    rw [hhead, hlast] at hz
    simp only [Option.toList_some, List.map_cons, List.map_nil, List.mem_append,
      List.mem_singleton] at hz
    unfold presc
    rcases hz with (rfl | hz) | rfl
    · rw [ite_eq_left (seamOf_fst _), ite_eq_left (by rw [hhead]; rfl), mem_filter]
      exact ⟨hA1 v₁, eq_oth hxy hℓ hk₁ (hseam v₁)⟩
    · have h2 := (hxyl z hz).1
      rw [ite_eq_right (by omega), mem_singleton]
      have hi := List.idxOf_lt_length_of_mem hz
      have := halt _ hi
      rwa [List.getElem_idxOf] at this
    · rw [ite_eq_left (seamOf_fst _), ite_eq_right (by rw [hhead]; simp [seamOf]; exact Ne.symm hv),
        mem_filter]
      refine ⟨hA1 v₂, eq_oth hxy (lab_mem hℓ _) hk₂ ?_⟩
      have hlen : l.length - 1 < l.length := by
        have := List.length_pos_of_ne_nil hne; omega
      have e1 : l[l.length - 1] = (fut0 hc, v₂) := by
        have := List.getLast_eq_getElem hne
        rw [← this]
        have h' := hlast
        rw [List.getLast?_eq_some_getLast hne] at h'
        exact Option.some.inj h'
      rw [← halt _ hlen, e1]
      exact hseam v₂

end Extract2

/-! ### The union bound -/

section Union

variable {hc : 1 ≤ c} {w x y : ℕ}

theorem chainOf_eq {l : List (Cell c m)} {v₁ v₂ : Fin m} (h1 : l.head? = some (fut0 hc, v₁))
    (h2 : l.getLast? = some (fut0 hc, v₂)) :
    chainOf l = (1, v₁) :: (l ++ [(1, v₂)]) := by
  unfold chainOf; rw [h1, h2]; simp [seamOf]

theorem chainOf_props {l : List (Cell c m)} (hl : CrossPath hc w l) :
    chainOf l ≠ [] ∧ (chainOf l).Nodup ∧ (chainOf l).IsChain slabAdj ∧
      (chainOf l).length = l.length + 2 ∧ ∀ z ∈ chainOf l, 1 ≤ z.1.val := by
  obtain ⟨hnd, hch, hfut, ⟨v₁, hw₁, h1⟩, ⟨v₂, hw₂, h2⟩⟩ := hl
  rw [chainOf_eq h1 h2]
  have hv : v₁ ≠ v₂ := fun h => by rw [h] at hw₁; omega
  have hcol1 : ((1 : Fin (c + 2))).val = 1 := Fin.val_one _
  have hne : l ≠ [] := by rintro rfl; simp at h1
  refine ⟨by simp, ?_, ?_, by simp, ?_⟩
  · rw [List.nodup_cons, List.nodup_append]
    refine ⟨?_, hnd, by simp, ?_⟩
    · simp only [List.mem_append, List.mem_singleton, not_or]
      refine ⟨fun h => ?_, fun h => hv (congrArg Prod.snd h)⟩
      have := hfut _ h; simp only [hcol1] at this; omega
    · intro a ha b hb; simp at hb; subst hb
      intro e; have := hfut _ ha; rw [e] at this; simp only [hcol1] at this; omega
  · rw [List.isChain_cons, List.isChain_append]
    refine ⟨?_, hch, List.isChain_singleton _, ?_⟩
    · intro b hb
      rw [List.head?_append, h1] at hb
      simp at hb; subst hb
      exact slabAdj_symm (slabAdj_symm (slabAdj_seam (fut0 hc, v₁) rfl))
    · intro a ha b hb
      rw [h2] at ha; simp at ha hb; subst ha; subst hb
      exact slabAdj_symm (slabAdj_seam (fut0 hc, v₂) rfl)
  · intro z hz
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | hz | rfl
    · simp [hcol1]
    · have := hfut z hz; omega
    · simp [hcol1]

/-- **The bad event is rare.** -/
theorem card_bad_le (hk : 5 ≤ k) (hK : KeyInj k A M) (hA : ∀ v, (A v).card = k) (hxy : x ≠ y)
    (hx : x < k) (hy : y < k) :
    (((slab c m k P A M).Ω.filter (Bad hc M w x y)).card : ℚ) ≤
      (slab c m k P A M).Ω.card *
        ∑ l ∈ crossPaths (m := m) hc w,
          (2 : ℚ) / (((k : ℚ) - 3) ^ (l.length + 1) * ((k : ℚ) - 4)) := by
  set C := slab c m k P A M
  set I := crossPaths (m := m) hc w ×ˢ ({x, y} : Finset ℕ)
  have hsub : C.Ω.filter (Bad hc M w x y) ⊆
      I.biUnion (fun i => C.Ω.filter (Event (A := A) M x y i.1 i.2)) := by
    intro f hf
    rw [mem_filter, CSP.mem_Ω] at hf
    obtain ⟨l, hl, ℓ₀, hℓ, he⟩ := bad_event (P := P) hxy hf.1 hf.2
    rw [mem_biUnion]
    exact ⟨(l, ℓ₀), mem_product.mpr ⟨hl, hℓ⟩, mem_filter.mpr ⟨(CSP.mem_Ω _).mpr hf.1, he⟩⟩
  have hk3 : (0 : ℚ) < (k : ℚ) - 3 := by
    have : (5 : ℚ) ≤ k := by exact_mod_cast hk
    linarith
  have hk4 : (0 : ℚ) < (k : ℚ) - 4 := by
    have : (5 : ℚ) ≤ k := by exact_mod_cast hk
    linarith
  -- one prescribed event
  have hone : ∀ i ∈ I, ((C.Ω.filter (Event (A := A) M x y i.1 i.2)).card : ℚ) ≤
      C.Ω.card / (((k : ℚ) - 3) ^ (i.1.length + 1) * ((k : ℚ) - 4)) := by
    rintro ⟨l, ℓ₀⟩ hi
    rw [mem_product] at hi
    obtain ⟨hl, hℓ⟩ := hi
    have hl' : CrossPath hc w l := (mem_filter.mp hl).2
    have hℓ' : ℓ₀ = x ∨ ℓ₀ = y := by simpa using hℓ
    obtain ⟨hne, hnd, hch, hlen, hcol⟩ := chainOf_props hl'
    have hpresc : ∀ z ∈ chainOf l, (presc (A := A) M x y l ℓ₀ z).card ≤ 1 := by
      intro z _
      unfold presc
      have hfil : ∀ t, (t = x ∨ t = y) → ((A z.2).filter (fun a => M z.2 a = t)).card ≤ 1 := by
        intro t ht
        refine card_le_one.mpr fun a ha a' ha' => ?_
        rw [mem_filter] at ha ha'
        exact hK z.2 a a' ha.1 ha'.1 (ha.2.trans ha'.2.symm) (by rcases ht with rfl | rfl <;>
          rw [ha.2] <;> assumption)
      split_ifs
      · exact hfil _ (oth_mem hℓ')
      · exact hfil _ (oth_mem (lab_mem hℓ' _))
      · simp
    have hD : ∀ z ∈ chainOf l, (C.D z).card = k := by
      intro z hz
      by_cases h1 : z.1.val = 1
      · rw [slab_D_one h1, hA]
      · rw [slab_D_fut (by have := hcol z hz; omega), card_range]
    have hprod := C.card_prescribed_mul_le (slab_match hK) slab_irrefl (chainOf l) hnd
      (presc (A := A) M x y l ℓ₀) hpresc
    have hge := chainProd_ge (P := P) (A := A) (M := M) (by omega) (chainOf l) hne hnd hch hD
    rw [hlen, show l.length + 2 - 1 = l.length + 1 by omega] at hge
    have heq : C.Ω.filter (Event (A := A) M x y l ℓ₀) =
        C.Ω.filter (fun f => ∀ z ∈ chainOf l, f z ∈ presc (A := A) M x y l ℓ₀ z) := by
      ext f; simp only [mem_filter, Event]
    have hq : ((C.Ω.filter (Event (A := A) M x y l ℓ₀)).card : ℚ) *
        (((k - 3 : ℕ) : ℚ) ^ (l.length + 1) * ((k - 4 : ℕ) : ℚ)) ≤ C.Ω.card := by
      have := le_trans (Nat.mul_le_mul_left _ hge) hprod
      rw [heq]
      exact_mod_cast this
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)] at hq
    push_cast at hq
    rw [le_div_iff₀ (by positivity)]
    exact hq
  calc ((C.Ω.filter (Bad hc M w x y)).card : ℚ)
      ≤ ∑ i ∈ I, ((C.Ω.filter (Event (A := A) M x y i.1 i.2)).card : ℚ) := by
        exact_mod_cast le_trans (card_le_card hsub) card_biUnion_le
    _ ≤ ∑ i ∈ I, (C.Ω.card : ℚ) / (((k : ℚ) - 3) ^ (i.1.length + 1) * ((k : ℚ) - 4)) :=
        sum_le_sum hone
    _ = ∑ l ∈ crossPaths (m := m) hc w, ∑ _ℓ ∈ ({x, y} : Finset ℕ),
          (C.Ω.card : ℚ) / (((k : ℚ) - 3) ^ (l.length + 1) * ((k : ℚ) - 4)) := sum_product _ _ _
    _ = _ := by
        rw [mul_sum]
        refine sum_congr rfl fun l _ => ?_
        rw [sum_const, card_pair hxy]
        simp only [nsmul_eq_mul]
        ring

end Union

end GridGen.Gauge
