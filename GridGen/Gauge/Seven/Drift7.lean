/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Seven.MoveB7

/-!
# The drift of the hit event

A move at the edge below row `r` with pair `{x, h}` leaves rows `≤ r` alone, so a star of row `r`
with hole `h` keeps its hole. Its hit event `{(1, r) = a₀, (2, r) = h}` can still grow. Run the
move backwards (the Kempe swap of `moveKey M r x h` lands in the slab of `M`). The hit event is
kept unless the solution is bad, or the cell `(2, r)` is swapped. Both cases are crossing chains
read off a set avoiding `(1, r)` and `(2, r)`, so the chain bound holds *inside* the hit event:

* `(2, r)` swapped: a chordless chain from a seed to `(2, r)`. Its last cell is forced by the hit
  event, so it is dropped (`truncOf`), and only one phase survives.
* bad but `(2, r)` not swapped: a chordless crossing chain avoiding `(2, r)`, with its last cell
  below row `r`.

So `#Hit after ≤ #Hit before + δ' · #Hit after`, with `δ' ≤ 301/2500` from the path counts
(`dM_le`), and `drift7` gives the factor `1 + 7/50`.
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m : ℕ} {P A : Fin m → Finset ℕ} {M : Fin m → ℕ → ℕ}

theorem moveKey_moveKey (M : Fin m → ℕ → ℕ) (w x y : ℕ) :
    moveKey (moveKey M w x y) w x y = M := by
  funext v a; unfold moveKey; split_ifs <;> simp

/-! ### Truncated chains -/

/-- The head's seam cell and the path without its last cell. -/
def truncOf (l : List (Cell c m)) : List (Cell c m) := l.head?.toList.map seamOf ++ l.dropLast

theorem truncOf_props {hc : 1 ≤ c} {w : ℕ} {l : List (Cell c m)} (hl : CrossPath hc w l)
    {v₁ : Fin m} (h1 : l.head? = some (fut0 hc, v₁)) :
    truncOf l = (1, v₁) :: l.dropLast ∧ (truncOf l).Nodup ∧ (truncOf l).IsChain slabAdj ∧
      (truncOf l).length = l.length ∧ ∀ z ∈ truncOf l, 1 ≤ z.1.val := by
  have h2 := two_le_length hl
  obtain ⟨hnd, hch, hfut, -, -⟩ := hl
  have hcol1 : ((1 : Fin (c + 2))).val = 1 := Fin.val_one _
  have he : truncOf l = (1, v₁) :: l.dropLast := by unfold truncOf; rw [h1]; simp [seamOf]
  have hsub : l.dropLast ⊆ l := (List.dropLast_sublist l).subset
  refine ⟨he, ?_, ?_, ?_, ?_⟩
  · rw [he, List.nodup_cons]
    refine ⟨fun h => ?_, hnd.sublist (List.dropLast_sublist l)⟩
    have := hfut _ (hsub h); simp only [hcol1] at this; omega
  · rw [he]
    obtain ⟨a, b, t, rfl⟩ : ∃ a b t, l = a :: b :: t := by
      match l, h2 with
      | a :: b :: t, _ => exact ⟨a, b, t, rfl⟩
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    rw [List.dropLast_cons₂, List.isChain_cons_cons]
    refine ⟨slabAdj_symm (slabAdj_symm (slabAdj_seam (fut0 hc, v₁) rfl)), ?_⟩
    rw [← List.dropLast_cons₂, List.dropLast_eq_take]
    exact hch.take _
  · rw [he]; simp; omega
  · intro z hz
    rw [he, List.mem_cons] at hz
    rcases hz with rfl | hz
    · simp [hcol1]
    · have := hfut z (hsub hz); omega

theorem not_mem_dropLast {l : List (Cell c m)} (hnd : l.Nodup) {z : Cell c m}
    (h : l.getLast? = some z) : z ∉ l.dropLast := by
  have hne : l ≠ [] := by rintro rfl; simp at h
  have e : l.getLast hne = z := by
    rw [List.getLast?_eq_some_getLast hne] at h; exact Option.some.inj h
  have hl := List.dropLast_append_getLast hne
  rw [e] at hl
  rw [← hl, List.nodup_append] at hnd
  intro hz
  exact hnd.2.2 z hz z (List.mem_singleton_self z) rfl

/-- The truncated event: the head's seam cell and the path but its last cell. -/
def EvT (M : Fin m → ℕ → ℕ) (x y : ℕ) (l : List (Cell c m)) (ℓ₀ : ℕ) (f : Cell c m → ℕ) : Prop :=
  ∀ z ∈ truncOf l, f z ∈ presc (A := A) M x y l ℓ₀ z

/-! ### Chain bounds inside an event -/

section Cond

variable (hK : KeyInj 7 A M) (hA : ∀ v, (A v).card = 7) (hc : 1 ≤ c)

include hK hA in
/-- **The truncated chain bound inside an event read off the chain.** -/
theorem evT_cond_le {w x y ℓ₀ : ℕ} (hx : x < 7) (hy : y < 7) (hℓ : ℓ₀ = x ∨ ℓ₀ = y)
    {l : List (Cell c m)} (hl : CrossPath hc w l) (R : (Cell c m → ℕ) → Prop) [DecidablePred R]
    (hR : CSP.OffU (truncOf l).toFinset R) :
    (((slab c m 7 P A M).Ω.filter R).filter (EvT (A := A) M x y l ℓ₀)).card *
        (4 ^ (l.length - 1) * 3) ≤ ((slab c m 7 P A M).Ω.filter R).card := by
  obtain ⟨v₁, -, h1⟩ := hl.2.2.2.1
  obtain ⟨he, hnd, hch, hlen, hcol⟩ := truncOf_props hl h1
  have hne : truncOf l ≠ [] := by rw [he]; simp
  have hprod := (slab c m 7 P A M).card_prescribed_cond (slab_match hK) slab_irrefl (truncOf l) hnd
    (presc (A := A) M x y l ℓ₀) (fun z _ => presc_card_le hK hx hy l hℓ z) R hR
  have hge := chainProd_ge (P := P) (A := A) (M := M) (k := 7) (by omega) (truncOf l) hne hnd hch
    (fun z hz => cell_card_seven hA (hcol z hz))
  rw [hlen] at hge
  have hge' : 4 ^ (l.length - 1) * 3 ≤ (slab c m 7 P A M).chainProd (truncOf l) := by
    simpa using hge
  have heq : ((slab c m 7 P A M).Ω.filter R).filter (EvT (A := A) M x y l ℓ₀) =
      ((slab c m 7 P A M).Ω.filter R).filter
        (fun f => ∀ z ∈ truncOf l, f z ∈ presc (A := A) M x y l ℓ₀ z) := by
    ext f; simp only [mem_filter, EvT]
  rw [heq]
  exact le_trans (Nat.mul_le_mul_left _ hge') hprod

include hK hA in
/-- **The chain bound inside an event read off the chain.** -/
theorem event_cond_le {w x y ℓ₀ : ℕ} (hx : x < 7) (hy : y < 7) (hℓ : ℓ₀ = x ∨ ℓ₀ = y)
    {l : List (Cell c m)} (hl : CrossPath hc w l) (R : (Cell c m → ℕ) → Prop) [DecidablePred R]
    (hR : CSP.OffU (chainOf l).toFinset R) :
    (((slab c m 7 P A M).Ω.filter R).filter (Event (A := A) M x y l ℓ₀)).card *
        (4 ^ (l.length + 1) * 3) ≤ ((slab c m 7 P A M).Ω.filter R).card := by
  obtain ⟨hne, hnd, hch, hlen, hcol⟩ := chainOf_props hl
  have hprod := (slab c m 7 P A M).card_prescribed_cond (slab_match hK) slab_irrefl (chainOf l) hnd
    (presc (A := A) M x y l ℓ₀) (fun z _ => presc_card_le hK hx hy l hℓ z) R hR
  have hge := chainProd_ge (P := P) (A := A) (M := M) (k := 7) (by omega) (chainOf l) hne hnd hch
    (fun z hz => cell_card_seven hA (hcol z hz))
  rw [hlen, show l.length + 2 - 1 = l.length + 1 by omega] at hge
  have hge' : 4 ^ (l.length + 1) * 3 ≤ (slab c m 7 P A M).chainProd (chainOf l) := by
    simpa using hge
  have heq : ((slab c m 7 P A M).Ω.filter R).filter (Event (A := A) M x y l ℓ₀) =
      ((slab c m 7 P A M).Ω.filter R).filter
        (fun f => ∀ z ∈ chainOf l, f z ∈ presc (A := A) M x y l ℓ₀ z) := by
    ext f; simp only [mem_filter, Event]
  rw [heq]
  exact le_trans (Nat.mul_le_mul_left _ hge') hprod

end Cond

theorem offU_hit {hc : 1 ≤ c} {r : Fin m} {a₀ h : ℕ} {U : Finset (Cell c m)} (h1 : (1, r) ∉ U)
    (h2 : (fut0 hc, r) ∉ U) : CSP.OffU U (Hit hc r a₀ h) := by
  intro f g hfg
  unfold Hit
  rw [hfg _ h1, hfg _ h2]

/-! ### Realizing the error events -/

/-- A chain of adjacent vertices: every vertex is reachable from the head. -/
theorem reach_of_chain {V : Type*} {G : SimpleGraph V} :
    ∀ (l : List V), l.IsChain G.Adj → ∀ a ∈ l.head?, ∀ z ∈ l, G.Reachable a z
  | [], _, _, ha, _, _ => by simp at ha
  | [b], _, a, ha, z, hz => by
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha
      simp only [List.mem_singleton] at hz
      rw [← ha, hz]
  | b :: b' :: t, h, a, ha, z, hz => by
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha
      subst ha
      rw [List.isChain_cons_cons] at h
      rcases List.mem_cons.mp hz with rfl | hz
      · exact SimpleGraph.Reachable.refl _
      · exact h.1.reachable.trans (reach_of_chain _ h.2 b' (by simp) z hz)

/-- The keys with every row `≤ w` unpaired except `a₀` in row `r`, keyed `h`. -/
def keyT (M : Fin m → ℕ → ℕ) (w : ℕ) (r : Fin m) (a₀ h : ℕ) : Fin m → ℕ → ℕ :=
  fun v a => if w < v.val then M v a else if v = r ∧ a = a₀ then h else 7

section Realize

variable {hc : 1 ≤ c} {x y : ℕ}

theorem seed_keyT {w : ℕ} {r : Fin m} {a₀ h : ℕ} {f : Cell c m → ℕ} {s : Cell c m}
    (hs : Seed hc M w x y f s) : Seed hc (keyT M w r a₀ h) w x y f s := by
  obtain ⟨v, hv, rfl, hk, hxy⟩ := hs
  exact ⟨v, hv, rfl, by simpa [keyT, hv] using hk, hxy⟩

theorem seam_ne {k : ℕ} {f : Cell c m → ℕ} (hf : (slab c m k P A M).Valid f) (v : Fin m) :
    M v (f (1, v)) ≠ f (fut0 hc, v) := by
  have := hf.2 (1, v) (fut0 hc, v) (slabAdj_seam (fut0 hc, v) rfl)
  rwa [slab_conf_seam (Fin.val_one _) rfl] at this

theorem seam_mem {k : ℕ} {f : Cell c m → ℕ} (hf : (slab c m k P A M).Valid f) (v : Fin m) :
    f (1, v) ∈ A v := by
  have := hf.1 (1, v); rwa [slab_D_one (Fin.val_one _)] at this

/-- **`(2, r)` swapped**: a chordless chain from a seed to `(2, r)`, realizing the truncated
event in the phase forced by the hit event. -/
theorem realize_inT {k w : ℕ} (hxy : x ≠ y) (hx7 : x ≠ 7) (hy7 : y ≠ 7) {r : Fin m} (hr : r.val = w)
    {a₀ h : ℕ} {f : Cell c m → ℕ} (hf : (slab c m k P A M).Valid f) (hhit : Hit hc r a₀ h f)
    (hhxy : h = x ∨ h = y) (hin : InT hc M w x y f (fut0 hc, r)) :
    ∃ l ∈ crossPaths hc w, Chordless l ∧ lastRow l = w ∧
      ∃ ℓ₀ ∈ ({x, y} : Finset ℕ), lab x y ℓ₀ (l.length - 1) = h ∧ EvT (A := A) M x y l ℓ₀ f := by
  obtain ⟨s, hs, hreach⟩ := hin
  have hb : Bad hc (keyT M w r a₀ h) w x y f := by
    refine ⟨s, seed_keyT hs, r, hr.le, ?_, hreach⟩
    have : keyT M w r a₀ h r (f (1, r)) = h := by simp [keyT, hr, hhit.1]
    rw [this]; exact hhxy
  obtain ⟨l, ⟨hnd, hch, hxyl, ⟨v₁, hw₁, h1, hk₁⟩, ⟨v₂, hw₂, h2, hk₂⟩⟩, hcl⟩ :=
    exists_chordless_witn hb
  have hv₂ : v₂ = r := by
    by_contra hne
    have : keyT M w r a₀ h v₂ (f (1, v₂)) = 7 := by
      simp only [keyT]; rw [ite_eq_right (by omega), ite_eq_right (by tauto)]
    rw [this] at hk₂; rcases hk₂ with e | e <;> [exact hx7 e.symm; exact hy7 e.symm]
  subst hv₂
  have hk₁' : M v₁ (f (1, v₁)) = x ∨ M v₁ (f (1, v₁)) = y := by simpa [keyT, hw₁] using hk₁
  have hcp : CrossPath hc w l := ⟨hnd, hch, fun z hz => (hxyl z hz).1, ⟨v₁, hw₁, h1⟩,
    ⟨v₂, hw₂, h2⟩⟩
  have hne : l ≠ [] := by rintro rfl; simp at h1
  have hkch : l.IsChain (kG x y f).Adj := by
    rw [List.IsChain.iff_mem] at hch
    exact hch.imp fun a b h => ⟨h.2.2, hxyl a h.1, hxyl b h.2.1⟩
  have hxy₁ : XY x y f (fut0 hc, v₁) := hxyl _ (List.mem_of_mem_head? h1)
  have hℓ := hxy₁.2
  have halt := alt_of_chain hxy hf l (f (fut0 hc, v₁)) hkch
    (fun a ha => by rw [h1] at ha; simp at ha; rw [ha]) hℓ
  have hlen : l.length - 1 < l.length := by
    have := List.length_pos_of_ne_nil hne; omega
  refine ⟨l, mem_filter.mpr ⟨mem_allLists hnd, hcp⟩, hcl, by rw [lastRow_of_last h2, hr],
    f (fut0 hc, v₁), by rcases hℓ with e | e <;> simp [e], ?_, ?_⟩
  · have e1 : l[l.length - 1] = (fut0 hc, v₂) := by
      have := List.getLast_eq_getElem hne
      rw [← this]
      rw [List.getLast?_eq_some_getLast hne] at h2
      exact Option.some.inj h2
    rw [← halt _ hlen, e1]; exact hhit.2
  · intro z hz
    obtain ⟨he, -⟩ := truncOf_props hcp h1
    rw [he, List.mem_cons] at hz
    unfold presc
    rcases hz with rfl | hz
    · rw [ite_eq_left (Fin.val_one _), ite_eq_left (by rw [h1]; rfl), mem_filter]
      exact ⟨seam_mem hf v₁, eq_oth hxy hℓ hk₁' (seam_ne hf v₁)⟩
    · have hzl := (List.dropLast_sublist l).subset hz
      have h2c := (hxyl z hzl).1
      rw [ite_eq_right (by omega), mem_singleton]
      have hi := List.idxOf_lt_length_of_mem hzl
      have := halt _ hi
      rwa [List.getElem_idxOf] at this

/-- **Bad, `(2, r)` not swapped**: a chordless crossing chain avoiding `(2, r)`, ending below
row `r`. -/
theorem realize_bad {k w : ℕ} (hxy : x ≠ y) {r : Fin m} (hr : r.val = w) {f : Cell c m → ℕ}
    (hf : (slab c m k P A M).Valid f) (hb : Bad hc M w x y f)
    (hnin : ¬ InT hc M w x y f (fut0 hc, r)) :
    ∃ l ∈ crossPaths hc w, (Chordless l ∧ lastRow l + 1 ≤ w ∧ (fut0 hc, r) ∉ l) ∧
      ∃ ℓ₀ ∈ ({x, y} : Finset ℕ), Event (A := A) M x y l ℓ₀ f := by
  obtain ⟨l, hW, hcl⟩ := exists_chordless_witn hb
  obtain ⟨hmem, ℓ₀, hℓ, he⟩ := event_of_witn (P := P) hxy hf hW
  obtain ⟨hnd, hch, hxyl, ⟨v₁, hw₁, h1, hk₁⟩, ⟨v₂, hw₂, h2, hk₂⟩⟩ := hW
  have hkch : l.IsChain (kG x y f).Adj := by
    rw [List.IsChain.iff_mem] at hch
    exact hch.imp fun a b h => ⟨h.2.2, hxyl a h.1, hxyl b h.2.1⟩
  have hseed : Seed hc M w x y f (fut0 hc, v₁) :=
    ⟨v₁, hw₁, rfl, hk₁, hxyl _ (List.mem_of_mem_head? h1)⟩
  have hinT : ∀ z ∈ l, InT hc M w x y f z := fun z hz =>
    ⟨_, hseed, reach_of_chain l hkch _ (by rw [h1]; rfl) z hz⟩
  have hnot : (fut0 hc, r) ∉ l := fun h => hnin (hinT _ h)
  have hv : v₂ ≠ r := by
    rintro rfl; exact hnot (List.mem_of_mem_getLast? h2)
  have hv' : v₂.val ≠ w := fun e => hv (Fin.ext (e.trans hr.symm))
  exact ⟨l, hmem, ⟨hcl, by rw [lastRow_of_last h2]; omega, hnot⟩, ℓ₀, hℓ, he⟩

end Realize

/-! ### The weights and the constant -/

/-- The weight of a chain to `(2, r)`. -/
noncomputable def dAw (L : ℕ) : ℚ := 4 / 3 * (1 / 4) ^ L

/-- The weight of a bad chain avoiding `(2, r)`, both phases. -/
noncomputable def dRw (L : ℕ) : ℚ := 1 / 6 * (1 / 4) ^ L

/-- **The drift constant.** -/
noncomputable def dM : ℚ :=
  ∑ L ∈ range 21, (A7 L : ℚ) * dAw L + 27 * M7 / 4 ^ 20 +
    (∑ L ∈ range 21, (R7 L : ℚ) * dRw L + 567 / 8 * M7 / 4 ^ 20)

theorem dM_le : dM ≤ 301 / 2500 := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20⟩ := A7_vals
  obtain ⟨r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19,
    r20⟩ := R7_vals
  have h0 : A7 0 = 0 := by decide
  have h1 : A7 1 = 0 := by decide
  have r0 : R7 0 = 0 := by simp [R7]
  have r1 : R7 1 = 0 := by simp [R7]
  unfold dM
  simp only [sum_range_succ, sum_range_zero, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, h14, h15, h16, h17, h18, h19, h20, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11,
    r12, r13, r14, r15, r16, r17, r18, r19, r20, dAw, dRw, M7]
  norm_num

theorem dA_sum_le (c m : ℕ) :
    ∑ L ∈ range 21, (A7 L : ℚ) * dAw L +
        ∑ L ∈ Ico 21 (Fintype.card (Cell c m) + 1), (tailA L : ℚ) * dAw L ≤
      ∑ L ∈ range 21, (A7 L : ℚ) * dAw L + 27 * M7 / 4 ^ 20 := by
  refine add_le_add le_rfl ?_
  have e : ∑ L ∈ Ico 21 (Fintype.card (Cell c m) + 1), (tailA L : ℚ) * dAw L =
      4 / 3 * ∑ L ∈ Ico 21 (Fintype.card (Cell c m) + 1), (tailA L : ℚ) * (1 / 4) ^ L := by
    rw [mul_sum]; refine sum_congr rfl fun L _ => ?_; rw [dAw]; ring
  rw [e]
  have := tailA_sum_le (Fintype.card (Cell c m) + 1)
  linarith

theorem dR_sum_le (c m : ℕ) :
    ∑ L ∈ range 21, (R7 L : ℚ) * dRw L +
        ∑ L ∈ Ico 21 (Fintype.card (Cell c m) + 1), (tailR L : ℚ) * dRw L ≤
      ∑ L ∈ range 21, (R7 L : ℚ) * dRw L + 567 / 8 * M7 / 4 ^ 20 := by
  refine add_le_add le_rfl ?_
  have e : ∑ L ∈ Ico 21 (Fintype.card (Cell c m) + 1), (tailR L : ℚ) * dRw L =
      1 / 6 * ∑ L ∈ Ico 21 (Fintype.card (Cell c m) + 1), (tailR L : ℚ) * (1 / 4) ^ L := by
    rw [mul_sum]; refine sum_congr rfl fun L _ => ?_; rw [dRw]; ring
  rw [e]
  have := tailR_sum_le (Fintype.card (Cell c m) + 1)
  linarith

theorem le_dA {E H : ℚ} (n : ℕ) (h : E * (4 ^ n * 3) ≤ H) : E ≤ dAw (n + 1) * H := by
  have e : dAw (n + 1) * H = H / (4 ^ n * 3) := by
    rw [dAw, pow_succ, one_div_pow]; field_simp
  rw [e, le_div_iff₀ (by positivity)]; exact h

theorem le_dR {E H : ℚ} (n : ℕ) (h : E * (4 ^ (n + 1) * 3) ≤ H) : 2 * E ≤ dRw n * H := by
  have e : dRw n * H = 2 * (H / (4 ^ (n + 1) * 3)) := by
    rw [dRw, one_div_pow, pow_succ]; field_simp; ring
  rw [e]
  have : E ≤ H / (4 ^ (n + 1) * 3) := by rw [le_div_iff₀ (by positivity)]; exact h
  linarith

/-! ### The drift -/

section Drift

variable (hK : KeyInj 7 A M) (hA : ∀ v, (A v).card = 7) (hc : 1 ≤ c)

include hK hA in
/-- **The error events are rare inside the hit event.** -/
theorem drift_err (r : Fin m) {x h : ℕ} (hx : x < 7) (hh : h < 7) (hxh : x ≠ h) {a₀ : ℕ} :
    ((((slab c m 7 P A M).Ω.filter (Hit hc r a₀ h)).filter
        (fun f => Bad hc M r.val x h f ∨ InT hc M r.val x h f (fut0 hc, r))).card : ℚ) ≤
      dM * ((slab c m 7 P A M).Ω.filter (Hit hc r a₀ h)).card := by
  set w := r.val with hw
  set C := slab c m 7 P A M
  set H₁ := C.Ω.filter (Hit hc r a₀ h)
  set SA := (crossPaths hc w).filter (fun l => Chordless l ∧ lastRow l = w)
  set SB := (crossPaths hc w).filter (fun l => Chordless l ∧ lastRow l + 1 ≤ w ∧ (fut0 hc, r) ∉ l)
  set FA := fun l : List (Cell c m) =>
    ({x, h} : Finset ℕ).filter (fun ℓ₀ => lab x h ℓ₀ (l.length - 1) = h)
  -- the error events lie in the chain events
  have hsub : H₁.filter (fun f => Bad hc M w x h f ∨ InT hc M w x h f (fut0 hc, r)) ⊆
      SA.biUnion (fun l => (FA l).biUnion (fun ℓ₀ => H₁.filter (EvT (A := A) M x h l ℓ₀))) ∪
        SB.biUnion (fun l => ({x, h} : Finset ℕ).biUnion
          (fun ℓ₀ => H₁.filter (Event (A := A) M x h l ℓ₀))) := by
    intro f hf
    rw [mem_filter] at hf
    have hfΩ := (mem_filter.mp hf.1).1
    have hhit := (mem_filter.mp hf.1).2
    have hval := (CSP.mem_Ω _).mp hfΩ
    rw [mem_union]
    by_cases hin : InT hc M w x h f (fut0 hc, r)
    · left
      obtain ⟨l, hl, hcl, hrow, ℓ₀, hℓ, hlab, hev⟩ := realize_inT (P := P) hxh (by omega)
        (by omega) rfl hval hhit (Or.inr rfl) hin
      rw [mem_biUnion]
      refine ⟨l, mem_filter.mpr ⟨hl, hcl, hrow⟩, mem_biUnion.mpr ⟨ℓ₀, mem_filter.mpr ⟨hℓ, hlab⟩,
        mem_filter.mpr ⟨hf.1, hev⟩⟩⟩
    · right
      have hb : Bad hc M w x h f := by tauto
      obtain ⟨l, hl, hp, ℓ₀, hℓ, hev⟩ := realize_bad (P := P) hxh rfl hval hb hin
      rw [mem_biUnion]
      exact ⟨l, mem_filter.mpr ⟨hl, hp⟩, mem_biUnion.mpr ⟨ℓ₀, hℓ, mem_filter.mpr ⟨hf.1, hev⟩⟩⟩
  have hcard := le_trans (card_le_card hsub) (card_union_le _ _)
  have hA1 : ((SA.biUnion (fun l => (FA l).biUnion
      (fun ℓ₀ => H₁.filter (EvT (A := A) M x h l ℓ₀)))).card : ℚ) ≤
      (∑ l ∈ SA, dAw l.length) * H₁.card := by
    refine le_trans (Nat.cast_le.mpr (card_biUnion_le)) ?_
    push_cast
    rw [sum_mul]
    refine sum_le_sum fun l hl => ?_
    obtain ⟨hlc, hcl, hrow⟩ := mem_filter.mp hl
    have hcp : CrossPath hc w l := (mem_filter.mp hlc).2
    have h2 := two_le_length hcp
    obtain ⟨v₁, hw₁, h1⟩ := hcp.2.2.2.1
    obtain ⟨v₂, -, h2'⟩ := hcp.2.2.2.2
    have hv₂ : v₂ = r := Fin.ext (by rw [lastRow_of_last h2'] at hrow; exact hrow)
    subst hv₂
    obtain ⟨he, -⟩ := truncOf_props hcp h1
    have hR : CSP.OffU (truncOf l).toFinset (Hit hc v₂ a₀ h) := by
      refine offU_hit ?_ ?_ <;> rw [List.mem_toFinset, he, List.mem_cons] <;> rintro (e | e)
      · have := congrArg (fun z : Cell c m => z.2.val) e; simp at this; omega
      · have := hcp.2.2.1 _ ((List.dropLast_sublist l).subset e); simp at this
      · have := congrArg (fun z : Cell c m => z.1.val) e; simp [fut0] at this
      · exact not_mem_dropLast hcp.1 h2' e
    have hF : (FA l).card ≤ 1 := by
      refine card_le_one.mpr fun a ha b hb => ?_
      rw [mem_filter] at ha hb
      exact lab_inj hxh (by simpa using ha.1) (by simpa using hb.1) _ (ha.2.trans hb.2.symm)
    obtain ⟨n, hn⟩ : ∃ n, l.length = n + 1 := ⟨l.length - 1, by omega⟩
    have hone : ∀ ℓ₀ ∈ FA l, ((H₁.filter (EvT (A := A) M x h l ℓ₀)).card : ℚ) ≤
        dAw l.length * H₁.card := fun ℓ₀ hℓ₀ => by
      have hℓ : ℓ₀ = x ∨ ℓ₀ = h := by simpa using (mem_filter.mp hℓ₀).1
      have := evT_cond_le (P := P) hK hA hc hx hh hℓ hcp _ hR
      rw [hn, show n + 1 - 1 = n by omega] at this
      rw [hn]; exact le_dA n (by exact_mod_cast this)
    refine le_trans (Nat.cast_le.mpr card_biUnion_le) ?_
    push_cast
    calc ∑ ℓ₀ ∈ FA l, ((H₁.filter (EvT (A := A) M x h l ℓ₀)).card : ℚ)
        ≤ ∑ ℓ₀ ∈ FA l, dAw l.length * H₁.card := sum_le_sum hone
      _ = (FA l).card * (dAw l.length * H₁.card) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 1 * (dAw l.length * H₁.card) := mul_le_mul_of_nonneg_right (by exact_mod_cast hF)
          (mul_nonneg (by unfold dAw; positivity) (by positivity))
      _ = _ := one_mul _
  have hB1 : ((SB.biUnion (fun l => ({x, h} : Finset ℕ).biUnion
      (fun ℓ₀ => H₁.filter (Event (A := A) M x h l ℓ₀)))).card : ℚ) ≤
      (∑ l ∈ SB, dRw l.length) * H₁.card := by
    refine le_trans (Nat.cast_le.mpr (card_biUnion_le)) ?_
    push_cast
    rw [sum_mul]
    refine sum_le_sum fun l hl => ?_
    obtain ⟨hlc, hcl, hrow, hnot⟩ := mem_filter.mp hl
    have hcp : CrossPath hc w l := (mem_filter.mp hlc).2
    obtain ⟨v₁, hw₁, h1⟩ := hcp.2.2.2.1
    obtain ⟨v₂, -, h2'⟩ := hcp.2.2.2.2
    have hrow' := hrow
    rw [lastRow_of_last h2'] at hrow'
    have hR : CSP.OffU (chainOf l).toFinset (Hit hc r a₀ h) := by
      refine offU_hit ?_ ?_ <;> rw [List.mem_toFinset, chainOf_eq h1 h2'] <;>
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil,
          or_false] <;> rintro (e | e | e)
      · have := congrArg (fun z : Cell c m => z.2.val) e; simp at this; omega
      · have := hcp.2.2.1 _ e; simp at this
      · have := congrArg (fun z : Cell c m => z.2.val) e; simp at this; omega
      · have := congrArg (fun z : Cell c m => z.1.val) e; simp [fut0] at this
      · exact hnot e
      · have := congrArg (fun z : Cell c m => z.1.val) e; simp [fut0] at this
    have hpair : ∀ ℓ₀ ∈ ({x, h} : Finset ℕ), 2 * ((H₁.filter (Event (A := A) M x h l ℓ₀)).card : ℚ) ≤
        dRw l.length * H₁.card := fun ℓ₀ hℓ₀ => by
      have hℓ : ℓ₀ = x ∨ ℓ₀ = h := by simpa using hℓ₀
      have := event_cond_le (P := P) hK hA hc hx hh hℓ hcp _ hR
      exact le_dR _ (by exact_mod_cast this)
    refine le_trans (Nat.cast_le.mpr card_biUnion_le) ?_
    push_cast
    rw [sum_pair hxh]
    have := hpair x (by simp)
    have := hpair h (by simp)
    linarith
  have hSA := sum_chordless_DA (m := m) hc w dAw (fun L => by unfold dAw; positivity)
  have hSB : ∑ l ∈ SB, dRw l.length ≤
      ∑ l ∈ (crossPaths hc w).filter (fun l => Chordless l ∧ lastRow l + 1 ≤ w), dRw l.length :=
    sum_le_sum_of_subset_of_nonneg
      (fun l hl => by
        obtain ⟨h1, h2, h3, -⟩ := mem_filter.mp hl
        exact mem_filter.mpr ⟨h1, h2, h3⟩)
      (fun L _ _ => by unfold dRw; positivity)
  have hSR := sum_chordless_DR (m := m) hc w dRw (fun L => by unfold dRw; positivity)
  have htot : ∑ l ∈ SA, dAw l.length + ∑ l ∈ SB, dRw l.length ≤ dM := by
    have := dA_sum_le c m
    have := dR_sum_le c m
    unfold dM
    linarith
  have hH0 : (0 : ℚ) ≤ H₁.card := by positivity
  calc _ ≤ (((SA.biUnion (fun l => (FA l).biUnion
          (fun ℓ₀ => H₁.filter (EvT (A := A) M x h l ℓ₀)))).card : ℚ) +
          ((SB.biUnion (fun l => ({x, h} : Finset ℕ).biUnion
            (fun ℓ₀ => H₁.filter (Event (A := A) M x h l ℓ₀)))).card : ℚ)) := by
        exact_mod_cast hcard
    _ ≤ (∑ l ∈ SA, dAw l.length) * H₁.card + (∑ l ∈ SB, dRw l.length) * H₁.card :=
        add_le_add hA1 hB1
    _ = (∑ l ∈ SA, dAw l.length + ∑ l ∈ SB, dRw l.length) * H₁.card := by ring
    _ ≤ dM * H₁.card := mul_le_mul_of_nonneg_right htot hH0

include hK hA in
/-- **The drift.** -/
theorem drift7 (r : Fin m) {x h : ℕ} (hx : x < 7) (hh : h < 7) (hxh : x ≠ h) {a₀ : ℕ} :
    (((slab c m 7 P A (moveKey M r.val x h)).Ω.filter (Hit hc r a₀ h)).card : ℚ) ≤
      (1 + 7 / 50) * ((slab c m 7 P A M).Ω.filter (Hit hc r a₀ h)).card := by
  set w := r.val
  set M₁ := moveKey M w x h
  have hK₁ : KeyInj 7 A M₁ := keyInj_moveKey hK w hx hh
  set H₁ := (slab c m 7 P A M₁).Ω.filter (Hit hc r a₀ h)
  set H₀ := (slab c m 7 P A M).Ω.filter (Hit hc r a₀ h)
  -- the solutions kept by the backward move
  have hkeep : (H₁.filter (fun f => ¬ (Bad hc M₁ w x h f ∨ InT hc M₁ w x h f (fut0 hc, r)))).card ≤
      H₀.card := by
    refine card_le_card_of_injOn (kswap hc M₁ w x h) (fun f hf => ?_) (fun f _ f' _ he => ?_)
    · rw [mem_coe, mem_filter, mem_filter, CSP.mem_Ω] at hf
      obtain ⟨⟨hval, hhit⟩, hn⟩ := hf
      rw [not_or] at hn
      rw [mem_coe, mem_filter, CSP.mem_Ω]
      have hv := valid_kswap (P := P) (A := A) (hc := hc) hx hh hval hn.1
      rw [moveKey_moveKey] at hv
      refine ⟨hv, ?_, ?_⟩
      · rw [kswap_of_lt (by simp)]; exact hhit.1
      · unfold kswap; rw [ite_eq_right (fun h' => absurd h' hn.2)]; exact hhit.2
    · have := congrArg (kswap hc (moveKey M₁ w x h) w x h) he
      rwa [kswap_kswap, kswap_kswap] at this
  have herr := drift_err (P := P) hK₁ hA hc r hx hh hxh (a₀ := a₀)
  have hsplit := card_filter_add_card_filter_not (s := H₁)
    (fun f => Bad hc M₁ w x h f ∨ InT hc M₁ w x h f (fut0 hc, r))
  have hsplit' : (H₁.card : ℚ) =
      ((H₁.filter (fun f => Bad hc M₁ w x h f ∨ InT hc M₁ w x h f (fut0 hc, r))).card : ℚ) +
        ((H₁.filter (fun f => ¬ (Bad hc M₁ w x h f ∨ InT hc M₁ w x h f (fut0 hc, r)))).card : ℚ) := by
    exact_mod_cast hsplit.symm
  have hkeep' : ((H₁.filter (fun f => ¬ (Bad hc M₁ w x h f ∨
      InT hc M₁ w x h f (fut0 hc, r)))).card : ℚ) ≤ H₀.card := by exact_mod_cast hkeep
  have hd := dM_le
  have hdM0 : 0 ≤ dM := by
    unfold dM
    have : ∀ L, 0 ≤ (A7 L : ℚ) * dAw L := fun L => mul_nonneg (by positivity)
      (by unfold dAw; positivity)
    have : ∀ L, 0 ≤ (R7 L : ℚ) * dRw L := fun L => mul_nonneg (by positivity)
      (by unfold dRw; positivity)
    have := sum_nonneg fun L (_ : L ∈ range 21) => (this L)
    have := sum_nonneg fun L (_ : L ∈ range 21) =>
      mul_nonneg (by positivity : (0 : ℚ) ≤ A7 L) (by unfold dAw; positivity : (0 : ℚ) ≤ dAw L)
    have : (0 : ℚ) ≤ M7 := by positivity
    positivity
  have hH1 : (0 : ℚ) ≤ H₁.card := by positivity
  -- `H₁ ≤ H₀ + dM · H₁` with `dM ≤ 301/2500`
  have h1 : (H₁.card : ℚ) ≤ H₀.card + 301 / 2500 * H₁.card := by
    have : dM * H₁.card ≤ 301 / 2500 * H₁.card := mul_le_mul_of_nonneg_right hd hH1
    linarith
  nlinarith

end Drift

end GridGen.Gauge
