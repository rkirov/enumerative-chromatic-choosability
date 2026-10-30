/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.ExType

/-!
# Height six at `k = 6`: the exact certificates are sound

`seam_shape`: a certificate (`certOK`) whose patterns all pass (`patS`, `patK` for the three kinds
of the first row) gives the seam inequality for every system of lists of shape `j`. See
`GridGen/Six/ExDefs.lean` for the checker and `GridGen/Six/ExType.lean` for the types.
-/

namespace GridGen.Six

open Finset

/-! ### Images and the common pattern values -/

theorem card_image_eq_of_iff {R : Finset ℕ} {f g : ℕ → ℕ}
    (h : ∀ a ∈ R, ∀ b ∈ R, f a = f b ↔ g a = g b) : (R.image f).card = (R.image g).card := by
  have h1 : (R.image f) = (R.image fun r => (f r, g r)).image Prod.fst := by
    rw [Finset.image_image]; rfl
  have h2 : (R.image g) = (R.image fun r => (f r, g r)).image Prod.snd := by
    rw [Finset.image_image]; rfl
  have e1 : ((R.image fun r => (f r, g r)).image Prod.fst).card
      = (R.image fun r => (f r, g r)).card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    simp only at hxy
    rw [(h a ha b hb).mp hxy, hxy]
  have e2 : ((R.image fun r => (f r, g r)).image Prod.snd).card
      = (R.image fun r => (f r, g r)).card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    simp only at hxy
    rw [(h a ha b hb).mpr hxy, hxy]
  rw [h1, h2, e1, e2]

section shape

variable {j : ℕ} {U V : Finset ℕ}

/-- The common rows of a column. -/
def wRows (j : ℕ) (U V : Finset ℕ) (s : T6) : Finset ℕ := (range 6).filter fun r => kap j U V s r = 0

theorem setOf_wm (s : T6) :
    setOf (wmK (canon s) (kap j U V s)) = (wRows j U V s).image fun r => rowAt r (canon s) := by
  ext x
  rw [mem_setOf_wmK _ _ (fun r hr => canon_lt s hr)]
  simp only [wRows, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨r, hr, h0, rfl⟩; exact ⟨r, ⟨hr, h0⟩, rfl⟩
  · rintro ⟨r, ⟨hr, h0⟩, rfl⟩; exact ⟨r, hr, h0, rfl⟩

/-- **At most five common pattern values.** -/
theorem popc_wm_le (hW : (U ∩ V).card = 5) {s : T6} (hs : Proper s) :
    popc (wmK (canon s) (kap j U V s)) ≤ 5 := by
  rw [← card_setOf, setOf_wm, card_image_eq_of_iff (g := fun r => rowAt r s)]
  · rw [← hW]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    exact (kap_zero_iff s r).mp (Finset.mem_filter.mp hr).2
  · intro a ha b hb
    exact canon_rows hs (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)

theorem kap_lt (s : T6) (r : ℕ) : kap j U V s r < 8 := by
  unfold kap kapC; split_ifs <;> omega

/-- The label of a common row is its rank, below `5`. -/
theorem lab_common (hW : (U ∩ V).card = 5) {s : T6} (hs : Proper s) {r : ℕ} (hr : r < 6)
    (h0 : kap j U V s r = 0) :
    (labL (canon s) (kap j U V s)).getD r 7 = rk (wmK (canon s) (kap j U V s)) (rowAt r (canon s)) ∧
      (labL (canon s) (kap j U V s)).getD r 7 < 5 := by
  have e : (labL (canon s) (kap j U V s)).getD r 7
      = rk (wmK (canon s) (kap j U V s)) (rowAt r (canon s)) := by
    rw [labL_getD _ _ hr]; unfold lab; rw [h0]; rfl
  refine ⟨e, e ▸ lt_of_lt_of_le (rk_lt_popc ?_ (by have := canon_lt s hr; omega)) (popc_wm_le hW hs)⟩
  rw [setOf_wm]
  exact Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, h0⟩, rfl⟩

theorem lab_other {s : T6} {r : ℕ} (hr : r < 6) (h0 : kap j U V s r ≠ 0) :
    (labL (canon s) (kap j U V s)).getD r 7 = kap j U V s r := by
  rw [labL_getD _ _ hr]
  unfold lab
  rw [nbeq, decide_eq_false h0, Bool.cond_false]

/-- Two common rows have the same label iff the same colour. -/
theorem lab_iff (hW : (U ∩ V).card = 5) {s : T6} (hs : Proper s) {r i : ℕ} (hr : r < 6)
    (hi : i < 6) (h0 : kap j U V s r = 0) (h0' : kap j U V s i = 0) :
    rowAt r s = rowAt i s ↔
      (labL (canon s) (kap j U V s)).getD r 7 = (labL (canon s) (kap j U V s)).getD i 7 := by
  rw [(lab_common hW hs hr h0).1, (lab_common hW hs hi h0').1, ← canon_rows hs hr hi]
  have mr : rowAt r (canon s) ∈ setOf (wmK (canon s) (kap j U V s)) := by
    rw [setOf_wm]
    exact Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, h0⟩, rfl⟩
  have mi : rowAt i (canon s) ∈ setOf (wmK (canon s) (kap j U V s)) := by
    rw [setOf_wm]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, h0'⟩, rfl⟩
  constructor
  · intro h; rw [h]
  · exact rk_inj mr mi (by have := canon_lt s hr; omega) (by have := canon_lt s hi; omega)

theorem lab_lt8 (hW : (U ∩ V).card = 5) {s : T6} (hs : Proper s) {r : ℕ} (hr : r < 6) :
    (labL (canon s) (kap j U V s)).getD r 7 < 8 := by
  by_cases h0 : kap j U V s r = 0
  · have := (lab_common hW hs hr h0).2; omega
  · rw [lab_other hr h0]; exact kap_lt s r

/-! ### The relabelling -/

/-- A map of the common colours onto `{0, …, 4}` extending a consistent labelling of rows. -/
theorem exists_W_map {W : Finset ℕ} (hW : W.card = 5) (c l : ℕ → ℕ)
    (hl : ∀ r < 6, c r ∈ W → l r < 5)
    (hc : ∀ r < 6, ∀ i < 6, c r ∈ W → c i ∈ W → (c r = c i ↔ l r = l i)) :
    ∃ g : ℕ → ℕ, Set.InjOn g ↑W ∧ W.image g = range 5 ∧ ∀ r < 6, c r ∈ W → g (c r) = l r := by
  let R : {x // x ∈ W} → Finset ℕ := fun x => (range 6).filter (fun r => c r = x.1)
  have hR : ∀ x r, r ∈ R x ↔ r < 6 ∧ c r = x.1 := fun x r => by simp [R]
  let f : {x // x ∈ W} → ℕ := fun x => if h : (R x).Nonempty then l ((R x).min' h) else 0
  let S : Finset {x // x ∈ W} := Finset.univ.filter (fun x => (R x).Nonempty)
  have hf : ∀ x (h : (R x).Nonempty), f x = l ((R x).min' h) := fun x h => dif_pos h
  have hmin : ∀ x (h : (R x).Nonempty), (R x).min' h < 6 ∧ c ((R x).min' h) = x.1 :=
    fun x h => (hR x _).mp (Finset.min'_mem _ h)
  have hfS : S.image f ⊆ range 5 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have h := (Finset.mem_filter.mp hx).2
    rw [hf x h, Finset.mem_range]
    have := hmin x h
    exact hl _ this.1 (by rw [this.2]; exact x.2)
  have hfinj : Set.InjOn f ↑S := by
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    have hy' := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
    rw [hf x hx', hf y hy'] at hxy
    have sx := hmin x hx'
    have sy := hmin y hy'
    apply Subtype.ext
    rw [← sx.2, ← sy.2]
    exact (hc _ sx.1 _ sy.1 (by rw [sx.2]; exact x.2) (by rw [sy.2]; exact y.2)).mpr hxy
  obtain ⟨e, he⟩ :=
    Finset.exists_equiv_extend_of_card_eq (by rw [Fintype.card_coe, hW, card_range]) hfS hfinj
  let g : ℕ → ℕ := fun x => if hx : x ∈ W then (e ⟨x, hx⟩ : ℕ) else x
  have hg : ∀ x (hx : x ∈ W), g x = e ⟨x, hx⟩ := fun x hx => dif_pos hx
  refine ⟨g, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [hg x hx, hg y hy] at hxy
    exact congrArg Subtype.val (e.injective (Subtype.ext hxy))
  · ext y
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩; rw [hg x hx]; exact (e ⟨x, hx⟩).2
    · intro hy
      refine ⟨(e.symm ⟨y, hy⟩ : ℕ), (e.symm ⟨y, hy⟩).2, ?_⟩
      rw [hg _ (e.symm ⟨y, hy⟩).2]
      simp
  · intro r hr hcr
    rw [hg _ hcr]
    have hex : (R ⟨c r, hcr⟩).Nonempty := ⟨r, (hR _ r).mpr ⟨hr, rfl⟩⟩
    rw [he ⟨c r, hcr⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hex⟩), hf _ hex]
    have := hmin _ hex
    exact (hc _ this.1 _ hr (by rw [this.2]; exact hcr) hcr).mp this.2

theorem setOf_63 : setOf 63 = range 6 := by decide
theorem setOf_95 : setOf 95 = insert 6 (range 5) := by decide

theorem bmJ_lt (j r : ℕ) : bmJ j r < 128 := by unfold bmJ; cases Nat.blt r j <;> decide

theorem not_mem_setOf_bmJ (j r x : ℕ) (hx : 7 ≤ x) : x ∉ setOf (bmJ j r) := by
  unfold setOf
  simp only [Finset.mem_filter, Finset.mem_range, not_and]
  intro hx8
  have : x = 7 := by omega
  subst this
  unfold bmJ; cases Nat.blt r j <;> decide

theorem testBit_em : ∀ l < 8, ∀ x < 8, (255 - 2 ^ l : ℕ).testBit x = !(x == l) := by decide

theorem setOf_em (m l : ℕ) (hl : l < 8) : setOf (em m l) = (setOf m).erase l := by
  have key : ∀ x, (em m l).testBit x = (m.testBit x && (255 - 2 ^ l : ℕ).testBit x) :=
    fun x => Nat.testBit_and m (255 - 2 ^ l) x
  ext x
  simp only [setOf, Finset.mem_filter, Finset.mem_range, Finset.mem_erase, key]
  constructor
  · rintro ⟨hx, h⟩
    rw [Bool.and_eq_true, testBit_em l hl x hx] at h
    exact ⟨by simpa using h.2, hx, h.1⟩
  · rintro ⟨hne, hx, h⟩
    refine ⟨hx, ?_⟩
    rw [Bool.and_eq_true, testBit_em l hl x hx]
    exact ⟨h, by simpa using hne⟩

/-- **The relabelling of the lists of a column.** -/
theorem exists_sigma (hU : U.card = 6) (hV : V.card = 6) (hW : (U ∩ V).card = 5) {s : T6}
    (hs : Proper s) : ∃ σ : ℕ → ℕ, Set.InjOn σ ↑(U ∪ V) ∧
      (∀ r < 6, (bj j U V r).image σ = setOf (bmJ j r)) ∧
      (∀ r < 6, ((bj j U V r).erase (rowAt r s)).image σ
        = setOf (em (bmJ j r) ((labL (canon s) (kap j U V s)).getD r 7))) := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (card_sdiff_one hU hW)
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp (card_sdiff_one hV (by rw [Finset.inter_comm]; exact hW))
  have haU : a ∈ U := (Finset.mem_sdiff.mp (by rw [ha]; simp : a ∈ U \ V)).1
  have haV : a ∉ V := (Finset.mem_sdiff.mp (by rw [ha]; simp : a ∈ U \ V)).2
  have hbV : b ∈ V := (Finset.mem_sdiff.mp (by rw [hb]; simp : b ∈ V \ U)).1
  have hbU : b ∉ U := (Finset.mem_sdiff.mp (by rw [hb]; simp : b ∈ V \ U)).2
  have hUe : U = insert a (U ∩ V) := by
    ext x; constructor
    · intro hx; by_cases hxV : x ∈ V
      · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hx, hxV⟩)
      · have : x ∈ U \ V := Finset.mem_sdiff.mpr ⟨hx, hxV⟩
        rw [ha] at this; simp at this; simp [this]
    · intro hx; rcases Finset.mem_insert.mp hx with rfl | hx
      · exact haU
      · exact (Finset.mem_inter.mp hx).1
  have hVe : V = insert b (U ∩ V) := by
    ext x; constructor
    · intro hx; by_cases hxU : x ∈ U
      · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hxU, hx⟩)
      · have : x ∈ V \ U := Finset.mem_sdiff.mpr ⟨hx, hxU⟩
        rw [hb] at this; simp at this; simp [this]
    · intro hx; rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hbV
      · exact (Finset.mem_inter.mp hx).2
  -- the map on the common colours
  obtain ⟨g, hginj, hgim, hgl⟩ := exists_W_map hW (fun r => rowAt r s)
    (fun r => (labL (canon s) (kap j U V s)).getD r 7)
    (fun r hr h => (lab_common hW hs hr ((kap_zero_iff s r).mpr h)).2)
    (fun r hr i hi h h' => lab_iff hW hs hr hi ((kap_zero_iff s r).mpr h) ((kap_zero_iff s i).mpr h'))
  have hg5 : ∀ x ∈ U ∩ V, g x < 5 := fun x hx => by
    have : g x ∈ (U ∩ V).image g := Finset.mem_image_of_mem g hx
    rw [hgim] at this; simpa using this
  let σ : ℕ → ℕ := fun x => if x ∈ U ∩ V then g x else if x = a then 5 else if x = b then 6 else x + 7
  have σW : ∀ x ∈ U ∩ V, σ x = g x := fun x hx => if_pos hx
  have haW : a ∉ U ∩ V := fun h => haV (Finset.mem_inter.mp h).2
  have hbW : b ∉ U ∩ V := fun h => hbU (Finset.mem_inter.mp h).1
  have hab : b ≠ a := fun h => hbU (h ▸ haU)
  have σa : σ a = 5 := by simp only [σ, if_neg haW, if_true]
  have σb : σ b = 6 := by simp only [σ, if_neg hbW, if_neg hab, if_true]
  have σo : ∀ x, x ∉ U ∪ V → σ x = x + 7 := by
    intro x hx
    have h1 : x ∉ U ∩ V := fun h => hx (Finset.mem_union_left _ (Finset.mem_inter.mp h).1)
    have h2 : x ≠ a := fun h => hx (Finset.mem_union_left _ (h ▸ haU))
    have h3 : x ≠ b := fun h => hx (Finset.mem_union_right _ (h ▸ hbV))
    simp only [σ, if_neg h1, if_neg h2, if_neg h3]
  have hinj : Set.InjOn σ ↑(U ∪ V) := by
    intro x hx y hy hxy
    have hx' : x ∈ U ∪ V := hx
    have hy' : y ∈ U ∪ V := hy
    have cases : ∀ z ∈ U ∪ V, z ∈ U ∩ V ∨ z = a ∨ z = b := by
      intro z hz
      rcases Finset.mem_union.mp hz with h | h
      · rw [hUe] at h; rcases Finset.mem_insert.mp h with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
      · rw [hVe] at h; rcases Finset.mem_insert.mp h with h | h
        · exact Or.inr (Or.inr h)
        · exact Or.inl h
    rcases cases x hx' with hxW | rfl | rfl <;> rcases cases y hy' with hyW | rfl | rfl
    · rw [σW x hxW, σW y hyW] at hxy; exact hginj hxW hyW hxy
    · rw [σW x hxW, σa] at hxy; have := hg5 x hxW; omega
    · rw [σW x hxW, σb] at hxy; have := hg5 x hxW; omega
    · rw [σW y hyW, σa] at hxy; have := hg5 y hyW; omega
    · rfl
    · rw [σa, σb] at hxy; omega
    · rw [σW y hyW, σb] at hxy; have := hg5 y hyW; omega
    · rw [σa, σb] at hxy; omega
    · rfl
  have himW : (U ∩ V).image σ = range 5 := by
    rw [← hgim]; exact Finset.image_congr (fun x hx => σW x hx)
  have himU : U.image σ = setOf 63 := by
    rw [setOf_63, hUe, Finset.image_insert, himW, σa]; decide
  have himV : V.image σ = setOf 95 := by
    rw [setOf_95, hVe, Finset.image_insert, himW, σb]
  have himB : ∀ r < 6, (bj j U V r).image σ = setOf (bmJ j r) := by
    intro r _
    unfold bj bmJ
    rw [nblt]
    by_cases h : r < j
    · simp only [h, if_true, decide_true, Bool.cond_true]; exact himU
    · simp only [h, if_false, decide_false, Bool.cond_false]; exact himV
  refine ⟨σ, hinj, himB, fun r hr => ?_⟩
  have hBsub : (bj j U V r) ⊆ U ∪ V := by
    unfold bj; split_ifs
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  by_cases hin : rowAt r s ∈ bj j U V r
  · rw [Lookback.image_erase_of_injOn (hinj.mono (by exact_mod_cast hBsub)) hin, himB r hr]
    -- the image of the colour is its label
    have hlab : σ (rowAt r s) = (labL (canon s) (kap j U V s)).getD r 7 := by
      by_cases h0 : rowAt r s ∈ U ∩ V
      · rw [σW _ h0]; exact hgl r hr h0
      · rw [lab_other hr (fun h => h0 ((kap_zero_iff s r).mp h))]
        unfold bj at hin
        unfold kap kapC
        rw [if_neg h0]
        split_ifs at hin with hrj
        · have hx : rowAt r s = a := by
            have : rowAt r s ∈ U \ V := Finset.mem_sdiff.mpr ⟨hin, fun hV' => h0
              (Finset.mem_inter.mpr ⟨hin, hV'⟩)⟩
            rw [ha] at this; simpa using this
          rw [if_pos ⟨hrj, hin⟩, hx, σa]
        · have hx : rowAt r s = b := by
            have : rowAt r s ∈ V \ U := Finset.mem_sdiff.mpr ⟨hin, fun hU' => h0
              (Finset.mem_inter.mpr ⟨hU', hin⟩)⟩
            rw [hb] at this; simpa using this
          rw [if_neg (fun h => hrj h.1), if_pos ⟨by omega, hin⟩, hx, σb]
    rw [hlab, setOf_em _ _ (lab_lt8 hW hs hr)]
  · rw [Finset.erase_eq_of_notMem hin, himB r hr]
    have h7 : (labL (canon s) (kap j U V s)).getD r 7 = 7 := by
      have h0 : kap j U V s r ≠ 0 := fun h => hin (by
        have := (kap_zero_iff s r).mp h
        unfold bj; split_ifs
        · exact (Finset.mem_inter.mp this).1
        · exact (Finset.mem_inter.mp this).2)
      rw [lab_other hr h0]
      unfold kap kapC
      unfold bj at hin
      rw [if_neg (fun h => h0 ((kap_zero_iff s r).mpr h))]
      split_ifs at hin with hrj
      · rw [if_neg (fun h => hin h.2), if_neg (fun h => by omega)]
      · rw [if_neg (fun h => hrj h.1), if_neg (fun h => hin h.2)]
    rw [h7, setOf_em _ _ (by norm_num), Finset.erase_eq_of_notMem
      (not_mem_setOf_bmJ j r 7 le_rfl)]

end shape

end GridGen.Six
