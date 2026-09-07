import Grid3.Three.Transport
import Grid3.Three.Cert.Parry

/-!
# Uniform columns

A column whose three lists agree (`Lc r = Lc 0`) has type `UTYPE`, and its seam with itself has
the symbolic key `MUU`, whose canonical patterns are `uPats = [7, 7, 7]`. Transporting the
uniform law `uLaw` along the colour maps of that seam identifies the concrete law `lawC Lc` with
`uLaw`, so the concrete uniform law has total mass one and collision mass exactly `3/34`
(`lawC_U_sum`, `lawC_U_sq`). These are the root facts of the entropy argument when the first
column is uniform (case B of the split).
-/

open Finset

namespace Grid3.Three.Seam

open Cert Col

/-- the collision mass of the uniform law -/
theorem uLaw_sq : ∑ c, uLaw c ^ 2 = 3 / 34 := by
  rw [sum_uFin (fun c => uLaw c ^ 2) (fun c hc => by rw [uLaw_zero c hc]; ring)]
  simp only [uFin_eq, List.map, List.sum_cons, List.sum_nil, uLaw_val, hm32, hm34, hm64, hm65,
    hm1025, hm1026, hm1088, hm1089, hm2049, hm2050, hm2080, hm2082, isABA]
  norm_num
  have h17 := s17_sq
  nlinarith [h17]

/-- the packed `U → U` key is valid and maximal -/
theorem validKey_MUU : validKey UTYPE UTYPE MUU = true := by decide
theorem keyMax_MUU : keyMax UTYPE UTYPE MUU = true := by decide
theorem MUU_lt : MUU < 16384 ^ 7 := by decide
theorem colours_MUU : Cert.colours UTYPE UTYPE MUU = [(7, 7), (7, 7), (7, 7)] := by decide

variable (Lc : Fin 3 → Finset ℕ) (hU : ∀ r, Lc r = Lc 0) (h3 : ∀ r, (Lc r).card = 3)

include hU in
theorem patOf_U (c : ℕ) (hc : c ∈ Col.colours Lc) : patOf Lc c = 7 := by
  obtain ⟨r, hr⟩ := (mem_colours Lc c).1 hc
  rw [hU r] at hr
  unfold patOf
  rw [if_pos hr, if_pos (by rw [hU 1]; exact hr), if_pos (by rw [hU 2]; exact hr)]

include hU in
theorem colours_U : Col.colours Lc = Lc 0 := by
  unfold Col.colours; rw [hU 1, hU 2]; simp

include hU h3 in
theorem cnt_U (p : ℕ) : cnt Lc p = if p = 6 then 3 else 0 := by
  unfold cnt
  by_cases hp : p = 6
  · subst hp
    rw [if_pos rfl, Finset.filter_true_of_mem (fun c hc => patOf_U Lc hU c hc), colours_U Lc hU]
    exact h3 0
  · rw [if_neg hp, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c hc h
    rw [patOf_U Lc hU c hc] at h
    omega

include hU h3 in
theorem packType_U : packType Lc = UTYPE := by
  rw [packType_eq]
  simp only [cnt_U Lc hU h3]
  decide

include hU in
theorem commonI_U : commonI Lc Lc = Col.colours Lc := by
  ext c
  rw [mem_commonI]
  constructor
  · rintro ⟨h, -, -⟩; exact h
  · intro h
    refine ⟨h, h, ?_⟩
    rw [patOf_U Lc hU c h]; decide

include hU h3 in
theorem mact_U (p q : ℕ) : mact Lc Lc p q = if p = 6 ∧ q = 6 then 3 else 0 := by
  unfold mact
  rw [commonI_U Lc hU]
  by_cases hpq : p = 6 ∧ q = 6
  · obtain ⟨rfl, rfl⟩ := hpq
    rw [if_pos ⟨rfl, rfl⟩, Finset.filter_true_of_mem, colours_U Lc hU]
    · exact h3 0
    · intro c hc; rw [patOf_U Lc hU c hc]; exact ⟨rfl, rfl⟩
  · rw [if_neg hpq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c hc ⟨h1, h2⟩
    rw [patOf_U Lc hU c hc] at h1 h2
    exact hpq ⟨by omega, by omega⟩

theorem mcount_MUU : ∀ p < 7, ∀ q < 7, mcount MUU p q = if p = 6 ∧ q = 6 then 3 else 0 := by
  decide

include hU h3 in
theorem keyLE_MUU : keyLE (Mact Lc Lc) MUU := by
  intro p hp q hq
  rw [mcount_Mact Lc Lc h3 p q hp hq, mact_U Lc hU h3, mcount_MUU p hp q hq]

/-! ### The concrete uniform law -/

section

variable (B C : ℕ) (hB : ∀ c ∈ Col.colours Lc, c < B) (hBC : B + 32 ≤ C)

include hU h3 hB hBC in
/-- the concrete law of a uniform column is the transported uniform law -/
theorem lawC_U_facts :
    ∑ s : Fin 3 → Fin C, lawC Lc s = 1 ∧ ∑ s : Fin 3 → Fin C, lawC Lc s ^ 2 = 3 / 34 := by
  have hv : validKey (packType Lc) (packType Lc) MUU = true := by
    rw [packType_U Lc hU h3]; exact validKey_MUU
  obtain ⟨cm⟩ := exists_colourMaps Lc Lc MUU h3 h3 hv (keyLE_MUU Lc hU h3)
  have hcols : cols Lc Lc MUU = [(7, 7), (7, 7), (7, 7)] := by
    unfold cols; rw [packType_U Lc hU h3]; exact colours_MUU
  have h32 : (cols Lc Lc MUU).length ≤ 32 := by rw [hcols]; decide
  have hpL : pL Lc Lc MUU = uPats := by
    show (cols Lc Lc MUU).map Prod.fst = uPats
    rw [hcols]; rfl
  have hlaw := liftLaw_fL Lc Lc MUU cm B C hB hBC h32
  rw [hpL, packType_U Lc hU h3] at hlaw
  have hinj := fL_injective Lc Lc MUU cm B C hB hBC
  constructor
  · rw [← hlaw, Transport.sum_liftLaw _ hinj]
    exact uLaw_sum
  · rw [← hlaw, Transport.sum_liftLaw_map _ hinj _ (fun x => x ^ 2) (by simp)]
    exact uLaw_sq

end

end Grid3.Three.Seam
