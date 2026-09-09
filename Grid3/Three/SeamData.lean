import Grid3.Three.UCol
import Grid3.Three.Package
import Grid3.Three.CertifiedEntropy
import Grid3.Three.Reflect

/-!
# One seam of the Markov chain

`seam_exists`: for two adjacent concrete columns there is a stochastic kernel on the actual
states `Fin 3 → Fin C` which carries the concrete law of the left column to that of the right
column, is supported on horizontally compatible pairs of proper states, and has conditional
entropy at least `log ρ` — with the `(18/17)` bonus when the left column is uniform and the right
one is not, and with the root facts (total mass one, collision mass at most `1/12`) for a
nonuniform left column.

Numerical seams come from the certificate (`Cert.seam_package`) transported along the colour
maps (`Transport.lean`, in `seam_of_package`); the uniform-to-uniform seam is the Parry kernel
(`Cert.parry_seam`). The certificate stores one record per row-reflection orbit of keys: when only
the reflected key has a record, the seam is built between the reflected columns and carried back
by `Reflect.seam_transport`.
-/

open Finset

namespace Grid3.Three.Seam

open Cert Col Transport

/-- a column of type `UTYPE` is uniform -/
theorem uniform_of_packType (Lc : Fin 3 → Finset ℕ) (h3 : ∀ r, (Lc r).card = 3)
    (h : packType Lc = UTYPE) : ∀ r, Lc r = Lc 0 := by
  have hcnt : cnt Lc 6 = 3 := by
    rw [← mult_packType Lc h3 6 (by decide), h]; decide
  have hsub : ∀ r, ((Col.colours Lc).filter fun c => patOf Lc c = 7) ⊆ Lc r := by
    intro r c hc
    rw [Finset.mem_filter] at hc
    rw [← patOf_testBit Lc c r, hc.2]
    fin_cases r <;> decide
  have heq : ∀ r, ((Col.colours Lc).filter fun c => patOf Lc c = 7) = Lc r := fun r =>
    Finset.eq_of_subset_of_card_le (hsub r) (by rw [h3 r]; exact le_of_eq hcnt.symm)
  intro r
  rw [← heq r, heq 0]

/-- for two uniform columns the actual key lies below `MUU` -/
theorem keyLE_MUU' (Lc Lc' : Fin 3 → Finset ℕ) (hU : ∀ r, Lc r = Lc 0) (hU' : ∀ r, Lc' r = Lc' 0)
    (h3 : ∀ r, (Lc r).card = 3) (h3' : ∀ r, (Lc' r).card = 3) : keyLE (Mact Lc Lc') MUU := by
  intro p hp q hq
  rw [mcount_Mact Lc Lc' h3 p q hp hq, mcount_MUU p hp q hq]
  by_cases hpq : p = 6 ∧ q = 6
  · obtain ⟨rfl, rfl⟩ := hpq
    rw [if_pos ⟨rfl, rfl⟩]
    exact (mact_le_cnt Lc Lc' 6 6).trans (cnt_le Lc h3 6 (by decide))
  · rw [if_neg hpq]
    apply Nat.le_of_eq
    unfold mact
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c hc ⟨h1, h2⟩
    rw [patOf_U Lc hU c (commonI_subset_left _ _ hc)] at h1
    rw [patOf_U Lc' hU' c (commonI_subset_right _ _ hc)] at h2
    exact hpq ⟨by omega, by omega⟩

/-- the seam statement -/
def SeamStmt (Lc Lc' : Fin 3 → Finset ℕ) (C : ℕ) : Prop :=
  ∃ K : (Fin 3 → Fin C) → (Fin 3 → Fin C) → ℝ,
    (∀ c s, 0 ≤ K c s) ∧ (∀ c, ∑ s, K c s = 1)
    ∧ (∀ s, ∑ c, lawC Lc c * K c s = lawC Lc' s)
    ∧ (∀ c s, 0 < lawC Lc c → 0 < K c s → ∀ i, c i ≠ s i)
    ∧ Real.log rho ≤ ∑ c, lawC Lc c * rowH K c
    ∧ ((∀ r, Lc r = Lc 0) → ¬ (∀ r, Lc' r = Lc' 0) →
        Real.log rho + Real.log (18 / 17) ≤ ∑ c, lawC Lc c * rowH K c)
    ∧ (¬ (∀ r, Lc r = Lc 0) → ∑ c : Fin 3 → Fin C, lawC Lc c = 1
        ∧ ∑ c : Fin 3 → Fin C, lawC Lc c ^ 2 ≤ 1 / 12)

/-- **A numerical seam** from a seam package for a valid key `M` above the actual key. -/
theorem seam_of_package (Lc Lc' : Fin 3 → Finset ℕ) (h3 : ∀ r, (Lc r).card = 3)
    (h3' : ∀ r, (Lc' r).card = 3) (B C : ℕ) (hB : ∀ c ∈ Col.colours Lc, c < B)
    (hB' : ∀ c ∈ Col.colours Lc', c < B) (hBC : B + 32 ≤ C) (M : ℕ)
    (hv : validKey (packType Lc) (packType Lc') M = true) (hle : keyLE (Mact Lc Lc') M)
    (pkg : Cert.SeamPkg (packType Lc) (packType Lc') M) : SeamStmt Lc Lc' C := by
  classical
  let fallback : (Fin 3 → Fin C) → ℝ := fun _ => 1 / (Fintype.card (Fin 3 → Fin C) : ℝ)
  have hfall0 : ∀ t, 0 ≤ fallback t := fun _ => by positivity
  have hfall1 : ∑ t, fallback t = 1 := by
    simp only [fallback, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (Fintype.card (Fin 3 → Fin C) : ℝ) ≠ 0 := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      have : 0 < C := by omega
      positivity
    field_simp
  obtain ⟨cm⟩ := exists_colourMaps Lc Lc' M h3 h3' hv hle
  obtain ⟨Kc, hSO, hbonus, h32, hroot⟩ := pkg
  have hlawL := liftLaw_fL Lc Lc' M cm B C hB hBC h32
  have hlawR := liftLaw_fR Lc Lc' M cm B C hB' hBC h32
  have hf := fL_injective Lc Lc' M cm B C hB hBC
  have hg := fR_injective Lc Lc' M cm B C hB' hBC
  -- total mass one on the left, in both cases
  have hsumL : ∑ c, lawR (packType Lc) (pL Lc Lc' M) c = 1 := by
    by_cases hU : ∀ r, Lc r = Lc 0
    · rw [← sum_liftLaw _ hf, hlawL]
      exact (lawC_U_facts Lc hU h3 B C hB hBC).1
    · have hnU : (packType Lc == UTYPE) = false := by
        rw [beq_eq_false_iff_ne]; intro h; exact hU (uniform_of_packType Lc h3 h)
      exact (hroot hnU).1
  have hent := SeamOK.row_entropy hSO hsumL
  refine ⟨liftKernel (fL Lc Lc' M cm B C hB hBC) (fR Lc Lc' M cm B C hB' hBC) Kc fallback,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun c s => liftKernel_nonneg _ hf _ hg Kc fallback hSO.nonneg hfall0 c s
  · exact fun c => liftKernel_rowsum _ hf _ hg Kc fallback hSO.rowsum hfall1 c
  · intro s
    rw [← hlawL, ← hlawR]
    exact liftKernel_step _ hf _ hg _ _ Kc fallback hSO.step s
  · intro c s hc hK
    rw [← hlawL] at hc
    refine liftKernel_support _ hf _ hg _ Kc fallback (fun s t => ∀ i, s i ≠ t i) ?_ c s hc hK
    intro a b ha hb
    obtain ⟨hcomp, ha', hb'⟩ := hSO.support a b ha hb
    exact compat_fL_fR Lc Lc' M cm B C hB hB' hBC h32 a b ha' hb' hcomp
  · rw [← hlawL]
    unfold rowH
    rw [liftKernel_entropy _ hf _ hg _ Kc fallback]
    exact hent
  · intro hU _
    have hUeq : (packType Lc == UTYPE) = true := by
      rw [beq_iff_eq]; exact packType_U Lc hU h3
    have := SeamOK.row_entropy_bonus hSO hsumL (hbonus hUeq)
    rw [← hlawL]
    unfold rowH
    rw [liftKernel_entropy _ hf _ hg _ Kc fallback]
    exact this
  · intro hU
    have hnU : (packType Lc == UTYPE) = false := by
      rw [beq_eq_false_iff_ne]; intro h; exact hU (uniform_of_packType Lc h3 h)
    obtain ⟨h1, h2⟩ := hroot hnU
    rw [← hlawL, sum_liftLaw _ hf, sum_liftLaw_map _ hf _ (fun x => x ^ 2) (by simp)]
    exact ⟨h1, h2⟩

/-- **One seam.** -/
theorem seam_exists (Lc Lc' : Fin 3 → Finset ℕ) (h3 : ∀ r, (Lc r).card = 3)
    (h3' : ∀ r, (Lc' r).card = 3) (B C : ℕ) (hB : ∀ c ∈ Col.colours Lc, c < B)
    (hB' : ∀ c ∈ Col.colours Lc', c < B) (hBC : B + 32 ≤ C) :
    ∃ K : (Fin 3 → Fin C) → (Fin 3 → Fin C) → ℝ,
      (∀ c s, 0 ≤ K c s) ∧ (∀ c, ∑ s, K c s = 1)
      ∧ (∀ s, ∑ c, lawC Lc c * K c s = lawC Lc' s)
      ∧ (∀ c s, 0 < lawC Lc c → 0 < K c s → ∀ i, c i ≠ s i)
      ∧ Real.log rho ≤ ∑ c, lawC Lc c * rowH K c
      ∧ ((∀ r, Lc r = Lc 0) → ¬ (∀ r, Lc' r = Lc' 0) →
          Real.log rho + Real.log (18 / 17) ≤ ∑ c, lawC Lc c * rowH K c)
      ∧ (¬ (∀ r, Lc r = Lc 0) → ∑ c : Fin 3 → Fin C, lawC Lc c = 1
          ∧ ∑ c : Fin 3 → Fin C, lawC Lc c ^ 2 ≤ 1 / 12) := by
  classical
  let fallback : (Fin 3 → Fin C) → ℝ := fun _ => 1 / (Fintype.card (Fin 3 → Fin C) : ℝ)
  have hfall0 : ∀ t, 0 ≤ fallback t := fun _ => by positivity
  have hfall1 : ∑ t, fallback t = 1 := by
    simp only [fallback, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (Fintype.card (Fin 3 → Fin C) : ℝ) ≠ 0 := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      have : 0 < C := by omega
      positivity
    field_simp
  by_cases hUU : (∀ r, Lc r = Lc 0) ∧ (∀ r, Lc' r = Lc' 0)
  · -- the symbolic seam
    obtain ⟨hU, hU'⟩ := hUU
    have hv : validKey (packType Lc) (packType Lc') MUU = true := by
      rw [packType_U Lc hU h3, packType_U Lc' hU' h3']; exact validKey_MUU
    obtain ⟨cm⟩ := exists_colourMaps Lc Lc' MUU h3 h3' hv (keyLE_MUU' Lc Lc' hU hU' h3 h3')
    have hcols : cols Lc Lc' MUU = [(7, 7), (7, 7), (7, 7)] := by
      unfold cols; rw [packType_U Lc hU h3, packType_U Lc' hU' h3']; exact colours_MUU
    have h32 : (cols Lc Lc' MUU).length ≤ 32 := by rw [hcols]; decide
    have hpL : pL Lc Lc' MUU = uPats := by
      show (cols Lc Lc' MUU).map Prod.fst = uPats
      rw [hcols]; rfl
    have hpR : pR Lc Lc' MUU = uPats := by
      show (cols Lc Lc' MUU).map Prod.snd = uPats
      rw [hcols]; rfl
    have hlawL := liftLaw_fL Lc Lc' MUU cm B C hB hBC h32
    rw [hpL, packType_U Lc hU h3] at hlawL
    change liftLaw (fL Lc Lc' MUU cm B C hB hBC) uLaw = lawC Lc at hlawL
    have hlawR := liftLaw_fR Lc Lc' MUU cm B C hB' hBC h32
    rw [hpR, packType_U Lc' hU' h3'] at hlawR
    change liftLaw (fR Lc Lc' MUU cm B C hB' hBC) uLaw = lawC Lc' at hlawR
    have hf := fL_injective Lc Lc' MUU cm B C hB hBC
    have hg := fR_injective Lc Lc' MUU cm B C hB' hBC
    obtain ⟨hK0, hK1, hstep, hsupp, -, hent⟩ := parry_seam
    refine ⟨liftKernel (fL Lc Lc' MUU cm B C hB hBC) (fR Lc Lc' MUU cm B C hB' hBC) KU fallback,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun c s => liftKernel_nonneg _ hf _ hg KU fallback hK0 hfall0 c s
    · exact fun c => liftKernel_rowsum _ hf _ hg KU fallback hK1 hfall1 c
    · intro s
      rw [← hlawL, ← hlawR]
      exact liftKernel_step _ hf _ hg uLaw uLaw KU fallback hstep s
    · intro c s hc hK
      rw [← hlawL] at hc
      refine liftKernel_support _ hf _ hg uLaw KU fallback (fun s t => ∀ i, s i ≠ t i) ?_ c s hc hK
      intro a b ha hb
      obtain ⟨hcomp, ha', hb'⟩ := hsupp a b ha hb
      exact compat_fL_fR Lc Lc' MUU cm B C hB hB' hBC h32 a b (by rw [hpL]; exact ha')
        (by rw [hpR]; exact hb') hcomp
    · rw [← hlawL]
      unfold rowH
      rw [liftKernel_entropy _ hf _ hg uLaw KU fallback]
      exact hent
    · intro _ hnU'; exact absurd hU' hnU'
    · intro hnU; exact absurd hU hnU
  · -- a numerical seam, for the key or for its reflection
    obtain ⟨M, hM, hv, hmax, hle⟩ := exists_Mmax Lc Lc' h3 h3'
    rcases seam_package (packType Lc) (packType Lc') M (packType_lt Lc h3) (packType_lt Lc' h3')
      (validType_packType Lc h3) (validType_packType Lc' h3') hM hv hmax with
      ⟨hUL, hUR⟩ | pkg | pkg
    · exact absurd ⟨uniform_of_packType Lc h3 hUL, uniform_of_packType Lc' h3' hUR⟩ hUU
    · exact seam_of_package Lc Lc' h3 h3' B C hB hB' hBC M hv hle pkg
    · rw [← Reflect.packType_mirror Lc h3, ← Reflect.packType_mirror Lc' h3'] at pkg
      have hv' : validKey (packType (Reflect.mirror Lc)) (packType (Reflect.mirror Lc')) (rM M)
          = true := by
        rw [Reflect.packType_mirror Lc h3, Reflect.packType_mirror Lc' h3']
        exact validKey_rM hv
      have hle' : keyLE (Mact (Reflect.mirror Lc) (Reflect.mirror Lc')) (rM M) := by
        rw [Reflect.Mact_mirror Lc Lc' h3]
        exact keyLE_rM hle
      obtain ⟨K', hK0, hK1, hstep, hsupp, hent, hbonus, hroot⟩ :=
        seam_of_package (Reflect.mirror Lc) (Reflect.mirror Lc') (Reflect.card_mirror Lc h3)
          (Reflect.card_mirror Lc' h3') B C (by rw [Reflect.colours_mirror]; exact hB)
          (by rw [Reflect.colours_mirror]; exact hB') hBC (rM M) hv' hle' pkg
      exact Reflect.seam_transport Lc Lc' h3 h3' C K' hK0 hK1 hstep hsupp hent hbonus hroot

end Grid3.Three.Seam
