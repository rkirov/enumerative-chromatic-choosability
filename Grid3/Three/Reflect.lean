/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.Three.Seam
import Grid3.Three.Cert.Mirror
import Grid3.Three.Entropy

/-!
# Reflecting a seam in the middle row

`mirror Lc` swaps rows `0` and `2` of a column; `rs` does the same to a state. The column
invariants transform by the packed reflections of `Cert/Mirror.lean`: `packType (mirror Lc) =
rtype (packType Lc)`, `Mact (mirror Lc) (mirror Lc') = rM (Mact Lc Lc')`, and the concrete law is
invariant, `lawC (mirror Lc) (rs c) = lawC Lc c`, because the law table is reflection-equivariant
(`lawSig_rsig`). `seam_transport` then carries a seam kernel between the reflected columns back to
the original ones: the certificate only stores one record per reflection orbit of keys, and
`SeamData.lean` reaches the other orbit member through here.
-/

open Finset

namespace Grid3.Three.Reflect

open Cert Col Seam

/-- the row reflection `0 ↔ 2` -/
def rrow (r : Fin 3) : Fin 3 := ⟨2 - r.val, by omega⟩

theorem rrow_rrow (r : Fin 3) : rrow (rrow r) = r := by
  ext; simp only [rrow]; omega

theorem rrow_0 : rrow 0 = 2 := rfl
theorem rrow_1 : rrow 1 = 1 := rfl
theorem rrow_2 : rrow 2 = 0 := rfl

/-- the reflected column -/
def mirror (Lc : Fin 3 → Finset ℕ) : Fin 3 → Finset ℕ := fun r => Lc (rrow r)

/-- the reflected state -/
def rs {C : ℕ} (c : Fin 3 → Fin C) : Fin 3 → Fin C := fun r => c (rrow r)

theorem rs_rs {C : ℕ} (c : Fin 3 → Fin C) : rs (rs c) = c := by
  funext r; simp only [rs, rrow_rrow]

/-- reflection as a bijection of states -/
def rsEquiv (C : ℕ) : (Fin 3 → Fin C) ≃ (Fin 3 → Fin C) := ⟨rs, rs, rs_rs, rs_rs⟩

theorem sum_rs {C : ℕ} (f : (Fin 3 → Fin C) → ℝ) : ∑ c, f (rs c) = ∑ c, f c :=
  (rsEquiv C).sum_comp f

theorem rowH_rs {C : ℕ} (K' : (Fin 3 → Fin C) → (Fin 3 → Fin C) → ℝ) (c : Fin 3 → Fin C) :
    rowH (fun a b => K' (rs a) (rs b)) c = rowH K' (rs c) :=
  sum_rs (fun s => K' (rs c) s * (- Real.log (K' (rs c) s)))

variable (Lc Lc' : Fin 3 → Finset ℕ)

theorem mirror_0 : mirror Lc 0 = Lc 2 := rfl
theorem mirror_1 : mirror Lc 1 = Lc 1 := rfl
theorem mirror_2 : mirror Lc 2 = Lc 0 := rfl

theorem card_mirror (h3 : ∀ r, (Lc r).card = 3) : ∀ r, (mirror Lc r).card = 3 := fun _ => h3 _

theorem colours_mirror : Col.colours (mirror Lc) = Col.colours Lc := by
  ext c
  simp only [Col.colours, Finset.mem_union, mirror_0, mirror_1, mirror_2]
  tauto

theorem uniform_mirror : (∀ r, mirror Lc r = mirror Lc 0) ↔ (∀ r, Lc r = Lc 0) := by
  constructor
  · intro h r
    have h1 : Lc 1 = Lc 2 := h 1
    have h2 : Lc 0 = Lc 2 := h 2
    fin_cases r
    · rfl
    · exact h1.trans h2.symm
    · exact h2.symm
  · intro h r
    have h1 : Lc 1 = Lc 0 := h 1
    have h2 : Lc 2 = Lc 0 := h 2
    fin_cases r
    · rfl
    · show Lc 1 = Lc 2
      exact h1.trans h2.symm
    · show Lc 0 = Lc 2
      exact h2.symm

/-! ### Patterns, types, keys -/

theorem patOf_mirror (c : ℕ) : patOf (mirror Lc) c = revPat (patOf Lc c) := by
  unfold patOf
  rw [mirror_0, mirror_1, mirror_2]
  by_cases h0 : c ∈ Lc 0 <;> by_cases h1 : c ∈ Lc 1 <;> by_cases h2 : c ∈ Lc 2 <;>
    simp only [h0, h1, h2, if_true, if_false] <;> decide

theorem cnt_mirror (p : ℕ) (hp : p < 7) : cnt (mirror Lc) p = cnt Lc (rp p) := by
  unfold cnt
  rw [colours_mirror]
  congr 1
  apply Finset.filter_congr
  intro c _
  rw [patOf_mirror]
  exact revPat_eq_iff _ (by have := patOf_le Lc c; omega) p hp

theorem packType_mirror (h3 : ∀ r, (Lc r).card = 3) :
    packType (mirror Lc) = rtype (packType Lc) := by
  rw [packType_eq (mirror Lc), rtype_eq, mult_packType Lc h3 3 (by decide),
    mult_packType Lc h3 1 (by decide), mult_packType Lc h3 5 (by decide),
    mult_packType Lc h3 0 (by decide), mult_packType Lc h3 4 (by decide),
    mult_packType Lc h3 2 (by decide), mult_packType Lc h3 6 (by decide),
    cnt_mirror Lc 0 (by decide), cnt_mirror Lc 1 (by decide), cnt_mirror Lc 2 (by decide),
    cnt_mirror Lc 3 (by decide), cnt_mirror Lc 4 (by decide), cnt_mirror Lc 5 (by decide),
    cnt_mirror Lc 6 (by decide), rp_0, rp_1, rp_2, rp_3, rp_4, rp_5, rp_6]

theorem commonI_mirror : commonI (mirror Lc) (mirror Lc') = commonI Lc Lc' := by
  ext c
  simp only [mem_commonI, colours_mirror, patOf_mirror]
  have hl := patOf_le Lc c
  have hr := patOf_le Lc' c
  rw [land_revPat _ (by omega) _ (by omega)]

theorem mact_mirror (p q : ℕ) (hp : p < 7) (hq : q < 7) :
    mact (mirror Lc) (mirror Lc') p q = mact Lc Lc' (rp p) (rp q) := by
  unfold mact
  rw [commonI_mirror]
  congr 1
  apply Finset.filter_congr
  intro c _
  rw [patOf_mirror, patOf_mirror, revPat_eq_iff _ (by have := patOf_le Lc c; omega) p hp,
    revPat_eq_iff _ (by have := patOf_le Lc' c; omega) q hq]

theorem packL_eq_pack4 : ∀ L : List ℕ, packL L = pack4 L
  | [] => rfl
  | d :: L => by simp only [packL, pack4, packL_eq_pack4 L]

theorem Mact_mirror (h3 : ∀ r, (Lc r).card = 3) :
    Mact (mirror Lc) (mirror Lc') = rM (Mact Lc Lc') := by
  conv_lhs => rw [Mact, packL_eq_pack4]
  unfold rM
  refine congrArg pack4 (congrArg List.ofFn (funext fun i => ?_))
  have hi := i.isLt
  rw [mcount_Mact Lc Lc' h3 _ _ (rp_lt _ (by omega)) (rp_lt _ (by omega)),
    mact_mirror Lc Lc' _ _ (by omega) (by omega)]

/-! ### States and laws -/

theorem isCol_mirror {C : ℕ} (c : Fin 3 → Fin C) : IsCol (mirror Lc) (rs c) ↔ IsCol Lc c := by
  unfold IsCol
  simp only [rs, mirror]
  rw [rrow_0, rrow_1, rrow_2]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun r => ?_, h3.symm, h2.symm⟩
    have := h1 (rrow r)
    rwa [rrow_rrow] at this
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun r => h1 (rrow r), h3.symm, h2.symm⟩

theorem patOf_bounds {C : ℕ} (c : Fin 3 → Fin C) (h : IsCol Lc c) (r : Fin 3) :
    1 ≤ patOf Lc (c r).val ∧ patOf Lc (c r).val ≤ 7 :=
  ⟨patOf_pos Lc _ ((mem_colours Lc _).2 ⟨r, h.1 r⟩), patOf_le Lc _⟩

theorem rsig_sig (p0 p1 p2 e : ℕ) (h0 : 1 ≤ p0 ∧ p0 ≤ 7) (h1 : 1 ≤ p1 ∧ p1 ≤ 7)
    (h2 : 1 ≤ p2 ∧ p2 ≤ 7) (he : e < 2) :
    rsig ((((p0 - 1) * 7 + (p1 - 1)) * 7 + (p2 - 1)) * 2 + e)
      = (((revPat p2 - 1) * 7 + (revPat p1 - 1)) * 7 + (revPat p0 - 1)) * 2 + e := by
  rw [rsig_formula (p0 - 1) (by omega) (p1 - 1) (by omega) (p2 - 1) (by omega) e he]
  simp only [rp, Nat.sub_add_cancel h0.1, Nat.sub_add_cancel h1.1, Nat.sub_add_cancel h2.1]

theorem sigC_mirror {C : ℕ} (c : Fin 3 → Fin C) (h : IsCol Lc c) :
    sigC (mirror Lc) (rs c) = rsig (sigC Lc c) := by
  have b0 := patOf_bounds Lc c h 0
  have b1 := patOf_bounds Lc c h 1
  have b2 := patOf_bounds Lc c h 2
  unfold sigC
  have e0 : rs c 0 = c 2 := rfl
  have e1 : rs c 1 = c 1 := rfl
  have e2 : rs c 2 = c 0 := rfl
  rw [e0, e1, e2, patOf_mirror, patOf_mirror, patOf_mirror]
  have he : (if c 2 = c 0 then 1 else 0 : ℕ) = if c 0 = c 2 then 1 else 0 := by
    by_cases hc : c 0 = c 2
    · rw [if_pos hc, if_pos hc.symm]
    · rw [if_neg hc, if_neg (Ne.symm hc)]
  rw [he, rsig_sig _ _ _ _ b0 b1 b2 (by split_ifs <;> decide)]

theorem sigC_lt {C : ℕ} (c : Fin 3 → Fin C) (h : IsCol Lc c) : sigC Lc c < 686 := by
  have b0 := patOf_bounds Lc c h 0
  have b1 := patOf_bounds Lc c h 1
  have b2 := patOf_bounds Lc c h 2
  unfold sigC
  split_ifs <;> omega

theorem lawSig_rsig (m : ℕ) (hm : m ∈ validTypes) (s : ℕ) (hs : s < 686) :
    lawSig (rtype m) (rsig s) = lawSig m s := by
  unfold lawSig
  by_cases hU : m = UTYPE
  · subst hU
    rw [rtype_UTYPE, rsig_mod_two]
    simp only [beq_self_eq_true, if_true]
  · have hU' : rtype m ≠ UTYPE := fun h => hU ((rtype_eq_UTYPE_iff m hm).1 h)
    rw [if_neg (by simpa using hU'), if_neg (by simpa using hU), subTable_rsig m hm s hs]

/-- **The concrete law is reflection-invariant.** -/
theorem lawC_mirror {C : ℕ} (h3 : ∀ r, (Lc r).card = 3) (c : Fin 3 → Fin C) :
    lawC (mirror Lc) (rs c) = lawC Lc c := by
  unfold lawC
  by_cases h : IsCol Lc c
  · rw [if_pos ((isCol_mirror Lc c).2 h), if_pos h, sigC_mirror Lc c h, packType_mirror Lc h3]
    exact lawSig_rsig (packType Lc)
      (validType_mem_validTypes _ (packType_lt Lc h3) (validType_packType Lc h3)) _ (sigC_lt Lc c h)
  · rw [if_neg (fun h' => h ((isCol_mirror Lc c).1 h')), if_neg h]

/-! ### Transporting a seam -/

/-- **A seam between the reflected columns gives a seam between the columns.** -/
theorem seam_transport (h3 : ∀ r, (Lc r).card = 3) (h3' : ∀ r, (Lc' r).card = 3) (C : ℕ)
    (K' : (Fin 3 → Fin C) → (Fin 3 → Fin C) → ℝ)
    (hK0 : ∀ c s, 0 ≤ K' c s) (hK1 : ∀ c, ∑ s, K' c s = 1)
    (hstep : ∀ s, ∑ c, lawC (mirror Lc) c * K' c s = lawC (mirror Lc') s)
    (hsupp : ∀ c s, 0 < lawC (mirror Lc) c → 0 < K' c s → ∀ i, c i ≠ s i)
    (hent : Real.log rho ≤ ∑ c, lawC (mirror Lc) c * rowH K' c)
    (hbonus : (∀ r, mirror Lc r = mirror Lc 0) → ¬ (∀ r, mirror Lc' r = mirror Lc' 0) →
      Real.log rho + Real.log (18 / 17) ≤ ∑ c, lawC (mirror Lc) c * rowH K' c)
    (hroot : ¬ (∀ r, mirror Lc r = mirror Lc 0) →
      ∑ c : Fin 3 → Fin C, lawC (mirror Lc) c = 1
        ∧ ∑ c : Fin 3 → Fin C, lawC (mirror Lc) c ^ 2 ≤ 1 / 12) :
    ∃ K : (Fin 3 → Fin C) → (Fin 3 → Fin C) → ℝ,
      (∀ c s, 0 ≤ K c s) ∧ (∀ c, ∑ s, K c s = 1)
      ∧ (∀ s, ∑ c, lawC Lc c * K c s = lawC Lc' s)
      ∧ (∀ c s, 0 < lawC Lc c → 0 < K c s → ∀ i, c i ≠ s i)
      ∧ Real.log rho ≤ ∑ c, lawC Lc c * rowH K c
      ∧ ((∀ r, Lc r = Lc 0) → ¬ (∀ r, Lc' r = Lc' 0) →
          Real.log rho + Real.log (18 / 17) ≤ ∑ c, lawC Lc c * rowH K c)
      ∧ (¬ (∀ r, Lc r = Lc 0) → ∑ c : Fin 3 → Fin C, lawC Lc c = 1
          ∧ ∑ c : Fin 3 → Fin C, lawC Lc c ^ 2 ≤ 1 / 12) := by
  have hE : ∑ c, lawC Lc c * rowH (fun a b => K' (rs a) (rs b)) c
      = ∑ c, lawC (mirror Lc) c * rowH K' c := by
    calc ∑ c, lawC Lc c * rowH (fun a b => K' (rs a) (rs b)) c
        = ∑ c, lawC (mirror Lc) (rs c) * rowH K' (rs c) := by
          simp only [lawC_mirror Lc h3, rowH_rs]
      _ = ∑ c, lawC (mirror Lc) c * rowH K' c := sum_rs (fun c => lawC (mirror Lc) c * rowH K' c)
  refine ⟨fun a b => K' (rs a) (rs b), fun c s => hK0 _ _, fun c => ?_, fun s => ?_, ?_, ?_, ?_, ?_⟩
  · exact (sum_rs (fun s => K' (rs c) s)).trans (hK1 _)
  · calc ∑ c, lawC Lc c * K' (rs c) (rs s)
        = ∑ c, lawC (mirror Lc) (rs c) * K' (rs c) (rs s) := by simp only [lawC_mirror Lc h3]
      _ = ∑ c, lawC (mirror Lc) c * K' c (rs s) := sum_rs (fun c => lawC (mirror Lc) c * K' c (rs s))
      _ = lawC (mirror Lc') (rs s) := hstep _
      _ = lawC Lc' s := lawC_mirror Lc' h3' s
  · intro c s hc hK i
    have := hsupp (rs c) (rs s) (by rw [lawC_mirror Lc h3]; exact hc) hK (rrow i)
    simpa only [rs, rrow_rrow] using this
  · rw [hE]; exact hent
  · intro hU hU'
    rw [hE]
    exact hbonus ((uniform_mirror Lc).2 hU) (fun h => hU' ((uniform_mirror Lc').1 h))
  · intro hU
    have h := hroot (fun h => hU ((uniform_mirror Lc).1 h))
    refine ⟨?_, ?_⟩
    · calc ∑ c, lawC Lc c = ∑ c, lawC (mirror Lc) (rs c) := by simp only [lawC_mirror Lc h3]
        _ = ∑ c, lawC (mirror Lc) c := sum_rs _
        _ = 1 := h.1
    · calc ∑ c, lawC Lc c ^ 2 = ∑ c, lawC (mirror Lc) (rs c) ^ 2 := by simp only [lawC_mirror Lc h3]
        _ = ∑ c, lawC (mirror Lc) c ^ 2 := sum_rs (fun c => lawC (mirror Lc) c ^ 2)
        _ ≤ 1 / 12 := h.2

end Grid3.Three.Reflect
