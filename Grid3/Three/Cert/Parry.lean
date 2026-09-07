import Grid3.Three.Cert.Bridge

/-!
# The symbolic `U → U` seam: the Parry kernel

The one seam key without a record is the uniform-to-uniform seam (`cert_complete`'s first
alternative). Its twelve states split into the six `ABA` states (top and bottom rows equal) and
the six `ABC` states; the class-level transfer matrix is `[[3, 2], [2, 2]]`, with Perron root
`rhoR = (5 + √17)/2` and right Perron vector `(1, (√17 - 1)/4)`. The bridge's uniform law
`lawR UTYPE [7,7,7]` is the Parry measure `π ∝ v²`, i.e. `(17 ± √17)/204`.

The Parry kernel `KU c s = v(s) / (rhoR · v(c))` on compatible pairs is stochastic, stationary
for the uniform law, supported in the compatibility relation, and its conditional entropy is
*exactly* `log rhoR` (`parry_entropy`): the collision and fourth-root certificates of
`EntropyCert` are strict and cannot hold here, so the seam contributes to the entropy capstone
through the bound `log rhoR ≤ ∑ c, law c · rowH (K c)` directly (`parry_seam`), which is the
form `seamterm_marginal` consumes.
-/

open Finset

namespace Grid3.Three.Cert

/-- the patterns of the canonical uniform column -/
def uPats : List Nat := [7, 7, 7]

/-- the packed `U → U` key: three matches at cell `(6, 6)` -/
def MUU : Nat := 237684487542793012780631851008

theorem colours_UU : (colours UTYPE UTYPE MUU).map Prod.fst = uPats
    ∧ (colours UTYPE UTYPE MUU).map Prod.snd = uPats := by decide

/-- the twelve uniform states -/
theorem uSts_eq : stsOf uPats = [32, 34, 64, 65, 1025, 1026, 1088, 1089, 2049, 2050, 2080, 2082] := by
  decide

theorem uSts_lt : ∀ st ∈ stsOf uPats, st < SB := by rw [uSts_eq]; decide

theorem hm32 : 32 ∈ stsOf uPats := by rw [uSts_eq]; decide
theorem hm34 : 34 ∈ stsOf uPats := by rw [uSts_eq]; decide
theorem hm64 : 64 ∈ stsOf uPats := by rw [uSts_eq]; decide
theorem hm65 : 65 ∈ stsOf uPats := by rw [uSts_eq]; decide
theorem hm1025 : 1025 ∈ stsOf uPats := by rw [uSts_eq]; decide
theorem hm1026 : 1026 ∈ stsOf uPats := by rw [uSts_eq]; decide
theorem hm1088 : 1088 ∈ stsOf uPats := by rw [uSts_eq]; decide
theorem hm1089 : 1089 ∈ stsOf uPats := by rw [uSts_eq]; decide
theorem hm2049 : 2049 ∈ stsOf uPats := by rw [uSts_eq]; decide
theorem hm2050 : 2050 ∈ stsOf uPats := by rw [uSts_eq]; decide
theorem hm2080 : 2080 ∈ stsOf uPats := by rw [uSts_eq]; decide
theorem hm2082 : 2082 ∈ stsOf uPats := by rw [uSts_eq]; decide
theorem hl32 : 32 < SB := by decide
theorem hl34 : 34 < SB := by decide
theorem hl64 : 64 < SB := by decide
theorem hl65 : 65 < SB := by decide
theorem hl1025 : 1025 < SB := by decide
theorem hl1026 : 1026 < SB := by decide
theorem hl1088 : 1088 < SB := by decide
theorem hl1089 : 1089 < SB := by decide
theorem hl2049 : 2049 < SB := by decide
theorem hl2050 : 2050 < SB := by decide
theorem hl2080 : 2080 < SB := by decide
theorem hl2082 : 2082 < SB := by decide

/-! ### The uniform law -/

/-- the uniform column's law (the bridge's `lawR` on `UTYPE`) -/
noncomputable def uLaw : Fin SB → ℝ := lawR UTYPE uPats

theorem uLaw_eq (c : Fin SB) : uLaw c =
    if c.val ∈ stsOf uPats then (if isABA c.val then (17 + s17) / 204 else (17 - s17) / 204)
    else 0 := by
  unfold uLaw lawR lawE0 lawE1
  simp only [UTYPE, beq_self_eq_true, if_true]
  by_cases hc : c.val ∈ stsOf uPats
  · rw [if_pos hc, if_pos hc]
    by_cases ha : isABA c.val
    · rw [if_pos ha, if_pos ha]; push_cast; ring
    · rw [if_neg ha, if_neg ha]; push_cast; ring
  · rw [if_neg hc, if_neg hc]

theorem uLaw_zero (c : Fin SB) (hc : c.val ∉ stsOf uPats) : uLaw c = 0 := by
  rw [uLaw_eq, if_neg hc]

theorem uLaw_val (x : Nat) (hx : x ∈ stsOf uPats) :
    uLaw (toFin x) = if isABA x then (17 + s17) / 204 else (17 - s17) / 204 := by
  rw [uLaw_eq, toFin_val x (uSts_lt x hx), if_pos hx]

/-! ### The Perron weight and the Parry kernel -/

theorem s17_gt_one : 1 < s17 := by
  have h := s17_sq; have h0 := s17_pos; nlinarith

theorem rhoR_pos : 0 < rhoR := by unfold rhoR; have := s17_pos; linarith

/-- the right Perron vector of the class matrix: `1` on `ABA`, `(√17 - 1)/4` on `ABC` -/
noncomputable def pv (st : Nat) : ℝ := if isABA st then 1 else (s17 - 1) / 4

theorem pv_pos (st : Nat) : 0 < pv st := by
  unfold pv; split_ifs
  · exact one_pos
  · have := s17_gt_one; linarith

/-- the Parry kernel on the uniform states, the identity kernel elsewhere -/
noncomputable def KU (c s : Fin SB) : ℝ :=
  if c.val ∈ stsOf uPats then
    (if s.val ∈ stsOf uPats ∧ compat c.val s.val = true then pv s.val / (rhoR * pv c.val) else 0)
  else if s = c then 1 else 0

theorem KU_nonneg (c s : Fin SB) : 0 ≤ KU c s := by
  unfold KU; split_ifs
  · exact div_nonneg (pv_pos _).le (mul_pos rhoR_pos (pv_pos _)).le
  · exact le_refl _
  · exact zero_le_one
  · exact le_refl _

theorem KU_support (c s : Fin SB) (hc : 0 < uLaw c) (hK : 0 < KU c s) :
    compat c.val s.val = true ∧ c.val ∈ stsOf uPats ∧ s.val ∈ stsOf uPats := by
  have hc' : c.val ∈ stsOf uPats := by
    by_contra h; rw [uLaw_zero c h] at hc; exact lt_irrefl _ hc
  unfold KU at hK
  rw [if_pos hc'] at hK
  by_cases hs : s.val ∈ stsOf uPats ∧ compat c.val s.val = true
  · exact ⟨hs.2, hc', hs.1⟩
  · rw [if_neg hs] at hK; exact absurd hK (lt_irrefl _)


theorem KU_val (x y : Nat) (hx : x ∈ stsOf uPats) (hy : y < SB) :
    KU (toFin x) (toFin y) =
      if y ∈ stsOf uPats ∧ compat x y = true then pv y / (rhoR * pv x) else 0 := by
  unfold KU; rw [toFin_val x (uSts_lt x hx), toFin_val y hy, if_pos hx]

/-! ### Sums over the packed state space reduce to the twelve states -/

/-- the uniform states as elements of `Fin SB` -/
def uFin : List (Fin SB) := (stsOf uPats).map toFin

theorem uFin_eq : uFin = [toFin 32, toFin 34, toFin 64, toFin 65, toFin 1025, toFin 1026,
    toFin 1088, toFin 1089, toFin 2049, toFin 2050, toFin 2080, toFin 2082] := by
  unfold uFin; rw [uSts_eq]; rfl

theorem uFin_nodup : uFin.Nodup := by
  rw [uFin_eq]; decide

theorem mem_uFin (s : Fin SB) : s ∈ uFin ↔ s.val ∈ stsOf uPats := by
  unfold uFin
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
    rw [toFin_val x (uSts_lt x hx)]; exact hx
  · intro h
    exact List.mem_map.2 ⟨s.val, h, Fin.ext (toFin_val _ s.isLt)⟩

/-- a function vanishing off the uniform states sums over the twelve of them -/
theorem sum_uFin (g : Fin SB → ℝ) (h0 : ∀ s : Fin SB, s.val ∉ stsOf uPats → g s = 0) :
    ∑ s, g s = (uFin.map g).sum := by
  rw [← List.sum_toFinset g uFin_nodup]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro s _ hs
  apply h0
  intro hmem
  exact hs (List.mem_toFinset.2 ((mem_uFin s).2 hmem))

theorem mem_uSts_cases (c : Fin SB) (hc : c.val ∈ stsOf uPats) :
    c = toFin 32 ∨ c = toFin 34 ∨ c = toFin 64 ∨ c = toFin 65 ∨ c = toFin 1025 ∨ c = toFin 1026
    ∨ c = toFin 1088 ∨ c = toFin 1089 ∨ c = toFin 2049 ∨ c = toFin 2050 ∨ c = toFin 2080
    ∨ c = toFin 2082 := by
  have h := (mem_uFin c).2 hc
  rw [uFin_eq] at h
  simpa using h

/-! ### Row sums, total mass, stationarity: twelve explicit computations each -/

set_option maxHeartbeats 1000000 in
theorem KU_rowsum (c : Fin SB) : ∑ s, KU c s = 1 := by
  by_cases hc : c.val ∈ stsOf uPats
  · rw [sum_uFin (KU c) (fun s hs => by unfold KU; rw [if_pos hc, if_neg (fun h => hs h.1)])]
    have h17 := s17_sq
    have h5 : (5 : ℝ) + s17 ≠ 0 := by have := s17_pos; linarith
    have hv : s17 - 1 ≠ 0 := by have := s17_gt_one; linarith
    rcases mem_uSts_cases c hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [uFin_eq, List.map, List.sum_cons, List.sum_nil, KU, pv, toFin, SB, compat, isABA,
        uSts_eq, rhoR]
      norm_num
      field_simp
      nlinarith [h17, s17_pos]
  · have : ∀ s, KU c s = if s = c then 1 else 0 := fun s => by unfold KU; rw [if_neg hc]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem uLaw_sum : ∑ c, uLaw c = 1 := by
  rw [sum_uFin uLaw uLaw_zero]
  simp only [uFin_eq, List.map, List.sum_cons, List.sum_nil, uLaw_val, hm32, hm34, hm64, hm65, hm1025, hm1026, hm1088, hm1089, hm2049, hm2050, hm2080, hm2082, isABA]
  norm_num
  ring

set_option maxHeartbeats 1000000 in
theorem KU_step (s : Fin SB) : ∑ c, uLaw c * KU c s = uLaw s := by
  by_cases hs : s.val ∈ stsOf uPats
  · rw [sum_uFin (fun c => uLaw c * KU c s) (fun c hc => by rw [uLaw_zero c hc, zero_mul])]
    have h17 := s17_sq
    have h3 : s17 ^ 3 = 17 * s17 := by rw [pow_succ, h17]
    have h4 : s17 ^ 4 = 289 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h17]; norm_num
    have h5 : (5 : ℝ) + s17 ≠ 0 := by have := s17_pos; linarith
    have hv : s17 - 1 ≠ 0 := by have := s17_gt_one; linarith
    rcases mem_uSts_cases s hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [uFin_eq, List.map, List.sum_cons, List.sum_nil, KU_val, uLaw_val, hm32, hm34, hm64, hm65, hm1025, hm1026, hm1088, hm1089, hm2049, hm2050, hm2080, hm2082, hl32, hl34, hl64, hl65, hl1025, hl1026, hl1088, hl1089, hl2049, hl2050, hl2080, hl2082,
        compat, isABA, pv, rhoR, bne]
      norm_num
      field_simp
      nlinarith [h17, h3, h4, s17_pos]
  · rw [uLaw_zero s hs]
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : c.val ∈ stsOf uPats
    · unfold KU; rw [if_pos hc, if_neg (fun h => hs h.1), mul_zero]
    · rw [uLaw_zero c hc, zero_mul]

/-! ### The conditional entropy is exactly `log rhoR` -/

theorem KU_log (c s : Fin SB) (hc : c.val ∈ stsOf uPats) :
    KU c s * (-Real.log (KU c s))
      = KU c s * (Real.log rhoR + Real.log (pv c.val) - Real.log (pv s.val)) := by
  unfold KU
  rw [if_pos hc]
  by_cases h : s.val ∈ stsOf uPats ∧ compat c.val s.val = true
  · rw [if_pos h, Real.log_div (pv_pos _).ne' (mul_pos rhoR_pos (pv_pos _)).ne',
      Real.log_mul rhoR_pos.ne' (pv_pos _).ne']
    ring
  · rw [if_neg h]; ring

theorem parry_entropy :
    ∑ c, uLaw c * ∑ s, KU c s * (-Real.log (KU c s)) = Real.log rhoR := by
  have h1 : ∀ c : Fin SB, uLaw c * ∑ s, KU c s * (-Real.log (KU c s))
      = uLaw c * (Real.log rhoR + Real.log (pv c.val))
        - ∑ s, uLaw c * KU c s * Real.log (pv s.val) := by
    intro c
    by_cases hc : c.val ∈ stsOf uPats
    · have : ∑ s, KU c s * (-Real.log (KU c s))
          = ∑ s, KU c s * (Real.log rhoR + Real.log (pv c.val) - Real.log (pv s.val)) :=
        Finset.sum_congr rfl fun s _ => KU_log c s hc
      rw [this]
      have h2 : ∑ s, KU c s * (Real.log rhoR + Real.log (pv c.val) - Real.log (pv s.val))
          = (Real.log rhoR + Real.log (pv c.val)) * ∑ s, KU c s
            - ∑ s, KU c s * Real.log (pv s.val) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro s _; ring
      rw [h2, KU_rowsum, mul_one, mul_sub, Finset.mul_sum]
      apply congrArg
      apply Finset.sum_congr rfl; intro s _; ring
    · rw [uLaw_zero c hc]; simp
  rw [Finset.sum_congr rfl fun c _ => h1 c, Finset.sum_sub_distrib]
  have h3 : ∑ c : Fin SB, ∑ s, uLaw c * KU c s * Real.log (pv s.val)
      = ∑ s : Fin SB, uLaw s * Real.log (pv s.val) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro s _
    rw [← Finset.sum_mul, KU_step]
  rw [h3]
  have h4 : ∑ c : Fin SB, uLaw c * (Real.log rhoR + Real.log (pv c.val))
      = Real.log rhoR * ∑ c, uLaw c + ∑ c, uLaw c * Real.log (pv c.val) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro c _; ring
  rw [h4, uLaw_sum]
  ring

/-- **The `U → U` seam package.** The Parry kernel is a stochastic kernel, stationary for the
uniform law, supported in the compatibility relation on the uniform states, with conditional
entropy at least (in fact exactly) `log rhoR`. -/
theorem parry_seam :
    (∀ c s, 0 ≤ KU c s) ∧ (∀ c, ∑ s, KU c s = 1) ∧ (∀ s, ∑ c, uLaw c * KU c s = uLaw s)
    ∧ (∀ c s, 0 < uLaw c → 0 < KU c s →
        compat c.val s.val = true ∧ c.val ∈ stsOf uPats ∧ s.val ∈ stsOf uPats)
    ∧ (∑ c, uLaw c = 1)
    ∧ Real.log rhoR ≤ ∑ c, uLaw c * ∑ s, KU c s * (-Real.log (KU c s)) :=
  ⟨KU_nonneg, KU_rowsum, KU_step, KU_support, uLaw_sum, parry_entropy.symm.le⟩

end Grid3.Three.Cert

