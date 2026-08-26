/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.Four.Column
import Grid3.DepthTwo

/-!
# The depth-two seam inequalities at `k = 4`

The vector one gets on a column `C₂` from a state `s₀` two columns back is a sum of indicator
vectors: one for each state `u` of the punctured column `C₁ \ s₀`, the indicator of the states of
`C₂ \ u`. Both seam inequalities are linear, so their slack is the sum over `u` of the depth-one
column sums `GH u`, `GC u` of `Grid3.Four.Column`.

`GH u ≥ 0` always. `GC u` can be `-1`, exactly when the punctured column `C₂ \ u` is Bad; but then
`C₂ \ u` and the next column pin `u.2.2` down (unflipped case), and moving the bottom colour of
`u` to any other colour of `Z` gives a state `u'` of `C₁ \ s₀` with `GC u' ≥ 1` — an injection
from the Bad states into the good ones, so the total is nonnegative.
-/

open Finset

namespace Grid3
namespace Four

/-! ### The column sums of a punctured column -/

/-- The `(H1)` column sum of `C₂ \ u` against `C₃`. -/
def GH (C₂ C₃ : ColumnLists) (u : State) : ℤ :=
  ∑ y ∈ C₂.2.1.erase u.2.1, QH 4 (C₂.1.erase u.1) (C₂.2.2.erase u.2.2) C₃.1 C₃.2.1 C₃.2.2 y

/-- The `(C1_r)` column sum of `C₂ \ u` against `C₃`. -/
def GC (C₂ C₃ : ColumnLists) (u : State) : ℤ :=
  ∑ y ∈ C₂.2.1.erase u.2.1, QC 4 (C₂.1.erase u.1) (C₂.2.2.erase u.2.2) C₃.1 C₃.2.1 C₃.2.2 y

/-- The seam slack of a vector, `(H1)`. -/
def slackH (S : Finset State) (N : State → ℕ) (T M B : Finset ℕ) : ℤ :=
  (total (states T M B) (step S N) : ℤ) - ene 4 * total S N - eqMass S N

/-- The seam slack of a vector, `(C1_r)`. -/
def slackC (S : Finset State) (N : State → ℕ) (T M B : Finset ℕ) : ℤ :=
  cc 4 * slackH S N T M B
    + ((eqMass (states T M B) (step S N) : ℤ) - gam 4 * total S N - del 4 * eqMass S N)

theorem H1_iff_slack (S : Finset State) (N : State → ℕ) (T M B : Finset ℕ) :
    H1 S N T M B 4 ↔ 0 ≤ slackH S N T M B := by
  unfold H1 slackH; omega

theorem C1r_iff_slack (S : Finset State) (N : State → ℕ) (T M B : Finset ℕ) :
    C1r S N T M B 4 ↔ 0 ≤ slackC S N T M B := by
  unfold C1r slackC slackH
  have hc : cc 4 = 14 := by decide
  have he : ene 4 = 16 := by decide
  have hg : gam 4 = 5 := by decide
  have hd : del 4 = 2 := by decide
  rw [hc, he, hg, hd]
  omega

/-- The slacks are additive. -/
theorem slackH_sum {ι : Type*} (I : Finset ι) (S : Finset State) (Ns : ι → State → ℕ)
    (T M B : Finset ℕ) :
    slackH S (fun s => ∑ i ∈ I, Ns i s) T M B = ∑ i ∈ I, slackH S (Ns i) T M B := by
  unfold slackH
  rw [total_sum, eqMass_sum, step_sum, total_sum]
  push_cast
  rw [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib]

theorem slackC_sum {ι : Type*} (I : Finset ι) (S : Finset State) (Ns : ι → State → ℕ)
    (T M B : Finset ℕ) :
    slackC S (fun s => ∑ i ∈ I, Ns i s) T M B = ∑ i ∈ I, slackC S (Ns i) T M B := by
  unfold slackC
  rw [slackH_sum, total_sum, eqMass_sum, step_sum, eqMass_sum]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- The slack of the indicator of a punctured column is its column sum. -/
theorem slackH_indicator {S : Finset State} {X Y Z : Finset ℕ} (hS : states X Y Z ⊆ S)
    (T M B : Finset ℕ) :
    slackH S (fun s => if s ∈ states X Y Z then 1 else 0) T M B
      = ∑ y ∈ Y, QH 4 X Z T M B y := by
  unfold slackH
  rw [total_indicator hS, eqMass_indicator hS, step_indicator hS, total_ones, eqMass_ones,
    total_step]
  simp only [one_mul]
  rw [← sum_dH, sum_states]
  rfl

theorem slackC_indicator {S : Finset State} {X Y Z : Finset ℕ} (hS : states X Y Z ⊆ S)
    (T M B : Finset ℕ) :
    slackC S (fun s => if s ∈ states X Y Z then 1 else 0) T M B
      = ∑ y ∈ Y, QC 4 X Z T M B y := by
  unfold slackC slackH
  rw [total_indicator hS, eqMass_indicator hS, step_indicator hS, total_ones, eqMass_ones,
    total_step, eqMass_step]
  simp only [one_mul]
  have := sum_dC 4 X Y Z T M B
  rw [sum_states] at this
  unfold QC
  rw [← this]

/-! ### The vector from two columns back -/

/-- The states of `C₂` reached from `u` are the states of `C₂ \ u`. -/
theorem compat_iff_mem_punct {C₂ : ColumnLists} {u v : State} (hv : v ∈ columnStates C₂) :
    Compat u v ↔ v ∈ states (C₂.1.erase u.1) (C₂.2.1.erase u.2.1) (C₂.2.2.erase u.2.2) := by
  rw [← filter_compat_eq_states, Finset.mem_filter]
  exact ⟨fun h => ⟨hv, h⟩, fun h => h.2⟩

/-- The vector from `s₀` two columns back is the sum of the indicators of `C₂ \ u` over the states
`u` of `C₁ \ s₀`. -/
theorem twoStepVec_eq (C₁ C₂ : ColumnLists) (s₀ : State) :
    ∀ v ∈ columnStates C₂, twoStepVec C₁ s₀ v
      = ∑ u ∈ states (C₁.1.erase s₀.1) (C₁.2.1.erase s₀.2.1) (C₁.2.2.erase s₀.2.2),
          (if v ∈ states (C₂.1.erase u.1) (C₂.2.1.erase u.2.1) (C₂.2.2.erase u.2.2) then 1 else 0) := by
  intro v hv
  unfold twoStepVec step
  rw [← filter_compat_eq_states, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases h1 : Compat s₀ u <;> by_cases h2 : Compat u v <;>
    simp [h1, h2, ← compat_iff_mem_punct hv]

/-- The vector after one transfer from the all-ones vector is the same sum, over the unpunctured
first column. -/
theorem stepOnes_eq (C₀ C₁ : ColumnLists) :
    ∀ v ∈ columnStates C₁, step (columnStates C₀) (fun _ => 1) v
      = ∑ u ∈ states C₀.1 C₀.2.1 C₀.2.2,
          (if v ∈ states (C₁.1.erase u.1) (C₁.2.1.erase u.2.1) (C₁.2.2.erase u.2.2) then 1 else 0) := by
  intro v hv
  unfold step
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases h2 : Compat u v <;> simp [h2, ← compat_iff_mem_punct hv]

/-- The seam inequalities for such a sum vector reduce to the sums of column sums. -/
theorem localSeamOK_of_sums {X Y Z : Finset ℕ} {C₂ C₃ : ColumnLists} {N : State → ℕ}
    (hN : ∀ v ∈ columnStates C₂, N v = ∑ u ∈ states X Y Z,
      (if v ∈ states (C₂.1.erase u.1) (C₂.2.1.erase u.2.1) (C₂.2.2.erase u.2.2) then 1 else 0))
    (hH : 0 ≤ ∑ u ∈ states X Y Z, GH C₂ C₃ u) (hC : 0 ≤ ∑ u ∈ states X Y Z, GC C₂ C₃ u) :
    LocalSeamOK 4 C₂ N C₃ := by
  have hsub : ∀ u : State, states (C₂.1.erase u.1) (C₂.2.1.erase u.2.1) (C₂.2.2.erase u.2.2)
      ⊆ columnStates C₂ := fun u => states_erase_subset _ _ _ u
  refine ⟨?_, ?_⟩
  · refine H1_congr (fun v hv => (hN v hv).symm) ?_
    rw [H1_iff_slack, slackH_sum]
    refine le_trans hH (le_of_eq ?_)
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [slackH_indicator (hsub u)]
    rfl
  · refine C1r_congr (fun v hv => (hN v hv).symm) ?_
    rw [C1r_iff_slack, slackC_sum]
    refine le_trans hC (le_of_eq ?_)
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [slackC_indicator (hsub u)]
    rfl

/-! ### The core: the sums of column sums are nonnegative -/

section core
variable {X Y Z : Finset ℕ} (hX : NearK 4 X) (hY : NearK 4 Y) (hZ : NearK 4 Z)
  {C₂ C₃ : ColumnLists} (h2 : IsKColumn 4 C₂) (h3 : IsKColumn 4 C₃)
include hX hY hZ h2 h3

theorem sum_GH_nonneg : 0 ≤ ∑ u ∈ states X Y Z, GH C₂ C₃ u := by
  refine Finset.sum_nonneg fun u _ => ?_
  unfold GH
  exact colH_four (nearK_erase h2.1 _) (nearK_erase h2.2.1 _) (nearK_erase h2.2.2 _) h3.1 h3.2.1
    h3.2.2

/-- `GC u ≥ -1`. -/
theorem GC_neg (u : State) : -1 ≤ GC C₂ C₃ u :=
  colC_neg (nearK_erase h2.1 _) (nearK_erase h2.2.1 _) (nearK_erase h2.2.2 _) h3.1 h3.2.1 h3.2.2

/-- `GC u ≥ 0` unless `C₂ \ u` is Bad. -/
theorem GC_or (u : State) :
    0 ≤ GC C₂ C₃ u ∨ BadCol (C₂.1.erase u.1) (C₂.2.1.erase u.2.1) (C₂.2.2.erase u.2.2)
      C₃.1 C₃.2.1 C₃.2.2 :=
  colC_or (nearK_erase h2.1 _) (nearK_erase h2.2.1 _) (nearK_erase h2.2.2 _) h3.1 h3.2.1 h3.2.2

end core

/-! ### Consequences of `BadU` -/

theorem card_filter_eq_zero_iff {Z T : Finset ℕ} : (Z.filter (· ∉ T)).card = 0 ↔ Z ⊆ T := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp only [not_not]
  exact ⟨fun h a ha => h ha, fun h a ha => h ha⟩

/-- In `BadU`, the punctured bottom list is `T ∩ M`, a set of three colours. -/
theorem badU_Z_eq {X Z T M B : Finset ℕ} {y : ℕ} (hM : M.card = 4) (hb : BadU X Z T M B y) :
    Z = T ∩ M ∧ (T ∩ M).card = 3 := by
  obtain ⟨-, -, -, -, -, -, hZ3, hZT, hZM, hMT, -, -⟩ := hb
  have hTM : (T ∩ M).card = 3 := by
    have := Finset.card_filter_add_card_filter_not (s := M) (p := (· ∈ T))
    rw [Finset.filter_mem_eq_inter, Finset.inter_comm, hM] at this
    have e : (M.filter (fun a => ¬ a ∈ T)).card = 1 := hMT
    omega
  have hsub : Z ⊆ T ∩ M := fun a ha =>
    Finset.mem_inter.mpr ⟨card_filter_eq_zero_iff.mp hZT ha, card_filter_eq_zero_iff.mp hZM ha⟩
  exact ⟨Finset.eq_of_subset_of_card_le hsub (by omega), hTM⟩

theorem badF_X_eq {X Z T M B : Finset ℕ} {y : ℕ} (hM : M.card = 4) (hb : BadF X Z T M B y) :
    X = M ∩ B ∧ (M ∩ B).card = 3 := by
  obtain ⟨-, -, -, -, -, hX3, -, hXB, hXM, hMB, -, -⟩ := hb
  have hMB' : (M ∩ B).card = 3 := by
    have := Finset.card_filter_add_card_filter_not (s := M) (p := (· ∈ B))
    rw [Finset.filter_mem_eq_inter, hM] at this
    have e : (M.filter (fun a => ¬ a ∈ B)).card = 1 := hMB
    omega
  have hsub : X ⊆ M ∩ B := fun a ha =>
    Finset.mem_inter.mpr ⟨card_filter_eq_zero_iff.mp hXM ha, card_filter_eq_zero_iff.mp hXB ha⟩
  exact ⟨Finset.eq_of_subset_of_card_le hsub (by omega), hMB'⟩

/-- A punctured list of three colours came from a member. -/
theorem mem_of_card_erase {B : Finset ℕ} (hB : B.card = 4) {c : ℕ} (h : (B.erase c).card = 3) :
    c ∈ B := by
  by_contra hc
  rw [Finset.erase_eq_of_notMem hc] at h
  omega

/-- Two punctures of a `4`-list giving the same `3`-list are the same puncture. -/
theorem erase_eq_erase {B : Finset ℕ} (hB : B.card = 4) {c c' : ℕ} (hc : c ∈ B)
    (h : B.erase c = B.erase c') : c = c' := by
  by_contra hne
  have : c ∈ B.erase c' := Finset.mem_erase.mpr ⟨hne, hc⟩
  rw [← h] at this
  exact (Finset.mem_erase.mp this).1 rfl

/-! ### The replacement colour -/

/-- A colour of `Z` different from two given colours. -/
noncomputable def repl (Z : Finset ℕ) (c b : ℕ) : ℕ :=
  if h : ((Z.erase c).erase b).Nonempty then ((Z.erase c).erase b).min' h else 0

theorem repl_mem {Z : Finset ℕ} (hZ : NearK 4 Z) (c b : ℕ) : repl Z c b ∈ (Z.erase c).erase b := by
  have hne : ((Z.erase c).erase b).Nonempty := by
    rw [← Finset.card_pos]
    have h1 := Finset.pred_card_le_card_erase (s := Z) (a := c)
    have h2 := Finset.pred_card_le_card_erase (s := Z.erase c) (a := b)
    rcases hZ with h | h <;> omega
  unfold repl
  rw [dif_pos hne]
  exact Finset.min'_mem _ hne

end Four
end Grid3

namespace Grid3
namespace Four

open Finset

/-! ### The accounting -/

section accounting
variable {X Y Z : Finset ℕ} (hX : NearK 4 X) (hY : NearK 4 Y) (hZ : NearK 4 Z)
  {C₂ C₃ : ColumnLists} (h2 : IsKColumn 4 C₂) (h3 : IsKColumn 4 C₃)
include hX hY hZ h2 h3

/-- **The core inequality, unflipped case.** If some Bad state is of the `BadU` kind, every Bad
state is, and the bottom-colour replacement compensates. -/
theorem sum_GC_nonneg_U {u₀ : State} (hu₀ : u₀ ∈ states X Y Z) {y₀ : ℕ}
    (hb₀ : BadU (C₂.1.erase u₀.1) (C₂.2.2.erase u₀.2.2) C₃.1 C₃.2.1 C₃.2.2 y₀) :
    0 ≤ ∑ u ∈ states X Y Z, GC C₂ C₃ u := by
  classical
  obtain ⟨hT2, hM2, hB2⟩ := h2
  obtain ⟨hT3, hM3, hB3⟩ := h3
  -- global facts from `hb₀`: `M₃ ⊆ B₃`, `|M₃ \ T₃| = 1`, `|T₃ ∩ M₃| = 3`
  have hMB3 : (C₃.2.1.filter (· ∉ C₃.2.2)).card = 0 := hb₀.2.2.2.2.2.2.2.2.2.2.1
  have hTM3 : (C₃.1 ∩ C₃.2.1).card = 3 := (badU_Z_eq hM3 hb₀).2
  -- every Bad state is `BadU`, with its punctured bottom list equal to `T₃ ∩ M₃`
  have hbadU : ∀ u ∈ states X Y Z,
      BadCol (C₂.1.erase u.1) (C₂.2.1.erase u.2.1) (C₂.2.2.erase u.2.2) C₃.1 C₃.2.1 C₃.2.2 →
      ∃ y ∈ C₂.2.1.erase u.2.1, y ∈ C₃.2.1 ∧ ¬ (y ∈ C₃.1 ∧ y ∈ C₃.2.2) ∧
        BadU (C₂.1.erase u.1) (C₂.2.2.erase u.2.2) C₃.1 C₃.2.1 C₃.2.2 y := by
    intro u _ ⟨y, hy, hyM, hirr, hb⟩
    refine ⟨y, hy, hyM, hirr, ?_⟩
    rcases hb with hb | hb
    · exact hb
    · exfalso
      have := hb.2.2.2.2.2.2.2.2.2.1
      omega
  have hZeq : ∀ u ∈ states X Y Z, ∀ y, BadU (C₂.1.erase u.1) (C₂.2.2.erase u.2.2) C₃.1 C₃.2.1 C₃.2.2 y →
      (C₂.2.2.erase u.2.2) = C₃.1 ∩ C₃.2.1 ∧ u.2.2 ∈ C₂.2.2 := by
    intro u _ y hb
    have h := (badU_Z_eq hM3 hb).1
    refine ⟨h, mem_of_card_erase hB2 ?_⟩
    rw [h]; exact hTM3
  -- the Bad states and the replacement map
  set S := states X Y Z with hS
  set bad := S.filter (fun u => BadCol (C₂.1.erase u.1) (C₂.2.1.erase u.2.1) (C₂.2.2.erase u.2.2) C₃.1 C₃.2.1 C₃.2.2) with hbad
  let φ : State → State := fun u => (u.1, u.2.1, repl Z u.2.2 u.2.1)
  have hφmem : ∀ u ∈ S, φ u ∈ S := by
    intro u hu
    rw [hS, mem_states] at hu ⊢
    have hr := repl_mem hZ u.2.2 u.2.1
    rw [Finset.mem_erase, Finset.mem_erase] at hr
    exact ⟨hu.1, hu.2.1, hr.2.2, hu.2.2.2.1, Ne.symm hr.1⟩
  have hφZ : ∀ u ∈ bad, C₂.2.2.erase (repl Z u.2.2 u.2.1) ≠ C₃.1 ∩ C₃.2.1 := by
    intro u hu heq
    obtain ⟨huS, hcol⟩ := Finset.mem_filter.mp hu
    obtain ⟨y, -, -, -, hb⟩ := hbadU u huS hcol
    obtain ⟨hZu, hmem⟩ := hZeq u huS y hb
    have hr := repl_mem hZ u.2.2 u.2.1
    rw [Finset.mem_erase, Finset.mem_erase] at hr
    by_cases hrB : repl Z u.2.2 u.2.1 ∈ C₂.2.2
    · exact hr.2.1 (erase_eq_erase hB2 hrB (heq.trans hZu.symm))
    · rw [Finset.erase_eq_of_notMem hrB] at heq
      have := congrArg Finset.card heq
      omega
  have hφgood : ∀ u ∈ bad, φ u ∉ bad := by
    intro u hu hφu
    obtain ⟨_, hcol⟩ := Finset.mem_filter.mp hφu
    obtain ⟨y, -, -, -, hb⟩ := hbadU (φ u) (hφmem u (Finset.mem_filter.mp hu).1) hcol
    exact hφZ u hu (badU_Z_eq hM3 hb).1
  have hφgap : ∀ u ∈ bad, 1 ≤ GC C₂ C₃ (φ u) := by
    intro u hu
    obtain ⟨huS, hcol⟩ := Finset.mem_filter.mp hu
    obtain ⟨y, hy, hyM, hirr, hb⟩ := hbadU u huS hcol
    unfold GC
    refine colC_gap (nearK_erase hT2 _) (nearK_erase hM2 _) (nearK_erase hB2 _) hT3 hM3 hB3 hy hyM
      hirr ?_
    rintro (hb' | hb')
    · exact hφZ u hu (badU_Z_eq hM3 hb').1
    · have := hb'.2.2.2.2.2.2.2.2.2.1
      omega
  have hφinj : Set.InjOn φ bad := by
    intro u hu u' hu' heq
    obtain ⟨huS, hcol⟩ := Finset.mem_filter.mp hu
    obtain ⟨hu'S, hcol'⟩ := Finset.mem_filter.mp hu'
    obtain ⟨y, -, -, -, hb⟩ := hbadU u huS hcol
    obtain ⟨y', -, -, -, hb'⟩ := hbadU u' hu'S hcol'
    obtain ⟨hZu, hmem⟩ := hZeq u huS y hb
    obtain ⟨hZu', hmem'⟩ := hZeq u' hu'S y' hb'
    simp only [φ, Prod.mk.injEq] at heq
    obtain ⟨h1, h2, -⟩ := heq
    have h3 : u.2.2 = u'.2.2 := erase_eq_erase hB2 hmem (hZu.trans hZu'.symm)
    exact Prod.ext h1 (Prod.ext h2 h3)
  -- the sum
  have hsplit := Finset.sum_filter_add_sum_filter_not S
    (fun u => BadCol (C₂.1.erase u.1) (C₂.2.1.erase u.2.1) (C₂.2.2.erase u.2.2) C₃.1 C₃.2.1 C₃.2.2) (GC C₂ C₃)
  rw [← hbad] at hsplit
  have hbad_ge : -(bad.card : ℤ) ≤ ∑ u ∈ bad, GC C₂ C₃ u := by
    have := Finset.sum_le_sum fun u (_ : u ∈ bad) => GC_neg hX hY hZ ⟨hT2, hM2, hB2⟩ ⟨hT3, hM3, hB3⟩ u
    simp only [Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one] at this
    exact this
  have himage : bad.image φ ⊆ S.filter (fun u => ¬ BadCol (C₂.1.erase u.1) (C₂.2.1.erase u.2.1) (C₂.2.2.erase u.2.2) C₃.1 C₃.2.1 C₃.2.2) := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_filter.mpr ⟨hφmem u (Finset.mem_filter.mp hu).1, ?_⟩
    intro hc
    exact hφgood u hu (Finset.mem_filter.mpr ⟨hφmem u (Finset.mem_filter.mp hu).1, hc⟩)
  have hgood_ge : ∑ u ∈ bad.image φ, GC C₂ C₃ u
      ≤ ∑ u ∈ S.filter (fun u => ¬ BadCol (C₂.1.erase u.1) (C₂.2.1.erase u.2.1) (C₂.2.2.erase u.2.2) C₃.1 C₃.2.1 C₃.2.2), GC C₂ C₃ u := by
    refine Finset.sum_le_sum_of_subset_of_nonneg himage fun u hu _ => ?_
    obtain ⟨huS, hnot⟩ := Finset.mem_filter.mp hu
    rcases GC_or hX hY hZ ⟨hT2, hM2, hB2⟩ ⟨hT3, hM3, hB3⟩ u with h | h
    · exact h
    · exact absurd h hnot
  have himage_ge : (bad.card : ℤ) ≤ ∑ u ∈ bad.image φ, GC C₂ C₃ u := by
    rw [Finset.sum_image fun x hx y hy h => hφinj hx hy h]
    have := Finset.sum_le_sum fun u (hu : u ∈ bad) => hφgap u hu
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at this
    exact this
  linarith

end accounting

end Four
end Grid3

namespace Grid3
namespace Four

open Finset

section accountingF
variable {X Y Z : Finset ℕ} (hX : NearK 4 X) (hY : NearK 4 Y) (hZ : NearK 4 Z)
  {C₂ C₃ : ColumnLists} (h2 : IsKColumn 4 C₂) (h3 : IsKColumn 4 C₃)
include hX hY hZ h2 h3

/-- **The core inequality, flipped case.** -/
theorem sum_GC_nonneg_F {u₀ : State} (hu₀ : u₀ ∈ states X Y Z) {y₀ : ℕ}
    (hb₀ : BadF (C₂.1.erase u₀.1) (C₂.2.2.erase u₀.2.2) C₃.1 C₃.2.1 C₃.2.2 y₀) :
    0 ≤ ∑ u ∈ states X Y Z, GC C₂ C₃ u := by
  classical
  obtain ⟨hT2, hM2, hB2⟩ := h2
  obtain ⟨hT3, hM3, hB3⟩ := h3
  have hMT3 : (C₃.2.1.filter (· ∉ C₃.1)).card = 0 := hb₀.2.2.2.2.2.2.2.2.2.2.1
  have hMB3 : (C₃.2.1 ∩ C₃.2.2).card = 3 := (badF_X_eq hM3 hb₀).2
  have hbadF : ∀ u ∈ states X Y Z,
      BadCol (C₂.1.erase u.1) (C₂.2.1.erase u.2.1) (C₂.2.2.erase u.2.2) C₃.1 C₃.2.1 C₃.2.2 →
      ∃ y ∈ C₂.2.1.erase u.2.1, y ∈ C₃.2.1 ∧ ¬ (y ∈ C₃.1 ∧ y ∈ C₃.2.2) ∧
        BadF (C₂.1.erase u.1) (C₂.2.2.erase u.2.2) C₃.1 C₃.2.1 C₃.2.2 y := by
    intro u _ ⟨y, hy, hyM, hirr, hb⟩
    refine ⟨y, hy, hyM, hirr, ?_⟩
    rcases hb with hb | hb
    · exfalso
      have := hb.2.2.2.2.2.2.2.2.2.1
      omega
    · exact hb
  have hXeq : ∀ u ∈ states X Y Z, ∀ y, BadF (C₂.1.erase u.1) (C₂.2.2.erase u.2.2) C₃.1 C₃.2.1 C₃.2.2 y →
      (C₂.1.erase u.1) = C₃.2.1 ∩ C₃.2.2 ∧ u.1 ∈ C₂.1 := by
    intro u _ y hb
    have h := (badF_X_eq hM3 hb).1
    refine ⟨h, mem_of_card_erase hT2 ?_⟩
    rw [h]; exact hMB3
  set S := states X Y Z with hS
  set bad := S.filter (fun u => BadCol (C₂.1.erase u.1) (C₂.2.1.erase u.2.1) (C₂.2.2.erase u.2.2) C₃.1 C₃.2.1 C₃.2.2) with hbad
  let φ : State → State := fun u => (repl X u.1 u.2.1, u.2.1, u.2.2)
  have hφmem : ∀ u ∈ S, φ u ∈ S := by
    intro u hu
    rw [hS, mem_states] at hu ⊢
    have hr := repl_mem hX u.1 u.2.1
    rw [Finset.mem_erase, Finset.mem_erase] at hr
    exact ⟨hr.2.2, hu.2.1, hu.2.2.1, hr.1, hu.2.2.2.2⟩
  have hφX : ∀ u ∈ bad, C₂.1.erase (repl X u.1 u.2.1) ≠ C₃.2.1 ∩ C₃.2.2 := by
    intro u hu heq
    obtain ⟨huS, hcol⟩ := Finset.mem_filter.mp hu
    obtain ⟨y, -, -, -, hb⟩ := hbadF u huS hcol
    obtain ⟨hXu, hmem⟩ := hXeq u huS y hb
    have hr := repl_mem hX u.1 u.2.1
    rw [Finset.mem_erase, Finset.mem_erase] at hr
    by_cases hrT : repl X u.1 u.2.1 ∈ C₂.1
    · exact hr.2.1 (erase_eq_erase hT2 hrT (heq.trans hXu.symm))
    · rw [Finset.erase_eq_of_notMem hrT] at heq
      have := congrArg Finset.card heq
      omega
  have hφgood : ∀ u ∈ bad, φ u ∉ bad := by
    intro u hu hφu
    obtain ⟨_, hcol⟩ := Finset.mem_filter.mp hφu
    obtain ⟨y, -, -, -, hb⟩ := hbadF (φ u) (hφmem u (Finset.mem_filter.mp hu).1) hcol
    exact hφX u hu (badF_X_eq hM3 hb).1
  have hφgap : ∀ u ∈ bad, 1 ≤ GC C₂ C₃ (φ u) := by
    intro u hu
    obtain ⟨huS, hcol⟩ := Finset.mem_filter.mp hu
    obtain ⟨y, hy, hyM, hirr, hb⟩ := hbadF u huS hcol
    unfold GC
    refine colC_gap (nearK_erase hT2 _) (nearK_erase hM2 _) (nearK_erase hB2 _) hT3 hM3 hB3 hy hyM
      hirr ?_
    rintro (hb' | hb')
    · have := hb'.2.2.2.2.2.2.2.2.2.1
      omega
    · exact hφX u hu (badF_X_eq hM3 hb').1
  have hφinj : Set.InjOn φ bad := by
    intro u hu u' hu' heq
    obtain ⟨huS, hcol⟩ := Finset.mem_filter.mp hu
    obtain ⟨hu'S, hcol'⟩ := Finset.mem_filter.mp hu'
    obtain ⟨y, -, -, -, hb⟩ := hbadF u huS hcol
    obtain ⟨y', -, -, -, hb'⟩ := hbadF u' hu'S hcol'
    obtain ⟨hXu, hmem⟩ := hXeq u huS y hb
    obtain ⟨hXu', hmem'⟩ := hXeq u' hu'S y' hb'
    simp only [φ, Prod.mk.injEq] at heq
    obtain ⟨-, h2, h3⟩ := heq
    have h1 : u.1 = u'.1 := erase_eq_erase hT2 hmem (hXu.trans hXu'.symm)
    exact Prod.ext h1 (Prod.ext h2 h3)
  have hsplit := Finset.sum_filter_add_sum_filter_not S
    (fun u => BadCol (C₂.1.erase u.1) (C₂.2.1.erase u.2.1) (C₂.2.2.erase u.2.2) C₃.1 C₃.2.1 C₃.2.2) (GC C₂ C₃)
  rw [← hbad] at hsplit
  have hbad_ge : -(bad.card : ℤ) ≤ ∑ u ∈ bad, GC C₂ C₃ u := by
    have := Finset.sum_le_sum fun u (_ : u ∈ bad) => GC_neg hX hY hZ ⟨hT2, hM2, hB2⟩ ⟨hT3, hM3, hB3⟩ u
    simp only [Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one] at this
    exact this
  have himage : bad.image φ ⊆ S.filter (fun u => ¬ BadCol (C₂.1.erase u.1) (C₂.2.1.erase u.2.1) (C₂.2.2.erase u.2.2) C₃.1 C₃.2.1 C₃.2.2) := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_filter.mpr ⟨hφmem u (Finset.mem_filter.mp hu).1, ?_⟩
    intro hc
    exact hφgood u hu (Finset.mem_filter.mpr ⟨hφmem u (Finset.mem_filter.mp hu).1, hc⟩)
  have hgood_ge : ∑ u ∈ bad.image φ, GC C₂ C₃ u
      ≤ ∑ u ∈ S.filter (fun u => ¬ BadCol (C₂.1.erase u.1) (C₂.2.1.erase u.2.1) (C₂.2.2.erase u.2.2) C₃.1 C₃.2.1 C₃.2.2), GC C₂ C₃ u := by
    refine Finset.sum_le_sum_of_subset_of_nonneg himage fun u hu _ => ?_
    obtain ⟨huS, hnot⟩ := Finset.mem_filter.mp hu
    rcases GC_or hX hY hZ ⟨hT2, hM2, hB2⟩ ⟨hT3, hM3, hB3⟩ u with h | h
    · exact h
    · exact absurd h hnot
  have himage_ge : (bad.card : ℤ) ≤ ∑ u ∈ bad.image φ, GC C₂ C₃ u := by
    rw [Finset.sum_image fun x hx y hy h => hφinj hx hy h]
    have := Finset.sum_le_sum fun u (hu : u ∈ bad) => hφgap u hu
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at this
    exact this
  linarith

/-- **The core inequality.** -/
theorem sum_GC_nonneg : 0 ≤ ∑ u ∈ states X Y Z, GC C₂ C₃ u := by
  classical
  by_cases hbad : ∃ u ∈ states X Y Z, BadCol (C₂.1.erase u.1) (C₂.2.1.erase u.2.1) (C₂.2.2.erase u.2.2) C₃.1 C₃.2.1 C₃.2.2
  · obtain ⟨u₀, hu₀, y₀, -, -, -, hb⟩ := hbad
    rcases hb with hb | hb
    · exact sum_GC_nonneg_U hX hY hZ h2 h3 hu₀ hb
    · exact sum_GC_nonneg_F hX hY hZ h2 h3 hu₀ hb
  · push_neg at hbad
    refine Finset.sum_nonneg fun u hu => ?_
    rcases GC_or hX hY hZ h2 h3 u with h | h
    · exact h
    · exact absurd h (hbad u hu)

end accountingF

end Four
end Grid3
