import Grid3.Three.Cert.Complete
import Grid3.Three.Sig

/-!
# The seam package with its root facts

`seam_package` extends `seamOK_of_key` with the facts the assembly needs beyond `SeamOK`:
the canonical colour list has at most `32` slots (so states pack into `Fin SB`), and for a
nonuniform left column the canonical law has total mass one and collision mass at most `1/12`
(from the record's `Σ count = 108` and `Σ count² ≤ 972`, via `Sig.lean`).
-/

open Finset

namespace Grid3.Three.Cert

theorem seam_package_of_record (fmt mL mR M ne blob : Nat) (hf : fmt < 4)
    (h : checkRecord fmt mL mR M ne blob = true) :
    ∃ K, SeamOK mL ((colours mL mR M).map Prod.fst) mR ((colours mL mR M).map Prod.snd) K
      ∧ ((mL == UTYPE) = true →
          18 / 17 * rhoR * ∑ c, ∑ s, lawR mL ((colours mL mR M).map Prod.fst) c * K c s ^ 2 < 1)
      ∧ (colours mL mR M).length ≤ 32
      ∧ ((mL == UTYPE) = false →
          ∑ c, lawR mL ((colours mL mR M).map Prod.fst) c = 1
          ∧ ∑ c, lawR mL ((colours mL mR M).map Prod.fst) c ^ 2 ≤ 1 / 12) := by
  obtain ⟨K, hK, hbonus⟩ := seamOK_of_record fmt mL mR M ne blob hf h
  refine ⟨K, hK, hbonus, ?_⟩
  rcases (by omega : fmt = 0 ∨ fmt = 1 ∨ fmt = 2 ∨ fmt = 3) with rfl | rfl | rfl | rfl
  · obtain ⟨-, -, h32, -, -, hLU, -, -, -, -, -, -, -, hs108, hs972, -⟩ :=
      checkRecord_zero_spec mL mR M ne blob h
    have h32' : ((colours mL mR M).map Prod.fst).length ≤ 32 := by
      rw [List.length_map]; exact h32
    refine ⟨h32, fun _ => ⟨?_, ?_⟩⟩
    · exact lawR_sum_one _ _ h32' hLU hs108
    · exact lawR_sq_le _ _ h32' hLU hs972
  · obtain ⟨-, -, h32, -, -, -, -, -, -, -, -, -, -, hnU, -⟩ :=
      checkRecord_one_spec mL mR M ne blob h
    have h32' : ((colours mL mR M).map Prod.fst).length ≤ 32 := by
      rw [List.length_map]; exact h32
    refine ⟨h32, fun hLU => ?_⟩
    obtain ⟨hs108, hs972, -, -⟩ := hnU hLU
    exact ⟨lawR_sum_one _ _ h32' hLU hs108, lawR_sq_le _ _ h32' hLU hs972⟩
  · obtain ⟨-, -, h32, -, -, hLU, -, -, -, -, -, -, -, hs108, hs972, -⟩ :=
      checkRecord_two_spec mL mR M ne blob h
    have h32' : ((colours mL mR M).map Prod.fst).length ≤ 32 := by
      rw [List.length_map]; exact h32
    refine ⟨h32, fun _ => ⟨?_, ?_⟩⟩
    · exact lawR_sum_one _ _ h32' hLU hs108
    · exact lawR_sq_le _ _ h32' hLU hs972
  · obtain ⟨-, -, h32, -, -, -, -, -, -, -, -, -, -, hnU, -⟩ :=
      checkRecord_three_spec mL mR M ne blob h
    have h32' : ((colours mL mR M).map Prod.fst).length ≤ 32 := by
      rw [List.length_map]; exact h32
    refine ⟨h32, fun hLU => ?_⟩
    obtain ⟨hs108, hs972, -, -⟩ := hnU hLU
    exact ⟨lawR_sum_one _ _ h32' hLU hs108, lawR_sq_le _ _ h32' hLU hs972⟩

/-- **The seam package.** Every valid maximal key is the symbolic `U → U` seam or carries a
kernel-checked seam package with the root facts. -/
theorem seam_package (mL mR M : Nat) (hLb : mL < 16384) (hRb : mR < 16384)
    (hL : validType mL = true) (hR : validType mR = true) (hM : M < 16384 ^ 7)
    (hv : validKey mL mR M = true) (hmax : keyMax mL mR M = true) :
    (mL = UTYPE ∧ mR = UTYPE) ∨
      ∃ K, SeamOK mL ((colours mL mR M).map Prod.fst) mR ((colours mL mR M).map Prod.snd) K
        ∧ ((mL == UTYPE) = true →
          18 / 17 * rhoR * ∑ c, ∑ s, lawR mL ((colours mL mR M).map Prod.fst) c * K c s ^ 2 < 1)
        ∧ (colours mL mR M).length ≤ 32
        ∧ ((mL == UTYPE) = false →
          ∑ c, lawR mL ((colours mL mR M).map Prod.fst) c = 1
          ∧ ∑ c, lawR mL ((colours mL mR M).map Prod.fst) c ^ 2 ≤ 1 / 12) := by
  rcases cert_complete mL mR M hLb hRb hL hR hM hv hmax with h | ⟨fmt, ne, blob, hf, h⟩
  · exact Or.inl h
  · exact Or.inr (seam_package_of_record fmt mL mR M ne blob hf h)

end Grid3.Three.Cert
