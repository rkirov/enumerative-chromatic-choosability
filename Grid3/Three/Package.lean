import Grid3.Three.Cert.Complete
import Grid3.Three.Sig

/-!
# The seam package with its root facts

`SeamPkg mL mR M` is `SeamOK` with the facts the assembly needs beyond it: the canonical colour
list has at most `32` slots (so states pack into `Fin SB`), and for a nonuniform left column the
canonical law has total mass one and collision mass at most `1/12` (from the record's
`Σ count = 108` and `Σ count² ≤ 972`, via `Sig.lean`). `seam_package_of_record` builds it from a
passing record; `seam_package` combines that with `cert_complete`: every valid maximal key is the
symbolic `U → U` seam, or has a package, or its row reflection has one.
-/

open Finset

namespace Grid3.Three.Cert

/-- the seam package of a key: a kernel-checked coupling with `SeamOK`, the strong bound when the
left column is uniform, the slot bound, and the root facts when it is not -/
def SeamPkg (mL mR M : Nat) : Prop :=
  ∃ K, SeamOK mL ((colours mL mR M).map Prod.fst) mR ((colours mL mR M).map Prod.snd) K
    ∧ ((mL == UTYPE) = true →
        18 / 17 * rhoR * ∑ c, ∑ s, lawR mL ((colours mL mR M).map Prod.fst) c * K c s ^ 2 < 1)
    ∧ (colours mL mR M).length ≤ 32
    ∧ ((mL == UTYPE) = false →
        ∑ c, lawR mL ((colours mL mR M).map Prod.fst) c = 1
        ∧ ∑ c, lawR mL ((colours mL mR M).map Prod.fst) c ^ 2 ≤ 1 / 12)

theorem seam_package_of_record (fmt mL mR M ne blob : Nat) (hf : fmt < 4)
    (h : checkRecord fmt mL mR M ne blob = true) : SeamPkg mL mR M := by
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

/-- **The seam package.** Every valid maximal key is the symbolic `U → U` seam, or carries a
kernel-checked seam package, or its row reflection does. -/
theorem seam_package (mL mR M : Nat) (hLb : mL < 16384) (hRb : mR < 16384)
    (hL : validType mL = true) (hR : validType mR = true) (hM : M < 16384 ^ 7)
    (hv : validKey mL mR M = true) (hmax : keyMax mL mR M = true) :
    (mL = UTYPE ∧ mR = UTYPE) ∨ SeamPkg mL mR M ∨ SeamPkg (rtype mL) (rtype mR) (rM M) := by
  rcases cert_complete mL mR M hLb hRb hL hR hM hv hmax with h | ⟨fmt, ne, blob, hf, h⟩ | ⟨fmt, ne, blob, hf, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl (seam_package_of_record fmt mL mR M ne blob hf h))
  · exact Or.inr (Or.inr (seam_package_of_record fmt _ _ _ ne blob hf h))

end Grid3.Three.Cert
