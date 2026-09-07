import Grid3.Three.Cert.Bridge
import Grid3.Three.Cert.Keys.All

/-!
# Every valid maximal seam key carries a seam package

`seamOK_of_key` joins the certificate completeness `cert_complete` (`Keys/All.lean`: every valid
maximal key is the symbolic `U → U` seam or has a passing record) with the four real-number
bridges of `Bridge.lean`: a concrete seam whose canonical key is valid and maximal either is the
`U → U` seam (handled symbolically downstream) or has a kernel-checked coupling `K` with the
`SeamOK` package at the canonical states of `colours mL mR M`.
-/

namespace Grid3.Three.Cert

/-- a passing record of any format yields a seam package, with the strong `(18/17)·ρ` collision
bound when the left column is uniform (only format `1` records have a uniform left column) -/
theorem seamOK_of_record (fmt mL mR M ne blob : Nat) (hf : fmt < 4)
    (h : checkRecord fmt mL mR M ne blob = true) :
    ∃ K, SeamOK mL ((colours mL mR M).map Prod.fst) mR ((colours mL mR M).map Prod.snd) K
      ∧ ((mL == UTYPE) = true →
          18 / 17 * rhoR * ∑ c, ∑ s, lawR mL ((colours mL mR M).map Prod.fst) c * K c s ^ 2 < 1) := by
  rcases (by omega : fmt = 0 ∨ fmt = 1 ∨ fmt = 2 ∨ fmt = 3) with rfl | rfl | rfl | rfl
  · obtain ⟨K, hK⟩ := bridge_zero mL mR M ne blob h
    obtain ⟨-, -, -, -, -, hLU, -⟩ := checkRecord_zero_spec mL mR M ne blob h
    exact ⟨K, hK, fun hU => by rw [hU] at hLU; exact absurd hLU (by decide)⟩
  · exact bridge_one mL mR M ne blob h
  · obtain ⟨K, hK⟩ := bridge_two mL mR M ne blob h
    obtain ⟨-, -, -, -, -, hLU, -⟩ := checkRecord_two_spec mL mR M ne blob h
    exact ⟨K, hK, fun hU => by rw [hU] at hLU; exact absurd hLU (by decide)⟩
  · obtain ⟨K, hK⟩ := bridge_three mL mR M ne blob h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hLU, -, -⟩ :=
      checkRecord_three_spec mL mR M ne blob h
    exact ⟨K, hK, fun hU => by rw [hU] at hLU; exact absurd hLU (by decide)⟩

/-- **Certificate completeness**: every valid maximal seam key is the symbolic `U → U` seam or
carries a kernel-checked seam package (with the strong bound when the left column is uniform). -/
theorem seamOK_of_key (mL mR M : Nat) (hLb : mL < 16384) (hRb : mR < 16384)
    (hL : validType mL = true) (hR : validType mR = true) (hM : M < 16384 ^ 7)
    (hv : validKey mL mR M = true) (hmax : keyMax mL mR M = true) :
    (mL = UTYPE ∧ mR = UTYPE) ∨
      ∃ K, SeamOK mL ((colours mL mR M).map Prod.fst) mR ((colours mL mR M).map Prod.snd) K
        ∧ ((mL == UTYPE) = true →
          18 / 17 * rhoR * ∑ c, ∑ s, lawR mL ((colours mL mR M).map Prod.fst) c * K c s ^ 2 < 1) := by
  rcases cert_complete mL mR M hLb hRb hL hR hM hv hmax with h | ⟨fmt, ne, blob, hf, h⟩
  · exact Or.inl h
  · exact Or.inr (seamOK_of_record fmt mL mR M ne blob hf h)

end Grid3.Three.Cert

