import Mathlib

/-!
# The exact telescoping identity — the k≥3 ECC proof skeleton.

`∏_{j<n} A_j − B^n = ∑_{j<n} (∏_{i<j} A_i)·(A_j − B)·B^{n-1-j}` in any ring.  Applied to grid
column-transfers (`A_j` the j-th seam, `B` the uniform transfer), sandwiched between the initial
and terminal vectors, this is `P(L) − u_n = ∑_j N_j·(M_j − H)·F_{n-1-j}` — the identity behind
every height/k proof, and the honest frame for the open k=3 cancellation.
-/

namespace Grid3.Three.Telescope
open Finset
variable {R : Type*} [Ring R]

/-- Prefix product `A_0 · A_1 ⋯ A_{m-1}`. -/
def pfx (A : ℕ → R) : ℕ → R
  | 0 => 1
  | (m + 1) => pfx A m * A m

/-- **The telescoping identity.** -/
theorem telescope (A : ℕ → R) (B : R) (n : ℕ) :
    pfx A n - B ^ n = ∑ j ∈ Finset.range n, pfx A j * (A j - B) * B ^ (n - 1 - j) := by
  induction n with
  | zero => simp [pfx]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have key : pfx A (n + 1) - B ^ (n + 1)
          = (pfx A n - B ^ n) * B + pfx A n * (A n - B) := by
        have h1 : pfx A (n + 1) = pfx A n * A n := rfl
        rw [h1, pow_succ]; noncomm_ring
      rw [key, ih, Finset.sum_mul]
      congr 1
      · refine Finset.sum_congr rfl (fun j hj => ?_)
        rw [Finset.mem_range] at hj
        rw [mul_assoc, ← pow_succ, show n - 1 - j + 1 = n + 1 - 1 - j from by omega]
      · rw [show n + 1 - 1 - n = 0 from by omega, pow_zero, mul_one]

end Grid3.Three.Telescope
