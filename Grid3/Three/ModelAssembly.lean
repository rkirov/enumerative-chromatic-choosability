import Grid3.Three.CertifiedEntropy
import Grid3.Three.Model

/-!
# The entropy bound for actual finite-colour grid states

This closes the Markov-support/cardinality part of the height-three model. The remaining
inputs are column laws and seam kernels on actual colours, with their local support and
entropy properties. In particular, no separate global path-to-colouring hypothesis is needed.

The count here is `Model.properC`; identification with the repository's `pathG` product
colouring count and construction of the actual-colour seam packages remain downstream.
-/

namespace Grid3.Three.Model

open Finset Real

variable {S : Type*} [Fintype S]

/-- Every column in a positive-mass path has positive mass under its prescribed column law. -/
theorem mu_pos_column_law (law : ℕ → S → ℝ) (K : ℕ → S → S → ℝ)
    (hL : ∀ k s, 0 ≤ law k s) (hK : ∀ k c s, 0 ≤ K k c s)
    (n : ℕ)
    (hstep : ∀ k, k < n → ∀ s, ∑ c, law k c * K k c s = law (k + 1) s)
    (p : PState S n) (hp : 0 < mu (law 0) K n p) :
    ∀ j : Fin (n + 1), 0 < law j (colAt n p j) := by
  obtain ⟨h0, htrace⟩ := mu_pos_trace (law 0) K (hL 0) hK n p hp
  intro j
  induction j using Fin.induction with
  | zero => exact h0
  | succ i ih =>
    have hterm := mul_pos ih (htrace i)
    have hle : law i.val (colAt n p i.castSucc) * K i.val (colAt n p i.castSucc)
        (colAt n p i.succ) ≤ ∑ c, law i.val c * K i.val c (colAt n p i.succ) :=
      Finset.single_le_sum (fun c _ => mul_nonneg (hL i.val c) (hK i.val c _))
        (Finset.mem_univ _)
    rw [hstep i.val i.isLt] at hle
    exact lt_of_lt_of_le hterm hle

variable {C : ℕ}

/-- Local law/kernel support alone guarantees a proper colouring for every positive path. -/
theorem positive_path_mem (n : ℕ) (L : Vtx (n + 1) → Finset ℕ)
    (law : ℕ → (Fin 3 → Fin C) → ℝ)
    (K : ℕ → (Fin 3 → Fin C) → (Fin 3 → Fin C) → ℝ)
    (hL : ∀ k s, 0 ≤ law k s) (hK : ∀ k c s, 0 ≤ K k c s)
    (hstep : ∀ k, k < n → ∀ s, ∑ c, law k c * K k c s = law (k + 1) s)
    (hval : ∀ (j : Fin (n + 1)) s, 0 < law j s → ∀ i, (s i).val ∈ L (i, j))
    (hvert : ∀ (j : Fin (n + 1)) s, 0 < law j s →
      ∀ i i', i.val + 1 = i'.val → s i ≠ s i')
    (hcompat : ∀ k, k < n → ∀ c s, 0 < law k c → 0 < K k c s → ∀ i, c i ≠ s i)
    (p : PState (Fin 3 → Fin C) n) (hp : 0 < mu (law 0) K n p) :
    toColouring n p ∈ properC (gridAdj (n + 1)) L := by
  have hcols := mu_pos_column_law law K hL hK n hstep p hp
  have htrace := (mu_pos_trace (law 0) K (hL 0) hK n p hp).2
  apply toColouring_mem_properC n L p
  · intro j i; exact hval j _ (hcols j) i
  · intro j i i' hii'; exact hvert j _ (hcols j) i i' hii'
  · intro i j j' hj
    let q : Fin n := ⟨j.val, by have := j'.isLt; omega⟩
    have hq : q.castSucc = j := Fin.ext rfl
    have hq' : q.succ = j' := Fin.ext hj
    have h := hcompat q.val q.isLt _ _ (hcols q.castSucc) (htrace q) i
    rwa [hq, hq'] at h

/-- The path support fits inside the actual proper-colouring set. The two staging files'
recursive path and mass definitions are definitionally equal; no axiomatic bridge is used. -/
theorem support_card_le_properC (n : ℕ) (L : Vtx (n + 1) → Finset ℕ)
    (law : ℕ → (Fin 3 → Fin C) → ℝ)
    (K : ℕ → (Fin 3 → Fin C) → (Fin 3 → Fin C) → ℝ)
    (hL : ∀ k s, 0 ≤ law k s) (hK : ∀ k c s, 0 ≤ K k c s)
    (hstep : ∀ k, k < n → ∀ s, ∑ c, law k c * K k c s = law (k + 1) s)
    (hval : ∀ (j : Fin (n + 1)) s, 0 < law j s → ∀ i, (s i).val ∈ L (i, j))
    (hvert : ∀ (j : Fin (n + 1)) s, 0 < law j s →
      ∀ i i', i.val + 1 = i'.val → s i ≠ s i')
    (hcompat : ∀ k, k < n → ∀ c s, 0 < law k c → 0 < K k c s → ∀ i, c i ≠ s i) :
    (Finset.univ.filter (fun p : Grid3.Three.PState (Fin 3 → Fin C) n =>
      0 < Grid3.Three.mu (law 0) K n p)).card ≤ (properC (gridAdj (n + 1)) L).card := by
  exact hcard_from_inj (law 0) K (n + 1) (properC (gridAdj (n + 1)) L)
    (toColouring n) (positive_path_mem n L law K hL hK hstep hval hvert hcompat)
    (fun p q _ _ hpq => toColouring_injective n hpq)

end Grid3.Three.Model
