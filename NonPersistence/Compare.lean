/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import NonPersistence.Marginal
import NonPersistence.Arith

/-!
# Failure at `k + 1` (Zhang–Dong, Lemmas 9–11 and Proposition 12)

Both counts at `k + 1 = m + 4` collapse, through `sum_col_iterCone`, to a sum over the colorings
of `H m` of the apexes' contribution. The contribution depends only on how many colors `s₁` and
`s₂` use between them:

* they agree — `k⁴` per block of four apexes;
* they differ — at most `k²(k² - 1)` per block, by `prod_four_le`.

So each count is (number of agreeing base colorings) `· k^{4t}` plus a smaller term. The bad list
assignment is built so that **strictly fewer** base colorings can make `s₁` and `s₂` agree than
the constant list allows: `s₂`'s list omits `B₁`, and the explicit coloring `fwit` — everything in
the clique colored by its own index, both `sᵢ` colored `m + 3` — agrees at `s₁, s₂` from the full
palette but is not an `LH`-coloring at all.

One coloring of slack is all it takes. The `(k² - 1)/k²` deficit at the apexes drives the
remaining terms to nothing, so for `t` past an explicit threshold the bad assignment wins.
-/

open Finset SimpleGraph

namespace ZhangDong

/-! ### The two coloring sets of the base -/

/-- Colorings of `H m` from the bad lists. -/
def Sbad (m : ℕ) : Finset (Option (Option (XV m)) → ℕ) := (H m).colorings (LH m)

/-- Those giving `s₁` and `s₂` the same color. -/
def SbadA (m : ℕ) : Finset (Option (Option (XV m)) → ℕ) :=
  (Sbad m).filter (fun θ => θ (s₁ m) = θ (s₂ m))

/-- Colorings of `H m` from the full palette of `k + 1 = m + 4` colors. -/
def Tconst (m : ℕ) : Finset (Option (Option (XV m)) → ℕ) :=
  (H m).colorings (constList (Option (Option (XV m))) (m + 4))

/-- Those giving `s₁` and `s₂` the same color. -/
def TconstA (m : ℕ) : Finset (Option (Option (XV m)) → ℕ) :=
  (Tconst m).filter (fun f => f (s₁ m) = f (s₂ m))

/-- The three list values of `LH`, as definitional rewrites. -/
@[simp] theorem LH_s₁ (m : ℕ) : LH m (s₁ m) = Finset.range (m + 4) := rfl

@[simp] theorem LH_s₂ (m : ℕ) : LH m (s₂ m) = C m ∪ {m + 4, m + 5} := rfl

@[simp] theorem LH_xv (m : ℕ) (i : XV m) : LH m (xv m i) = Finset.range (m + 4) := rfl

theorem image_sPair (m : ℕ) (θ : Option (Option (XV m)) → ℕ) :
    (sPair m).image θ = {θ (s₁ m), θ (s₂ m)} := by
  rw [sPair, Finset.image_insert, Finset.image_singleton]

theorem mem_range_s₁ {m : ℕ} {θ : Option (Option (XV m)) → ℕ} (hθ : θ ∈ Sbad m) :
    θ (s₁ m) ∈ Finset.range (m + 4) := by
  have h := mem_list_of_mem_colorings hθ (s₁ m)
  rwa [LH_s₁] at h

theorem mem_union_s₂ {m : ℕ} {θ : Option (Option (XV m)) → ℕ} (hθ : θ ∈ Sbad m) :
    θ (s₂ m) ∈ C m ∪ {m + 4, m + 5} := by
  have h := mem_list_of_mem_colorings hθ (s₂ m)
  rwa [LH_s₂] at h

/-! ### The apex contribution -/

/-- If `s₁` and `s₂` agree under an `LH`-coloring, the common color is one of the shared colors:
it must lie in both `range (m + 4)` and `C ∪ B₂`. -/
theorem mem_C_of_agree {m : ℕ} {θ : Option (Option (XV m)) → ℕ} (hθ : θ ∈ Sbad m)
    (h : θ (s₁ m) = θ (s₂ m)) : θ (s₁ m) ∈ C m := by
  have h1 : θ (s₁ m) < m + 4 := Finset.mem_range.mp (mem_range_s₁ hθ)
  have h2 : θ (s₁ m) ∈ C m ∪ {m + 4, m + 5} := by rw [h]; exact mem_union_s₂ hθ
  rcases Finset.mem_union.mp h2 with hc | hb
  · exact hc
  · rw [Finset.mem_insert, Finset.mem_singleton] at hb
    omega

/-- Agreement: every apex list loses exactly the one common color, so a block of four offers
`k⁴`. -/
theorem prod_eq_of_agree {m : ℕ} {θ : Option (Option (XV m)) → ℕ} (hθ : θ ∈ Sbad m)
    (h : θ (s₁ m) = θ (s₂ m)) (t : ℕ) :
    ∏ i ∈ Finset.range (4 * t), (A m i \ (sPair m).image θ).card = (m + 3) ^ (4 * t) := by
  have himg : (sPair m).image θ = {θ (s₁ m)} := by
    rw [image_sPair, ← h]
    exact Finset.insert_eq_self.mpr (Finset.mem_singleton_self _)
  have hstep : ∀ i ∈ Finset.range (4 * t), (A m i \ (sPair m).image θ).card = m + 3 := by
    intro i _
    rw [himg]
    exact card_A_sdiff_single m i (mem_C_of_agree hθ h)
  rw [Finset.prod_congr rfl hstep, Finset.prod_const, Finset.card_range]

/-- Disagreement: at most `k²(k² - 1)` per block, by `prod_four_le`. -/
theorem prod_le_of_disagree {m : ℕ} {θ : Option (Option (XV m)) → ℕ} (hθ : θ ∈ Sbad m)
    (h : θ (s₁ m) ≠ θ (s₂ m)) (t : ℕ) :
    ∏ i ∈ Finset.range (4 * t), (A m i \ (sPair m).image θ).card
      ≤ ((m + 3) ^ 2 * ((m + 2) * (m + 4))) ^ t := by
  have hstep : ∀ i ∈ Finset.range (4 * t), (A m i \ (sPair m).image θ).card
      = (fun j => ((C m ∪ D m j) \ {θ (s₁ m), θ (s₂ m)}).card) (i % 4) := by
    intro i _
    rw [image_sPair]
    rfl
  rw [Finset.prod_congr rfl hstep]
  refine le_trans (le_of_eq (prod_range_four_mul
    (fun j => ((C m ∪ D m j) \ {θ (s₁ m), θ (s₂ m)}).card) t)) ?_
  exact Nat.pow_le_pow_left (prod_four_le m h (mem_range_s₁ hθ) (mem_union_s₂ hθ)) t

/-- The same computation from the full palette: agreement again gives `k⁴` per block. -/
theorem prod_eq_of_agree_const {m : ℕ} {f : Option (Option (XV m)) → ℕ} (hf : f ∈ Tconst m)
    (h : f (s₁ m) = f (s₂ m)) (t : ℕ) :
    ∏ _i ∈ Finset.range (4 * t), (Finset.range (m + 4) \ (sPair m).image f).card
      = (m + 3) ^ (4 * t) := by
  have hmem : f (s₁ m) ∈ Finset.range (m + 4) := by
    have := mem_list_of_mem_colorings hf (s₁ m)
    rwa [show constList (Option (Option (XV m))) (m + 4) (s₁ m) = Finset.range (m + 4) from rfl]
      at this
  have himg : (sPair m).image f = {f (s₁ m)} := by
    rw [image_sPair, ← h]
    exact Finset.insert_eq_self.mpr (Finset.mem_singleton_self _)
  have hval : (Finset.range (m + 4) \ (sPair m).image f).card = m + 3 := by
    rw [himg, card_sdiff_singleton_of_mem _ hmem, Finset.card_range]
    omega
  rw [hval, Finset.prod_const, Finset.card_range]

/-! ### One coloring of slack -/

/-- The witness: every clique vertex takes its own index as color, and both `s₁` and `s₂` take
`m + 3`. It is a proper coloring from the full palette agreeing at `s₁, s₂`, and it is not an
`LH`-coloring, because `m + 3` is not on `s₂`'s list. -/
def fwit (m : ℕ) : Option (Option (XV m)) → ℕ
  | none => m + 3
  | some none => m + 3
  | some (some i) => i.val

theorem fwit_mem_Tconst (m : ℕ) : fwit m ∈ Tconst m := by
  rw [Tconst, mem_colorings]
  refine ⟨fun v => ?_, ?_⟩
  · rcases v with _ | _ | i
    · show (m + 3) ∈ Finset.range (m + 4)
      simp
    · show (m + 3) ∈ Finset.range (m + 4)
      simp
    · show (i : ℕ) ∈ Finset.range (m + 4)
      have : (i : ℕ) < m + 3 := i.isLt
      simp only [Finset.mem_range]
      omega
  · rintro (_ | _ | i) (_ | _ | j) hadj
    · exact absurd rfl hadj.ne
    · exact absurd hadj.symm (H_not_adj_s₁_s₂ m)
    · have hj : (j : ℕ) < m + 3 := j.isLt
      show (m + 3) ≠ (j : ℕ)
      omega
    · exact absurd hadj (H_not_adj_s₁_s₂ m)
    · exact absurd rfl hadj.ne
    · have hj : (j : ℕ) < m + 3 := j.isLt
      show (m + 3) ≠ (j : ℕ)
      omega
    · have hi : (i : ℕ) < m + 3 := i.isLt
      show (i : ℕ) ≠ (m + 3)
      omega
    · have hi : (i : ℕ) < m + 3 := i.isLt
      show (i : ℕ) ≠ (m + 3)
      omega
    · have hij : i ≠ j := (H_adj_xv m i j).mp hadj
      show (i : ℕ) ≠ (j : ℕ)
      exact fun hcon => hij (Fin.ext hcon)

theorem fwit_agree (m : ℕ) : fwit m (s₁ m) = fwit m (s₂ m) := rfl

theorem fwit_notMem_Sbad (m : ℕ) : fwit m ∉ Sbad m := by
  intro hcon
  have h2 : fwit m (s₂ m) ∈ LH m (s₂ m) := mem_list_of_mem_colorings hcon _
  simp only [LH, s₂, fwit, C, Finset.mem_union, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton] at h2
  omega

/-- Every agreeing `LH`-coloring is an agreeing full-palette coloring: the only list that is not
already `range (m + 4)` is `s₂`'s, and there the color is copied from `s₁`. -/
theorem SbadA_subset_TconstA (m : ℕ) : SbadA m ⊆ TconstA m := by
  intro θ hθ
  rw [SbadA, Finset.mem_filter] at hθ
  obtain ⟨hθS, hθa⟩ := hθ
  rw [TconstA, Finset.mem_filter]
  refine ⟨?_, hθa⟩
  rw [Tconst, mem_colorings]
  have hproper : (H m).IsProperColoring θ := isProperColoring_of_mem_colorings hθS
  refine ⟨fun v => ?_, hproper⟩
  have hs₁ : θ (s₁ m) ∈ Finset.range (m + 4) := mem_list_of_mem_colorings hθS (s₁ m)
  rcases v with _ | _ | i
  · show θ (s₂ m) ∈ Finset.range (m + 4)
    rw [← hθa]
    exact hs₁
  · exact hs₁
  · show θ (xv m i) ∈ Finset.range (m + 4)
    have h := mem_list_of_mem_colorings hθS (xv m i)
    rwa [LH_xv] at h

/-- **The strict inclusion**: `fwit` is agreeing from the full palette but not an `LH`-coloring. -/
theorem SbadA_ssubset_TconstA (m : ℕ) : SbadA m ⊂ TconstA m := by
  refine (Finset.ssubset_iff_of_subset (SbadA_subset_TconstA m)).mpr ⟨fwit m, ?_, ?_⟩
  · rw [TconstA, Finset.mem_filter]
    exact ⟨fwit_mem_Tconst m, fwit_agree m⟩
  · intro hcon
    rw [SbadA, Finset.mem_filter] at hcon
    exact fwit_notMem_Sbad m hcon.1

theorem card_SbadA_lt (m : ℕ) : (SbadA m).card < (TconstA m).card :=
  Finset.card_lt_card (SbadA_ssubset_TconstA m)

end ZhangDong
