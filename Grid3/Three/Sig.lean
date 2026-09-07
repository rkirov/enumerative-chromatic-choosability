import Grid3.Three.Cert.Bridge

/-!
# The canonical law depends only on the state's signature

`lawR m pats c` (the bridge's real law of a canonical column) is `lawSig m (sigOf pats c)` on the
states `stsOf pats` and `0` elsewhere. The signature `sigOf` records the three colours' patterns
and whether the top and bottom colours agree, so any pattern-preserving injective relabelling of
the colours transports the law exactly: this is what lets one column carry the same law in the
seam to its left and the seam to its right.

Also here: the membership characterization of `stsOf`, the reduction of a sum over `Fin SB` to
the list `stsOf pats`, and the two root facts for a nonuniform column (total mass one, collision
mass at most `1/12`) from the integer facts of the record specs.
-/

open Finset

namespace Grid3.Three.Cert

/-! ### States -/

theorem mem_rowList (pats : List Nat) (r i : Nat) :
    i ∈ rowList pats r ↔ i < pats.length ∧ (pats.getD i 0).testBit r = true := by
  unfold rowList; simp [List.mem_filter, List.mem_range]

theorem mem_stsOf (pats : List Nat) (st : Nat) :
    st ∈ stsOf pats ↔ ∃ i0 ∈ rowList pats 0, ∃ i1 ∈ rowList pats 1, i1 ≠ i0 ∧
      ∃ i2 ∈ rowList pats 2, i2 ≠ i1 ∧ st = i0 * 1024 + i1 * 32 + i2 := by
  unfold stsOf; exact mem_states _ _ _ st

theorem stsOf_lt (pats : List Nat) (h32 : pats.length ≤ 32) :
    ∀ st ∈ stsOf pats, st < SB := by
  intro st hst
  obtain ⟨i0, h0, i1, h1, -, i2, h2, -, rfl⟩ := (mem_stsOf pats st).1 hst
  rw [mem_rowList] at h0 h1 h2
  show i0 * 1024 + i1 * 32 + i2 < 32768
  omega

/-- the three labels of a packed state -/
theorem stsOf_digits (pats : List Nat) (h32 : pats.length ≤ 32) (st : Nat)
    (hst : st ∈ stsOf pats) :
    st / 1024 ∈ rowList pats 0 ∧ st / 32 % 32 ∈ rowList pats 1 ∧ st % 32 ∈ rowList pats 2
      ∧ st / 1024 ≠ st / 32 % 32 ∧ st / 32 % 32 ≠ st % 32 := by
  obtain ⟨i0, h0, i1, h1, h10, i2, h2, h21, rfl⟩ := (mem_stsOf pats st).1 hst
  have l0 := ((mem_rowList pats 0 i0).1 h0).1
  have l1 := ((mem_rowList pats 1 i1).1 h1).1
  have l2 := ((mem_rowList pats 2 i2).1 h2).1
  have e0 : (i0 * 1024 + i1 * 32 + i2) / 1024 = i0 := by omega
  have e1 : (i0 * 1024 + i1 * 32 + i2) / 32 % 32 = i1 := by omega
  have e2 : (i0 * 1024 + i1 * 32 + i2) % 32 = i2 := by omega
  rw [e0, e1, e2]
  exact ⟨h0, h1, h2, fun h => h10 h.symm, fun h => h21 h.symm⟩

/-- conversely, three labels of the right rows pack to a state -/
theorem mem_stsOf_of_labels (pats : List Nat) (i0 i1 i2 : Nat)
    (h0 : i0 ∈ rowList pats 0) (h1 : i1 ∈ rowList pats 1) (h2 : i2 ∈ rowList pats 2)
    (h10 : i0 ≠ i1) (h21 : i1 ≠ i2) : i0 * 1024 + i1 * 32 + i2 ∈ stsOf pats :=
  (mem_stsOf pats _).2 ⟨i0, h0, i1, h1, fun h => h10 h.symm, i2, h2, fun h => h21 h.symm, rfl⟩

/-- a function vanishing off the canonical states sums over the state list -/
theorem sum_stsOf (pats : List Nat) (h32 : pats.length ≤ 32) (g : Fin SB → ℝ)
    (h0 : ∀ c : Fin SB, c.val ∉ stsOf pats → g c = 0) :
    ∑ c, g c = ((stsOf pats).map (fun st => g (toFin st))).sum := by
  have hnd : ((stsOf pats).map toFin).Nodup := by
    refine (stsOf_nodup pats h32).map_on ?_
    intro x hx y hy hxy
    have := congrArg Fin.val hxy
    rwa [toFin_val x (stsOf_lt pats h32 x hx), toFin_val y (stsOf_lt pats h32 y hy)] at this
  rw [show ((stsOf pats).map fun st => g (toFin st)) = ((stsOf pats).map toFin).map g by
    rw [List.map_map]; rfl, ← List.sum_toFinset _ hnd]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro c _ hc
  apply h0
  intro hmem
  apply hc
  rw [List.mem_toFinset, List.mem_map]
  exact ⟨c.val, hmem, Fin.ext (toFin_val _ c.isLt)⟩

/-! ### The law by signature -/

/-- the real law of a column type at a signature -/
noncomputable def lawSig (m sig : Nat) : ℝ :=
  if m == UTYPE then
    9000 / 108000 + (if sig % 2 = 1 then (1000 : ℝ) else -1000) / 204000 * s17
  else (((1000 * ((subTable (typeIndex m) / 100 ^ sig) % 100) : ℕ) : ℝ)) / 108000

theorem sigOf_mod_two (pats : List Nat) (st : Nat) :
    sigOf pats st % 2 = if isABA st then 1 else 0 := by
  dsimp only [sigOf]; split_ifs <;> omega

theorem lawR_eq_lawSig (m : Nat) (pats : List Nat) (c : Fin SB) :
    lawR m pats c = if c.val ∈ stsOf pats then lawSig m (sigOf pats c.val) else 0 := by
  unfold lawR lawSig lawE0 lawE1 cntOf countOf
  by_cases hc : c.val ∈ stsOf pats
  · rw [if_pos hc, if_pos hc]
    by_cases hU : (m == UTYPE) = true
    · rw [if_pos hU, if_pos hU, if_pos hU, sigOf_mod_two]
      by_cases ha : isABA c.val = true
      · rw [if_pos ha, if_pos ha]; push_cast; ring
      · rw [if_neg ha, if_neg ha]; push_cast; ring
    · rw [if_neg hU, if_neg hU, if_neg hU]; push_cast; ring
  · rw [if_neg hc, if_neg hc]

theorem lawSig_nonneg (m sig : Nat) : 0 ≤ lawSig m sig := by
  unfold lawSig
  have h17 : s17 < 5 := by have := s17_sq; have := s17_pos; nlinarith
  have h0 := s17_pos
  split_ifs
  · linarith
  · nlinarith
  · positivity

/-- on a nonuniform column the law is the count over `108` -/
theorem lawR_nonU (m : Nat) (pats : List Nat) (hU : (m == UTYPE) = false) (st : Nat)
    (hst : st ∈ stsOf pats) (hlt : st < SB) :
    lawR m pats (toFin st) = (cntOf m pats st : ℝ) / 108 := by
  unfold lawR lawE0 lawE1
  rw [toFin_val st hlt, if_pos hst, hU]
  simp only [Bool.false_eq_true, if_false]
  push_cast; ring

theorem sumNat_eq (l : List Nat) : sumNat l = l.sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [sumNat, ih]

theorem sum_lawR_list (m : Nat) (pats : List Nat) (hU : (m == UTYPE) = false)
    (h32 : pats.length ≤ 32) :
    ∀ l : List Nat, (∀ st ∈ l, st ∈ stsOf pats) →
      (l.map fun st => lawR m pats (toFin st)).sum = ((l.map (cntOf m pats)).sum : ℝ) / 108
  | [], _ => by simp
  | st :: l, h => by
    have hst : st ∈ stsOf pats := h st (by simp)
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
      sum_lawR_list m pats hU h32 l (fun x hx => h x (by simp [hx])),
      lawR_nonU m pats hU st hst (stsOf_lt pats h32 st hst)]
    push_cast; ring

theorem sum_lawR_sq_list (m : Nat) (pats : List Nat) (hU : (m == UTYPE) = false)
    (h32 : pats.length ≤ 32) :
    ∀ l : List Nat, (∀ st ∈ l, st ∈ stsOf pats) →
      (l.map fun st => lawR m pats (toFin st) ^ 2).sum
        = ((((l.map (cntOf m pats)).map fun k => k * k).sum : ℕ) : ℝ) / 11664
  | [], _ => by simp
  | st :: l, h => by
    have hst : st ∈ stsOf pats := h st (by simp)
    rw [List.map_cons, List.sum_cons, List.map_cons, List.map_cons, List.sum_cons,
      sum_lawR_sq_list m pats hU h32 l (fun x hx => h x (by simp [hx])),
      lawR_nonU m pats hU st hst (stsOf_lt pats h32 st hst)]
    push_cast; ring

/-- **Total mass one** for a nonuniform column, from the record's `Σ count = 108`. -/
theorem lawR_sum_one (m : Nat) (pats : List Nat) (h32 : pats.length ≤ 32)
    (hU : (m == UTYPE) = false) (h108 : sumNat ((stsOf pats).map (cntOf m pats)) = 108) :
    ∑ c, lawR m pats c = 1 := by
  rw [sum_stsOf pats h32 _ (fun c hc => by rw [lawR_eq_lawSig, if_neg hc]),
    sum_lawR_list m pats hU h32 _ (fun st hst => hst), ← sumNat_eq, h108]
  norm_num

/-- **Collision mass at most `1/12`** for a nonuniform column, from `Σ count² ≤ 972`. -/
theorem lawR_sq_le (m : Nat) (pats : List Nat) (h32 : pats.length ≤ 32)
    (hU : (m == UTYPE) = false)
    (h972 : sumNat (((stsOf pats).map (cntOf m pats)).map fun k => k * k) ≤ 972) :
    ∑ c, lawR m pats c ^ 2 ≤ 1 / 12 := by
  rw [sum_stsOf pats h32 (fun c => lawR m pats c ^ 2)
      (fun c hc => by rw [lawR_eq_lawSig, if_neg hc]; ring),
    sum_lawR_sq_list m pats hU h32 _ (fun st hst => hst)]
  rw [sumNat_eq] at h972
  have : (((((stsOf pats).map (cntOf m pats)).map fun k => k * k).sum : ℕ) : ℝ) ≤ 972 := by
    exact_mod_cast h972
  linarith

end Grid3.Three.Cert
