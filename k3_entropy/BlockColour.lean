import Mathlib
open Finset
namespace Grid3.Three.BlockColour

-- === Sec2 type + block layer ===
def patHasRow (p : Fin 7) (i : Fin 3) : Bool := Nat.testBit (p.val + 1) i.val
def blockList (m : Fin 7 → Fin 4) : List (Fin 7) :=
  (List.finRange 7).flatMap (fun p => List.replicate (m p) p)
def numBlocks (m : Fin 7 → Fin 4) : ℕ := (blockList m).length
def blockPat (m : Fin 7 → Fin 4) (j : Fin (numBlocks m)) : Fin 7 := (blockList m)[j]

theorem count_eq_fiber {α : Type*} [DecidableEq α] (l : List α) (a : α) :
    (Finset.univ.filter (fun i : Fin l.length => l[i] = a)).card = l.count a := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [Finset.card_filter]
      show (∑ i : Fin (xs.length + 1), if (x :: xs)[i] = a then 1 else 0) = (x :: xs).count a
      rw [Fin.sum_univ_succ]
      show (if x = a then 1 else 0) + (∑ i : Fin xs.length, if xs[i] = a then 1 else 0)
        = (x :: xs).count a
      rw [← Finset.card_filter, ih, List.count_cons]
      simp only [beq_iff_eq]
      by_cases h : x = a <;> simp [h] <;> omega

theorem count_blockList (m : Fin 7 → Fin 4) (q : Fin 7) : (blockList m).count q = m q := by
  fin_cases q <;>
    simp [blockList, List.finRange, List.flatMap, List.count_append, List.count_replicate]

theorem block_fiber (m : Fin 7 → Fin 4) (q : Fin 7) :
    Fintype.card {b : Fin (numBlocks m) // blockPat m b = q} = m q := by
  rw [Fintype.card_subtype]
  show (Finset.univ.filter (fun b : Fin (blockList m).length => (blockList m)[b] = q)).card = m q
  rw [count_eq_fiber]; exact count_blockList m q

-- === Bridge colour layer + subset ===
variable (L : Fin 3 → Finset ℕ)
def colColors : Finset ℕ := L 0 ∪ L 1 ∪ L 2
def pat (c : ℕ) : Finset (Fin 3) := Finset.univ.filter (fun i => c ∈ L i)
def mS (S : Finset (Fin 3)) : ℕ := ((colColors L).filter (fun c => pat L c = S)).card
def subset (p : Fin 7) : Finset (Fin 3) := Finset.univ.filter (fun i => patHasRow p i)

theorem colour_fiber (q : Fin 7) :
    Fintype.card {c : {x // x ∈ colColors L} // pat L c.val = subset q} = mS L (subset q) := by
  classical
  rw [Fintype.card_subtype, mS, Finset.univ_eq_attach]
  rw [Finset.filter_attach' (colColors L) (fun c => pat L c = subset q),
      Finset.card_map, Finset.card_attach]
  congr 1
  refine Finset.filter_congr (fun x hx => ?_)
  simp only [eq_iff_iff]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hx, h⟩⟩
def colType (p : Fin 7) : ℕ := mS L (subset p)

theorem subset_inj : Function.Injective subset := by decide

theorem subset_range (S : Finset (Fin 3)) (hS : S.Nonempty) : ∃ p, subset p = S := by
  revert hS; revert S; decide

/-- Colour → its pattern index (Fin 7). -/
noncomputable def patIdx (c : {x // x ∈ colColors L}) : Fin 7 :=
  Function.invFun subset (pat L c.val)

theorem pat_nonempty (c : {x // x ∈ colColors L}) : (pat L c.val).Nonempty := by
  have hc := c.property
  simp only [colColors, Finset.mem_union] at hc
  rcases hc with (h | h) | h
  · exact ⟨0, by simp [pat, h]⟩
  · exact ⟨1, by simp [pat, h]⟩
  · exact ⟨2, by simp [pat, h]⟩

theorem patIdx_section (c : {x // x ∈ colColors L}) : subset (patIdx L c) = pat L c.val := by
  obtain ⟨p, hp⟩ := subset_range (pat L c.val) (pat_nonempty L c)
  unfold patIdx
  exact Function.invFun_eq ⟨p, hp⟩

theorem colour_fiber' (q : Fin 7) :
    Fintype.card {c : {x // x ∈ colColors L} // patIdx L c = q} = mS L (subset q) := by
  rw [← colour_fiber L q]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro c
  constructor
  · intro h; rw [← patIdx_section L c, h]
  · intro h; exact subset_inj ((patIdx_section L c).trans h)

/-- **Pattern-respecting block↔colour bijection** (for any `m` with `m q = mS(subset q)`). -/
noncomputable def blockColourEquiv (m : Fin 7 → Fin 4)
    (hm : ∀ q, (m q : ℕ) = mS L (subset q)) :
    Fin (numBlocks m) ≃ {c : ℕ // c ∈ colColors L} :=
  (Equiv.sigmaFiberEquiv (blockPat m)).symm.trans
    ((Equiv.sigmaCongrRight (fun q =>
        Fintype.equivOfCardEq (by rw [block_fiber, colour_fiber']; exact hm q))).trans
      (Equiv.sigmaFiberEquiv (patIdx L)))

theorem blockColourEquiv_patIdx (m : Fin 7 → Fin 4)
    (hm : ∀ q, (m q : ℕ) = mS L (subset q)) (b : Fin (numBlocks m)) :
    patIdx L (blockColourEquiv L m hm b) = blockPat m b := by
  have hfib : ∀ (z : Σ q, {c : {y // y ∈ colColors L} // patIdx L c = q}),
      patIdx L ((Equiv.sigmaFiberEquiv (patIdx L)) z) = z.1 := fun z => z.2.property
  simp only [blockColourEquiv, Equiv.trans_apply, hfib, Equiv.sigmaCongrRight_apply,
    Equiv.sigmaFiberEquiv_symm_apply_fst]

/-- **Pattern-respecting property.** -/
theorem blockColourEquiv_pat (m : Fin 7 → Fin 4)
    (hm : ∀ q, (m q : ℕ) = mS L (subset q)) (b : Fin (numBlocks m)) :
    pat L (blockColourEquiv L m hm b).val = subset (blockPat m b) := by
  rw [← patIdx_section L (blockColourEquiv L m hm b), blockColourEquiv_patIdx]

theorem mem_subset (p : Fin 7) (i : Fin 3) : i ∈ subset p ↔ patHasRow p i := by
  simp [subset]

def IsState (m : Fin 7 → Fin 4) (s : Fin 3 → Fin (numBlocks m)) : Prop :=
  (∀ i : Fin 3, patHasRow (blockPat m (s i)) i = true) ∧ s 0 ≠ s 1 ∧ s 1 ≠ s 2

/-- The colouring a state spells out (per column). -/
noncomputable def colOfState (m : Fin 7 → Fin 4) (hm : ∀ q, (m q : ℕ) = mS L (subset q))
    (s : Fin 3 → Fin (numBlocks m)) (i : Fin 3) : ℕ := (blockColourEquiv L m hm (s i)).val

theorem colOfState_mem (m : Fin 7 → Fin 4) (hm : ∀ q, (m q : ℕ) = mS L (subset q))
    (s : Fin 3 → Fin (numBlocks m)) (hs : IsState m s) (i : Fin 3) :
    colOfState L m hm s i ∈ L i := by
  have hp : pat L (colOfState L m hm s i) = subset (blockPat m (s i)) :=
    blockColourEquiv_pat L m hm (s i)
  have hi : i ∈ subset (blockPat m (s i)) := (mem_subset _ i).mpr (hs.1 i)
  rw [← hp, pat, Finset.mem_filter] at hi
  exact hi.2

theorem colOfState_ne (m : Fin 7 → Fin 4) (hm : ∀ q, (m q : ℕ) = mS L (subset q))
    (s : Fin 3 → Fin (numBlocks m)) {i i' : Fin 3} (h : s i ≠ s i') :
    colOfState L m hm s i ≠ colOfState L m hm s i' := by
  intro he
  exact h ((blockColourEquiv L m hm).injective (Subtype.ext he))

theorem colOfState_injective (m : Fin 7 → Fin 4) (hm : ∀ q, (m q : ℕ) = mS L (subset q)) :
    Function.Injective (colOfState L m hm) := by
  intro s s' h
  funext i
  exact (blockColourEquiv L m hm).injective (Subtype.ext (congrFun h i))

abbrev Matching (mL mR : Fin 7 → Fin 4) := Fin (numBlocks mL) → Option (Fin (numBlocks mR))

def Me (mL mR : Fin 7 → Fin 4) (M : Matching mL mR)
    (s : Fin 3 → Fin (numBlocks mL)) (t : Fin 3 → Fin (numBlocks mR)) : Bool :=
  (List.finRange 3).all (fun i => M (s i) != some (t i))

/-- The seam matching induced by the two columns' bijections: same colour ⇒ matched. -/
noncomputable def seamMatching (R : Fin 3 → Finset ℕ) (mL mR : Fin 7 → Fin 4)
    (hmL : ∀ q, (mL q : ℕ) = mS L (subset q)) (hmR : ∀ q, (mR q : ℕ) = mS R (subset q)) :
    Matching mL mR := fun bL =>
  if h : (blockColourEquiv L mL hmL bL).val ∈ colColors R
  then some ((blockColourEquiv R mR hmR).symm ⟨(blockColourEquiv L mL hmL bL).val, h⟩) else none

/-- **`Me` ⇒ concrete horizontal compatibility.** -/
theorem Me_imp_compat (R : Fin 3 → Finset ℕ) (mL mR : Fin 7 → Fin 4)
    (hmL : ∀ q, (mL q : ℕ) = mS L (subset q)) (hmR : ∀ q, (mR q : ℕ) = mS R (subset q))
    (s : Fin 3 → Fin (numBlocks mL)) (t : Fin 3 → Fin (numBlocks mR))
    (hMe : Me mL mR (seamMatching L R mL mR hmL hmR) s t = true) (i : Fin 3) :
    colOfState L mL hmL s i ≠ colOfState R mR hmR t i := by
  intro he
  have hval : (blockColourEquiv L mL hmL (s i)).val = (blockColourEquiv R mR hmR (t i)).val := he
  have hc : (blockColourEquiv L mL hmL (s i)).val ∈ colColors R := by
    rw [hval]; exact (blockColourEquiv R mR hmR (t i)).property
  have hM : seamMatching L R mL mR hmL hmR (s i) = some (t i) := by
    rw [seamMatching, dif_pos hc]
    congr 1
    apply (blockColourEquiv R mR hmR).injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext hval
  have hne := (List.all_eq_true.mp hMe) i (List.mem_finRange i)
  rw [hM] at hne
  simp at hne

end Grid3.Three.BlockColour
