import Mathlib

/-!
# Gluing class-wise bijections

A colour injection for a seam is assembled from bijections between classes: the colours of one
kind (a pattern, or a matched pair of patterns) and the canonical slots of that kind. Each class
bijection exists because the two finsets have the same cardinality; `exists_glued` packages the
glued map together with an inverse on the union of the target classes.
-/

namespace Grid3.Three.Glue

variable {ι α β : Type*} [DecidableEq α] [DecidableEq β]

/-- a bijection between two finsets of equal cardinality -/
noncomputable def finsetEquiv (s : Finset α) (t : Finset β) (h : s.card = t.card) : s ≃ t :=
  s.equivFin.trans ((finCongr h).trans t.equivFin.symm)

/-- a map `α → β` with an inverse, bijective between `A i` and `B i` for every class `i` -/
structure Glued (A : ι → Finset α) (B : ι → Finset β) where
  toFun : α → β
  invFun : β → α
  mem : ∀ i, ∀ a ∈ A i, toFun a ∈ B i
  inv_mem : ∀ i, ∀ b ∈ B i, invFun b ∈ A i
  left_inv : ∀ i, ∀ a ∈ A i, invFun (toFun a) = a
  right_inv : ∀ i, ∀ b ∈ B i, toFun (invFun b) = b

omit [DecidableEq α] [DecidableEq β] in
theorem Glued.injOn {A : ι → Finset α} {B : ι → Finset β} (g : Glued A B) (i j : ι)
    (a : α) (ha : a ∈ A i) (a' : α) (ha' : a' ∈ A j) (h : g.toFun a = g.toFun a') : a = a' := by
  have h1 := g.left_inv i a ha
  have h2 := g.left_inv j a' ha'
  rw [← h1, ← h2, h]

/-- **Gluing.** Class functions `cls`, `clsB` that identify the class of every element, and equal
class cardinalities, give a glued map. -/
theorem exists_glued [Inhabited α] [Inhabited β] (A : ι → Finset α) (B : ι → Finset β)
    (cls : α → ι) (clsB : β → ι)
    (hA : ∀ i, ∀ a ∈ A i, cls a = i) (hB : ∀ i, ∀ b ∈ B i, clsB b = i)
    (hcard : ∀ i, (A i).card = (B i).card) : Nonempty (Glued A B) := by
  classical
  let e : ∀ i, A i ≃ B i := fun i => finsetEquiv (A i) (B i) (hcard i)
  let f : α → β := fun a => if h : a ∈ A (cls a) then (e (cls a) ⟨a, h⟩).1 else default
  let g : β → α := fun b => if h : b ∈ B (clsB b) then ((e (clsB b)).symm ⟨b, h⟩).1 else default
  have hf : ∀ i, ∀ a, ∀ (ha : a ∈ A i), f a = (e i ⟨a, ha⟩).1 := by
    intro i a ha
    have hc := hA i a ha
    simp only [f]
    subst hc
    rw [dif_pos ha]
  have hg : ∀ i, ∀ b, ∀ (hb : b ∈ B i), g b = ((e i).symm ⟨b, hb⟩).1 := by
    intro i b hb
    have hc := hB i b hb
    simp only [g]
    subst hc
    rw [dif_pos hb]
  refine ⟨⟨f, g, ?_, ?_, ?_, ?_⟩⟩
  · intro i a ha
    rw [hf i a ha]; exact (e i ⟨a, ha⟩).2
  · intro i b hb
    rw [hg i b hb]; exact ((e i).symm ⟨b, hb⟩).2
  · intro i a ha
    rw [hf i a ha, hg i _ (e i ⟨a, ha⟩).2]
    simp
  · intro i b hb
    rw [hg i b hb, hf i _ ((e i).symm ⟨b, hb⟩).2]
    simp

/-- **Index-fiber card = count** (as in `the retired staging module FiberCard.lean`). -/
theorem count_eq_fiber {γ : Type*} [BEq γ] [LawfulBEq γ] [DecidableEq γ] (l : List γ) (a : γ) :
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

end Grid3.Three.Glue
