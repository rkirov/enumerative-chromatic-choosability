import Mathlib
open Finset
namespace Grid3.Three.FiberCard

/-- **Index-fiber card = count** (general list lemma, by induction). -/
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

def blockList (m : Fin 7 → Fin 4) : List (Fin 7) :=
  (List.finRange 7).flatMap (fun p => List.replicate (m p) p)
def numBlocks (m : Fin 7 → Fin 4) : ℕ := (blockList m).length
def blockPat (m : Fin 7 → Fin 4) (j : Fin (numBlocks m)) : Fin 7 := (blockList m).get j

theorem count_blockList (m : Fin 7 → Fin 4) (q : Fin 7) : (blockList m).count q = m q := by
  fin_cases q <;>
    simp [blockList, List.finRange, List.flatMap, List.count_append, List.count_replicate]

/-- Number of blocks with pattern `q` is `m q`. -/
theorem fiber_card (m : Fin 7 → Fin 4) (q : Fin 7) :
    (Finset.univ.filter (fun b : Fin (numBlocks m) => blockPat m b = q)).card = m q := by
  show (Finset.univ.filter (fun b : Fin (blockList m).length => (blockList m)[b] = q)).card = m q
  rw [count_eq_fiber]; exact count_blockList m q

end Grid3.Three.FiberCard
