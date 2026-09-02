import Mathlib
open Finset
namespace Grid3.Three.BlockCount

def blockList (m : Fin 7 → Fin 4) : List (Fin 7) :=
  (List.finRange 7).flatMap (fun p => List.replicate (m p) p)
def numBlocks (m : Fin 7 → Fin 4) : ℕ := (blockList m).length

/-- Count of pattern `q` among the blocks equals `m q`. -/
theorem count_blockList (m : Fin 7 → Fin 4) (q : Fin 7) :
    (blockList m).count q = m q := by
  fin_cases q <;>
    simp [blockList, List.finRange, List.flatMap, List.count_append, List.count_replicate]

end Grid3.Three.BlockCount
