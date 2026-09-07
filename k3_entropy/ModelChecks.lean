import k3_entropy.FinalModel
import k3_entropy.KernelTransport

/-! Small regression examples and axiom audits for the actual-colour model interface. -/

namespace Grid3.Three.Model

/-- Regression: the two endpoints of a proper three-vertex column may have equal colours. -/
example :
    toColouring 0 (![0, 1, 0] : Fin 3 → Fin 2) ∈
      properC (gridAdj 1) (fun _ => ({0, 1} : Finset ℕ)) := by
  apply toColouring_mem_properC
  · intro j i; fin_cases j; fin_cases i <;> decide
  · intro j i i' h; fin_cases j; fin_cases i <;> fin_cases i' <;> norm_num [colAt] at *
  · intro i j j' h; have := j.isLt; have := j'.isLt; omega

example : pathEquiv 2 (ListColoring.pathStart 2) = 0 := by decide
example : pathEquiv 2 (ListColoring.pathEnd 2) = 2 := by decide

end Grid3.Three.Model

#print axioms Grid3.Three.Cert.EntropyCert.row_entropy
#print axioms Grid3.Three.Cert.SeamOK.row_entropy_bonus
#print axioms Grid3.Three.Cert.parry_row_entropy
#print axioms Grid3.Three.Transport.liftKernel_entropy
#print axioms Grid3.Three.Transport.liftKernel_step
#print axioms Grid3.Three.Transport.liftKernel_support
#print axioms Grid3.Three.Model.support_card_le_properC
#print axioms Grid3.Three.Model.col_eq_properC
#print axioms Grid3.Three.Model.colConst_three_eq_a
#print axioms Grid3.Three.colConst_le_col_of_model
