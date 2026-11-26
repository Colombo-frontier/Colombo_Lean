import NCConcave16991.MixedHaarWordDimension
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Every word layer has enough ambient rank for all finite requests -/

namespace NCConcave16991.MixedHaar

theorem formalLayer_finrank (n t D : ℕ) :
    Module.finrank ℝ (BranchOracle.FormalLayer (ι := Fin n) (Space D) t) = n ^ t * D := by
  have he := (WithLp.linearEquiv 2 ℝ (BranchOracle.Word (Fin n) t → Space D)).finrank_eq
  rw [he,Module.finrank_pi_fintype]
  simp [finrank_euclideanSpace_fin,BranchOracle.Word,nsmul_eq_mul]

theorem formalLayer_finrank_ge (n t D : ℕ) (hn : 0 < n) :
    D ≤ Module.finrank ℝ (BranchOracle.FormalLayer (ι := Fin n) (Space D) t) := by
  rw [formalLayer_finrank]
  simpa only [one_mul] using Nat.mul_le_mul_right D (Nat.one_le_pow t n (by omega))

theorem wordAmbientDimension_layer_gt (n H N U t : ℕ) (hn : 0 < n) (a : ℝ) :
    U < Module.finrank ℝ (BranchOracle.FormalLayer (ι := Fin n)
      (Space (wordAmbientDimension n H N U a)) t) :=
  (wordAmbientDimension_gt n H N U a).trans_le (formalLayer_finrank_ge _ _ _ hn)

end NCConcave16991.MixedHaar
