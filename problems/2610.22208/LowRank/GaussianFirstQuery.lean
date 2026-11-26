import LowRank.GaussianRevealGram

/-! The first coordinate query to XXᵀ. Its actual reply is a measurable
function of the exposed state, so the residual Gaussian block is independent
of that reply. This is one fixed query, not the adaptive induction theorem. -/

namespace LowRank
open MeasureTheory ProbabilityTheory
open scoped Matrix
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {r s : ℕ}

def exposedFirstReply (b : OrthonormalBasis (Fin (s + 1)) ℝ E)
    (p : (Fin (s + 1) → ℝ) × (Fin r → ℝ)) : ℝ × (Fin r → ℝ) :=
  (‖(basisCoordinates b).symm p.1‖ ^ 2, ‖(basisCoordinates b).symm p.1‖ • p.2)

theorem measurable_exposedFirstReply (b : OrthonormalBasis (Fin (s + 1)) ℝ E) :
    Measurable (exposedFirstReply (r := r) b) := by
  unfold exposedFirstReply
  fun_prop

def firstGramReply (X : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) : ℝ × (Fin r → ℝ) :=
  ((X * Xᵀ) 0 0, fun i => (X * Xᵀ) i.succ 0)

theorem firstGramReply_eq_exposed (b : OrthonormalBasis (Fin (s + 1)) ℝ E)
    (X : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    firstGramReply X = exposedFirstReply b (revealGaussianBlock b X).1 := by
  apply Prod.ext
  · exact revealGaussianBlock_gram_pivot b X
  · funext i
    exact revealGaussianBlock_gram_column b X i

theorem firstGramReply_residual_independent (b : OrthonormalBasis (Fin (s + 1)) ℝ E)
    (v : NNReal) :
    IndepFun (firstGramReply (r := r) (s := s))
      (fun X => (revealGaussianBlock b X).2) (iidMatrixLaw (r + 1) (s + 1) v) := by
  have h := (revealGaussianBlock_independent (r := r) b v).comp
    (measurable_exposedFirstReply b) measurable_id
  simpa only [Function.comp_def, id_eq, ← firstGramReply_eq_exposed] using h

end
end LowRank
