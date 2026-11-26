import LowRank.OrthogonalOracleProgram
import LowRank.GaussianCoordinates

/-! The exact orthogonal program simulation in the original finite matrix
coordinate type. Euclidean norms are computed through an orthonormal basis,
not through the sup norm on the underlying function type. -/

namespace LowRank
open Matrix
open scoped Matrix InnerProductSpace
noncomputable section

variable {E O : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {d : ℕ}

def liftMatrixOracle (b : OrthonormalBasis (Fin d) ℝ E) (W : Matrix (Fin d) (Fin d) ℝ) : E →ₗ[ℝ] E :=
  (basisCoordinates b).symm.toLinearMap.comp (W.mulVecLin.comp (basisCoordinates b).toLinearMap)

def liftMatrixProgram (b : OrthonormalBasis (Fin d) ℝ E)
    (p : OracleProgram (Fin d → ℝ) (Fin d → ℝ) O) : OracleProgram E E O :=
  p.simulate (basisCoordinates b).symm (fun _ r => basisCoordinates b r)

def lowerMatrixProgram (b : OrthonormalBasis (Fin d) ℝ E) (p : OracleProgram E E O) :
    OracleProgram (Fin d → ℝ) (Fin d → ℝ) O :=
  p.simulate (basisCoordinates b) (fun _ r => (basisCoordinates b).symm r)

def normalizeMatrixProgram (b : OrthonormalBasis (Fin d) ℝ E)
    (p : OracleProgram (Fin d → ℝ) (Fin d → ℝ) O) : OracleProgram (Fin d → ℝ) (Fin d → ℝ) O :=
  lowerMatrixProgram b ((liftMatrixProgram b p).orthogonalize ⊥ 0)

def CoordinateOrthogonalQueries (b : OrthonormalBasis (Fin d) ℝ E) :
    OracleProgram (Fin d → ℝ) (Fin d → ℝ) O → Submodule ℝ E → Prop
  | .done _, _ => True
  | .ask u next, K =>
      ‖(basisCoordinates b).symm u‖ = 1 ∧ (basisCoordinates b).symm u ∈ Kᗮ ∧
        ∀ w, CoordinateOrthogonalQueries b (next w) (K ⊔ ℝ ∙ (basisCoordinates b).symm u)

theorem lowerMatrixProgram_orthogonal (b : OrthonormalBasis (Fin d) ℝ E) (p : OracleProgram E E O)
    (K : Submodule ℝ E) (hp : p.OrthogonalQueries K) :
    CoordinateOrthogonalQueries b (lowerMatrixProgram b p) K := by
  induction p generalizing K with
  | done o => trivial
  | ask v next ih =>
    change ‖(basisCoordinates b).symm ((basisCoordinates b) v)‖ = 1 ∧
      (basisCoordinates b).symm ((basisCoordinates b) v) ∈ Kᗮ ∧ _
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    exact ⟨hp.1, hp.2.1, fun w => ih _ _ (hp.2.2 _)⟩

theorem normalizeMatrixProgram_orthogonal (b : OrthonormalBasis (Fin d) ℝ E)
    (p : OracleProgram (Fin d → ℝ) (Fin d → ℝ) O) :
    CoordinateOrthogonalQueries b (normalizeMatrixProgram b p) ⊥ :=
  lowerMatrixProgram_orthogonal b _ ⊥ (OracleProgram.orthogonalize_queries _ ⊥ 0)

theorem liftMatrixProgram_simulation (b : OrthonormalBasis (Fin d) ℝ E)
    (W : Matrix (Fin d) (Fin d) ℝ) (p : OracleProgram (Fin d → ℝ) (Fin d → ℝ) O) :
    (liftMatrixProgram b p).eval (liftMatrixOracle b W) = p.eval (Matrix.mulVec W) ∧
      (liftMatrixProgram b p).calls (liftMatrixOracle b W) = p.calls (Matrix.mulVec W) := by
  have h : ∀ v, (basisCoordinates b) (liftMatrixOracle b W ((basisCoordinates b).symm v)) = W *ᵥ v := by
    intro v
    simp [liftMatrixOracle, ContinuousLinearEquiv.apply_symm_apply]
    exact (basisCoordinates b).apply_symm_apply _
  exact ⟨OracleProgram.eval_simulate _ _ _ _ h p, OracleProgram.calls_simulate _ _ _ _ h p⟩

theorem lowerMatrixProgram_simulation (b : OrthonormalBasis (Fin d) ℝ E)
    (W : Matrix (Fin d) (Fin d) ℝ) (p : OracleProgram E E O) :
    (lowerMatrixProgram b p).eval (Matrix.mulVec W) = p.eval (liftMatrixOracle b W) ∧
      (lowerMatrixProgram b p).calls (Matrix.mulVec W) = p.calls (liftMatrixOracle b W) := by
  have h : ∀ v, (basisCoordinates b).symm (W *ᵥ ((basisCoordinates b) v)) = liftMatrixOracle b W v :=
    fun _ => rfl
  exact ⟨OracleProgram.eval_simulate _ _ _ _ h p, OracleProgram.calls_simulate _ _ _ _ h p⟩

theorem normalizeMatrixProgram_simulation (b : OrthonormalBasis (Fin d) ℝ E)
    (W : Matrix (Fin d) (Fin d) ℝ) (p : OracleProgram (Fin d → ℝ) (Fin d → ℝ) O) :
    (normalizeMatrixProgram b p).eval (Matrix.mulVec W) = p.eval (Matrix.mulVec W) ∧
      (normalizeMatrixProgram b p).calls (Matrix.mulVec W) ≤ p.calls (Matrix.mulVec W) := by
  have hl := lowerMatrixProgram_simulation b W ((liftMatrixProgram b p).orthogonalize ⊥ 0)
  have ho := OracleProgram.orthogonal_program_simulation (liftMatrixOracle b W) (liftMatrixProgram b p)
  have hi := liftMatrixProgram_simulation b W p
  exact ⟨hl.1.trans (ho.1.trans hi.1), hl.2.le.trans (ho.2.1.trans hi.2.le)⟩

theorem normalizeMatrixProgram_budget (b : OrthonormalBasis (Fin d) ℝ E) (q : ℕ)
    (p : OracleProgram (Fin d → ℝ) (Fin d → ℝ) O) (hp : p.HasBudget q) :
    (normalizeMatrixProgram b p).HasBudget q :=
  OracleProgram.budget_simulate _ _
    (OracleProgram.budget_orthogonalize q _ (OracleProgram.budget_simulate _ _ hp) ⊥ 0)

end
end LowRank
