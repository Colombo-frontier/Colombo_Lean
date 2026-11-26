import LowRank.MatrixOracleNormalization

/-! Each informative orthogonal query increases the learned dimension by
one, so a normalized program cannot make more calls than the ambient dimension. -/

namespace LowRank
open scoped InnerProductSpace
noncomputable section

variable {E O : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem orthogonal_span_finrank (K : Submodule ℝ E) (u : E) (hu : ‖u‖ = 1) (ho : u ∈ Kᗮ) :
    Module.finrank ℝ (K ⊔ ℝ ∙ u : Submodule ℝ E) = Module.finrank ℝ K + 1 := by
  have hne : u ≠ 0 := by intro h; simp [h] at hu
  have hs : (ℝ ∙ u : Submodule ℝ E) ≤ Kᗮ := Submodule.span_le.mpr (by simpa using ho)
  have hd : Disjoint K (ℝ ∙ u) := K.orthogonal_disjoint.mono_right hs
  have h := K.finrank_sup_add_finrank_inf_eq (ℝ ∙ u)
  rw [hd.eq_bot, finrank_bot, add_zero, finrank_span_singleton hne] at h
  exact h

theorem OracleProgram.orthogonal_calls_finrank_le (oracle : E → E) (p : OracleProgram E E O)
    (K : Submodule ℝ E) (hp : p.OrthogonalQueries K) :
    Module.finrank ℝ K + p.calls oracle ≤ Module.finrank ℝ E := by
  induction p generalizing K with
  | done o => simpa [OracleProgram.calls] using Submodule.finrank_le K
  | ask u next ih =>
    have h := ih (oracle u) (K ⊔ ℝ ∙ u) (hp.2.2 _)
    rw [orthogonal_span_finrank K u hp.1 hp.2.1] at h
    simp only [OracleProgram.calls]
    omega

theorem OracleProgram.orthogonalize_calls_dimension_le (oracle : E → E)
    (p : OracleProgram E E O) : (p.orthogonalize ⊥ 0).calls oracle ≤ Module.finrank ℝ E := by
  simpa using OracleProgram.orthogonal_calls_finrank_le oracle (p.orthogonalize ⊥ 0) ⊥
    (OracleProgram.orthogonalize_queries p ⊥ 0)

theorem normalizeMatrixProgram_calls_dimension_le [MeasurableSpace E] [BorelSpace E] {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ E) (W : Matrix (Fin d) (Fin d) ℝ)
    (p : OracleProgram (Fin d → ℝ) (Fin d → ℝ) O) :
    (normalizeMatrixProgram b p).calls (Matrix.mulVec W) ≤ d := by
  have h := OracleProgram.orthogonalize_calls_dimension_le (liftMatrixOracle b W) (liftMatrixProgram b p)
  have hd : Module.finrank ℝ E = d := by
    have he := (basisCoordinates b).toLinearEquiv.finrank_eq
    simpa using he
  rw [hd] at h
  exact (lowerMatrixProgram_simulation b W ((liftMatrixProgram b p).orthogonalize ⊥ 0)).2.le.trans h

end
end LowRank
