import LowRank.GaussianMatrixCompression
import LowRank.GaussianFullRank
import LowRank.InverseGramSpectralMoments
import LowRank.ProjectionApproximation

/-! A total measurable right inverse formula, its almost sure validity for
wide Gaussian matrices, and its squared Frobenius norm as an inverse-Gram trace. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators ENNReal
noncomputable section

def gramRightInverse {k s : ℕ} (G : Matrix (Fin k) (Fin s) ℝ) : Matrix (Fin s) (Fin k) ℝ :=
  Gᵀ * inverseGram Gᵀ

theorem measurable_gramRightInverse (k s : ℕ) :
    Measurable (gramRightInverse : Matrix (Fin k) (Fin s) ℝ → _) := by
  have hm : Measurable (fun G : Matrix (Fin k) (Fin s) ℝ => inverseGram Gᵀ) :=
    (measurable_inverseGram s k).comp (by fun_prop)
  unfold gramRightInverse
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  fun_prop

theorem mul_gramRightInverse {k s : ℕ} (G : Matrix (Fin k) (Fin s) ℝ)
    (hG : Function.Injective Gᵀ.mulVec) : G * gramRightInverse G = 1 := by
  simpa only [gramRightInverse, inverseGram, Matrix.transpose_transpose, Matrix.mul_assoc] using
    Matrix.mul_nonsing_inv (Gᵀᵀ * Gᵀ) (gram_det_isUnit_of_injective Gᵀ hG)

theorem gramRightInverse_gram {k s : ℕ} (G : Matrix (Fin k) (Fin s) ℝ) :
    (gramRightInverse G)ᵀ * gramRightInverse G = inverseGram Gᵀ := by
  have hs : (inverseGram Gᵀ)ᵀ = inverseGram Gᵀ := by
    simp only [inverseGram, Matrix.transpose_nonsing_inv, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  calc
    _ = inverseGram Gᵀ * (G * Gᵀ) * inverseGram Gᵀ := by
      simp only [gramRightInverse, Matrix.transpose_mul, Matrix.transpose_transpose, hs,
        Matrix.mul_assoc]
    _ = _ := by
      change (G * Gᵀ)⁻¹ * (G * Gᵀ) * (G * Gᵀ)⁻¹ = (G * Gᵀ)⁻¹
      rcases Matrix.nonsing_inv_cancel_or_zero (G * Gᵀ) with h | h
      · rw [h.1, Matrix.one_mul]
      · simp only [h, Matrix.zero_mul]

theorem frobeniusSq_gramRightInverse {k s : ℕ} (G : Matrix (Fin k) (Fin s) ℝ) :
    frobeniusSq (gramRightInverse G) = (inverseGram Gᵀ).trace := by
  rw [frobeniusSq_eq_trace_right, gramRightInverse_gram]

theorem iidMatrixLaw_rightInverse_ae {k s : ℕ} (hs : k ≤ s) {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ G ∂iidMatrixLaw k s v, G * gramRightInverse G = 1 := by
  have h := (iidMatrixLaw_transpose_preserving k s v).quasiMeasurePreserving.ae
    (iidMatrixLaw_mulVec_injective_ae s k hs hv)
  filter_upwards [h] with G hG
  exact mul_gramRightInverse G hG

theorem iidMatrixLaw_compressed_rightInverse_ae {d k s : ℕ}
    (V : Matrix (Fin d) (Fin k) ℝ) (hV : Vᵀ * V = 1)
    (hs : k ≤ s) {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ U ∂iidMatrixLaw d s v, (Vᵀ * U) * gramRightInverse (Vᵀ * U) = 1 :=
  (iidMatrixLaw_left_compression_preserving V hV v).quasiMeasurePreserving.ae
    (iidMatrixLaw_rightInverse_ae hs hv)

end
end LowRank
