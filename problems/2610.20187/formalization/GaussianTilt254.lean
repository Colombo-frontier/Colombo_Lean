import GaussianAlgebra254
import GaussianAnalysis254

noncomputable section
open scoped Matrix BigOperators
open Matrix
namespace Paper254

theorem PrecisionGaussian.tilt_mean {d : ℕ} (P : PrecisionGaussian d)
    (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (g w : Coordinates d) :
    (P.tilt lam γ hlam hγ g w).mean = P.mean -
      (lam*(1+γ*(g ⬝ᵥ (P.mean-w)))/(1+lam*γ*matrixQuadratic P.precision⁻¹ g)) •
        (P.precision⁻¹ *ᵥ g) := by
  let A := rankOnePrecision P.precision (lam*γ) g
  have hA : A.PosDef := rankOnePrecision_posDef P.positive _ (mul_nonneg hlam hγ) g
  have hb : P.precision *ᵥ P.mean-lam • g+(lam*γ*(g ⬝ᵥ w)) • g =
      A *ᵥ P.mean-(lam*(1+γ*(g ⬝ᵥ (P.mean-w)))) • g := by
    simp only [A, rankOnePrecision, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.vecMulVec_mulVec, dotProduct_sub]
    ext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, op_smul_eq_mul]
    ring
  change A⁻¹ *ᵥ _ = _
  rw [hb, Matrix.mulVec_sub, Matrix.mulVec_smul, precision_inverse_cancel_left hA]
  dsimp only [A]
  rw [rankOnePrecision_inverse_gradient P.positive _ (mul_nonneg hlam hγ), smul_smul]
  congr 2
  ring

theorem inverse_quadratic_identity {d : ℕ} {A : Precision d} (hA : A.PosDef)
    (g : Coordinates d) : matrixQuadratic A (A⁻¹ *ᵥ g) = matrixQuadratic A⁻¹ g := by
  rw [matrixQuadratic, precision_inverse_cancel hA, dotProduct_comm]
  rfl

theorem tilt_quadratic_expansion {d : ℕ} {A : Precision d} (hA : A.PosDef)
    (g x : Coordinates d) (θ k : ℝ) :
    matrixQuadratic (rankOnePrecision A θ g) (x+k • (A⁻¹ *ᵥ g)) =
      matrixQuadratic A x+2*k*(g ⬝ᵥ x)+k^2*matrixQuadratic A⁻¹ g+
        θ*((g ⬝ᵥ x)+k*matrixQuadratic A⁻¹ g)^2 := by
  rw [rankOnePrecision_quadratic, matrixQuadratic_add_smul hA.isHermitian,
    precision_inverse_cancel hA, inverse_quadratic_identity hA, dotProduct_comm x g]
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, matrixQuadratic]

theorem precisionCovariancePart_rankOne {d : ℕ} {A : Precision d} (hA : A.PosDef)
    (q θ : ℝ) (hq : 0 < q) (hθ : 0 ≤ θ) (g : Coordinates d) :
    precisionCovariancePart q (rankOnePrecision A θ g) =
      precisionCovariancePart q A+q*θ*(g ⬝ᵥ g)-
        Real.log (1+θ*matrixQuadratic A⁻¹ g) := by
  have hv := matrixQuadratic_nonneg hA.inv g
  have hden : 0 < 1+θ*matrixQuadratic A⁻¹ g := by positivity
  simp only [precisionCovariancePart, rankOnePrecision_trace, rankOnePrecision_det hA]
  rw [← mul_assoc, Real.log_mul (ne_of_gt (mul_pos (pow_pos hq _) hA.det_pos))
    (ne_of_gt hden)]
  ring

end Paper254
#print axioms Paper254.PrecisionGaussian.tilt_mean
#print axioms Paper254.tilt_quadratic_expansion
#print axioms Paper254.precisionCovariancePart_rankOne
