import GradientHessian.GaussianConcentrationHilbertIBP
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Dual

/-! The actual Gaussian generator and its coordinate integration-by-parts
identity.  All growth conditions are explicit integrabilities of the terms
appearing in the identity. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory ProbabilityTheory GaussianHilbert
open scoped InnerProductSpace BigOperators

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def coordinateDerivative (f : E → ℝ) (i : Fin (Module.finrank ℝ E)) (x : E) : ℝ :=
  fderiv ℝ f x (stdOrthonormalBasis ℝ E i)

def diagonalSecond (f : E → ℝ) (i : Fin (Module.finrank ℝ E)) (x : E) : ℝ :=
  fderiv ℝ (fderiv ℝ f) x (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i)

def gaussianGenerator (f : E → ℝ) (x : E) : ℝ :=
  (∑ i, diagonalSecond E f i x) - fderiv ℝ f x x

omit [MeasurableSpace E] [BorelSpace E] in
theorem partial_hasFDerivAt {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (i : Fin (Module.finrank ℝ E)) (x : E) :
    HasFDerivAt (coordinateDerivative E f i)
      ((fderiv ℝ (fderiv ℝ f) x).flip (stdOrthonormalBasis ℝ E i)) x := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  have h := (hd x).hasFDerivAt.clm_apply (hasFDerivAt_const (stdOrthonormalBasis ℝ E i) x)
  simpa only [ContinuousLinearMap.comp_zero, zero_add] using h

omit [MeasurableSpace E] [BorelSpace E] in
theorem weighted_partial_fderiv {u v : E → ℝ} (hu : Differentiable ℝ u)
    (hv : ContDiff ℝ 2 v) (i : Fin (Module.finrank ℝ E)) (x : E) :
    fderiv ℝ (fun y => u y * coordinateDerivative E v i y) x (stdOrthonormalBasis ℝ E i) =
      coordinateDerivative E u i x * coordinateDerivative E v i x + u x * diagonalSecond E v i x := by
  rw [((hu x).hasFDerivAt.mul (partial_hasFDerivAt E hv i x)).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul, coordinateDerivative, diagonalSecond]
  ring

theorem gaussian_coordinate_green {u v : E → ℝ} (hu : Differentiable ℝ u)
    (hv : ContDiff ℝ 2 v) (i : Fin (Module.finrank ℝ E))
    (h0 : Integrable (fun x => u x * coordinateDerivative E v i x) (euclideanGaussianLaw E))
    (h1 : Integrable (fun x => coordinateDerivative E u i x * coordinateDerivative E v i x) (euclideanGaussianLaw E))
    (h2 : Integrable (fun x => u x * diagonalSecond E v i x) (euclideanGaussianLaw E))
    (hX : Integrable (fun x => ⟪stdOrthonormalBasis ℝ E i, x⟫_ℝ *
      (u x * coordinateDerivative E v i x)) (euclideanGaussianLaw E)) :
    (∫ x, u x * diagonalSecond E v i x ∂euclideanGaussianLaw E) -
        (∫ x, ⟪stdOrthonormalBasis ℝ E i, x⟫_ℝ * (u x * coordinateDerivative E v i x)
          ∂euclideanGaussianLaw E) =
      -(∫ x, coordinateDerivative E u i x * coordinateDerivative E v i x ∂euclideanGaussianLaw E) := by
  have hd : Differentiable ℝ (fun x => u x * coordinateDerivative E v i x) :=
    fun x => ((hu x).hasFDerivAt.mul (partial_hasFDerivAt E hv i x)).differentiableAt
  have hD : Integrable (fun x => fderiv ℝ (fun y => u y * coordinateDerivative E v i y) x
      (stdOrthonormalBasis ℝ E i)) (euclideanGaussianLaw E) := by
    simp_rw [weighted_partial_fderiv E hu hv]
    exact h1.add h2
  have hi := hilbert_gaussian_integration_by_parts E i hd h0 hD hX
  simp_rw [weighted_partial_fderiv E hu hv] at hi
  rw [integral_add h1 h2] at hi
  linarith only [hi]

end GradientHessian.GaussianConcentration
