import Nonsmooth.GaussianPrior
import Nonsmooth.GaussianRealMoments
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory ProbabilityTheory Metric Filter Function
open scoped Topology InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

theorem standardGaussianCoordinates_characteristic (d : ℕ) (t : Fin d → ℝ) :
    (∫ v : Fin d → ℝ, Complex.exp (((∑ i, t i * v i : ℝ) : ℂ) * Complex.I)
      ∂standardGaussianCoordinates d) = Complex.exp (-((∑ i, (t i) ^ 2 : ℝ) : ℂ) / 2) := by
  have he (v : Fin d → ℝ) :
      Complex.exp (((∑ i, t i * v i : ℝ) : ℂ) * Complex.I) =
        ∏ i, Complex.exp ((t i : ℂ) * (v i : ℂ) * Complex.I) := by
    rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
    simp only [Complex.ofReal_mul]
  simp_rw [he]
  have hp : (∫ v : Fin d → ℝ, ∏ i, Complex.exp ((t i : ℂ) * (v i : ℂ) * Complex.I)
      ∂standardGaussianCoordinates d) =
        ∏ i, ∫ z : ℝ, Complex.exp ((t i : ℂ) * (z : ℂ) * Complex.I) ∂gaussianReal 0 1 := by
    letI : MeasureSpace ℝ := ⟨gaussianReal 0 1⟩
    letI : SigmaFinite (volume : Measure ℝ) := by
      change SigmaFinite (gaussianReal 0 1)
      infer_instance
    exact integral_fintype_prod_eq_prod (fun (i : Fin d) (z : ℝ) => Complex.exp ((t i : ℂ) * (z : ℂ) * Complex.I))
  rw [hp]
  have hg (i : Fin d) :
      (∫ z : ℝ, Complex.exp ((t i : ℂ) * (z : ℂ) * Complex.I) ∂gaussianReal 0 1) =
        Complex.exp (-(t i : ℂ) ^ 2 / 2) := by
    simpa only [charFun_apply_real, Complex.ofReal_zero, Complex.ofReal_one,
      NNReal.coe_one, mul_zero, zero_mul, zero_sub, one_mul, neg_div] using
      (charFun_gaussianReal (μ := 0) (v := 1) (t i))
  simp_rw [hg]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_pow, ← Finset.sum_neg_distrib, ← Finset.sum_div]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem euclideanGaussian_characteristic (t : E) :
    charFun (euclideanGaussianLaw E) t = Complex.exp (-(‖t‖ : ℂ) ^ 2 / 2) := by
  change charFun (stdGaussian E) t = _
  simpa only [Complex.ofReal_pow] using (charFun_stdGaussian (E := E) t)

theorem euclideanGaussianLaw_isometry (e : E ≃ₗᵢ[ℝ] E) :
    Measure.map e (euclideanGaussianLaw E) = euclideanGaussianLaw E := by
  change Measure.map e (stdGaussian E) = stdGaussian E
  exact stdGaussian_map e

end
end Nonsmooth
