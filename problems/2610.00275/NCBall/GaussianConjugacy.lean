import Mathlib.Probability.Distributions.Gaussian
import Mathlib.Tactic

/-!
# Scalar Gaussian conjugacy from actual densities

This is a fully proved building block for Lemma 8.1, not the adaptive vector
posterior theorem. A scalar prior N(μ,v) and one independent observation of
u plus N(0,t) noise yield posterior variance vt/(v+t).
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace NCBall

def posteriorVar (v t : ℝ≥0) : ℝ≥0 := v * t / (v + t)

def posteriorMean (μ y : ℝ) (v t : ℝ≥0) : ℝ :=
  ((t : ℝ) * μ + (v : ℝ) * y) / ((v : ℝ) + t)

theorem posteriorVar_pos {v t : ℝ≥0} (hv : 0 < v) (ht : 0 < t) :
    0 < posteriorVar v t := by unfold posteriorVar; positivity

theorem scalar_precision_update {v t : ℝ≥0} (hv : 0 < v) (ht : 0 < t) :
    ((posteriorVar v t : ℝ≥0) : ℝ)⁻¹ = (v : ℝ)⁻¹ + (t : ℝ)⁻¹ := by
  have hv' : (v : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hv)
  have ht' : (t : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast ht)
  simp only [posteriorVar, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_add]
  field_simp
  ring

theorem gaussian_exponent_completion (μ y x v t : ℝ) (hv : 0 < v) (ht : 0 < t) :
    -(x - μ) ^ 2 / (2 * v) + -(y - x) ^ 2 / (2 * t) =
      -(y - μ) ^ 2 / (2 * (v + t)) +
      -(x - (t * μ + v * y) / (v + t)) ^ 2 / (2 * (v * t / (v + t))) := by
  have hsum : v + t ≠ 0 := ne_of_gt (add_pos hv ht)
  field_simp
  ring

/-- A positive normalizing factor; its closed-form evidence density is not needed. -/
def gaussianEvidenceFactor (μ y : ℝ) (v t : ℝ≥0) : ℝ :=
  (Real.sqrt (2 * Real.pi * (posteriorVar v t : ℝ))) *
    (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
    (Real.sqrt (2 * Real.pi * (t : ℝ)))⁻¹ *
    Real.exp (-(y - μ) ^ 2 / (2 * ((v : ℝ) + t)))

theorem gaussianEvidenceFactor_pos (μ y : ℝ) {v t : ℝ≥0}
    (hv : 0 < v) (ht : 0 < t) : 0 < gaussianEvidenceFactor μ y v t := by
  have hp : (0 : ℝ) < posteriorVar v t := by exact_mod_cast posteriorVar_pos hv ht
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  unfold gaussianEvidenceFactor
  positivity

/-- Exact factorization of the prior times likelihood into a posterior density. -/
theorem gaussian_density_factorization (μ y x : ℝ) {v t : ℝ≥0}
    (hv : 0 < v) (ht : 0 < t) :
    gaussianPDFReal μ v x * gaussianPDFReal x t y =
      gaussianEvidenceFactor μ y v t *
        gaussianPDFReal (posteriorMean μ y v t) (posteriorVar v t) x := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hp : (0 : ℝ) < posteriorVar v t := by exact_mod_cast posteriorVar_pos hv ht
  have hs : Real.sqrt (2 * Real.pi * (posteriorVar v t : ℝ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hexp := congrArg Real.exp (gaussian_exponent_completion μ y x v t hv' ht')
  simp only [Real.exp_add] at hexp
  unfold gaussianPDFReal gaussianEvidenceFactor posteriorMean
  have he : ((posteriorVar v t : ℝ≥0) : ℝ) = (v : ℝ) * t / ((v : ℝ) + t) := by
    simp [posteriorVar]
  rw [← he] at hexp
  calc
    _ = (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
        (Real.sqrt (2 * Real.pi * (t : ℝ)))⁻¹ *
        (Real.exp (-(x - μ) ^ 2 / (2 * v)) * Real.exp (-(y - x) ^ 2 / (2 * t))) := by ring
    _ = _ := by rw [hexp]; field_simp; ring

theorem gaussian_likelihood_integrable (μ y : ℝ) {v t : ℝ≥0}
    (hv : 0 < v) (ht : 0 < t) :
    Integrable (fun x : ℝ => gaussianPDFReal μ v x * gaussianPDFReal x t y) := by
  simp_rw [gaussian_density_factorization μ y _ hv ht]
  exact (integrable_gaussianPDFReal _ _).const_mul _

theorem gaussian_likelihood_integral (μ y : ℝ) {v t : ℝ≥0}
    (hv : 0 < v) (ht : 0 < t) :
    (∫ x : ℝ, gaussianPDFReal μ v x * gaussianPDFReal x t y) =
      gaussianEvidenceFactor μ y v t := by
  simp_rw [gaussian_density_factorization μ y _ hv ht]
  rw [integral_const_mul, integral_gaussianPDFReal_eq_one _ (ne_of_gt (posteriorVar_pos hv ht)), mul_one]

/-- The normalized density is exactly the conjugate Gaussian density.
No conditional-distribution theorem is assumed in this statement. -/
theorem normalized_gaussian_posterior (μ y x : ℝ) {v t : ℝ≥0}
    (hv : 0 < v) (ht : 0 < t) :
    (gaussianPDFReal μ v x * gaussianPDFReal x t y) /
      (∫ u : ℝ, gaussianPDFReal μ v u * gaussianPDFReal u t y) =
      gaussianPDFReal (posteriorMean μ y v t) (posteriorVar v t) x := by
  rw [gaussian_likelihood_integral μ y hv ht, gaussian_density_factorization μ y x hv ht]
  exact mul_div_cancel_left₀ _ (ne_of_gt (gaussianEvidenceFactor_pos μ y hv ht))

end NCBall
