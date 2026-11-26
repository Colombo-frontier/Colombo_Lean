import HeavyTail.GaussianDirections
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Exact Gaussian likelihood calculations. The scalar change-of-measure theorem
identifies actual Gaussian measures, and the Hilbert-space exponential ratio
has exact first and second moments under the concrete standard Gaussian law.
This file alone does not assert an adaptive transcript testing bound.
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace NNReal ENNReal

namespace HeavyTail.GaussianLower
noncomputable section

def exponentialRatio {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d z : E) : ℝ := Real.exp (⟪d, z⟫_ℝ - ‖d‖ ^ 2 / 2)

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem exponentialRatio_integrable (d : E) :
    Integrable (exponentialRatio d) (GaussianEstimates.euclideanGaussianLaw E) := by
  change Integrable (fun z ↦ Real.exp (⟪d, z⟫_ℝ - ‖d‖ ^ 2 / 2)) _
  simp_rw [Real.exp_sub]
  simpa only [one_mul] using
    (GaussianEstimates.gaussian_inner_exp_integrable E d 1).div_const
      (Real.exp (‖d‖ ^ 2 / 2))

theorem exponentialRatio_mean (d : E) :
    (∫ z, exponentialRatio d z ∂GaussianEstimates.euclideanGaussianLaw E) = 1 := by
  simp_rw [exponentialRatio, Real.exp_sub]
  rw [integral_div, GaussianEstimates.gaussian_exp_inner]
  exact div_self (Real.exp_ne_zero _)

theorem exponentialRatio_square_integrable (d : E) :
    Integrable (fun z ↦ exponentialRatio d z ^ 2)
      (GaussianEstimates.euclideanGaussianLaw E) := by
  have he (z : E) : exponentialRatio d z ^ 2 =
      Real.exp (2 * ⟪d, z⟫_ℝ) / Real.exp (‖d‖ ^ 2) := by
    rw [exponentialRatio, ← Real.exp_nat_mul, ← Real.exp_sub]
    congr 1
    norm_num
    ring
  simp_rw [he]
  exact (GaussianEstimates.gaussian_inner_exp_integrable E d 2).div_const _

theorem exponentialRatio_second (d : E) :
    (∫ z, exponentialRatio d z ^ 2 ∂GaussianEstimates.euclideanGaussianLaw E) =
      Real.exp (‖d‖ ^ 2) := by
  have he (z : E) : exponentialRatio d z ^ 2 =
      Real.exp ⟪(2 : ℝ) • d, z⟫_ℝ / Real.exp (‖d‖ ^ 2) := by
    rw [exponentialRatio, ← Real.exp_nat_mul, ← Real.exp_sub, real_inner_smul_left]
    congr 1
    norm_num
    ring
  simp_rw [he]
  rw [integral_div, GaussianEstimates.gaussian_exp_inner, ← Real.exp_sub]
  congr 1
  rw [norm_smul, Real.norm_eq_abs]
  norm_num
  ring

theorem exponentialRatio_centered_second (d : E) :
    (∫ z, (exponentialRatio d z - 1) ^ 2 ∂GaussianEstimates.euclideanGaussianLaw E) =
      Real.exp (‖d‖ ^ 2) - 1 := by
  have he (z : E) : (exponentialRatio d z - 1) ^ 2 =
      exponentialRatio d z ^ 2 - 2 * exponentialRatio d z + 1 := by ring
  simp_rw [he]
  have hi : Integrable (fun z ↦ exponentialRatio d z ^ 2 - 2 * exponentialRatio d z)
      (GaussianEstimates.euclideanGaussianLaw E) :=
    (exponentialRatio_square_integrable E d).sub ((exponentialRatio_integrable E d).const_mul 2)
  have hi2 : Integrable (fun z ↦ 2 * exponentialRatio d z)
      (GaussianEstimates.euclideanGaussianLaw E) := (exponentialRatio_integrable E d).const_mul 2
  rw [integral_add hi (integrable_const _),
    integral_sub (exponentialRatio_square_integrable E d) hi2,
    integral_const_mul, exponentialRatio_second, exponentialRatio_mean, integral_const]
  simp
  ring

def scalarRatio (μ ν σ y : ℝ) : ℝ :=
  Real.exp ((μ - ν) * (y - ν) / σ ^ 2 - (μ - ν) ^ 2 / (2 * σ ^ 2))

lemma scalarRatio_pos (μ ν σ y : ℝ) : 0 < scalarRatio μ ν σ y := Real.exp_pos _

lemma scalarRatio_measurable (μ ν σ : ℝ) : Measurable (scalarRatio μ ν σ) := by
  unfold scalarRatio
  fun_prop

theorem scalar_pdf_ratio {σ : ℝ} (hσ : σ ≠ 0) (μ ν y : ℝ) :
    gaussianPDFReal μ ⟨σ ^ 2, sq_nonneg σ⟩ y =
      scalarRatio μ ν σ y * gaussianPDFReal ν ⟨σ ^ 2, sq_nonneg σ⟩ y := by
  unfold gaussianPDFReal scalarRatio
  simp only [NNReal.coe_mk]
  rw [mul_left_comm, ← Real.exp_add]
  congr 1
  congr 1
  field_simp
  ring

/-- An equality of actual shifted Gaussian measures, not an assumed derivative. -/
theorem scalar_gaussian_change_of_measure {σ : ℝ} (hσ : σ ≠ 0) (μ ν : ℝ) :
    gaussianReal μ ⟨σ ^ 2, sq_nonneg σ⟩ =
      (gaussianReal ν ⟨σ ^ 2, sq_nonneg σ⟩).withDensity
        (fun y ↦ ENNReal.ofReal (scalarRatio μ ν σ y)) := by
  have hv : (⟨σ ^ 2, sq_nonneg σ⟩ : ℝ≥0) ≠ 0 := by
    intro he
    have := congrArg (fun r : ℝ≥0 ↦ (r : ℝ)) he
    exact hσ (sq_eq_zero_iff.mp this)
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ hv,
    ← withDensity_mul volume (measurable_gaussianPDF _ _)
      (scalarRatio_measurable μ ν σ).ennreal_ofReal]
  congr 1
  funext y
  change ENNReal.ofReal (gaussianPDFReal μ ⟨σ ^ 2, sq_nonneg σ⟩ y) =
    ENNReal.ofReal (gaussianPDFReal ν ⟨σ ^ 2, sq_nonneg σ⟩ y) *
      ENNReal.ofReal (scalarRatio μ ν σ y)
  rw [scalar_pdf_ratio hσ μ ν y,
    ENNReal.ofReal_mul (scalarRatio_pos μ ν σ y).le, mul_comm]

theorem scalarRatio_at_sample {σ : ℝ} (hσ : σ ≠ 0) (μ ν z : ℝ) :
    scalarRatio μ ν σ (ν + σ * z) =
      Real.exp (((μ - ν) / σ) * z - ((μ - ν) / σ) ^ 2 / 2) := by
  unfold scalarRatio
  congr 1
  field_simp
  ring

theorem scalar_gaussian_affine_sample (ν σ : ℝ) :
    (gaussianReal 0 1).map (fun z ↦ ν + σ * z) =
      gaussianReal ν ⟨σ ^ 2, sq_nonneg σ⟩ := by
  have he : (fun z : ℝ ↦ ν + σ * z) = (fun y : ℝ ↦ ν + y) ∘ (fun z : ℝ ↦ σ * z) := rfl
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop),
    gaussianReal_map_const_mul, gaussianReal_map_const_add]
  simp

theorem scalarRatio_mean {σ : ℝ} (hσ : σ ≠ 0) (μ ν : ℝ) :
    (∫ y, scalarRatio μ ν σ y ∂gaussianReal ν ⟨σ ^ 2, sq_nonneg σ⟩) = 1 := by
  rw [← scalar_gaussian_affine_sample ν σ,
    integral_map_of_stronglyMeasurable (by fun_prop)
      (by unfold scalarRatio; exact Continuous.stronglyMeasurable (by fun_prop))]
  simp_rw [scalarRatio_at_sample hσ, Real.exp_sub]
  have hm : (∫ z : ℝ, Real.exp (((μ - ν) / σ) * z) ∂gaussianReal 0 1) =
      Real.exp (((μ - ν) / σ) ^ 2 / 2) := GaussianEstimates.standard_mgf _
  rw [integral_div, hm]
  exact div_self (Real.exp_ne_zero _)

theorem scalarRatio_second {σ : ℝ} (hσ : σ ≠ 0) (μ ν : ℝ) :
    (∫ y, scalarRatio μ ν σ y ^ 2 ∂gaussianReal ν ⟨σ ^ 2, sq_nonneg σ⟩) =
      Real.exp (((μ - ν) / σ) ^ 2) := by
  rw [← scalar_gaussian_affine_sample ν σ,
    integral_map_of_stronglyMeasurable (by fun_prop)
      (by unfold scalarRatio; exact Continuous.stronglyMeasurable (by fun_prop))]
  have he (z : ℝ) : scalarRatio μ ν σ (ν + σ * z) ^ 2 =
      Real.exp ((2 * ((μ - ν) / σ)) * z) / Real.exp (((μ - ν) / σ) ^ 2) := by
    rw [scalarRatio_at_sample hσ, ← Real.exp_nat_mul, ← Real.exp_sub]
    congr 1
    norm_num
    ring
  simp_rw [he]
  have hm : (∫ z : ℝ, Real.exp ((2 * ((μ - ν) / σ)) * z) ∂gaussianReal 0 1) =
      Real.exp ((2 * ((μ - ν) / σ)) ^ 2 / 2) := GaussianEstimates.standard_mgf _
  rw [integral_div, hm, ← Real.exp_sub]
  congr 1
  ring

end
end HeavyTail.GaussianLower
