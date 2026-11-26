import GradientHessian.GaussianHilbert

/-! Exponential integrability for arbitrary Lipschitz functions under the
actual standard Gaussian law.  These are prerequisites for the approximation
step in Gaussian concentration, not an assertion of the concentration bound. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory ProbabilityTheory GaussianHilbert
open scoped NNReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem norm_square_exponential_integrable {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun x : E => Real.exp (t * ‖x‖ ^ 2)) (euclideanGaussianLaw E) := by
  rw [euclideanGaussianLaw]
  apply (integrable_map_measure ((by fun_prop :
    Continuous (fun x : E => Real.exp (t * ‖x‖ ^ 2))).aestronglyMeasurable)
    (gaussianSynthesis_continuous E).measurable.aemeasurable).mpr
  change Integrable (fun v => Real.exp (t * ‖gaussianSynthesis E v‖ ^ 2)) _
  simpa only [gaussianSynthesis_norm_square] using
    GaussianSquare.energy_exponential_integrable (Module.finrank ℝ E) ht

theorem norm_square_exponential_integral {t : ℝ} (ht : t < 1 / 2) :
    (∫ x : E, Real.exp (t * ‖x‖ ^ 2) ∂euclideanGaussianLaw E) =
      ((Real.sqrt (1 - 2 * t))⁻¹) ^ Module.finrank ℝ E := by
  rw [euclideanGaussianLaw,
    integral_map_of_stronglyMeasurable (gaussianSynthesis_continuous E).measurable
      ((by fun_prop : Continuous (fun x : E => Real.exp (t * ‖x‖ ^ 2))).stronglyMeasurable)]
  simp only [gaussianSynthesis_norm_square]
  exact GaussianSquare.energy_exponential_integral _ ht

theorem exponential_norm_integrable (a : ℝ) :
    Integrable (fun x : E => Real.exp (a * ‖x‖)) (euclideanGaussianLaw E) := by
  have hi := (norm_square_exponential_integrable E (t := 1 / 4) (by norm_num)).const_mul
    (Real.exp (a ^ 2))
  refine hi.mono' ((by fun_prop : Continuous (fun x : E => Real.exp (a * ‖x‖))).aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (‖x‖ / 2 - a)]

theorem norm_integrable : Integrable (fun x : E => ‖x‖) (euclideanGaussianLaw E) := by
  have hi := exponential_norm_integrable E 1
  refine hi.mono' continuous_norm.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [norm_norm, one_mul]
  linarith [Real.add_one_le_exp ‖x‖]

variable {E}

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem lipschitz_growth {b : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith b f) (x : E) :
    ‖f x‖ ≤ ‖f 0‖ + (b : ℝ) * ‖x‖ := by
  have hd := hf.dist_le_mul x 0
  rw [dist_zero_right, dist_eq_norm] at hd
  have hn := norm_add_le (f x - f 0) (f 0)
  rw [sub_add_cancel] at hn
  linarith

theorem lipschitz_integrable {b : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith b f) :
    Integrable f (euclideanGaussianLaw E) := by
  have hi := (integrable_const ‖f 0‖).add ((norm_integrable E).const_mul (b : ℝ))
  exact hi.mono' hf.continuous.aestronglyMeasurable (ae_of_all _ (lipschitz_growth hf))

/-- Every real exponential moment exists, including for unbounded Lipschitz functions. -/
theorem lipschitz_exponential_integrable {b : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzWith b f) (t : ℝ) :
    Integrable (fun x => Real.exp (t * f x)) (euclideanGaussianLaw E) := by
  have hi := (exponential_norm_integrable E (|t| * b)).const_mul
    (Real.exp (|t| * ‖f 0‖))
  refine hi.mono' ((continuous_const.mul hf.continuous).rexp.aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 := mul_le_mul_of_nonneg_left (lipschitz_growth hf x) (abs_nonneg t)
  have h2 : t * f x ≤ |t| * ‖f x‖ := by
    simpa only [abs_mul, Real.norm_eq_abs] using le_abs_self (t * f x)
  nlinarith only [h1, h2]

theorem lipschitz_centered_exponential_integrable {b : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzWith b f) (t : ℝ) :
    Integrable (fun x => Real.exp (t * (f x - ∫ y, f y ∂euclideanGaussianLaw E)))
      (euclideanGaussianLaw E) := by
  have hi := (lipschitz_exponential_integrable hf t).const_mul
    (Real.exp (-t * ∫ y, f y ∂euclideanGaussianLaw E))
  convert hi using 1
  funext x
  rw [← Real.exp_add]
  congr 1
  ring

end GradientHessian.GaussianConcentration
