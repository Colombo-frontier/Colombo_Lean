import Nonsmooth.GaussianPotentialDensity
import Nonsmooth.VectorPotentialExpectation

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem standardGaussian_potential_integral (U : ℝ → ℝ) (A : ℝ) :
    (∫ x, Real.exp (A + x ^ 2 / 2 - U x) ∂gaussianReal 0 1) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp A * ∫ x, Real.exp (-U x) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  simp only [smul_eq_mul, standardGaussian_pdf_cancel]
  rw [integral_const_mul]

theorem standardGaussian_potential_integrable (U : ℝ → ℝ)
    (hi : Integrable (fun x => Real.exp (-U x))) (A : ℝ) :
    Integrable (fun x => Real.exp (A + x ^ 2 / 2 - U x)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : NNReal) ≠ 0),
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (Eventually.of_forall (fun _ => gaussianPDF_lt_top))]
  simpa only [gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _),
    smul_eq_mul, standardGaussian_pdf_cancel] using
    hi.const_mul ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp A)

/-- Integrating one standard Gaussian coordinate gives precisely the
negative-log Lebesgue marginal potential, after normalization. -/
theorem gaussian_coordinate_weight_marginal {F : Type} [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [SFinite μ]
    (V : F → ℝ → ℝ) (hV : Continuous (Function.uncurry V))
    {a B : ℝ} (ha : 0 < a) (hb : ∀ t x, a * x ^ 2 - B ≤ V t x) :
    (weightedDensityLaw (μ.prod (gaussianReal 0 1))
      (fun p => Real.exp ((‖p.1‖ ^ 2 + p.2 ^ 2) / 2 - V p.1 p.2))).map Prod.fst =
        weightedDensityLaw μ
          (gaussianPotentialWeight (fun t => -Real.log (∫ x, Real.exp (-V t x)))) := by
  let Z : F → ℝ := fun t => ∫ x, Real.exp (-V t x)
  have hi (t : F) : Integrable (fun x => Real.exp (-V t x)) :=
    potential_negative_exp_integrable (V t)
      (hV.comp (continuous_const.prodMk continuous_id)) ha (hb t)
  have hz (t : F) : 0 < Z t := integral_exp_pos (hi t)
  have hZm : Measurable Z := hV.measurable.neg.exp.stronglyMeasurable.integral_prod_right'.measurable
  have hwm : Measurable
      (gaussianPotentialWeight (fun t => -Real.log (∫ x, Real.exp (-V t x)))) :=
    (((continuous_norm.pow 2).measurable.div_const 2).sub hZm.log.neg).exp
  have he (t : F) (x : ℝ) :
      (‖t‖ ^ 2 + x ^ 2) / 2 - V t x = ‖t‖ ^ 2 / 2 + x ^ 2 / 2 - V t x := by ring
  have hw : Measurable (fun p : F × ℝ => Real.exp ((‖p.1‖ ^ 2 + p.2 ^ 2) / 2 - V p.1 p.2)) :=
    ((((continuous_fst.norm.pow 2).add (continuous_snd.pow 2)).measurable.div_const 2).sub hV.measurable).exp
  rw [weightedDensityLaw_product_marginal μ _ _ hw (fun _ => (Real.exp_pos _).le)
    (fun t => by simp_rw [he]; exact standardGaussian_potential_integrable (V t) (hi t) _)]
  have hweight : (fun t => ∫ x, Real.exp ((‖t‖ ^ 2 + x ^ 2) / 2 - V t x) ∂gaussianReal 0 1) =
      fun t => (Real.sqrt (2 * Real.pi))⁻¹ *
        gaussianPotentialWeight (fun t => -Real.log (∫ x, Real.exp (-V t x))) t := by
    funext t
    simp_rw [he]
    rw [standardGaussian_potential_integral]
    change _ = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (‖t‖ ^ 2 / 2 - -Real.log (Z t))
    rw [sub_neg_eq_add, Real.exp_add, Real.exp_log (hz t)]
    exact mul_assoc _ _ _
  rw [hweight, weightedDensityLaw_const_mul μ _ hwm _ (by positivity)]

end
end Nonsmooth
