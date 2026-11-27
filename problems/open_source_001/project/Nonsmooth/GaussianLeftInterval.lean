import Nonsmooth.GaussianWinnerCovariance

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem standardGaussianPDF_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, sub_zero, mul_one]
  convert (((((hasDerivAt_id x).pow 2).neg).div_const 2).exp).const_mul
    (1 / Real.sqrt (2 * Real.pi)) using 1 <;>
      first | rfl | (simp only [id_eq, Pi.neg_apply, Pi.pow_apply]; ring_nf)

theorem standardGaussian_left_interval_weighted_second {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0) :
    (∫ x in a..b, (x - b) ^ 2 * gaussianPDFReal 0 1 x) ≤
      ∫ x in a..b, gaussianPDFReal 0 1 x := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => (y - b) * gaussianPDFReal 0 1 y)
      (gaussianPDFReal 0 1 x - (x - b) * x * gaussianPDFReal 0 1 x) x := by
    convert ((hasDerivAt_id x).sub_const b).mul (standardGaussianPDF_hasDerivAt x) using 1 <;>
      first | rfl | (simp only [id_eq]; ring_nf)
  have hp : Continuous (gaussianPDFReal 0 1) :=
    continuous_iff_continuousAt.mpr (fun x => (standardGaussianPDF_hasDerivAt x).continuousAt)
  have hq : Continuous (fun x : ℝ => (x - b) * x * gaussianPDFReal 0 1 x) := by fun_prop
  have hs : Continuous (fun x : ℝ => (x - b) ^ 2 * gaussianPDFReal 0 1 x) := by fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((hp.sub hq).intervalIntegrable a b)
  rw [intervalIntegral.integral_sub (hp.intervalIntegrable a b) (hq.intervalIntegrable a b)] at he
  have hbd : 0 ≤ (b - b) * gaussianPDFReal 0 1 b - (a - b) * gaussianPDFReal 0 1 a := by
    have hnon := gaussianPDFReal_nonneg 0 1 a
    nlinarith
  have hstep : (∫ x in a..b, (x - b) * x * gaussianPDFReal 0 1 x) ≤
      ∫ x in a..b, gaussianPDFReal 0 1 x := by linarith
  apply le_trans ?_ hstep
  apply intervalIntegral.integral_mono_on hab (hs.intervalIntegrable a b) (hq.intervalIntegrable a b)
  intro x hx
  apply mul_le_mul_of_nonneg_right ?_ (gaussianPDFReal_nonneg 0 1 x)
  nlinarith [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hx.2) hb]

theorem standardGaussian_setIntegral_density (A : Set ℝ) (hA : MeasurableSet A) (f : ℝ → ℝ) :
    (∫ x in A, f x ∂gaussianReal 0 1) = ∫ x in A, gaussianPDFReal 0 1 x * f x := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : NNReal) ≠ 0),
    setIntegral_withDensity_eq_setIntegral_toReal_smul (measurable_gaussianPDF 0 1)
      (Eventually.of_forall (fun _ => gaussianPDF_lt_top)) f hA]
  simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), smul_eq_mul]

/-- On any interval ending at a nonpositive point, the standard Gaussian squared
distance to the right endpoint has unnormalized expectation at most the interval mass. -/
theorem standardGaussian_left_interval_second (a : ℝ) {b : ℝ} (hb : b ≤ 0) :
    (∫ x in Icc a b, (x - b) ^ 2 ∂gaussianReal 0 1) ≤ (gaussianReal 0 1).real (Icc a b) := by
  by_cases hab : a ≤ b
  · rw [standardGaussian_setIntegral_density _ measurableSet_Icc]
    have hm : (gaussianReal 0 1).real (Icc a b) = ∫ x in Icc a b, gaussianPDFReal 0 1 x := by
      rw [measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num : (1 : NNReal) ≠ 0),
        ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg 0 1))]
    rw [hm, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hab]
    simpa only [mul_comm] using standardGaussian_left_interval_weighted_second hab hb
  · have he : Icc a b = ∅ := Icc_eq_empty hab
    simp [he]

end
end Nonsmooth
