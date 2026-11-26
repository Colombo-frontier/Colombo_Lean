import NCBall.GaussianConjugacy

/-! # A translated Gaussian square has a small negative exponential moment

This is the analytic building block for an exponential small-ball estimate;
it is uniform in the Gaussian mean and in the center of the target ball.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace NCBall

theorem gaussianLaplace_integrable (μ y : ℝ) (v t : ℝ≥0) :
    Integrable (fun x : ℝ => Real.exp (-(x - y) ^ 2 / (2 * (t : ℝ))))
      (gaussianReal μ v) := by
  have hc : Continuous (fun x : ℝ => Real.exp (-(x - y) ^ 2 / (2 * (t : ℝ)))) := by fun_prop
  apply (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)

theorem gaussianLaplace_integral (μ y : ℝ) {v t : ℝ≥0}
    (hv : 0 < v) (ht : 0 < t) :
    (∫ x : ℝ, Real.exp (-(x - y) ^ 2 / (2 * (t : ℝ))) ∂gaussianReal μ v) =
      Real.sqrt (2 * Real.pi * (t : ℝ)) * gaussianEvidenceFactor μ y v t := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hs : Real.sqrt (2 * Real.pi * (t : ℝ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hex (x : ℝ) : Real.exp (-(x - y) ^ 2 / (2 * (t : ℝ))) =
      Real.sqrt (2 * Real.pi * (t : ℝ)) * gaussianPDFReal x t y := by
    unfold gaussianPDFReal
    rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul, sub_sq_comm]
  rw [integral_gaussianReal_eq_integral_smul (ne_of_gt hv)]
  simp only [smul_eq_mul]
  simp_rw [hex]
  have hmul : (fun x => gaussianPDFReal μ v x *
      (Real.sqrt (2 * Real.pi * (t : ℝ)) * gaussianPDFReal x t y)) =
      (fun x => Real.sqrt (2 * Real.pi * (t : ℝ)) *
        (gaussianPDFReal μ v x * gaussianPDFReal x t y)) := by
    ext x
    ring
  rw [hmul, integral_const_mul, gaussian_likelihood_integral μ y hv ht]

theorem gaussianLaplace_le_three_quarters (μ y : ℝ) {v t : ℝ≥0}
    (ht : 0 < t) (htv : t ≤ v) :
    (∫ x : ℝ, Real.exp (-(x - y) ^ 2 / (2 * (t : ℝ))) ∂gaussianReal μ v) ≤ 3 / 4 := by
  have hv := lt_of_lt_of_le ht htv
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have htv' : (t : ℝ) ≤ v := by exact_mod_cast htv
  have hp : (0 : ℝ) < posteriorVar v t := by exact_mod_cast posteriorVar_pos hv ht
  have hsT : Real.sqrt (2 * Real.pi * (t : ℝ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hsV : Real.sqrt (2 * Real.pi * (v : ℝ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  let A := Real.sqrt (2 * Real.pi * (posteriorVar v t : ℝ)) /
    Real.sqrt (2 * Real.pi * (v : ℝ))
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hAsq : A ^ 2 = (t : ℝ) / ((v : ℝ) + t) := by
    dsimp [A]
    rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    simp only [posteriorVar, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_add]
    field_simp
    ring
  have hhalf : (t : ℝ) / ((v : ℝ) + t) ≤ 1 / 2 := by
    apply (div_le_iff₀ (add_pos hv' ht')).2
    linarith
  have hA : A ≤ 3 / 4 := by nlinarith
  have hex : Real.exp (-(y - μ) ^ 2 / (2 * ((v : ℝ) + t))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  rw [gaussianLaplace_integral μ y hv ht]
  have heq : Real.sqrt (2 * Real.pi * (t : ℝ)) * gaussianEvidenceFactor μ y v t =
      A * Real.exp (-(y - μ) ^ 2 / (2 * ((v : ℝ) + t))) := by
    unfold gaussianEvidenceFactor A
    field_simp
    ring
  rw [heq]
  exact (mul_le_of_le_one_right hA0 hex).trans hA

end NCBall
