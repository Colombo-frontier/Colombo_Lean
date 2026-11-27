import Nonsmooth.VectorPotentialDifferentiation

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem realDensityLaw_vector_integral {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (w : ℝ → ℝ) (hwm : Measurable w) (hw : Integrable w)
    (hw0 : ∀ x, 0 ≤ w x) (F : ℝ → G) :
    (∫ x, F x ∂realDensityLaw w) = (∫ x : ℝ, w x)⁻¹ • ∫ x : ℝ, w x • F x := by
  rw [realDensityLaw, ProbabilityTheory.cond, Measure.restrict_univ, integral_smul_measure,
    realDensityMeasure_mass w hw hw0, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (integral_nonneg hw0)]
  rw [integral_withDensity_eq_integral_toReal_smul hwm.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hw0 _)]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem potential_partition_hasFDerivAt
    (V : E → ℝ → ℝ) (s : E → ℝ → E →L[ℝ] ℝ) (t : E)
    (hV : Continuous (Function.uncurry V)) (hs : Continuous (Function.uncurry s))
    (hdV : ∀ r x, HasFDerivAt (fun r => V r x) (s r x) r)
    {a B C : ℝ} {m : ℕ} (ha : 0 < a)
    (hVb : ∀ r ∈ Metric.ball t 1, ∀ x, a * x ^ 2 - B ≤ V r x)
    (hsb : ∀ r ∈ Metric.ball t 1, ∀ x, ‖s r x‖ ≤ C * (1 + |x| ^ m)) :
    HasFDerivAt (fun r => ∫ x : ℝ, Real.exp (-V r x))
      (-(∫ x : ℝ, Real.exp (-V t x) • s t x)) t := by
  have h := potential_vector_moment_hasFDerivAt V s (fun _ _ => (1 : ℝ)) (fun _ _ => 0) t
    hV hs continuous_const continuous_const hdV (fun r _ => hasFDerivAt_const (1 : ℝ) r)
    (C := 1) (m := 0) ha hVb (fun _ => by norm_num)
    (fun r hr x => by
      simpa only [zero_sub, norm_neg, ContinuousLinearMap.norm_smulRight_apply, norm_one, mul_one]
        using hsb r hr x)
  have he (x : ℝ) : (0 : E →L[ℝ] ℝ) - (s t x).smulRight 1 = -s t x := by
    ext v
    simp only [sub_apply, ContinuousLinearMap.zero_apply,
      ContinuousLinearMap.smulRight_apply, neg_apply, smul_eq_mul, mul_one, zero_sub]
  simpa only [smul_eq_mul, mul_one, he, smul_neg, integral_neg] using h

/-- The gradient of the actual negative log marginal is the conditional mean
of the original score, with normalization and differentiation proved. -/
theorem potential_negative_log_hasFDerivAt
    (V : E → ℝ → ℝ) (s : E → ℝ → E →L[ℝ] ℝ) (t : E)
    (hV : Continuous (Function.uncurry V)) (hs : Continuous (Function.uncurry s))
    (hdV : ∀ r x, HasFDerivAt (fun r => V r x) (s r x) r)
    {a B C : ℝ} {m : ℕ} (ha : 0 < a)
    (hVb : ∀ r ∈ Metric.ball t 1, ∀ x, a * x ^ 2 - B ≤ V r x)
    (hsb : ∀ r ∈ Metric.ball t 1, ∀ x, ‖s r x‖ ≤ C * (1 + |x| ^ m)) :
    HasFDerivAt (fun r => -Real.log (∫ x : ℝ, Real.exp (-V r x)))
      (∫ x : ℝ, s t x ∂realDensityLaw (fun x => Real.exp (-V t x))) t := by
  have hpair : Continuous (fun x : ℝ => (t, x)) := continuous_const.prodMk continuous_id
  have hw : Continuous (fun x : ℝ => Real.exp (-V t x)) := by
    simpa only [Function.uncurry, Function.comp_def, Pi.neg_apply] using Real.continuous_exp.comp (hV.comp hpair).neg
  have hi : Integrable (fun x : ℝ => Real.exp (-V t x)) := by
    have hm : AEStronglyMeasurable (fun x : ℝ => Real.exp (-V t x) • (1 : ℝ)) := by
      simpa only [smul_eq_mul, mul_one] using hw.aestronglyMeasurable
    simpa only [smul_eq_mul, mul_one] using potential_vector_weighted_integrable (V t)
      (fun _ => (1 : ℝ)) hm (C := 1) (m := 0) ha (hVb t (by simp)) (fun _ => by norm_num)
  have hz := integral_exp_pos hi
  have he := realDensityLaw_vector_integral _ hw.measurable hi (fun _ => (Real.exp_pos _).le) (s t)
  rw [he]
  convert! ((potential_partition_hasFDerivAt V s t hV hs hdV ha hVb hsb).log hz.ne').neg using 1 <;>
    simp only [Pi.neg_apply, smul_neg, neg_neg]

end
end Nonsmooth
