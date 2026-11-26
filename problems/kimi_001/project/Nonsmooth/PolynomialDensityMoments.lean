import Nonsmooth.GaussianPolynomialEnvelope

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem realDensityLaw_integrable_of_weighted (w f : ℝ → ℝ) (hwm : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) (hi : Integrable (fun x => f x * w x)) :
    Integrable f (realDensityLaw w) := by
  have hraw : Integrable f (volume.withDensity (fun x => ENNReal.ofReal (w x))) := by
    rw [integrable_withDensity_iff hwm.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simpa only [ENNReal.toReal_ofReal (hw0 _)] using hi
  by_cases hz : (volume.withDensity (fun x => ENNReal.ofReal (w x))) univ = 0
  · rw [realDensityLaw, cond_eq_zero_of_meas_eq_zero hz]
    exact integrable_zero_measure
  · simpa only [realDensityLaw, ProbabilityTheory.cond, Measure.restrict_univ] using
      hraw.smul_measure (ENNReal.inv_ne_top.mpr hz)

theorem polynomial_growth_square (F : ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C) {m : ℕ}
    (hF : ∀ x, |F x| ≤ C * (1 + |x| ^ m)) (x : ℝ) :
    |(F x) ^ 2| ≤ (2 * C ^ 2) * (1 + |x| ^ (2 * m)) := by
  have hpow : |x| ^ (2 * m) = (|x| ^ m) ^ 2 := by rw [Nat.mul_comm, pow_mul]
  have hp : (1 + |x| ^ m) ^ 2 ≤ 2 * (1 + |x| ^ (2 * m)) := by
    rw [hpow]
    nlinarith [sq_nonneg (|x| ^ m - 1)]
  have hs := (sq_le_sq₀ (abs_nonneg (F x))
    (mul_nonneg hC (by positivity : 0 ≤ 1 + |x| ^ m))).mpr (hF x)
  rw [sq_abs, mul_pow] at hs
  rw [abs_of_nonneg (sq_nonneg (F x))]
  have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg C)
  nlinarith

theorem polynomial_growth_coordinate_product (F : ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ x, |F x| ≤ C * (1 + |x| ^ 2)) (x : ℝ) :
    |x * F x| ≤ (2 * C) * (1 + |x| ^ 4) := by
  have hx : |x| ≤ 1 + |x| ^ 2 := by nlinarith [sq_nonneg (|x| - 1)]
  have hpow : (1 + |x| ^ 2) ^ 2 ≤ 2 * (1 + |x| ^ 4) := by
    nlinarith [sq_nonneg (|x| ^ 2 - 1), sq_nonneg (|x| ^ 2)]
  have h1 := mul_le_mul (hF x) hx (abs_nonneg x)
    (mul_nonneg hC (by positivity : 0 ≤ 1 + |x| ^ 2))
  have h2 := mul_le_mul_of_nonneg_left hpow hC
  rw [abs_mul]
  nlinarith

theorem real_potential_polynomial_integrable (V F : ℝ → ℝ)
    (hV : Continuous V) (hF : Continuous F) {a C : ℝ} {m : ℕ} (ha : 0 < a)
    (hVb : ∀ x, a * x ^ 2 ≤ V x) (hFb : ∀ x, |F x| ≤ C * (1 + |x| ^ m)) :
    Integrable F (realDensityLaw (fun x => Real.exp (-V x))) := by
  have hw : Continuous (fun x => Real.exp (-V x)) := Real.continuous_exp.comp hV.neg
  exact realDensityLaw_integrable_of_weighted _ F hw.measurable (fun _ => (Real.exp_pos _).le)
    (potential_weighted_polynomial_integrable V F (hF.mul hw).aestronglyMeasurable ha hVb hFb)

theorem real_potential_polynomial_memLp_two (V F : ℝ → ℝ)
    (hV : Continuous V) (hF : Continuous F) {a C : ℝ} {m : ℕ} (ha : 0 < a) (hC : 0 ≤ C)
    (hVb : ∀ x, a * x ^ 2 ≤ V x) (hFb : ∀ x, |F x| ≤ C * (1 + |x| ^ m)) :
    MemLp F 2 (realDensityLaw (fun x => Real.exp (-V x))) := by
  apply (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).mpr
  exact real_potential_polynomial_integrable V (fun x => (F x) ^ 2) hV (hF.pow 2) ha hVb
    (polynomial_growth_square F hC hFb)

end
end Nonsmooth
