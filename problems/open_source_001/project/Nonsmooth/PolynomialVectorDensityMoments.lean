import Nonsmooth.VectorGaussianEnvelope
import Nonsmooth.PolynomialDensityMoments

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem realDensityLaw_vector_integrable_of_weighted (w : ℝ → ℝ) (F : ℝ → G)
    (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hi : Integrable (fun x => w x • F x)) :
    Integrable F (realDensityLaw w) := by
  have hraw : Integrable F (volume.withDensity (fun x => ENNReal.ofReal (w x))) := by
    rw [integrable_withDensity_iff_integrable_smul' hwm.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simpa only [ENNReal.toReal_ofReal (hw0 _)] using hi
  by_cases hz : (volume.withDensity (fun x => ENNReal.ofReal (w x))) univ = 0
  · rw [realDensityLaw, cond_eq_zero_of_meas_eq_zero hz]
    exact integrable_zero_measure
  · simpa only [realDensityLaw, ProbabilityTheory.cond, Measure.restrict_univ] using
      hraw.smul_measure (ENNReal.inv_ne_top.mpr hz)

theorem potential_vector_polynomial_integrable (V : ℝ → ℝ) (F : ℝ → G)
    (hV : Continuous V) (hF : Continuous F) {a B C : ℝ} {m : ℕ} (ha : 0 < a)
    (hVb : ∀ x, a * x ^ 2 - B ≤ V x) (hFb : ∀ x, ‖F x‖ ≤ C * (1 + |x| ^ m)) :
    Integrable F (realDensityLaw (fun x => Real.exp (-V x))) := by
  have hw : Continuous (fun x => Real.exp (-V x)) := Real.continuous_exp.comp hV.neg
  exact realDensityLaw_vector_integrable_of_weighted _ F hw.measurable (fun _ => (Real.exp_pos _).le)
    (potential_vector_weighted_integrable V F (hw.smul hF).aestronglyMeasurable ha hVb hFb)

theorem potential_vector_polynomial_memLp_two (V : ℝ → ℝ) (F : ℝ → G)
    (hV : Continuous V) (hF : Continuous F) {a B C : ℝ} {m : ℕ} (ha : 0 < a) (hC : 0 ≤ C)
    (hVb : ∀ x, a * x ^ 2 - B ≤ V x) (hFb : ∀ x, ‖F x‖ ≤ C * (1 + |x| ^ m)) :
    MemLp F 2 (realDensityLaw (fun x => Real.exp (-V x))) := by
  apply (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mpr
  apply potential_vector_polynomial_integrable V (fun x => ‖F x‖ ^ 2) hV (hF.norm.pow 2) ha hVb
  intro x
  simpa only [Real.norm_eq_abs] using
    polynomial_growth_square (fun x => ‖F x‖) hC
      (fun x => by simpa only [abs_of_nonneg (norm_nonneg _)] using hFb x) x

end
end Nonsmooth
