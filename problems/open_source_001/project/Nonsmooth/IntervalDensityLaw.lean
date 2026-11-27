import Nonsmooth.IntervalDensityVariance
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def intervalDensityMeasure (w : ℝ → ℝ) (a b : ℝ) : Measure ℝ :=
  (volume.restrict (Icc a b)).withDensity (fun x => ENNReal.ofReal (w x))

def intervalDensityLaw (w : ℝ → ℝ) (a b : ℝ) : Measure ℝ :=
  (intervalDensityMeasure w a b)[|univ]

theorem intervalDensityMeasure_mass {a b : ℝ} (hab : a ≤ b)
    (w : ℝ → ℝ) (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x) :
    intervalDensityMeasure w a b univ = ENNReal.ofReal (∫ x in a..b, w x) := by
  rw [intervalDensityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hw.continuousOn.integrableOn_Icc
      (Eventually.of_forall hw0), integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

theorem intervalDensityLaw_probability {a b : ℝ} (hab : a ≤ b)
    (w : ℝ → ℝ) (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
    (hZ : 0 < ∫ x in a..b, w x) : IsProbabilityMeasure (intervalDensityLaw w a b) := by
  apply cond_isProbabilityMeasure_of_finite
  · rw [intervalDensityMeasure_mass hab w hw hw0]
    exact (ENNReal.ofReal_pos.mpr hZ).ne'
  · rw [intervalDensityMeasure_mass hab w hw hw0]
    exact ENNReal.ofReal_ne_top

theorem intervalDensityLaw_integral {a b : ℝ} (hab : a ≤ b)
    (w : ℝ → ℝ) (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x) (f : ℝ → ℝ) :
    (∫ x, f x ∂intervalDensityLaw w a b) =
      (∫ x in a..b, f x * w x) / (∫ x in a..b, w x) := by
  rw [intervalDensityLaw, ProbabilityTheory.cond, Measure.restrict_univ, integral_smul_measure,
    intervalDensityMeasure_mass hab w hw hw0, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hab (fun x _ => hw0 x)), smul_eq_mul]
  rw [intervalDensityMeasure, integral_withDensity_eq_integral_toReal_smul
    hw.measurable.ennreal_ofReal (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hw0 _), smul_eq_mul]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, div_eq_inv_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  exact mul_comm _ _

/-- The interval probability law with density proportional to exp(-U) has variance
at most the reciprocal of the strong convexity parameter. -/
theorem convex_potential_interval_law_variance {a b ρ : ℝ} (hab : a < b) (hρ : 0 < ρ)
    (U s : ℝ → ℝ) (hU : Continuous U) (hs : Continuous s)
    (hd : ∀ x ∈ Icc a b, HasDerivAt U (s x) x)
    (hmono : MonotoneOn (fun x => s x - ρ * x) (Icc a b)) :
    variance (fun x : ℝ => x) (intervalDensityLaw (fun x => Real.exp (-U x)) a b) ≤ ρ⁻¹ := by
  have hw : Continuous (fun x => Real.exp (-U x)) := Real.continuous_exp.comp hU.neg
  have hw0 : ∀ x, 0 ≤ Real.exp (-U x) := fun x => (Real.exp_pos _).le
  have hid : Measurable (fun x : ℝ => x) := measurable_id
  rw [variance_eq_integral hid.aemeasurable,
    intervalDensityLaw_integral hab.le _ hw hw0 (fun x => x),
    intervalDensityLaw_integral hab.le _ hw hw0]
  exact convex_potential_interval_variance hab hρ U s hU hs hd hmono

theorem intervalDensityLaw_eq_cond_withDensity (w : ℝ → ℝ) (a b : ℝ) :
    intervalDensityLaw w a b =
      (volume.withDensity (fun x => ENNReal.ofReal (w x)))[|Icc a b] := by
  rw [intervalDensityLaw, intervalDensityMeasure, ← restrict_withDensity measurableSet_Icc,
    ProbabilityTheory.cond, Measure.restrict_apply_univ, Measure.restrict_univ]
  rfl

theorem strong_score_interval_law_variance {a b ρ : ℝ} (hab : a ≤ b) (hρ : 0 < ρ)
    (w s : ℝ → ℝ) (hw : Continuous w) (hs : Continuous s)
    (hw0 : ∀ x, 0 ≤ w x) (hZ : 0 < ∫ x in a..b, w x)
    (hd : ∀ x ∈ Icc a b, HasDerivAt w (-s x * w x) x)
    (hmono : MonotoneOn (fun x => s x - ρ * x) (Icc a b)) :
    variance (fun x : ℝ => x) (intervalDensityLaw w a b) ≤ ρ⁻¹ := by
  have hid : Measurable (fun x : ℝ => x) := measurable_id
  rw [variance_eq_integral hid.aemeasurable,
    intervalDensityLaw_integral hab w hw hw0 (fun x => x),
    intervalDensityLaw_integral hab w hw hw0]
  exact strong_score_interval_variance hab hρ w s hw hs (fun x _ => hw0 x) hZ hd hmono


end
end Nonsmooth
