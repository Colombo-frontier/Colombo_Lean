import Nonsmooth.StrongPotentialTails
import Nonsmooth.ConditioningExhaustion

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def realDensityLaw (w : ℝ → ℝ) : Measure ℝ :=
  (volume.withDensity (fun x => ENNReal.ofReal (w x)))[|univ]

theorem realDensityMeasure_mass (w : ℝ → ℝ) (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x) :
    (volume.withDensity (fun x => ENNReal.ofReal (w x))) univ = ENNReal.ofReal (∫ x, w x) := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hw (Eventually.of_forall hw0)]

theorem realDensityLaw_probability (w : ℝ → ℝ) (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x)
    (hZ : 0 < ∫ x, w x) : IsProbabilityMeasure (realDensityLaw w) := by
  apply cond_isProbabilityMeasure_of_finite
  · rw [realDensityMeasure_mass w hw hw0]
    exact (ENNReal.ofReal_pos.mpr hZ).ne'
  · rw [realDensityMeasure_mass w hw hw0]
    exact ENNReal.ofReal_ne_top

theorem realDensityLaw_memLp_two (w : ℝ → ℝ) (hwm : Measurable w) (hw : Integrable w)
    (hw0 : ∀ x, 0 ≤ w x) (hZ : 0 < ∫ x, w x)
    (hsq : Integrable (fun x : ℝ => x ^ 2 * w x)) :
    MemLp (fun x : ℝ => x) 2 (realDensityLaw w) := by
  let Q := volume.withDensity (fun x => ENNReal.ofReal (w x))
  have hid : AEStronglyMeasurable (fun x : ℝ => x) Q := measurable_id.aestronglyMeasurable
  have hbase : MemLp (fun x : ℝ => x) 2 Q := by
    apply (memLp_two_iff_integrable_sq hid).mpr
    change Integrable (fun x : ℝ => x ^ 2) (volume.withDensity (fun x => ENNReal.ofReal (w x)))
    rw [integrable_withDensity_iff hwm.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simpa only [ENNReal.toReal_ofReal (hw0 _)] using hsq
  have hm : Q univ ≠ 0 := by
    dsimp only [Q]
    rw [realDensityMeasure_mass w hw hw0]
    exact (ENNReal.ofReal_pos.mpr hZ).ne'
  simpa only [realDensityLaw, ProbabilityTheory.cond, Measure.restrict_univ] using
    hbase.smul_measure (ENNReal.inv_ne_top.mpr hm)

theorem realDensityLaw_condition_interval (w : ℝ → ℝ) (hw : Integrable w)
    (hw0 : ∀ x, 0 ≤ w x) (a b : ℝ) :
    (realDensityLaw w)[|Icc a b] = intervalDensityLaw w a b := by
  have hfinite : (volume.withDensity (fun x => ENNReal.ofReal (w x))) univ ≠ ∞ := by
    rw [realDensityMeasure_mass w hw hw0]
    exact ENNReal.ofReal_ne_top
  rw [realDensityLaw, cond_cond_eq_cond_inter' MeasurableSet.univ measurableSet_Icc hfinite,
    univ_inter, intervalDensityLaw_eq_cond_withDensity]

theorem realDensityLaw_interval_positive {a b : ℝ} (hab : a ≤ b)
    (w : ℝ → ℝ) (hwc : Continuous w) (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x)
    (hZi : 0 < ∫ x in a..b, w x) :
    (realDensityLaw w) (Icc a b) ≠ 0 := by
  have hi : (volume.withDensity (fun x => ENNReal.ofReal (w x))) (Icc a b) =
      ENNReal.ofReal (∫ x in a..b, w x) := by
    have h := intervalDensityMeasure_mass hab w hwc hw0
    rwa [intervalDensityMeasure, ← restrict_withDensity measurableSet_Icc,
      Measure.restrict_apply_univ] at h
  rw [realDensityLaw, cond_apply MeasurableSet.univ, univ_inter,
    realDensityMeasure_mass w hw hw0, hi]
  exact mul_ne_zero (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top) (ENNReal.ofReal_pos.mpr hZi).ne'

end
end Nonsmooth
