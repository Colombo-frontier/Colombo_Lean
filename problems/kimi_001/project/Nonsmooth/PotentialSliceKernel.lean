import Nonsmooth.ParametricPotentialExpectation
import Nonsmooth.ConditionalEventKernel

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem potentialPartition_measurable (V : ℝ → ℝ → ℝ)
    (hV : Measurable (Function.uncurry V)) : Measurable (potentialPartition V) := by
  have hw : Measurable (fun p : ℝ × ℝ => Real.exp (-V p.1 p.2)) :=
    Real.continuous_exp.measurable.comp hV.neg
  exact hw.stronglyMeasurable.integral_prod_right'.measurable

theorem potentialSliceLaw_measurable (V : ℝ → ℝ → ℝ)
    (hV : Measurable (Function.uncurry V)) :
    Measurable (fun t => realDensityLaw (fun x => Real.exp (-V t x))) := by
  have hw : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-V p.1 p.2))) :=
    (Real.continuous_exp.measurable.comp hV.neg).ennreal_ofReal
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hmass : Measurable (fun t =>
      (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V t x)))) univ) := by
    simp_rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hw.lintegral_prod_right' (ν := volume)
  have hevent : Measurable (fun t =>
      (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V t x)))) A) := by
    simp_rw [withDensity_apply _ hA]
    exact hw.lintegral_prod_right' (ν := volume.restrict A)
  have he (t : ℝ) : realDensityLaw (fun x => Real.exp (-V t x)) A =
      ((volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V t x)))) univ)⁻¹ *
        (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V t x)))) A := by
    rw [realDensityLaw, cond_apply MeasurableSet.univ, univ_inter]
  simp_rw [he]
  exact hmass.inv.mul hevent

def potentialSliceKernel (V : ℝ → ℝ → ℝ) (hV : Measurable (Function.uncurry V)) : Kernel ℝ ℝ where
  toFun t := realDensityLaw (fun x => Real.exp (-V t x))
  measurable' := potentialSliceLaw_measurable V hV

theorem potentialSliceKernel_apply (V : ℝ → ℝ → ℝ) (hV : Measurable (Function.uncurry V)) (t : ℝ) :
    potentialSliceKernel V hV t = realDensityLaw (fun x => Real.exp (-V t x)) := rfl

theorem potentialSliceKernel_markov (V : ℝ → ℝ → ℝ) (hV : Measurable (Function.uncurry V))
    (hi : ∀ t, Integrable (fun x => Real.exp (-V t x))) : IsMarkovKernel (potentialSliceKernel V hV) where
  isProbabilityMeasure t := realDensityLaw_probability _ (hi t)
    (fun _ => (Real.exp_pos _).le) (integral_exp_pos (hi t))

theorem potentialSliceKernel_weighted_measure (V : ℝ → ℝ → ℝ) (hV : Measurable (Function.uncurry V))
    (t : ℝ) (hi : Integrable (fun x => Real.exp (-V t x))) :
    ENNReal.ofReal (potentialPartition V t) • potentialSliceKernel V hV t =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V t x))) := by
  have hZ : 0 < potentialPartition V t := integral_exp_pos hi
  rw [potentialSliceKernel_apply, realDensityLaw, ProbabilityTheory.cond, Measure.restrict_univ,
    smul_smul, realDensityMeasure_mass _ hi (fun _ => (Real.exp_pos _).le)]
  change (ENNReal.ofReal (potentialPartition V t) * (ENNReal.ofReal (potentialPartition V t))⁻¹) • _ = _
  rw [ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hZ).ne' ENNReal.ofReal_ne_top, one_smul]

theorem potentialSliceKernel_weighted_apply (V : ℝ → ℝ → ℝ) (hV : Measurable (Function.uncurry V))
    (t : ℝ) (hi : Integrable (fun x => Real.exp (-V t x))) (A : Set ℝ) :
    ENNReal.ofReal (potentialPartition V t) * potentialSliceKernel V hV t A =
      (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V t x)))) A := by
  have he := congrArg (fun μ : Measure ℝ => μ A) (potentialSliceKernel_weighted_measure V hV t hi)
  simpa only [Measure.smul_apply, smul_eq_mul] using he

end
end Nonsmooth
