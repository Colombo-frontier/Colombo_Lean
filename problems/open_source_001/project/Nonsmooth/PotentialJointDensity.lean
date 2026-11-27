import Nonsmooth.PotentialSliceKernel
import Nonsmooth.ConditionalEventBayes

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def potentialJointMeasure (V : ℝ → ℝ → ℝ) : Measure (ℝ × ℝ) :=
  ((volume : Measure ℝ).prod volume).withDensity
    (fun p => ENNReal.ofReal (Real.exp (-V p.1 p.2)))

def potentialJointLaw (V : ℝ → ℝ → ℝ) : Measure (ℝ × ℝ) := (potentialJointMeasure V)[|univ]

instance potentialJointLaw_finite (V : ℝ → ℝ → ℝ) : IsFiniteMeasure (potentialJointLaw V) := by
  by_cases htop : potentialJointMeasure V univ = ∞
  · simp only [potentialJointLaw, ProbabilityTheory.cond, htop, ENNReal.inv_top, zero_smul]
    infer_instance
  · by_cases hzero : potentialJointMeasure V univ = 0
    · rw [potentialJointLaw, cond_eq_zero_of_meas_eq_zero hzero]
      infer_instance
    · letI := cond_isProbabilityMeasure_of_finite hzero htop
      change IsFiniteMeasure ((potentialJointMeasure V)[|univ])
      infer_instance

/-- Fubini disintegration of the actual two-dimensional density, before normalization. -/
theorem potentialJointMeasure_disintegrates (V : ℝ → ℝ → ℝ)
    (hV : Measurable (Function.uncurry V)) (hi : ∀ t, Integrable (fun x => Real.exp (-V t x))) :
    potentialJointMeasure V =
      (volume.withDensity (fun t => ENNReal.ofReal (potentialPartition V t))) ⊗ₘ potentialSliceKernel V hV := by
  letI := potentialSliceKernel_markov V hV hi
  have hw : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-V p.1 p.2))) :=
    (Real.continuous_exp.measurable.comp hV.neg).ennreal_ofReal
  ext A hA
  rw [potentialJointMeasure, withDensity_apply _ hA,
    Measure.compProd_apply hA, lintegral_withDensity_eq_lintegral_mul _
      (potentialPartition_measurable V hV).ennreal_ofReal (Kernel.measurable_kernel_prodMk_left hA),
    ← lintegral_indicator hA, lintegral_prod _ (hw.indicator hA).aemeasurable]
  apply lintegral_congr
  intro t
  simp only [Pi.mul_apply]
  rw [potentialSliceKernel_weighted_apply V hV t (hi t),
    withDensity_apply _ (measurable_prodMk_left hA),
    ← lintegral_indicator (measurable_prodMk_left hA)]
  apply lintegral_congr
  intro x
  by_cases hx : (t, x) ∈ A
  · simp [hx]
  · simp [hx]

theorem potentialJointLaw_disintegrates (V : ℝ → ℝ → ℝ)
    (hV : Measurable (Function.uncurry V)) (hi : ∀ t, Integrable (fun x => Real.exp (-V t x))) :
    potentialJointLaw V = realDensityLaw (potentialPartition V) ⊗ₘ potentialSliceKernel V hV := by
  letI := potentialSliceKernel_markov V hV hi
  rw [potentialJointLaw, potentialJointMeasure_disintegrates V hV hi,
    ProbabilityTheory.cond, Measure.restrict_univ, Measure.compProd_apply_univ,
    realDensityLaw, ProbabilityTheory.cond, Measure.restrict_univ, Measure.compProd_smul_left]

theorem potentialJointLaw_probability (V : ℝ → ℝ → ℝ)
    (hi : Integrable (fun p : ℝ × ℝ => Real.exp (-V p.1 p.2)) ((volume : Measure ℝ).prod volume)) :
    IsProbabilityMeasure (potentialJointLaw V) := by
  have hm : potentialJointMeasure V univ =
      ENNReal.ofReal (∫ p : ℝ × ℝ, Real.exp (-V p.1 p.2) ∂(volume : Measure ℝ).prod volume) := by
    rw [potentialJointMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => (Real.exp_pos _).le))]
  apply cond_isProbabilityMeasure_of_finite
  · rw [hm]
    exact (ENNReal.ofReal_pos.mpr (integral_exp_pos hi)).ne'
  · rw [hm]
    exact ENNReal.ofReal_ne_top

theorem potentialJointLaw_marginal (V : ℝ → ℝ → ℝ)
    (hV : Measurable (Function.uncurry V)) (hi : ∀ t, Integrable (fun x => Real.exp (-V t x))) :
    (potentialJointLaw V).map Prod.fst = realDensityLaw (potentialPartition V) := by
  letI := potentialSliceKernel_markov V hV hi
  letI : SFinite (realDensityLaw (potentialPartition V)) := by
    unfold realDensityLaw ProbabilityTheory.cond
    infer_instance
  rw [potentialJointLaw_disintegrates V hV hi, ← Measure.fst, Measure.fst_compProd]

/-- The normalized scalar slice law is the actual regular conditional posterior
of the second coordinate, almost everywhere under the actual first marginal. -/
theorem potentialJointLaw_posterior (V : ℝ → ℝ → ℝ)
    (hV : Measurable (Function.uncurry V)) (hi : ∀ t, Integrable (fun x => Real.exp (-V t x))) :
    ∀ᵐ t ∂realDensityLaw (potentialPartition V),
      condDistrib Prod.snd Prod.fst (potentialJointLaw V) t =
        realDensityLaw (fun x => Real.exp (-V t x)) := by
  letI := potentialSliceKernel_markov V hV hi
  have hpair : (potentialJointLaw V).map (fun p : ℝ × ℝ => (p.1, p.2)) =
      ((potentialJointLaw V).map Prod.fst) ⊗ₘ potentialSliceKernel V hV := by
    change (potentialJointLaw V).map id = _
    rw [Measure.map_id]
    rw [potentialJointLaw_marginal V hV hi]
    exact potentialJointLaw_disintegrates V hV hi
  have he := (condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    measurable_fst measurable_snd hpair).symm
  rw [potentialJointLaw_marginal V hV hi] at he
  filter_upwards [he] with t ht
  exact ht.symm

end
end Nonsmooth
