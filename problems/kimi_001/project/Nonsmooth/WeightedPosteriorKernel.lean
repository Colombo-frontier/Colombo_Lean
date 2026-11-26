import Nonsmooth.WeightedDensityLaw
import Nonsmooth.ConditionalEventKernel

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]

theorem kernel_weightedDensityLaw_measurable (κ : Kernel α β) [IsMarkovKernel κ]
    (w : β → ℝ) (hw : Measurable w) : Measurable (fun x => weightedDensityLaw (κ x) w) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  simp_rw [weightedDensityLaw, cond_apply MeasurableSet.univ, univ_inter,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, withDensity_apply _ hS]
  exact hw.ennreal_ofReal.lintegral_kernel.inv.mul (hw.ennreal_ofReal.setLIntegral_kernel hS)

def kernelWeightMass (κ : Kernel α β) (w : β → ℝ) (x : α) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (w z) ∂κ x

theorem kernelWeightMass_measurable (κ : Kernel α β) [IsMarkovKernel κ]
    (w : β → ℝ) (hw : Measurable w) : Measurable (kernelWeightMass κ w) :=
  hw.ennreal_ofReal.lintegral_kernel

theorem kernelWeightMass_le_one (κ : Kernel α β) [IsMarkovKernel κ]
    (w : β → ℝ) (hb : ∀ z, w z ≤ 1) (x : α) : kernelWeightMass κ w x ≤ 1 := by
  calc
    _ ≤ ∫⁻ _ : β, (1 : ℝ≥0∞) ∂κ x := lintegral_mono (fun z => by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hb z))
    _ = 1 := by simp

/-- Bayes reweighting of each conditional law, retaining the original law
when the local normalizing mass vanishes. -/
def weightedPosteriorKernel (κ : Kernel α β) [IsMarkovKernel κ]
    (w : β → ℝ) (hw : Measurable w) : Kernel α β where
  toFun x := if kernelWeightMass κ w x = 0 then κ x else weightedDensityLaw (κ x) w
  measurable' := Measurable.ite ((kernelWeightMass_measurable κ w hw) (measurableSet_singleton 0))
    κ.measurable (kernel_weightedDensityLaw_measurable κ w hw)

theorem weightedPosteriorKernel_apply (κ : Kernel α β) [IsMarkovKernel κ]
    (w : β → ℝ) (hw : Measurable w) (x : α) (hx : kernelWeightMass κ w x ≠ 0) :
    weightedPosteriorKernel κ w hw x = weightedDensityLaw (κ x) w := by
  change (if kernelWeightMass κ w x = 0 then κ x else _) = _
  rw [if_neg hx]

theorem weightedPosteriorKernel_markov (κ : Kernel α β) [IsMarkovKernel κ]
    (w : β → ℝ) (hw : Measurable w) (hb : ∀ z, w z ≤ 1) :
    IsMarkovKernel (weightedPosteriorKernel κ w hw) where
  isProbabilityMeasure x := by
    by_cases hx : kernelWeightMass κ w x = 0
    · change IsProbabilityMeasure (if kernelWeightMass κ w x = 0 then κ x else _)
      rw [if_pos hx]
      infer_instance
    · rw [weightedPosteriorKernel_apply κ w hw x hx]
      apply cond_isProbabilityMeasure_of_finite
      · simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, kernelWeightMass] using hx
      · have hn := (kernelWeightMass_le_one κ w hb x).trans_lt (by simp : (1 : ℝ≥0∞) < ∞)
        simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, kernelWeightMass] using hn.ne

theorem weightedPosteriorKernel_weighted_apply (κ : Kernel α β) [IsMarkovKernel κ]
    (w : β → ℝ) (hw : Measurable w) (hb : ∀ z, w z ≤ 1) (x : α) (S : Set β) :
    kernelWeightMass κ w x * weightedPosteriorKernel κ w hw x S =
      ((κ x).withDensity (fun z => ENNReal.ofReal (w z))) S := by
  have hm : ((κ x).withDensity (fun z => ENNReal.ofReal (w z))) univ = kernelWeightMass κ w x := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rfl
  by_cases hx : kernelWeightMass κ w x = 0
  · rw [hx, zero_mul]
    exact (measure_mono_null (subset_univ S) (hm.trans hx)).symm
  · rw [weightedPosteriorKernel_apply κ w hw x hx, weightedDensityLaw,
      cond_apply MeasurableSet.univ, univ_inter, hm, ← mul_assoc,
      ENNReal.mul_inv_cancel hx ((kernelWeightMass_le_one κ w hb x).trans_lt (by simp)).ne, one_mul]

end
end Nonsmooth
