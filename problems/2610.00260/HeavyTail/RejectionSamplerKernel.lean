import HeavyTail.RejectionSampler
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
History-dependent rejection sampling as a genuine Markov kernel. At each
history the raw law is frozen during retries. The kernel is defined by the
actual first-acceptance sampler on iid raw paths, and its measurability follows
from the proved output-law identity. Laws may change arbitrarily between
histories; variation of the raw law within one retry loop is outside this file.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HeavyTail

variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]

theorem rejectionSampler_law_measurable (κ : Kernel H Ω) [IsMarkovKernel κ]
    {A : Set (H × Ω)} (hA : MeasurableSet A)
    (hpos : ∀ h, κ h (Prod.mk h ⁻¹' A) ≠ 0) :
    Measurable (fun h => (iidRawLaw (κ h)).map (rejectionSample (Prod.mk h ⁻¹' A))) := by
  apply Measure.measurable_of_measurable_coe
  intro T hT
  have he : (fun h => (iidRawLaw (κ h)).map (rejectionSample (Prod.mk h ⁻¹' A)) T) =
      (fun h => (κ h (Prod.mk h ⁻¹' A))⁻¹ * κ h (Prod.mk h ⁻¹' (A ∩ Prod.snd ⁻¹' T))) := by
    funext h
    rw [rejectionSample_map (κ h) (hA.preimage measurable_prodMk_left) (hpos h),
      ProbabilityTheory.cond, Measure.smul_apply, Measure.restrict_apply hT]
    simp only [smul_eq_mul, preimage_inter, preimage_preimage, Function.comp_def,
      preimage_id', inter_comm]
  rw [he]
  exact (Kernel.measurable_kernel_prodMk_left (κ := κ) hA).inv.mul
    (Kernel.measurable_kernel_prodMk_left (κ := κ) (hA.inter (hT.preimage measurable_snd)))

def rejectionSamplerKernel (κ : Kernel H Ω) [IsMarkovKernel κ]
    {A : Set (H × Ω)} (hA : MeasurableSet A)
    (hpos : ∀ h, κ h (Prod.mk h ⁻¹' A) ≠ 0) : Kernel H Ω where
  toFun h := (iidRawLaw (κ h)).map (rejectionSample (Prod.mk h ⁻¹' A))
  measurable' := rejectionSampler_law_measurable κ hA hpos

theorem rejectionSamplerKernel_apply (κ : Kernel H Ω) [IsMarkovKernel κ]
    {A : Set (H × Ω)} (hA : MeasurableSet A)
    (hpos : ∀ h, κ h (Prod.mk h ⁻¹' A) ≠ 0) (h : H) :
    rejectionSamplerKernel κ hA hpos h =
      (iidRawLaw (κ h)).map (rejectionSample (Prod.mk h ⁻¹' A)) := rfl

theorem rejectionSamplerKernel_eq_cond (κ : Kernel H Ω) [IsMarkovKernel κ]
    {A : Set (H × Ω)} (hA : MeasurableSet A)
    (hpos : ∀ h, κ h (Prod.mk h ⁻¹' A) ≠ 0) (h : H) :
    rejectionSamplerKernel κ hA hpos h = ProbabilityTheory.cond (κ h) (Prod.mk h ⁻¹' A) :=
  rejectionSample_map (κ h) (hA.preimage measurable_prodMk_left) (hpos h)

instance rejectionSamplerKernel_markov (κ : Kernel H Ω) [IsMarkovKernel κ]
    {A : Set (H × Ω)} (hA : MeasurableSet A)
    (hpos : ∀ h, κ h (Prod.mk h ⁻¹' A) ≠ 0) :
    IsMarkovKernel (rejectionSamplerKernel κ hA hpos) := by
  constructor
  intro h
  rw [rejectionSamplerKernel_eq_cond]
  exact ProbabilityTheory.cond_isProbabilityMeasure (hpos h)

end HeavyTail
