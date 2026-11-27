import Nonsmooth.GaussianProjectionPosterior

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]

theorem kernel_conditioning_measurable (κ : Kernel α β) [IsMarkovKernel κ]
    {A : Set β} (hA : MeasurableSet A) : Measurable (fun x : α => (κ x)[|A]) := by
  apply Measure.measurable_of_measurable_coe
  intro B hB
  simp_rw [cond_apply hA]
  exact (κ.measurable_coe hA).inv.mul (κ.measurable_coe (hA.inter hB))

/-- Normalize an event within each conditional law. The original conditional law
is retained at parameters where the event has zero probability. -/
def conditionalEventKernel (κ : Kernel α β) [IsMarkovKernel κ]
    (A : Set β) (hA : MeasurableSet A) : Kernel α β where
  toFun x := if κ x A = 0 then κ x else (κ x)[|A]
  measurable' := Measurable.ite ((κ.measurable_coe hA) (measurableSet_singleton 0))
    κ.measurable (kernel_conditioning_measurable κ hA)

theorem conditionalEventKernel_apply (κ : Kernel α β) [IsMarkovKernel κ]
    (A : Set β) (hA : MeasurableSet A) (x : α) (hx : κ x A ≠ 0) :
    conditionalEventKernel κ A hA x = (κ x)[|A] := by
  change (if κ x A = 0 then κ x else (κ x)[|A]) = _
  rw [if_neg hx]

instance conditionalEventKernel_markov (κ : Kernel α β) [IsMarkovKernel κ]
    (A : Set β) (hA : MeasurableSet A) : IsMarkovKernel (conditionalEventKernel κ A hA) where
  isProbabilityMeasure x := by
    by_cases hx : κ x A = 0
    · change IsProbabilityMeasure (if κ x A = 0 then κ x else (κ x)[|A])
      rw [if_pos hx]
      infer_instance
    · rw [conditionalEventKernel_apply κ A hA x hx]
      exact cond_isProbabilityMeasure hx

theorem conditionalEventKernel_weighted_apply (κ : Kernel α β) [IsMarkovKernel κ]
    (A : Set β) (hA : MeasurableSet A) (x : α) (B : Set β) :
    κ x A * conditionalEventKernel κ A hA x B = κ x (A ∩ B) := by
  by_cases hx : κ x A = 0
  · rw [hx, zero_mul, measure_mono_null inter_subset_left hx]
  · rw [conditionalEventKernel_apply κ A hA x hx, cond_apply hA,
      ← mul_assoc, ENNReal.mul_inv_cancel hx (measure_ne_top _ _), one_mul]

theorem kernel_event_density_finite (ν : Measure α) [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] (A : Set β) :
    IsFiniteMeasure (ν.withDensity (fun x => κ x A)) := by
  apply isFiniteMeasure_of_le ν
  calc
    _ ≤ ν.withDensity (fun _ => 1) := withDensity_mono
      (Eventually.of_forall (fun x => prob_le_one))
    _ = ν := by simp

/-- Exact Bayes disintegration before normalization, including zero-mass slices. -/
theorem conditionalEventKernel_restrict_disintegration (ν : Measure α) [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] (A : Set β) (hA : MeasurableSet A) :
    (ν ⊗ₘ κ).restrict (Prod.snd ⁻¹' A) =
      (ν.withDensity (fun x => κ x A)) ⊗ₘ conditionalEventKernel κ A hA := by
  letI := kernel_event_density_finite ν κ A
  ext S hS
  rw [Measure.restrict_apply hS, Measure.compProd_apply (hS.inter (measurable_snd hA)),
    Measure.compProd_apply hS,
    lintegral_withDensity_eq_lintegral_mul _ (κ.measurable_coe hA)
      (Kernel.measurable_kernel_prodMk_left hS)]
  apply lintegral_congr
  intro x
  simp only [Pi.mul_apply]
  rw [conditionalEventKernel_weighted_apply]
  congr 1
  ext z
  simp only [mem_preimage, mem_inter_iff]
  exact and_comm

end
end Nonsmooth
