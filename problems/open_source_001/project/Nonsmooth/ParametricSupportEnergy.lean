import Nonsmooth.ParametricSelection
import Nonsmooth.PosteriorEnergyReencoding

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E α : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace α] {k : ℕ} [Nonempty (Fin k)]

def supportUpdateMeanIncrement (κ : Kernel α (Fin k → E)) [IsMarkovKernel κ]
    (u : α → E) (hu : Measurable u) (p : α × (Fin k × ℝ)) : E :=
  (∫ a : Fin k → E, ∑ i, a i ∂supportPosteriorUpdate κ u hu p) -
    ∫ a : Fin k → E, ∑ i, a i ∂κ p.1

def supportUpdateMeanEnergy (κ : Kernel α (Fin k → E)) [IsMarkovKernel κ]
    (u : α → E) (hu : Measurable u) (x : α) : ℝ :=
  ∫ y, ‖supportUpdateMeanIncrement κ u hu (x, y)‖ ^ 2
    ∂(observedKernel κ (fun p => supportSingleObservation (u p.1) p.2)
      (supportParametricObservation_measurable u hu)).fst x

theorem supportUpdateMeanIncrement_measurable (κ : Kernel α (Fin k → E)) [IsMarkovKernel κ]
    (u : α → E) (hu : Measurable u) : Measurable (supportUpdateMeanIncrement κ u hu) := by
  have hf : StronglyMeasurable (fun a : Fin k → E => ∑ i, a i) :=
    (by fun_prop : Continuous (fun a : Fin k → E => ∑ i, a i)).stronglyMeasurable
  exact hf.integral_kernel.measurable.sub (hf.integral_kernel.measurable.comp measurable_fst)

theorem supportUpdateMeanEnergy_measurable (κ : Kernel α (Fin k → E)) [IsMarkovKernel κ]
    (u : α → E) (hu : Measurable u) : Measurable (supportUpdateMeanEnergy κ u hu) := by
  have hf := ((supportUpdateMeanIncrement_measurable κ u hu).norm.pow_const 2).stronglyMeasurable
  exact hf.integral_kernel_prod_right'.measurable

theorem supportUpdateMeanEnergy_eq_actual (κ : Kernel α (Fin k → E)) [IsMarkovKernel κ]
    (u : α → E) (hu : Measurable u) (x : α) :
    supportUpdateMeanEnergy κ u hu x =
      ∫ y, ‖posteriorAggregateShift (κ x) (supportSingleObservation (u x)) y‖ ^ 2
        ∂(κ x).map (supportSingleObservation (u x)) := by
  unfold supportUpdateMeanEnergy
  rw [observedKernel_fst]
  apply integral_congr_ae
  have hp := observedPosterior_ae_eq_condDistrib κ
    (fun p : α × (Fin k → E) => supportSingleObservation (u p.1) p.2)
    (supportParametricObservation_measurable u hu) x
  filter_upwards [hp] with y hy
  change ‖(∫ a : Fin k → E, ∑ i, a i ∂observedPosterior κ _ _ (x, y)) -
    ∫ a : Fin k → E, ∑ i, a i ∂κ x‖ ^ 2 = _
  rw [hy]
  rfl

end
end Nonsmooth
