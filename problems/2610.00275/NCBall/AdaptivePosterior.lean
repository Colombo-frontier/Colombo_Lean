import NCBall.AdaptiveGaussianLaw
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.Prod

/-! # The regular conditional law given the algorithm's actual transcript -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace ENNReal
namespace NCBall

variable {S E : Type*} [MeasurableSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def linearPosteriorKernel (p : LinearQueryPolicy S E) (t : ℕ) : Kernel (LinearHistory S t) E :=
  (Kernel.id ×ₖ Kernel.const (LinearHistory S t) (euclideanGaussianLaw E)).map
    (fun hz : LinearHistory S t × E =>
      linearPosteriorMean p t hz.1 + linearPosteriorProjection p t hz.1 hz.2)

instance linearPosteriorKernel_markov (p : LinearQueryPolicy S E) (t : ℕ) :
    IsMarkovKernel (linearPosteriorKernel p t) := by
  apply Kernel.IsMarkovKernel.map
  exact (linearPosteriorRepresentation_measurable p t).snd

theorem linearPosteriorKernel_apply (p : LinearQueryPolicy S E) (t : ℕ) (h : LinearHistory S t) :
    linearPosteriorKernel p t h = (euclideanGaussianLaw E).map
      (fun z => linearPosteriorMean p t h + linearPosteriorProjection p t h z) := by
  have hm : Measurable (fun hz : LinearHistory S t × E =>
      linearPosteriorMean p t hz.1 + linearPosteriorProjection p t hz.1 hz.2) :=
    (linearPosteriorRepresentation_measurable p t).snd
  ext B hB
  rw [linearPosteriorKernel, Kernel.map_apply' _ hm _ hB,
    Kernel.id_prod_apply' _ _ (hm hB), Measure.map_apply (by fun_prop) hB]
  rfl

theorem linearPosteriorKernel_disintegrates (ν : Measure S) [IsProbabilityMeasure ν]
    (p : LinearQueryPolicy S E) (t : ℕ) :
    (ν.prod (euclideanGaussianLaw E)).map
      (fun w : S × E => (linearTranscript p t w, w.2)) =
      (linearHistoryLaw ν p t) ⊗ₘ linearPosteriorKernel p t := by
  rw [adaptive_gaussian_joint_law ν p t]
  ext B hB
  have hm := linearPosteriorRepresentation_measurable p t
  rw [Measure.map_apply hm hB, Measure.prod_apply (hm hB), Measure.compProd_apply hB]
  apply lintegral_congr
  intro h
  rw [linearPosteriorKernel_apply, Measure.map_apply (by fun_prop) (measurable_prodMk_left hB)]
  rfl

/-- Actual regular conditional distribution, with the usual almost-everywhere
qualification. The mean and projection on the right are explicit functions
of the complete observed history. -/
theorem adaptive_gaussian_conditional_law (ν : Measure S) [IsProbabilityMeasure ν]
    (p : LinearQueryPolicy S E) (t : ℕ) :
    ∀ᵐ h ∂linearHistoryLaw ν p t,
      condDistrib Prod.snd (linearTranscript p t) (ν.prod (euclideanGaussianLaw E)) h =
        (euclideanGaussianLaw E).map
          (fun z => linearPosteriorMean p t h + linearPosteriorProjection p t h z) := by
  have he := condDistrib_ae_eq_of_measure_eq_compProd
    (linearTranscript_measurable p t) (measurable_snd : Measurable (Prod.snd : S × E → E))
    (linearPosteriorKernel p t) (linearPosteriorKernel_disintegrates ν p t)
  filter_upwards [he] with h hh
  rw [← hh, linearPosteriorKernel_apply]

/-- Transfer a pointwise bound under the computed posterior to an actual
history-dependent event. This is the interface needed for adaptive estimators. -/
theorem adaptive_gaussian_event_bound (ν : Measure S) [IsProbabilityMeasure ν]
    (p : LinearQueryPolicy S E) (t : ℕ)
    (B : Set (LinearHistory S t × E)) (hB : MeasurableSet B) (c : ℝ≥0∞)
    (hbound : ∀ h, (euclideanGaussianLaw E)
      {z | (h, linearPosteriorMean p t h + linearPosteriorProjection p t h z) ∈ B} ≤ c) :
    (ν.prod (euclideanGaussianLaw E)) {w | (linearTranscript p t w, w.2) ∈ B} ≤ c := by
  have hrec := (linearTranscript_measurable p t).prodMk measurable_snd
  change (ν.prod (euclideanGaussianLaw E))
    ((fun w : S × E => (linearTranscript p t w, w.2)) ⁻¹' B) ≤ c
  rw [← Measure.map_apply hrec hB, adaptive_gaussian_joint_law ν p t,
    Measure.map_apply (linearPosteriorRepresentation_measurable p t) hB,
    Measure.prod_apply ((linearPosteriorRepresentation_measurable p t) hB)]
  calc
    _ ≤ ∫⁻ _h, c ∂linearHistoryLaw ν p t := lintegral_mono hbound
    _ = c := by simp

end NCBall
