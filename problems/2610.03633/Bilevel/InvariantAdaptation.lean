import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Measure.Prod

/-!
An adaptive symmetry chosen from invariant observations preserves the original
law. This is the averaging step needed for conditioning a rotational experiment;
it does not assume a conditional distribution or a conditional tail estimate.
-/
noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace Bilevel.InvariantAdaptation

variable {G X I : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
  [MeasurableSpace X] [MeasurableSpace I] [MulAction G X] [MeasurableSMul₂ G X]
  (ν : Measure G) [IsProbabilityMeasure ν] [IsMulLeftInvariant ν]
  (μ : Measure X) [SFinite μ]

omit [MeasurableMul₂ G] [MeasurableSMul₂ G X] [IsMulLeftInvariant ν] [SFinite μ] in
theorem lintegral_action_average
    (hp : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ)
    (f : X → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ g, ∫⁻ x, f (g • x) ∂μ ∂ν) = ∫⁻ x, f x ∂μ := by
  simp_rw [(hp _).lintegral_comp hf]
  simp

include ν in
theorem adaptive_lintegral
    (hp : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ)
    (observation : X → I) (ho : Measurable observation)
    (hinv : ∀ (g : G) (x : X), observation (g • x) = observation x)
    (choice : I → G) (hc : Measurable choice)
    (f : X → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f (choice (observation x) • x) ∂μ) = ∫⁻ x, f x ∂μ := by
  have hF : Measurable (fun x : X => f (choice (observation x) • x)) :=
    hf.comp ((hc.comp ho).smul measurable_id)
  calc
    (∫⁻ x, f (choice (observation x) • x) ∂μ) =
        ∫⁻ g, ∫⁻ x, f (choice (observation (g • x)) • (g • x)) ∂μ ∂ν :=
      (lintegral_action_average ν μ hp _ hF).symm
    _ = ∫⁻ g, ∫⁻ x, f ((choice (observation x) * g) • x) ∂μ ∂ν := by
      simp_rw [hinv, mul_smul]
    _ = ∫⁻ x, ∫⁻ g, f ((choice (observation x) * g) • x) ∂ν ∂μ := by
      apply lintegral_lintegral_swap
      exact (hf.comp ((((hc.comp ho).comp measurable_snd).mul measurable_fst).smul measurable_snd)).aemeasurable
    _ = ∫⁻ x, ∫⁻ g, f (g • x) ∂ν ∂μ := by
      congr 1
      funext x
      exact lintegral_mul_left_eq_self (fun g : G => f (g • x)) (choice (observation x))
    _ = ∫⁻ g, ∫⁻ x, f (g • x) ∂μ ∂ν := by
      apply lintegral_lintegral_swap
      exact (hf.comp (measurable_snd.smul measurable_fst)).aemeasurable
    _ = ∫⁻ x, f x ∂μ := lintegral_action_average ν μ hp f hf

include ν in
theorem adaptive_preserving
    (hp : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ)
    (observation : X → I) (ho : Measurable observation)
    (hinv : ∀ (g : G) (x : X), observation (g • x) = observation x)
    (choice : I → G) (hc : Measurable choice) :
    MeasurePreserving (fun x => choice (observation x) • x) μ μ := by
  have hT : Measurable (fun x => choice (observation x) • x) :=
    (hc.comp ho).smul measurable_id
  refine ⟨hT, ?_⟩
  ext s hs
  rw [Measure.map_apply hT hs]
  have h := adaptive_lintegral ν μ hp observation ho hinv choice hc
    (s.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hs)
  have he : (fun x => s.indicator (fun _ => (1 : ℝ≥0∞)) (choice (observation x) • x)) =
      ((fun x => choice (observation x) • x) ⁻¹' s).indicator 1 := by
    funext x
    by_cases hx : choice (observation x) • x ∈ s <;> simp [hx]
  rw [he, lintegral_indicator_one (hT hs)] at h
  change μ ((fun x => choice (observation x) • x) ⁻¹' s) = ∫⁻ x, s.indicator 1 x ∂μ at h
  rw [lintegral_indicator_one hs] at h
  exact h

end Bilevel.InvariantAdaptation
