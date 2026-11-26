import HeavyTail.LocalizationModelGeometry
import HeavyTail.AdaptiveKernelStages
import HeavyTail.AdaptiveKernelPadding

/-! Localized objective-error probability for the actual composed policies.
Earlier objective guarantees certify radii; the last guarantee bounds the
objective itself. The proof never reverses strong-convex growth. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HeavyTail
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {θ : OracleParameters}

theorem measure_le_of_real_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (S : Set X) {δ : ℝ} (h : μ.real S ≤ δ) :
    μ S ≤ ENNReal.ofReal δ := by
  calc
    μ S = ENNReal.ofReal (μ.real S) := (ENNReal.ofReal_toReal (measure_ne_top μ S)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal h

namespace PrivateInstance
variable {B : PublicProblem E θ}

theorem localized_policies_error (I : PrivateInstance B) (hμ : 0 < θ.μ)
    {budget : ℕ → ℕ} (A : ∀ j, AdaptiveKernel.Policy B.X B.X E B.X (budget j))
    (c₀ : B.X) (R : ℕ → ℝ) (hR : ∀ j, 0 ≤ R j)
    (hc₀ : ‖(c₀ : E) - I.minimizer‖ ≤ R 0) (ε : ℕ → ℝ≥0∞) (N : ℕ)
    (hstage : ∀ j ≤ N, ∀ c : B.X, ‖(c : E) - I.minimizer‖ ≤ R j →
      (A j).outputLaw (Measure.dirac c) I.oracle
        {x | ENNReal.ofReal (θ.μ / 2 * (R (j + 1)) ^ 2) < I.loss x} ≤ ε j) :
    (AdaptiveKernel.Policy.stages c₀ A (N + 1)).outputLaw (Measure.dirac c₀) I.oracle
      {x | ENNReal.ofReal (θ.μ / 2 * (R (N + 1)) ^ 2) < I.loss x} ≤
        ∑ j ∈ Finset.range (N + 1), ε j := by
  let K : ℕ → Kernel B.X B.X := fun j => (A j).outputKernel I.oracle
  let bad : ℕ → Set B.X := fun j => {x | R j < ‖(x : E) - I.minimizer‖}
  have hb : ∀ j, MeasurableSet (bad j) := fun j => I.radiusBad_measurable (R j)
  have hinit : (Measure.dirac c₀) (bad 0) = 0 := by
    have hnmem : c₀ ∉ bad 0 := not_lt_of_ge hc₀
    rw [Measure.dirac_apply' c₀ (hb 0), Set.indicator_of_not_mem hnmem]
  have hprev : ∀ j < N, ∀ c ∉ bad j, K j c (bad (j + 1)) ≤ ε j := by
    intro j hj c hc
    rw [show K j c = (A j).outputLaw (Measure.dirac c) I.oracle from
      (A j).outputKernel_apply I.oracle c]
    exact (measure_mono (I.radius_bad_subset_loss_bad hμ (hR (j + 1)))).trans
      (hstage j hj.le c (le_of_not_gt hc))
  have hlast : ∀ c ∉ bad N, K N c
      {x | ENNReal.ofReal (θ.μ / 2 * (R (N + 1)) ^ 2) < I.loss x} ≤ ε N := by
    intro c hc
    rw [show K N c = (A N).outputLaw (Measure.dirac c) I.oracle from
      (A N).outputKernel_apply I.oracle c]
    exact hstage N le_rfl c (le_of_not_gt hc)
  rw [AdaptiveKernel.Policy.stages_outputLaw]
  have h := stageKernelLaw_terminal_failure K (Measure.dirac c₀) bad hb ε N hprev _
    (I.lossBad_measurable _) (ε N) hlast
  simpa only [hinit, zero_add, Finset.sum_range_succ] using h

end PrivateInstance
end HeavyTail
