import UpperOptimizationConvex
import UpperSmoothingInstance

/-! Global auxiliary smoothed objective and its exact local convexity. -/
open MeasureTheory Metric Set
open scoped NNReal
namespace Task006.Full

theorem ballSmooth_lipschitz_global {d : ℕ} {f : Space d → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {ρ : ℝ} (hρ : 0 < ρ) :
    LipschitzWith L (ballSmooth f ρ) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    (fun x => (ballSmooth_hasFDerivAt_global hf hρ x).2.differentiableAt)
  intro x
  apply NNReal.coe_le_coe.mp
  change ‖fderiv ℝ (ballSmooth f ρ) x‖ ≤ (L : ℝ)
  rw [(ballSmooth_hasFDerivAt_global hf hρ x).2.fderiv]
  exact ballSmoothDerivative_norm_le hf ρ x

namespace SampleInstance
variable {d : ℕ} {L R : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] (I : SampleInstance d L R Ω μ)

noncomputable def smoothedObjective (hL : 0 ≤ L) (hR : 0 ≤ R) (ρ : ℝ) : Space d → ℝ :=
  ballSmooth (I.objectiveExtension hL hR) ρ

theorem smoothedObjective_lipschitz (hL : 0 ≤ L) (hR : 0 ≤ R) {ρ : ℝ} (hρ : 0 < ρ) :
    LipschitzWith ⟨L, hL⟩ (I.smoothedObjective hL hR ρ) :=
  ballSmooth_lipschitz_global (I.objectiveExtension_lipschitz hL hR) hρ

theorem smoothedObjective_convex (hL : 0 ≤ L) (hR : 0 ≤ R) {ρ r : ℝ}
    (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) (hrR : r ≤ R) :
    ConvexOn ℝ (closedBall (0 : Space d) r) (I.smoothedObjective hL hR ρ) := by
  apply ((ballSmooth_convex (I.objective_lipschitzOn hL hR) (I.objective_convex hR) hρ hρR).subset
    (closedBall_subset_closedBall hrR) (convex_closedBall _ _)).congr
  intro x hx
  have hxn : ‖x‖ ≤ R := by
    have hn : ‖x‖ ≤ r := by simpa using hx
    exact hn.trans hrR
  exact I.ballSmooth_eq_extension hL hR hρ hρR hxn

theorem smoothedObjective_gradient_gap (hL : 0 ≤ L) (hR : 0 ≤ R) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρR : ρ ≤ R) (hrR : r ≤ R)
    {x z : Space d} (hx : ‖x‖ ≤ r) (hz : ‖z‖ ≤ r) :
    I.smoothedObjective hL hR ρ x - I.smoothedObjective hL hR ρ z ≤
      inner ℝ (x - z) (I.smoothedGradient hL hR ρ x) := by
  apply convex_gradient_gap (I.smoothedObjective_convex hL hR hρ.le hρR hrR)
    (by simpa using hx) (by simpa using hz)
  exact ballSmooth_hasGradientAt_global (I.objectiveExtension_lipschitz hL hR) hρ x

theorem smoothedObjective_error (hL : 0 ≤ L) (hR : 0 ≤ R) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) {x : Space d} (hx : ‖x‖ ≤ R) :
    |I.smoothedObjective hL hR ρ x - I.objective x| ≤ ρ * L := by
  change |ballSmooth (I.objectiveExtension hL hR) ρ x - I.objective x| ≤ _
  rw [← I.ballSmooth_eq_extension hL hR hρ hρR hx]
  exact ballSmooth_error (I.objective_lipschitzOn hL hR) hρ hρR hx

end SampleInstance

#print axioms ballSmooth_lipschitz_global
#print axioms SampleInstance.smoothedObjective_gradient_gap
end Task006.Full
