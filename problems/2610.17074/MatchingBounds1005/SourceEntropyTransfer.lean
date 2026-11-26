import MatchingBounds1005.SourceTraceEnergy
import MatchingBounds1005.CensoredGaussianEvent

/-! Actual source protocol entropy transfer, with no remaining signal or
cost hypotheses: only the reference geometry failure probability is needed. -/
noncomputable section
open MeasureTheory RandomizedFO2003.Rotations
open scoped NNReal
namespace MatchingBounds1005.SourceReferenceReplay
open SourceReferenceProgram TensorGeometry CensoredGaussianProcess
variable {Seed : Type} [MeasurableSpace Seed] {d H N : ℕ}

def normCostCap (P : Parameters d N) : ℝ≥0 := ⟨
    (N : ℝ) ^ 2 * (-120 * P.τ * P.a ^ 3) ^ 2 / (2 * P.σ₃ ^ 2) +
    (N : ℝ) ^ 2 * (120 * P.τ * P.a ^ 4) ^ 2 / (2 * P.σ₄ ^ 2), by positivity⟩

theorem source_true_bad_probability (P : Parameters d N) (A : Model.Algorithm d Seed)
    (hτ : ∀ i, 0 < P.disclosure i) (hunit : ∀ i, ‖P.b i‖ = 1)
    (ν : Measure (Rotation (Vec d) × Seed)) [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : 0 ≤ θ) (ζ : ℝ)
    (hfail : (referenceLaw (sourceProtocol P A) 1 ν H).real (traceGood P A θ)ᶜ ≤ ζ) :
    (trueLaw (sourceProtocol P A) 1 ν H).real (traceGood P A θ)ᶜ ≤
      (4 / 3 : ℝ) * (pairCostCap P θ + ζ * pairCostCap P 1 + Real.log 4 * ζ) := by
  apply CensoredGaussianEvent.true_bad_probability (sourceProtocol P A) (by norm_num) ν
    (fun _ => normCostCap P) ?_ H (traceGood P A θ) (traceGood_measurable P A θ)
    (pairCostCap P θ) (pairCostCap P 1) ζ (pairCostCap_nonneg P θ) (pairCostCap_nonneg P 1)
    (fun h hh => traceGood_cost P A hτ hunit hθ h hh) (global_cost P A hτ hunit) hfail
  intro n h
  exact protocol_hidden_norm P A (rotationMap d) (fun i => rotationMap_column_measurable (P.b i))
    (rotationMap_column_measurable P.c) (rotationMap_quadratic_measurable P.Q) hτ
    (fun ρ i => by change ‖isometry _ ρ (P.b i)‖ = 1; rw [LinearIsometryEquiv.norm_map, hunit i]) n h

end MatchingBounds1005.SourceReferenceReplay
