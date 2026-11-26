import MatchingBounds1005.SourceEntropyTransfer

/-! The actual adaptive reference/static transcript KL estimate, stated
separately from its event-probability consequence. -/
noncomputable section
open MeasureTheory RandomizedFO2003.Rotations InformationTheory
open scoped NNReal ENNReal
namespace MatchingBounds1005.SourceReferenceReplay
open SourceReferenceProgram TensorGeometry CensoredGaussianProcess
variable {Seed : Type} [MeasurableSpace Seed] {d H N : ℕ}

theorem source_klDiv_le (P : Parameters d N) (A : Model.Algorithm d Seed)
    (hτ : ∀ i, 0 < P.disclosure i) (hunit : ∀ i, ‖P.b i‖ = 1)
    (ν : Measure (Rotation (Vec d) × Seed)) [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : 0 ≤ θ) (ζ : ℝ)
    (hfail : (referenceLaw (sourceProtocol P A) 1 ν H).real (traceGood P A θ)ᶜ ≤ ζ) :
    klDiv (referenceLaw (sourceProtocol (H := H) P A) 1 ν H)
      (trueLaw (sourceProtocol (H := H) P A) 1 ν H) ≤
      ENNReal.ofReal (pairCostCap P θ + ζ * pairCostCap P 1) := by
  apply CensoredGaussianEvent.transcript_klDiv_le_good_event (sourceProtocol P A) (by norm_num) ν
    (fun _ => normCostCap P) ?_ H (traceGood P A θ) (traceGood_measurable P A θ)
    (pairCostCap P θ) (pairCostCap P 1) ζ (pairCostCap_nonneg P θ) (pairCostCap_nonneg P 1)
    (fun h hh => traceGood_cost P A hτ hunit hθ h hh) (global_cost P A hτ hunit) hfail
  intro n h
  exact protocol_hidden_norm P A (rotationMap d) (fun i => rotationMap_column_measurable (P.b i))
    (rotationMap_column_measurable P.c) (rotationMap_quadratic_measurable P.Q) hτ
    (fun ρ i => by change ‖isometry _ ρ (P.b i)‖ = 1; rw [LinearIsometryEquiv.norm_map, hunit i]) n h

end MatchingBounds1005.SourceReferenceReplay
