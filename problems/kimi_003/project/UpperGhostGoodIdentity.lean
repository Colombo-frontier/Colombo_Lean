import UpperGhostClosedBasis

/-! Exact identification of the ghost's non-strict good set with the original
raw oracle moments at every legal center and every actual Haar column. -/

open MeasureTheory Set
open Task006.HaarRebalancing
namespace Task006.Full.SampleInstance

theorem sourceGoodRebalancedBasis_iff_raw {d : ℕ} {L : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (P : UpperProgramParameters)
    (I : SampleInstance d L P.R Ω μ) (hR : 0 ≤ P.R) {ρ δ s : ℝ}
    (hρ : 0 ≤ ρ) (hρR : ρ ≤ P.R) (hδ : 0 < δ) {x : Space d}
    (hx : ‖x‖ + δ ≤ P.R) (Q : OrthogonalGroup d) :
    I.sourceGoodRebalancedBasis P hR ρ δ s x Q ↔
      ∀ i : Fin d, I.oracleDirectionalMoment ρ δ x (column Q i) ≤ rebalancingThreshold L d s := by
  unfold sourceGoodRebalancedBasis
  apply forall_congr'
  intro i
  rw [I.rebalancedDirectionalMoment_eq_oracle hR hρ hρR hδ hx ((orthonormal_column Q).norm_eq_one i)]

#print axioms sourceGoodRebalancedBasis_iff_raw
end Task006.Full.SampleInstance
