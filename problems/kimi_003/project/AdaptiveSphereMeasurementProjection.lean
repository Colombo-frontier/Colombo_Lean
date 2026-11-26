import AdaptiveSphereSpanTranscript
import AdaptiveSphereSpanGeometry
import AdaptiveSpherePosteriorAllRanks

open MeasureTheory Set
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereSpan
open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereFrame Task006.AdaptiveSphereState
open Task006.AdaptiveSphereAction Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereMean
open Task006.AdaptiveSphereReframe Task006.PosteriorCenter Task006.PosteriorResidualEnergy
noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

/-- Residual reframing changes neither the measured subspace nor its projector. -/
theorem frameSpan_reframe (state : FrameState d) (H : ResidualControls d) :
    frameSpan (reframe state H) = frameSpan state := by
  apply le_antisymm
  · intro x hx
    have he := (frameSpan (reframe state H)).starProjection_eq_self_iff.mpr hx
    rw [frameSpan_starProjection,reframe_projectedCenter,← frameSpan_starProjection] at he
    exact (frameSpan state).starProjection_eq_self_iff.mp he
  · intro x hx
    have he := (frameSpan state).starProjection_eq_self_iff.mpr hx
    rw [frameSpan_starProjection,← reframe_projectedCenter state H,
      ← frameSpan_starProjection] at he
    exact (frameSpan (reframe state H)).starProjection_eq_self_iff.mp he

/-- The posterior center is the ordinary orthogonal projection onto the span
of the actual effective measurements, exactly as denoted C=P_V Θ in the paper. -/
theorem actual_center_eq_measurement_projection (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (t : ℕ) (ht : t ≤ N)
    (j : Fin d) (Q : OrthogonalGroup d) :
    (measurementSpanBefore A weight tape seed t (column Q j)).starProjection (column Q j) =
      actualCenter A weight tape seed d le_rfl t j Q := by
  rw [← actual_frameSpan_eq_measurementSpan A weight tape seed t ht,
    frameSpan_starProjection,actualCenter_eq_projected A weight tape seed d le_rfl t ht j Q]
  rfl

/-- The actual measurement-span dimension equals the maintained independent
measurement rank, without any algorithmic span restriction. -/
theorem actual_measurementSpan_finrank (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (t : ℕ) (ht : t ≤ N) (θ : E d) :
    Module.finrank ℝ (measurementSpanBefore A weight tape seed t θ) =
      (frameFromTranscript A weight tape seed d le_rfl t
        (A.runPrefix (linearSample weight θ) tape seed t)).1.val := by
  rw [← actual_frameSpan_eq_measurementSpan A weight tape seed t ht,frameSpan_finrank]

#print axioms frameSpan_reframe
#print axioms actual_center_eq_measurement_projection
#print axioms actual_measurementSpan_finrank
end
end Task006.AdaptiveSphereSpan
