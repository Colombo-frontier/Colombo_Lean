import AdaptiveSphereOriginalPosterior
import AdaptiveSphereDegeneratePosterior

/-! One actual regular conditional distribution identity covering every rank,
without stopping assumptions or rank-dependent exceptional sets. -/
open MeasureTheory Set ProbabilityTheory
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereKernel
open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereBlock
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereResidualFrame
open Task006.AdaptiveSphereState Task006.AdaptiveSphereAction
open Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereMeasurable
open Task006.AdaptiveSphereGeometry Task006.PosteriorCenter Task006.AdaptiveSphereActualStep
open Task006.AdaptiveSphereMean Task006.AdaptiveSphereReframe
noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

def fiberLawAtRank (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (t : ℕ) (H : Transcript N → ResidualControls d)
    (r : Fin (d+1)) (h : Transcript N) : Measure (E d) :=
  if hrd : r.val < d then
    Measure.map (fun Q : OrthogonalGroup (d-r.val) =>
      centerFromTranscript A weight tape seed d le_rfl t h +
        action (observedFrame A weight tape seed d le_rfl t H h).2
          (liftResidual r.val (by omega) (action Q
            (canonicalRadiusVector (d-r.val) (by omega)
              (observedResidualEnergy A weight tape seed d le_rfl t r h)))))
      (orthogonalHaarProbability (d-r.val))
  else Measure.dirac (centerFromTranscript A weight tape seed d le_rfl t h)

def observedSphereFiberLaw (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (t : ℕ) (H : Transcript N → ResidualControls d)
    (h : Transcript N) : Measure (E d) :=
  fiberLawAtRank A weight tape seed t H (observedFrame A weight tape seed d le_rfl t H h).1 h

/-- Full conditional-law theorem for the original unrestricted canonical
adaptive protocol. The exceptional set is independent of the observed rank. -/
theorem original_condDistrib_eq_sphere_fiber (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (t : ℕ) (ht : t ≤ N) (j : Fin d)
    (H : Transcript N → ResidualControls d) (hH : Measurable H) :
    condDistrib (fun Q => column Q j) (history A weight tape seed t j) (orthogonalHaarProbability d)
      =ᵐ[(orthogonalHaarProbability d).map (history A weight tape seed t j)]
      observedSphereFiberLaw A weight tape seed t H := by
  have hall : ∀ᵐ h ∂(orthogonalHaarProbability d).map (history A weight tape seed t j),
      ∀ r : Fin (d+1), (observedFrame A weight tape seed d le_rfl t H h).1 = r →
        condDistrib (fun Q => column Q j) (history A weight tape seed t j) (orthogonalHaarProbability d) h =
          fiberLawAtRank A weight tape seed t H r h := by
    rw [ae_all_iff]
    intro r
    by_cases hrd : r.val < d
    · have hl := original_full_posterior_fiber A weight tape seed t ht j H hH r hrd
      simpa only [fiberLawAtRank,dif_pos hrd] using hl
    · have hrfull : r = fullRank d := Fin.ext (by change r.val=d; omega)
      have hh := full_rank_condDistrib_dirac A weight tape seed d le_rfl t ht j H hH
      filter_upwards [hh] with h hcond
      intro hR
      rw [fiberLawAtRank,dif_neg hrd]
      exact hcond (hR.trans hrfull)
  filter_upwards [hall] with h hh
  exact hh _ rfl

#print axioms original_condDistrib_eq_sphere_fiber
end
end Task006.AdaptiveSphereKernel
