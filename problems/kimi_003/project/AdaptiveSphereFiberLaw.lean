import AdaptiveSphereKernelRadius
import HaarRebalancingRadius

/-! Concrete Haar orbit identification of the actual regular conditional
residual distribution, including zero-radius fibers. -/
open MeasureTheory Set ProbabilityTheory
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereKernel
open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereBlock
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereResidualFrame
open Task006.AdaptiveSphereState Task006.AdaptiveSphereAction
open Task006.AdaptiveSphereStopped Task006.AdaptiveSphereInvariance
open Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereMeasurable
open Task006.AdaptiveSphereGeometry Task006.PosteriorCenter Task006.AdaptiveSphereActualStep
open Task006.AdaptiveSphereMean Task006.AdaptiveSphereReframe Task006.AdaptiveSphere
open Task006.AdaptiveSphereIsotropy Task006.PosteriorResidualEnergy
noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

def canonicalRadiusVector (n : ℕ) (hn : 0<n) (a : ℝ) : E n :=
  Real.sqrt a • (EuclideanSpace.basisFun (Fin n) ℝ) (⟨0,hn⟩ : Fin n)

theorem canonicalRadiusVector_norm (n : ℕ) (hn : 0<n) (a : ℝ) :
    ‖canonicalRadiusVector n hn a‖ = Real.sqrt a := by
  rw [canonicalRadiusVector,norm_smul,
    (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg a),mul_one]

/-- The actual regular conditional law in residual coordinates IS the concrete
uniform Haar sphere law at the observed radius. This is a measure equality,
not just equality of its first or second moments. -/
theorem rankResidual_condDistrib_eq_haar_sphere (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (ht : t ≤ N) (j : Fin d) (hstop : RankStopped A weight tape seed k hkd)
    (H : Transcript N → ResidualControls d) (hH : Measurable H)
    (r : Fin (d+1)) (hrd : r.val < d) :
    ∀ᵐ h ∂(orthogonalHaarProbability d).map (history A weight tape seed t j),
      condDistrib (rankResidual A weight tape seed k hkd t j H r)
        (history A weight tape seed t j) (orthogonalHaarProbability d) h =
      Measure.map (fun Q : OrthogonalGroup (d-r.val) => action Q
        (canonicalRadiusVector (d-r.val) (by omega)
          (observedResidualEnergy A weight tape seed k hkd t r h)))
        (orthogonalHaarProbability (d-r.val)) := by
  filter_upwards [rankResidual_condDistrib_sphere_support A weight tape seed k hkd t ht j H hH r,
    rankResidual_condDistrib_all_rotations A weight tape seed k hkd t ht j hstop H hH r]
    with h hs hr
  apply invariant_radius_probability_eq_haar
  · filter_upwards [hs] with x hx
    rw [canonicalRadiusVector_norm]
    calc
      ‖x‖ = Real.sqrt (‖x‖^2) := (Real.sqrt_sq (norm_nonneg x)).symm
      _ = Real.sqrt (observedResidualEnergy A weight tape seed k hkd t r h) := congrArg Real.sqrt hx
  · exact hr

#print axioms canonicalRadiusVector_norm
#print axioms rankResidual_condDistrib_eq_haar_sphere
end
end Task006.AdaptiveSphereKernel
