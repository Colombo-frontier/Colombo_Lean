import AdaptiveSpherePosteriorKernel
import AdaptiveSphereKernelRadius
import AdaptiveSphereFiberLaw

/-! Reusable posterior reductions from actual residual symmetries. The original
policy theorem instantiates these premises with proved invariance; no posterior
mean, moment, fiber law, or terminal energy is postulated. -/
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
open Task006.AdaptiveSphereIsotropy Task006.PosteriorResidualEnergy Task006.AdaptiveSphereOrbit
noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

def ResidualInvariance (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d) : Prop :=
  (∀ g : ResidualControls d, MeasurePreserving (orbitTransform A weight tape seed k hkd t j g)
    (orthogonalHaarProbability d) (orthogonalHaarProbability d)) ∧
  (∀ (g : ResidualControls d) (Q : OrthogonalGroup d),
    history A weight tape seed t j (orbitTransform A weight tape seed k hkd t j g Q) =
      history A weight tape seed t j Q)

theorem reframedOrbit_mp_of_invariance (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d)
    (hInv : ResidualInvariance A weight tape seed k hkd t j)
    (H : Transcript N → ResidualControls d) (hH : Measurable H) (g : ResidualControls d) :
    MeasurePreserving (reframedOrbit A weight tape seed k hkd t j H g)
      (orthogonalHaarProbability d) (orthogonalHaarProbability d) := by
  have hc : Measurable (fun h => conjugateControls (H h) g) := by
    have hin : Measurable (fun h : Transcript N => (H h,g)) := hH.prodMk measurable_const
    have hr := (conjugateControls_joint_continuous (d := d)).measurable.comp hin
    simpa only [Function.comp_def] using hr
  have hr := observable_dependent_symmetry_measurePreserving
    (history A weight tape seed t j) (measurable_history A weight tape seed t j)
    (fun h => conjugateControls (H h) g) hc
    (orbitTransform A weight tape seed k hkd t j) hInv.1
    (orbitTransform_joint_measurable A weight tape seed k hkd t j)
    (orbitTransform_control_continuous A weight tape seed k hkd t j) hInv.2
  have heq : (fun Q => orbitTransform A weight tape seed k hkd t j
      (conjugateControls (H (history A weight tape seed t j Q)) g) Q) =
      reframedOrbit A weight tape seed k hkd t j H g := by
    funext Q
    exact (reframedOrbit_factorization A weight tape seed k hkd t j H g Q).symm
  rw [heq] at hr
  exact hr

theorem reframedOrbit_fix_of_invariance (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d)
    (hInv : ResidualInvariance A weight tape seed k hkd t j)
    (H : Transcript N → ResidualControls d) (g : ResidualControls d) (Q : OrthogonalGroup d) :
    history A weight tape seed t j (reframedOrbit A weight tape seed k hkd t j H g Q) =
      history A weight tape seed t j Q := by
  rw [reframedOrbit_factorization]
  exact hInv.2 _ Q

theorem residual_condDistrib_rotation_of_invariance (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (j : Fin d) (hInv : ResidualInvariance A weight tape seed k hkd t j)
    (H : Transcript N → ResidualControls d) (hH : Measurable H)
    (r : Fin (d+1)) (g : OrthogonalGroup (d-r.val)) :
    (condDistrib (rankResidual A weight tape seed k hkd t j H r)
      (history A weight tape seed t j) (orthogonalHaarProbability d)).map (action g)
      =ᵐ[(orthogonalHaarProbability d).map (history A weight tape seed t j)]
    condDistrib (rankResidual A weight tape seed k hkd t j H r)
      (history A weight tape seed t j) (orthogonalHaarProbability d) := by
  let control : ResidualControls d := Function.update (fun _ => 1) r g
  let T := reframedOrbit A weight tape seed k hkd t j H control
  have hmp := reframedOrbit_mp_of_invariance A weight tape seed k hkd t j hInv H hH control
  have hfix := reframedOrbit_fix_of_invariance A weight tape seed k hkd t j hInv H control
  apply condDistrib_map_eq_of_preserving_observable (orthogonalHaarProbability d)
    (history A weight tape seed t j) (measurable_history A weight tape seed t j)
    (rankResidual A weight tape seed k hkd t j H r)
    (rankResidual_measurable A weight tape seed k hkd t j H hH r)
    T hmp (action g) (action g).continuous.measurable hfix
  intro Q
  have hs : reframedState A weight tape seed k hkd t j H (T Q) =
      reframedState A weight tape seed k hkd t j H Q := by
    change reframe (frameFromTranscript A weight tape seed k hkd t
      (history A weight tape seed t j (T Q))) (H (history A weight tape seed t j (T Q))) = _
    rw [hfix]
    rfl
  unfold rankResidual
  rw [hs]
  by_cases hr : (reframedState A weight tape seed k hkd t j H Q).1 = r
  · rw [if_pos hr,if_pos hr]
    have hstateQ : reframedState A weight tape seed k hkd t j H Q =
        (r,(reframedState A weight tape seed k hkd t j H Q).2) := Prod.ext hr rfl
    have hcol : column (T Q) j = action
        (rotateAtState (reframedState A weight tape seed k hkd t j H Q) control) (column Q j) :=
      column_mul_action _ Q j
    rw [hcol,hstateQ,rotated_residualCoordinates]
    simp only [control,Function.update_self]
  · rw [if_neg hr,if_neg hr,map_zero]

theorem residual_condDistrib_haar_of_invariance (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (ht : t ≤ N) (j : Fin d) (hInv : ResidualInvariance A weight tape seed k hkd t j)
    (H : Transcript N → ResidualControls d) (hH : Measurable H)
    (r : Fin (d+1)) (hrd : r.val < d) :
    ∀ᵐ h ∂(orthogonalHaarProbability d).map (history A weight tape seed t j),
      condDistrib (rankResidual A weight tape seed k hkd t j H r)
        (history A weight tape seed t j) (orthogonalHaarProbability d) h =
      Measure.map (fun Q : OrthogonalGroup (d-r.val) => action Q
        (canonicalRadiusVector (d-r.val) (by omega)
          (observedResidualEnergy A weight tape seed k hkd t r h)))
        (orthogonalHaarProbability (d-r.val)) := by
  have hrot : ∀ᵐ h ∂(orthogonalHaarProbability d).map (history A weight tape seed t j),
      ∀ g : OrthogonalGroup (d-r.val),
      Measure.map (action g) (condDistrib (rankResidual A weight tape seed k hkd t j H r)
        (history A weight tape seed t j) (orthogonalHaarProbability d) h) =
      condDistrib (rankResidual A weight tape seed k hkd t j H r)
        (history A weight tape seed t j) (orthogonalHaarProbability d) h := by
    apply ae_all_orthogonal_invariance_of_each _ (d-r.val) _ (fun _ => inferInstance)
    intro g
    have he := residual_condDistrib_rotation_of_invariance A weight tape seed k hkd t j hInv H hH r g
    filter_upwards [he] with h hh
    simpa only [Kernel.map_apply _ (action g).continuous.measurable] using hh
  filter_upwards [rankResidual_condDistrib_sphere_support A weight tape seed k hkd t ht j H hH r,hrot]
    with h hs hr
  apply invariant_radius_probability_eq_haar
  · filter_upwards [hs] with x hx
    rw [canonicalRadiusVector_norm]
    calc
      ‖x‖ = Real.sqrt (‖x‖^2) := (Real.sqrt_sq (norm_nonneg x)).symm
      _ = Real.sqrt (observedResidualEnergy A weight tape seed k hkd t r h) := congrArg Real.sqrt hx
  · exact hr

#print axioms reframedOrbit_mp_of_invariance
#print axioms residual_condDistrib_haar_of_invariance
end
end Task006.AdaptiveSphereKernel
