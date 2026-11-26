import AdaptiveSphereFullPosterior
import AdaptiveSpherePosteriorInterfaces
import AdaptiveSphereFullRank

/-! Full regular conditional sphere-fiber law for an unrestricted ORIGINAL
canonical policy. It may continue making queries after obtaining full rank. -/
open MeasureTheory Set ProbabilityTheory
open scoped Matrix RealInnerProductSpace
namespace Task006.AdaptiveSphereKernel
open Task006.ConditionalKernelComposition Task006.AdaptiveSphereFullRank
noncomputable section
open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereBlock
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereResidualFrame
open Task006.AdaptiveSphereState Task006.AdaptiveSphereAction
open Task006.AdaptiveSphereStopped Task006.AdaptiveSphereInvariance
open Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereMeasurable
open Task006.AdaptiveSphereGeometry Task006.PosteriorCenter Task006.AdaptiveSphereActualStep
open Task006.AdaptiveSphereMean Task006.AdaptiveSphereReframe Task006.AdaptiveSphere
open Task006.AdaptiveSphereIsotropy Task006.PosteriorResidualEnergy
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

theorem full_posterior_of_invariance (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (ht : t ≤ N) (j : Fin d) (hInv : ResidualInvariance A weight tape seed k hkd t j)
    (H : Transcript N → ResidualControls d) (hH : Measurable H)
    (r : Fin (d+1)) (hrd : r.val < d) :
    ∀ᵐ h ∂(orthogonalHaarProbability d).map (history A weight tape seed t j),
      (observedFrame A weight tape seed k hkd t H h).1 = r →
      condDistrib (fun Q => column Q j) (history A weight tape seed t j) (orthogonalHaarProbability d) h =
      Measure.map (fun Q : OrthogonalGroup (d-r.val) =>
        centerFromTranscript A weight tape seed k hkd t h +
          action (observedFrame A weight tape seed k hkd t H h).2
            (liftResidual r.val (by omega) (action Q
              (canonicalRadiusVector (d-r.val) (by omega)
                (observedResidualEnergy A weight tape seed k hkd t r h)))))
        (orthogonalHaarProbability (d-r.val)) := by
  classical
  let p : Transcript N → Prop := fun h => (observedFrame A weight tape seed k hkd t H h).1 = r
  have hp : MeasurableSet {h : Transcript N | p h} :=
    (measurable_fst.comp (observedFrame_measurable A weight tape seed k hkd t H hH))
      (measurableSet_singleton r)
  have hgate := condDistrib_observable_gate (orthogonalHaarProbability d)
    (history A weight tape seed t j) (measurable_history A weight tape seed t j)
    (fun Q => column Q j) (measurable_column j) p hp
  let f : Transcript N × E (d-r.val) → E d :=
    fun q => fiberAffine A weight tape seed k hkd t H r q.1 q.2
  have hf : Measurable f := fiberAffine_joint_measurable A weight tape seed k hkd t H hH r
  have haff := condDistrib_dependent_comp (orthogonalHaarProbability d)
    (history A weight tape seed t j) (measurable_history A weight tape seed t j)
    (rankResidual A weight tape seed k hkd t j H r)
    (rankResidual_measurable A weight tape seed k hkd t j H hH r) f hf
  have heq : (fun Q => f (history A weight tape seed t j Q,
      rankResidual A weight tape seed k hkd t j H r Q)) =
      rankTheta A weight tape seed k hkd t j H r := by
    funext Q
    exact (rankTheta_eq_fiberAffine A weight tape seed k hkd t ht j H r Q).symm
  rw [heq] at haff
  have hres := residual_condDistrib_haar_of_invariance A weight tape seed k hkd t ht j hInv H hH r hrd
  filter_upwards [hgate,haff,hres] with h hg ha hr
  intro hR
  have hg' : condDistrib (rankTheta A weight tape seed k hkd t j H r)
      (history A weight tape seed t j) (orthogonalHaarProbability d) h =
      condDistrib (fun Q => column Q j) (history A weight tape seed t j) (orthogonalHaarProbability d) h :=
    hg hR
  rw [← hg',ha,dependentMap_apply _ f hf,hr]
  have hfa : Measurable (fun z : E (d-r.val) => f (h,z)) := hf.comp measurable_prodMk_left
  have hOrbit : Measurable (fun Q : OrthogonalGroup (d-r.val) => action Q
      (canonicalRadiusVector (d-r.val) (by omega)
        (observedResidualEnergy A weight tape seed k hkd t r h))) := by
    let x0 : E (d-r.val) := canonicalRadiusVector (d-r.val) (by omega)
      (observedResidualEnergy A weight tape seed k hkd t r h)
    have hin : Measurable (fun Q : OrthogonalGroup (d-r.val) => (Q,x0)) :=
      measurable_id.prodMk measurable_const
    have hm := (action_joint_continuous (d := d-r.val)).measurable.comp hin
    simpa only [Function.comp_def,x0] using hm
  rw [Measure.map_map hfa hOrbit]
  congr 1
  funext Q
  simp only [Function.comp_def,f,fiberAffine,if_pos hR]

/-- No stopping assumption occurs in this actual original-policy theorem. -/
theorem original_full_posterior_fiber (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S)
    (t : ℕ) (ht : t ≤ N) (j : Fin d)
    (H : Transcript N → ResidualControls d) (hH : Measurable H)
    (r : Fin (d+1)) (hrd : r.val < d) :
    ∀ᵐ h ∂(orthogonalHaarProbability d).map (history A weight tape seed t j),
      (observedFrame A weight tape seed d le_rfl t H h).1 = r →
      condDistrib (fun Q => column Q j) (history A weight tape seed t j) (orthogonalHaarProbability d) h =
      Measure.map (fun Q : OrthogonalGroup (d-r.val) =>
        centerFromTranscript A weight tape seed d le_rfl t h +
          action (observedFrame A weight tape seed d le_rfl t H h).2
            (liftResidual r.val (by omega) (action Q
              (canonicalRadiusVector (d-r.val) (by omega)
                (observedResidualEnergy A weight tape seed d le_rfl t r h)))))
        (orthogonalHaarProbability (d-r.val)) := by
  exact full_posterior_of_invariance A weight tape seed d le_rfl t ht j
    (original_residual_invariance A weight tape seed j t ht) H hH r hrd

#print axioms full_posterior_of_invariance
#print axioms original_full_posterior_fiber
end
end Task006.AdaptiveSphereKernel
