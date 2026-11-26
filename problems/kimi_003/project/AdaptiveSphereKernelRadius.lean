import AdaptiveSpherePosteriorKernel
import AdaptiveSphereKernelContinuity

open MeasureTheory Set ProbabilityTheory
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereKernel
noncomputable section

/-- The genuine conditional kernel is supported on an observed norm sphere.
This is obtained from disintegration functoriality, not assumed as a posterior
support premise. -/
theorem condDistrib_normsq_support
    {W H V : Type*} [MeasurableSpace W] [MeasurableSpace H]
    [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [StandardBorelSpace V] [Nonempty V]
    (μ : Measure W) [IsFiniteMeasure μ]
    (obs : W → H) (Y : W → V) (hY : Measurable Y)
    (F : H → ℝ) (hF : Measurable F) (henergy : ∀ w, ‖Y w‖^2 = F (obs w)) :
    ∀ᵐ h ∂μ.map obs, ∀ᵐ x ∂condDistrib Y obs μ h, ‖x‖^2 = F h := by
  have hnorm : Measurable (fun x : V => ‖x‖^2) := measurable_id.norm.pow_const 2
  have hcomp := condDistrib_comp (μ := μ) (mβ := (inferInstance : MeasurableSpace H)) obs hY.aemeasurable hnorm
  have heq : (fun x : V => ‖x‖^2) ∘ Y = F ∘ obs := funext henergy
  rw [heq] at hcomp
  have hdet := condDistrib_comp_self (μ := μ) (mβ := (inferInstance : MeasurableSpace H)) obs hF
  filter_upwards [hcomp,hdet] with h hc hd
  have hm : Measure.map (fun x : V => ‖x‖^2) (condDistrib Y obs μ h) = Measure.dirac (F h) := by
    have he := hc.symm.trans hd
    simpa only [Kernel.map_apply _ hnorm,Kernel.deterministic_apply hF] using he
  have ha : ∀ᵐ y ∂Measure.map (fun x : V => ‖x‖^2) (condDistrib Y obs μ h), y = F h := by
    rw [hm]
    simp
  exact ae_of_ae_map hnorm.aemeasurable ha

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

def observedResidualEnergy (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (r : Fin (d+1)) (h : Transcript N) : ℝ :=
  if (frameFromTranscript A weight tape seed k hkd t h).1 = r then
    1-‖centerFromTranscript A weight tape seed k hkd t h‖^2 else 0

theorem observedResidualEnergy_measurable (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (r : Fin (d+1)) :
    Measurable (observedResidualEnergy A weight tape seed k hkd t r) := by
  have hr := measurable_fst.comp (measurable_frameFromTranscript A weight tape seed k hkd t)
  have hc := measurable_centerFromTranscript A weight tape seed k hkd t
  change Measurable (fun h => if (frameFromTranscript A weight tape seed k hkd t h).1 = r then
    1-‖centerFromTranscript A weight tape seed k hkd t h‖^2 else 0)
  exact Measurable.ite (hr (measurableSet_singleton r))
    (measurable_const.sub (hc.norm.pow_const 2)) measurable_const

theorem rankResidual_normsq_eq_observed (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (ht : t ≤ N)
    (j : Fin d) (H : Transcript N → ResidualControls d) (r : Fin (d+1))
    (Q : OrthogonalGroup d) :
    ‖rankResidual A weight tape seed k hkd t j H r Q‖^2 =
      observedResidualEnergy A weight tape seed k hkd t r (history A weight tape seed t j Q) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have he : (fun i : Fin (d-r.val) => rankResidual A weight tape seed k hkd t j H r Q i) =
      (fun i => restrictedCoordinate A weight tape seed k hkd t j H r i Q) := by
    funext i
    unfold rankResidual restrictedCoordinate
    split_ifs <;> rfl
  have hesum : (∑ i : Fin (d-r.val), (rankResidual A weight tape seed k hkd t j H r Q i)^2) =
      ∑ i : Fin (d-r.val), (restrictedCoordinate A weight tape seed k hkd t j H r i Q)^2 := by
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun z : ℝ => z^2) (congrFun he i))
  rw [hesum,restrictedCoordinate_sum_squares_eq_residualEnergy A weight tape seed k hkd t ht j H r Q]
  rfl

theorem rankResidual_condDistrib_sphere_support (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (ht : t ≤ N) (j : Fin d)
    (H : Transcript N → ResidualControls d) (hH : Measurable H) (r : Fin (d+1)) :
    ∀ᵐ h ∂(orthogonalHaarProbability d).map (history A weight tape seed t j),
      ∀ᵐ x ∂condDistrib (rankResidual A weight tape seed k hkd t j H r)
        (history A weight tape seed t j) (orthogonalHaarProbability d) h,
      ‖x‖^2 = observedResidualEnergy A weight tape seed k hkd t r h :=
  condDistrib_normsq_support _ _ _ (rankResidual_measurable A weight tape seed k hkd t j H hH r)
    _ (observedResidualEnergy_measurable A weight tape seed k hkd t r)
    (rankResidual_normsq_eq_observed A weight tape seed k hkd t ht j H r)

/-- A single full-measure set of transcripts works simultaneously for EVERY
orthogonal residual rotation; countable density removes the separate nullsets. -/
theorem rankResidual_condDistrib_all_rotations (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (ht : t ≤ N) (j : Fin d) (hstop : RankStopped A weight tape seed k hkd)
    (H : Transcript N → ResidualControls d) (hH : Measurable H) (r : Fin (d+1)) :
    ∀ᵐ h ∂(orthogonalHaarProbability d).map (history A weight tape seed t j),
      ∀ g : OrthogonalGroup (d-r.val),
      Measure.map (action g)
        (condDistrib (rankResidual A weight tape seed k hkd t j H r)
          (history A weight tape seed t j) (orthogonalHaarProbability d) h) =
        condDistrib (rankResidual A weight tape seed k hkd t j H r)
          (history A weight tape seed t j) (orthogonalHaarProbability d) h := by
  apply ae_all_orthogonal_invariance_of_each
    ((orthogonalHaarProbability d).map (history A weight tape seed t j)) (d-r.val)
    (condDistrib (rankResidual A weight tape seed k hkd t j H r)
      (history A weight tape seed t j) (orthogonalHaarProbability d))
  · intro h
    infer_instance
  · intro g
    have he := rankResidual_condDistrib_rotation A weight tape seed k hkd t ht j hstop H hH r g
    filter_upwards [he] with h hh
    simpa only [Kernel.map_apply _ (action g).continuous.measurable] using hh

#print axioms condDistrib_normsq_support
#print axioms rankResidual_normsq_eq_observed
#print axioms rankResidual_condDistrib_sphere_support
#print axioms rankResidual_condDistrib_all_rotations
end
end Task006.AdaptiveSphereKernel
