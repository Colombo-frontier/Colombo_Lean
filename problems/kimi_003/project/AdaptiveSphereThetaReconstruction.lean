import AdaptiveSphereFiberLaw

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

theorem continuous_liftResidual (r : ℕ) (hr : r ≤ d) :
    Continuous (liftResidual (d := d) r hr) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
  apply continuous_pi
  intro i
  by_cases hi : i.val < r
  · simp only [dif_pos hi]
    exact (continuous_const : Continuous (fun _ : E (d-r) => (0:ℝ)))
  · simp only [dif_neg hi]
    exact (EuclideanSpace.proj (⟨i.val-r,by omega⟩ : Fin (d-r))).continuous

def observedFrame (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ)
    (H : Transcript N → ResidualControls d) (h : Transcript N) : FrameState d :=
  reframe (frameFromTranscript A weight tape seed k hkd t h) (H h)

theorem observedFrame_measurable (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ)
    (H : Transcript N → ResidualControls d) (hH : Measurable H) :
    Measurable (observedFrame A weight tape seed k hkd t H) := by
  have hm := (reframe_joint_measurable (d := d)).comp
    ((measurable_frameFromTranscript A weight tape seed k hkd t).prodMk hH)
  change Measurable (fun h => reframe (frameFromTranscript A weight tape seed k hkd t h) (H h))
  simpa only [Function.comp_def] using hm

def rankTheta (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d)
    (H : Transcript N → ResidualControls d) (r : Fin (d+1)) (Q : OrthogonalGroup d) : E d :=
  if (observedFrame A weight tape seed k hkd t H (history A weight tape seed t j Q)).1 = r
    then column Q j else 0

def fiberAffine (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ)
    (H : Transcript N → ResidualControls d) (r : Fin (d+1))
    (h : Transcript N) (z : E (d-r.val)) : E d :=
  if (observedFrame A weight tape seed k hkd t H h).1 = r then
    centerFromTranscript A weight tape seed k hkd t h +
      action (observedFrame A weight tape seed k hkd t H h).2 (liftResidual r.val (by omega) z)
  else 0

theorem fiberAffine_joint_measurable (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ)
    (H : Transcript N → ResidualControls d) (hH : Measurable H) (r : Fin (d+1)) :
    Measurable (fun p : Transcript N × E (d-r.val) =>
      fiberAffine A weight tape seed k hkd t H r p.1 p.2) := by
  have hs := (observedFrame_measurable A weight tape seed k hkd t H hH).comp
    (measurable_fst : Measurable (Prod.fst : Transcript N × E (d-r.val) → Transcript N))
  have hr := measurable_fst.comp hs
  have hB := measurable_snd.comp hs
  have hlift := (continuous_liftResidual r.val (by omega)).measurable.comp
    (measurable_snd : Measurable (Prod.snd : Transcript N × E (d-r.val) → E (d-r.val)))
  have ha := orthogonal_action_measurable.comp (hB.prodMk hlift)
  have hC := (measurable_centerFromTranscript A weight tape seed k hkd t).comp
    (measurable_fst : Measurable (Prod.fst : Transcript N × E (d-r.val) → Transcript N))
  change Measurable (fun p : Transcript N × E (d-r.val) =>
    if (observedFrame A weight tape seed k hkd t H p.1).1 = r then
      centerFromTranscript A weight tape seed k hkd t p.1 +
        action (observedFrame A weight tape seed k hkd t H p.1).2 (liftResidual r.val (by omega) p.2)
    else 0)
  exact Measurable.ite (hr (measurableSet_singleton r)) (hC.add ha) measurable_const

/-- The actual hidden vector is reconstructed from its observed center and
residual coordinates on the corresponding rank event. -/
theorem rankTheta_eq_fiberAffine (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (ht : t ≤ N)
    (j : Fin d) (H : Transcript N → ResidualControls d) (r : Fin (d+1))
    (Q : OrthogonalGroup d) :
    rankTheta A weight tape seed k hkd t j H r Q =
      fiberAffine A weight tape seed k hkd t H r (history A weight tape seed t j Q)
        (rankResidual A weight tape seed k hkd t j H r Q) := by
  let state := observedFrame A weight tape seed k hkd t H (history A weight tape seed t j Q)
  have hstate : state = reframedState A weight tape seed k hkd t j H Q := rfl
  by_cases hr : state.1 = r
  · have hc : centerFromTranscript A weight tape seed k hkd t (history A weight tape seed t j Q) =
        projectedCenter state (column Q j) := by
      rw [hstate,reframedState,reframe_projectedCenter]
      exact actualCenter_eq_projected A weight tape seed k hkd t ht j Q
    have hr' : (reframedState A weight tape seed k hkd t j H Q).1 = r := hstate ▸ hr
    simp only [rankTheta,fiberAffine,show
      (observedFrame A weight tape seed k hkd t H (history A weight tape seed t j Q)).1 = r from hr,
      if_true,rankResidual,if_pos hr']
    rw [hc,projectedCenter,hr]
    have hdecomp := congrArg (action state.2)
      (coordinate_decomposition r.val (by omega) (action state.2⁻¹ (column Q j)))
    rw [action_inverse_cancel,map_add] at hdecomp
    exact hdecomp
  · have hr' : (reframedState A weight tape seed k hkd t j H Q).1 ≠ r := by
      rw [← hstate]
      exact hr
    simp only [rankTheta,fiberAffine,show
      ¬(observedFrame A weight tape seed k hkd t H (history A weight tape seed t j Q)).1 = r from hr,
      if_false]

#print axioms continuous_liftResidual
#print axioms fiberAffine_joint_measurable
#print axioms rankTheta_eq_fiberAffine
end
end Task006.AdaptiveSphereKernel
