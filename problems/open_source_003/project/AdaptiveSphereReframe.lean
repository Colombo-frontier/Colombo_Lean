import AdaptiveSphereInvariance
import AdaptiveSphereCoordinateSwap

/-! Measurable residual changes of frame preserve the already proved adaptive
posterior symmetry. This permits preparing the next query direction before its
reply, without presupposing its conditional second moment. -/
open MeasureTheory Set
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereReframe
open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereBlock
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereResidualFrame
open Task006.AdaptiveSphereState Task006.AdaptiveSphereAction
open Task006.AdaptiveSphereStopped Task006.AdaptiveSphereInvariance
open Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereMeasurable
open Task006.AdaptiveSphereOrbit Task006.AdaptiveSphereCoordinateRotations
noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

def conjugateControls (H g : ResidualControls d) : ResidualControls d :=
  fun r => H r * g r * (H r)⁻¹

theorem conjugateControls_joint_continuous :
    Continuous (fun p : ResidualControls d × ResidualControls d => conjugateControls p.1 p.2) := by
  apply continuous_pi
  intro r
  exact (((continuous_apply r).comp continuous_fst).mul
    ((continuous_apply r).comp continuous_snd)).mul
      (((continuous_apply r).comp continuous_fst).inv)

def reframe (state : FrameState d) (H : ResidualControls d) : FrameState d :=
  (state.1,state.2 * blockOrthogonal d state.1.val (by omega) (H state.1))

theorem reframe_joint_measurable :
    Measurable (fun p : FrameState d × ResidualControls d => reframe p.1 p.2) := by
  have hfixed (r : Fin (d+1)) : Measurable
      (fun p : OrthogonalGroup d × ResidualControls d => reframe (r,p.1) p.2) := by
    have heval : Measurable (fun p : OrthogonalGroup d × ResidualControls d => p.2 r) :=
      (measurable_pi_apply r).comp measurable_snd
    have hblock := (blockOrthogonal_measurable d r.val (by omega)).comp heval
    have hrot := measurable_fst.mul hblock
    exact measurable_const.prodMk hrot
  have hall : Measurable (fun p : Fin (d+1) × (OrthogonalGroup d × ResidualControls d) =>
      reframe (p.1,p.2.1) p.2.2) := measurable_from_prod_countable_right hfixed
  have hin : Measurable (fun p : FrameState d × ResidualControls d =>
      (p.1.1,(p.1.2,p.2))) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hr := hall.comp hin
  simpa only [Function.comp_def] using hr

theorem reframe_rotation (state : FrameState d) (H g : ResidualControls d) :
    rotateAtState (reframe state H) g = rotateAtState state (conjugateControls H g) := by
  simp only [rotateAtState,reframe,conjugateControls,blockOrthogonal_mul,blockOrthogonal_inv,
    mul_inv_rev]
  group

def reframedState (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d)
    (H : Transcript N → ResidualControls d) (Q : OrthogonalGroup d) : FrameState d :=
  reframe (actualState A weight tape seed k hkd t j Q) (H (history A weight tape seed t j Q))

def reframedOrbit (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d)
    (H : Transcript N → ResidualControls d) (g : ResidualControls d)
    (Q : OrthogonalGroup d) : OrthogonalGroup d :=
  rotateAtState (reframedState A weight tape seed k hkd t j H Q) g * Q

theorem reframedOrbit_factorization (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d)
    (H : Transcript N → ResidualControls d) (g : ResidualControls d) (Q : OrthogonalGroup d) :
    reframedOrbit A weight tape seed k hkd t j H g Q =
      orbitTransform A weight tape seed k hkd t j
        (conjugateControls (H (history A weight tape seed t j Q)) g) Q := by
  unfold reframedOrbit reframedState
  rw [reframe_rotation]
  rfl

theorem reframedOrbit_measurePreserving (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (ht : t ≤ N)
    (j : Fin d) (hstop : RankStopped A weight tape seed k hkd)
    (H : Transcript N → ResidualControls d) (hH : Measurable H) (g : ResidualControls d) :
    MeasurePreserving (reframedOrbit A weight tape seed k hkd t j H g)
      (orthogonalHaarProbability d) (orthogonalHaarProbability d) := by
  obtain ⟨hmp,hfix⟩ := rankStopped_residual_invariance A weight tape seed k hkd j hstop t ht
  have hc : Measurable (fun h => conjugateControls (H h) g) := by
    have hin : Measurable (fun h : Transcript N => (H h,g)) := hH.prodMk measurable_const
    have hr := (conjugateControls_joint_continuous (d := d)).measurable.comp hin
    simpa only [Function.comp_def] using hr
  have hr := observable_dependent_symmetry_measurePreserving
    (history A weight tape seed t j) (measurable_history A weight tape seed t j)
    (fun h => conjugateControls (H h) g) hc
    (orbitTransform A weight tape seed k hkd t j) hmp
    (orbitTransform_joint_measurable A weight tape seed k hkd t j)
    (orbitTransform_control_continuous A weight tape seed k hkd t j) hfix
  have heq : (fun Q => orbitTransform A weight tape seed k hkd t j
      (conjugateControls (H (history A weight tape seed t j Q)) g) Q) =
      reframedOrbit A weight tape seed k hkd t j H g := by
    funext Q
    exact (reframedOrbit_factorization A weight tape seed k hkd t j H g Q).symm
  rw [heq] at hr
  exact hr

theorem reframedOrbit_fixes_history (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (ht : t ≤ N)
    (j : Fin d) (hstop : RankStopped A weight tape seed k hkd)
    (H : Transcript N → ResidualControls d) (g : ResidualControls d) (Q : OrthogonalGroup d) :
    history A weight tape seed t j (reframedOrbit A weight tape seed k hkd t j H g Q) =
      history A weight tape seed t j Q := by
  rw [reframedOrbit_factorization]
  exact (rankStopped_residual_invariance A weight tape seed k hkd j hstop t ht).2 _ Q

#print axioms conjugateControls_joint_continuous
#print axioms reframe_joint_measurable
#print axioms reframe_rotation
#print axioms reframedOrbit_measurePreserving
#print axioms reframedOrbit_fixes_history
end
end Task006.AdaptiveSphereReframe
