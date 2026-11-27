import AdaptiveSphereJointObjects
import AdaptiveSphereInvariance

open MeasureTheory

namespace Task006.AdaptiveSphereGlobal

open Task006.Full Task006.Full.OracleAlgorithm Task006.HaarRebalancing
open Task006.AdaptiveSphereState Task006.AdaptiveSphereStopped Task006.AdaptiveSphereAction
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereTranscript
open Task006.AdaptiveSphereJoint Task006.AdaptiveSphereInvariance

set_option maxHeartbeats 1000000
noncomputable section
variable {d N : ℕ} {S : Type*} [MeasurableSpace S]

abbrev Exogenous (S : Type*) := S × (ℕ → ℝ)

def exogenousHaarInput (j : Fin d) (w : Exogenous S × OrthogonalGroup d) : JointInput d S :=
  ((column w.2 j,w.1.1),w.1.2)

theorem exogenousHaarInput_measurable (j : Fin d) :
    Measurable (exogenousHaarInput (S := S) j) :=
  (((measurable_column j).comp measurable_snd).prodMk measurable_fst.fst).prodMk measurable_fst.snd

def jointHistory (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (j : Fin d) (w : Exogenous S × OrthogonalGroup d) : Transcript N :=
  (stoppedObserver A id w.1.2 w.1.1 k hkd).runPrefix (linearSample id (column w.2 j)) w.1.2 () t

theorem jointHistory_measurable (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (j : Fin d) : Measurable (jointHistory A k hkd t j) := by
  change Measurable (fun w : Exogenous S × OrthogonalGroup d =>
    (stoppedObserver A id w.1.2 w.1.1 k hkd).runPrefix (linearSample id (column w.2 j)) w.1.2 () t)
  have hm := (stopped_runPrefix_joint_measurable A k hkd t).comp (exogenousHaarInput_measurable j)
  simpa only [exogenousHaarInput,Function.comp_def] using hm

def jointFrame (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (j : Fin d) (w : Exogenous S × OrthogonalGroup d) : FrameState d :=
  frameFromTranscript A id w.1.2 w.1.1 k hkd t (jointHistory A k hkd t j w)

theorem jointFrame_measurable (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (j : Fin d) : Measurable (jointFrame A k hkd t j) := by
  change Measurable (fun w : Exogenous S × OrthogonalGroup d =>
    frameFromTranscript A id w.1.2 w.1.1 k hkd t (jointHistory A k hkd t j w))
  have hm := (frameFromTranscript_joint_measurable A k hkd t).comp
    (measurable_fst.prodMk (jointHistory_measurable A k hkd t j))
  simpa only [Function.comp_def] using hm

def jointOrbit (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (j : Fin d) (g : ResidualControls d)
    (w : Exogenous S × OrthogonalGroup d) : Exogenous S × OrthogonalGroup d :=
  (w.1,rotateAtState (jointFrame A k hkd t j w) g * w.2)

theorem jointOrbit_measurable (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (j : Fin d) (g : ResidualControls d) : Measurable (jointOrbit A k hkd t j g) := by
  change Measurable (fun w : Exogenous S × OrthogonalGroup d =>
    (w.1,rotateAtState (jointFrame A k hkd t j w) g * w.2))
  have hr := (rotateAtState_joint_measurable (d := d)).comp
    ((jointFrame_measurable A k hkd t j).prodMk (measurable_const (a := g)))
  have hm := measurable_fst.prodMk (hr.mul measurable_snd)
  simpa only [jointOrbit,Function.comp_def,Pi.mul_apply] using hm

theorem jointOrbit_snd_eq (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (j : Fin d) (g : ResidualControls d) (z : Exogenous S) (Q : OrthogonalGroup d) :
    (jointOrbit A k hkd t j g (z,Q)).2 =
      orbitTransform (stoppedObserver A id z.2 z.1 k hkd) id z.2 () k hkd t j g Q := by
  simp only [jointOrbit,jointFrame,jointHistory,orbitTransform,actualState,history,
    stoppedObserver_frame_eq]

theorem jointOrbit_measurePreserving (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (ht : t ≤ N) (j : Fin d) (g : ResidualControls d)
    (γ : Measure (Exogenous S)) [SFinite γ] :
    MeasurePreserving (jointOrbit A k hkd t j g)
      (γ.prod (orthogonalHaarProbability d)) (γ.prod (orthogonalHaarProbability d)) := by
  have hsecond : Measurable (fun w : Exogenous S × OrthogonalGroup d =>
      (jointOrbit A k hkd t j g w).2) := measurable_snd.comp (jointOrbit_measurable A k hkd t j g)
  have hmap (z : Exogenous S) :
      Measure.map (fun Q => (jointOrbit A k hkd t j g (z,Q)).2) (orthogonalHaarProbability d) =
        orthogonalHaarProbability d := by
    have he : (fun Q => (jointOrbit A k hkd t j g (z,Q)).2) =
        orbitTransform (stoppedObserver A id z.2 z.1 k hkd) id z.2 () k hkd t j g :=
      funext (jointOrbit_snd_eq A k hkd t j g z)
    rw [he]
    exact ((stoppedObserver_residual_invariance A id z.2 z.1 k hkd j t ht).1 g).map_eq
  have hp := (MeasurePreserving.id γ).skew_product hsecond (Filter.Eventually.of_forall hmap)
  change MeasurePreserving (fun w : Exogenous S × OrthogonalGroup d =>
    (w.1,rotateAtState (jointFrame A k hkd t j w) g * w.2)) _ _
  simpa only [jointOrbit,id_eq,Prod.eta] using hp

theorem jointOrbit_fixes_history (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (ht : t ≤ N) (j : Fin d) (g : ResidualControls d)
    (w : Exogenous S × OrthogonalGroup d) :
    jointHistory A k hkd t j (jointOrbit A k hkd t j g w) = jointHistory A k hkd t j w := by
  rcases w with ⟨z,Q⟩
  change history (stoppedObserver A id z.2 z.1 k hkd) id z.2 () t j
      ((jointOrbit A k hkd t j g (z,Q)).2) =
    history (stoppedObserver A id z.2 z.1 k hkd) id z.2 () t j Q
  rw [jointOrbit_snd_eq]
  exact (stoppedObserver_residual_invariance A id z.2 z.1 k hkd j t ht).2 g Q

end
end Task006.AdaptiveSphereGlobal
