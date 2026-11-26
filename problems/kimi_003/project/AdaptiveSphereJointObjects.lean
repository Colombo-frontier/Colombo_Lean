import AdaptiveSphereJoint
import PosteriorCenterEnergy
import ExternalPriorHandleCount

open MeasureTheory

namespace Task006.AdaptiveSphereJoint

open Task006.Full Task006.Full.OracleAlgorithm Task006.HaarRebalancing
open Task006.AdaptiveSphereState Task006.AdaptiveSphereStopped
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereTranscript Task006.PosteriorCenter

noncomputable section
variable {d N : ℕ} {S : Type*} [MeasurableSpace S]

abbrev JointInput (d : ℕ) (S : Type*) := (Space d × S) × (ℕ → ℝ)

def stoppedHistory (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (w : JointInput d S) : Transcript N :=
  (stoppedObserver A id w.2 w.1.2 k hkd).finalTranscript (linearSample id w.1.1) w.2 ()

def stoppedFrame (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (w : JointInput d S) : FrameState d :=
  frameFromTranscript A id w.2 w.1.2 k hkd t (stoppedHistory A k hkd w)

def stoppedCenter (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (w : JointInput d S) : Space d :=
  centerFromTranscript A id w.2 w.1.2 k hkd t (stoppedHistory A k hkd w)

def stoppedRank (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (w : JointInput d S) : ℕ := (stoppedFrame A k hkd t w).1.val

theorem stoppedHistory_measurable (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d) :
    Measurable (stoppedHistory A k hkd) := stopped_runPrefix_joint_measurable A k hkd N

theorem stoppedFrame_measurable (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) :
    Measurable (stoppedFrame A k hkd t) := by
  change Measurable (fun w : JointInput d S =>
    frameFromTranscript A id w.2 w.1.2 k hkd t (stoppedHistory A k hkd w))
  have hm := (frameFromTranscript_joint_measurable A k hkd t).comp
    ((measurable_fst.snd.prodMk measurable_snd).prodMk (stoppedHistory_measurable A k hkd))
  simpa only [stoppedFrame,Function.comp_def] using hm

theorem stoppedCenter_measurable (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) :
    Measurable (stoppedCenter A k hkd t) := by
  change Measurable (fun w : JointInput d S =>
    centerFromTranscript A id w.2 w.1.2 k hkd t (stoppedHistory A k hkd w))
  have hm := (centerFromTranscript_joint_measurable A k hkd t).comp
    ((measurable_fst.snd.prodMk measurable_snd).prodMk (stoppedHistory_measurable A k hkd))
  simpa only [stoppedCenter,Function.comp_def] using hm

theorem stoppedRank_measurable (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) :
    Measurable (stoppedRank A k hkd t) := by
  have hv : Measurable (fun r : Fin (d+1) => r.val) := measurable_of_countable _
  exact hv.comp (measurable_fst.comp (stoppedFrame_measurable A k hkd t))

theorem stoppedObserver_center_eq (A : OracleAlgorithm d N S) (tape : ℕ → ℝ)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (h : Transcript N) :
    centerFromTranscript (stoppedObserver A id tape seed k hkd) id tape () k hkd t h =
      centerFromTranscript A id tape seed k hkd t h := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [centerFromTranscript,centerFromTranscript]
    split_ifs with ht
    · rw [ih,stoppedObserver_frame_eq]
      change centerStep k hkd (frameFromTranscript A id tape seed k hkd t h)
          (centerFromTranscript A id tape seed k hkd t h)
          (effectiveVector id tape (stopAction A id tape seed k hkd ⟨t,ht⟩ h)) (h ⟨t,ht⟩) = _
      by_cases hr : (frameFromTranscript A id tape seed k hkd t h).1.val < k
      · simp only [stopAction,if_pos hr]
      · simp only [stopAction,if_neg hr,centerStep,dif_neg hr]
    · exact ih

theorem stoppedCenter_eq_projected (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (w : JointInput d S) :
    stoppedCenter A k hkd t w = projectedCenter (stoppedFrame A k hkd t w) w.1.1 := by
  have h := centerFromTranscript_actual_eq_projected
    (stoppedObserver A id w.2 w.1.2 k hkd) id w.2 () k hkd w.1.1 t
  rw [stoppedObserver_center_eq,stoppedObserver_frame_eq] at h
  exact h

theorem stoppedCenter_norm_le (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (w : JointInput d S) : ‖stoppedCenter A k hkd t w‖ ≤ ‖w.1.1‖ := by
  rw [stoppedCenter_eq_projected]
  exact projectedCenter_norm_le _ _

def haarInput (j : Fin d) (w : (S × OrthogonalGroup d) × (ℕ → ℝ)) : JointInput d S :=
  ((column w.1.2 j,w.1.1),w.2)

theorem haarInput_measurable (j : Fin d) : Measurable (haarInput (S := S) j) :=
  (((measurable_column j).comp measurable_fst.snd).prodMk measurable_fst.fst).prodMk measurable_snd

theorem haar_stopped_center_integrable (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (j : Fin d)
    (γ : Measure ((S × OrthogonalGroup d) × (ℕ → ℝ))) [IsFiniteMeasure γ] :
    Integrable (fun w => stoppedCenter A k hkd t (haarInput j w)) γ := by
  have hm := (stoppedCenter_measurable A k hkd t).comp (haarInput_measurable j)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro w
  have hb := stoppedCenter_norm_le A k hkd t (haarInput j w)
  have hn : ‖column w.1.2 j‖ = 1 := (orthonormal_column w.1.2).norm_eq_one j
  simpa only [haarInput,hn,Function.comp_def] using hb

end
end Task006.AdaptiveSphereJoint
