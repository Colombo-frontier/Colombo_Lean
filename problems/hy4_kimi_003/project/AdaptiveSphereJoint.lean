import AdaptiveSphereStoppedCoupling
import PosteriorCenter
import OracleParameterizedMeasurable

open MeasureTheory

namespace Task006.AdaptiveSphereJoint

open Task006.Full Task006.Full.OracleAlgorithm
open Task006.AdaptiveSphereState Task006.AdaptiveSphereStopped
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereTranscript Task006.PosteriorCenter

set_option maxHeartbeats 1000000

noncomputable section
variable {d N : ℕ} {S : Type*} [MeasurableSpace S]

theorem effectiveVector_joint_measurable :
    Measurable (fun w : (ℕ → ℝ) × QueryAction d => effectiveVector id w.1 w.2) := by
  have heval : Measurable (fun w : (ℕ → ℝ) × ℕ => w.1 w.2) :=
    measurable_from_prod_countable_left (fun k => measurable_pi_apply k)
  let f : (Unit × (ℕ → ℝ)) ⊕ ((ℕ × Space d) × (ℕ → ℝ)) → Space d :=
    Sum.elim (fun _ => 0) (fun p => p.2 p.1.1 • p.1.2)
  have hf : Measurable f := by
    apply Measurable.sumElim measurable_const
    exact (heval.comp (measurable_snd.prodMk measurable_fst.fst)).smul measurable_fst.snd
  have hs := (MeasurableEquiv.sumProdDistrib Unit (ℕ × Space d) (ℕ → ℝ)).measurable
  have hm := hf.comp (hs.comp
    (((measurable_actionToSum d).comp measurable_snd).prodMk measurable_fst))
  have heq : (fun w : (ℕ → ℝ) × QueryAction d => effectiveVector id w.1 w.2) =
      fun w => f ((MeasurableEquiv.sumProdDistrib Unit (ℕ × Space d) (ℕ → ℝ))
        (actionToSum d w.2,w.1)) := by
    funext w
    rcases w with ⟨tape,a⟩
    cases a <;> rfl
  rw [heq]
  exact hm

theorem query_joint_measurable (A : OracleAlgorithm d N S) (t : Fin N) :
    Measurable (fun w : (S × (ℕ → ℝ)) × Transcript N =>
      effectiveVector id w.1.2 (A.action t w.1.1 w.2)) := by
  have ha : Measurable (fun w : (S × (ℕ → ℝ)) × Transcript N => A.action t w.1.1 w.2) :=
    (A.action_measurable t).comp (measurable_fst.fst.prodMk measurable_snd)
  have hm := (effectiveVector_joint_measurable (d := d)).comp (measurable_fst.snd.prodMk ha)
  simpa only [Function.comp_def] using hm

theorem frameFromTranscript_joint_measurable (A : OracleAlgorithm d N S)
    (k : ℕ) (hkd : k ≤ d) (t : ℕ) :
    Measurable (fun w : (S × (ℕ → ℝ)) × Transcript N =>
      frameFromTranscript A id w.1.2 w.1.1 k hkd t w.2) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    by_cases ht : t < N
    · have hm := (measurable_stateStep k hkd).comp (ih.prodMk (query_joint_measurable A ⟨t,ht⟩))
      simpa only [frameFromTranscript,dif_pos ht,Function.comp_def] using hm
    · simpa only [frameFromTranscript,dif_neg ht] using ih

theorem centerFromTranscript_joint_measurable (A : OracleAlgorithm d N S)
    (k : ℕ) (hkd : k ≤ d) (t : ℕ) :
    Measurable (fun w : (S × (ℕ → ℝ)) × Transcript N =>
      centerFromTranscript A id w.1.2 w.1.1 k hkd t w.2) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    by_cases ht : t < N
    · have hreply : Measurable (fun w : (S × (ℕ → ℝ)) × Transcript N => w.2 ⟨t,ht⟩) :=
        (measurable_pi_apply (⟨t,ht⟩ : Fin N)).comp measurable_snd
      have hm := (measurable_centerStep k hkd).comp
        ((frameFromTranscript_joint_measurable A k hkd t).prodMk
          (ih.prodMk ((query_joint_measurable A ⟨t,ht⟩).prodMk hreply)))
      simpa only [centerFromTranscript,dif_pos ht,Function.comp_def] using hm
    · simpa only [centerFromTranscript,dif_neg ht] using ih

theorem stopAction_joint_measurable (A : OracleAlgorithm d N S)
    (k : ℕ) (hkd : k ≤ d) (t : Fin N) :
    Measurable (fun w : (S × (ℕ → ℝ)) × Transcript N =>
      stopAction A id w.1.2 w.1.1 k hkd t w.2) := by
  have hframe := frameFromTranscript_joint_measurable A k hkd t.val
  have hval : Measurable (fun r : Fin (d+1) => r.val) := measurable_of_countable _
  have hnat := hval.comp (measurable_fst.comp hframe)
  have hset : MeasurableSet {w : (S × (ℕ → ℝ)) × Transcript N |
      (frameFromTranscript A id w.1.2 w.1.1 k hkd t.val w.2).1.val < k} :=
    hnat measurableSet_Iio
  have ha : Measurable (fun w : (S × (ℕ → ℝ)) × Transcript N => A.action t w.1.1 w.2) :=
    (A.action_measurable t).comp (measurable_fst.fst.prodMk measurable_snd)
  exact Measurable.ite hset ha measurable_const

theorem stopped_runPrefix_joint_measurable (A : OracleAlgorithm d N S)
    (k : ℕ) (hkd : k ≤ d) (t : ℕ) :
    Measurable (fun w : (Space d × S) × (ℕ → ℝ) =>
      (stoppedObserver A id w.2 w.1.2 k hkd).runPrefix (linearSample id w.1.1) w.2 () t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    by_cases ht : t < N
    · have ha := (stopAction_joint_measurable A k hkd ⟨t,ht⟩).comp
        ((measurable_fst.snd.prodMk measurable_snd).prodMk ih)
      have hF : Measurable (fun p : Space d × (Space d × ℝ) => linearSample id p.1 p.2.1 p.2.2) :=
        measurable_snd.snd.mul (measurable_fst.inner measurable_snd.fst)
      have hr := (scalarReply_parameter_measurable (linearSample id) hF).comp
        (measurable_fst.fst.prodMk (measurable_snd.prodMk ha))
      have hm : Measurable (fun w : (Space d × S) × (ℕ → ℝ) =>
          Function.update
            ((stoppedObserver A id w.2 w.1.2 k hkd).runPrefix (linearSample id w.1.1) w.2 () t)
            (⟨t,ht⟩ : Fin N)
            (scalarReply (linearSample id w.1.1) w.2
              (stopAction A id w.2 w.1.2 k hkd ⟨t,ht⟩
                ((stoppedObserver A id w.2 w.1.2 k hkd).runPrefix (linearSample id w.1.1) w.2 () t)))) :=
        measurable_update'.comp (ih.prodMk hr)
      simpa only [runPrefix,dif_pos ht,stoppedObserver,Function.comp_def] using hm
    · simpa only [runPrefix,dif_neg ht] using ih

end
end Task006.AdaptiveSphereJoint
