import AdaptiveSphereStoppedSpan
import InformativeHandleCount

/-! Exact identification of the manuscript event {2 K_original < k} with the
corresponding stopped-transcript event, rather than substituting a different
good-rank event. -/
open MeasureTheory Set

namespace Task006.AdaptiveSphereOriginalHandleEvent
open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereFrame Task006.AdaptiveSphereState
open Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereStopped Task006.AdaptiveSphereMean
open Task006.AdaptiveSphereStoppedCoupling Task006.RankHandleCount
noncomputable section
variable {d N : ℕ} {S : Type*} [MeasurableSpace S]

/-- If stopping has not occurred, EVERY paid action and none padding agree,
not just the nonempty stopped actions. -/
theorem executedAction_eq_of_stop_rank_lt (A : OracleAlgorithm d N S)
    (tape : ℕ → ℝ) (seed : S) (k : ℕ) (hkd : k ≤ d) (θ : Space d)
    (hr : (frameFromTranscript A id tape seed k hkd N
      ((stoppedObserver A id tape seed k hkd).finalTranscript (linearSample id θ) tape ())).1.val < k)
    (i : Fin N) :
    A.executedAction (linearSample id θ) tape seed i =
      (stoppedObserver A id tape seed k hkd).executedAction (linearSample id θ) tape () i := by
  have hh := finalTranscript_eq_of_rank_lt A id tape seed k hkd θ hr
  have hri := (frame_rank_mono A id tape seed k hkd
    ((stoppedObserver A id tape seed k hkd).finalTranscript (linearSample id θ) tape ())
      (Nat.le_of_lt i.isLt)).trans_lt hr
  rw [← action_finalTranscript_eq A (linearSample id θ) tape seed i,hh,
    ← action_finalTranscript_eq (stoppedObserver A id tape seed k hkd) (linearSample id θ) tape () i]
  change A.action i seed _ = stopAction A id tape seed k hkd i _
  simp only [stopAction,if_pos hri]

theorem informativeHandles_eq_of_stop_rank_lt (A : OracleAlgorithm d N S)
    (tape : ℕ → ℝ) (seed : S) (k : ℕ) (hkd : k ≤ d) (θ : Space d)
    (hr : (frameFromTranscript A id tape seed k hkd N
      ((stoppedObserver A id tape seed k hkd).finalTranscript (linearSample id θ) tape ())).1.val < k) :
    A.informativeHandles (linearSample id θ) tape seed =
      (stoppedObserver A id tape seed k hkd).informativeHandles (linearSample id θ) tape () := by
  have hq : A.queriedHandles (linearSample id θ) tape seed =
      (stoppedObserver A id tape seed k hkd).queriedHandles (linearSample id θ) tape () := by
    unfold queriedHandles
    congr 1
    funext i
    rw [executedAction_eq_of_stop_rank_lt A tape seed k hkd θ hr i]
  unfold informativeHandles
  rw [hq]

/-- Exact source event equivalence. The two-query legality condition is used
here, so a single handle cannot supply arbitrarily many independent equations. -/
theorem original_stopped_informative_event_iff (A : OracleAlgorithm d N S)
    (tape : ℕ → ℝ) (seed : S) (k : ℕ) (hkd : k ≤ d) (θ : Space d)
    (hcap : ∀ h, (A.handleSlots (linearSample id θ) tape seed h).card ≤ 2) :
    2*(A.informativeHandles (linearSample id θ) tape seed).card < k ↔
      2*((stoppedObserver A id tape seed k hkd).informativeHandles (linearSample id θ) tape ()).card < k := by
  constructor
  · intro h
    exact (Nat.mul_le_mul_left 2
      (Finset.card_le_card (stopped_informativeHandles_subset A tape seed k hkd θ))).trans_lt h
  · intro h
    have hcapS (a : ℕ) :
        ((stoppedObserver A id tape seed k hkd).handleSlots (linearSample id θ) tape () a).card ≤ 2 :=
      (Finset.card_le_card (stopped_handleSlots_subset A id tape seed k hkd θ a)).trans (hcap a)
    have hr := actual_frame_rank_le_twice_informative_handles
      (stoppedObserver A id tape seed k hkd) tape () θ k hkd hcapS
    rw [stoppedObserver_frame_eq] at hr
    have he := informativeHandles_eq_of_stop_rank_lt A tape seed k hkd θ (hr.trans_lt h)
    rw [he]
    exact h

#print axioms executedAction_eq_of_stop_rank_lt
#print axioms informativeHandles_eq_of_stop_rank_lt
#print axioms original_stopped_informative_event_iff
end
end Task006.AdaptiveSphereOriginalHandleEvent
