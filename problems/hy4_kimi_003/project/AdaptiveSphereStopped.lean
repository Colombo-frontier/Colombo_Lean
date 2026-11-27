import AdaptiveSphereState

/-!
A genuinely stopped observation policy for the posterior argument. Original
private seed and exogenous tape are fixed parameters here; the original policy
receives no extra tape information. The stopped observer is an analysis object.
-/

open MeasureTheory Set

namespace Task006.AdaptiveSphereStopped

open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereFrame
open Task006.AdaptiveSphereState Task006.AdaptiveSphereTranscript
open Task006.AdaptiveSphereMeasurable

noncomputable section

variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

def stopAction (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N) (h : Transcript N) : QueryAction d :=
  if (frameFromTranscript A weight tape seed k hkd t.val h).1.val < k then A.action t seed h
  else none

theorem measurable_stopAction (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N) :
    Measurable (stopAction A weight tape seed k hkd t) := by
  have hf := measurable_frameFromTranscript A weight tape seed k hkd t.val
  have hrank : Measurable (fun h : Transcript N =>
      (frameFromTranscript A weight tape seed k hkd t.val h).1) := measurable_fst.comp hf
  have hval : Measurable (fun r : Fin (d+1) => r.val) := measurable_of_countable _
  have hnat := hval.comp hrank
  have hset : MeasurableSet {h : Transcript N |
      (frameFromTranscript A weight tape seed k hkd t.val h).1.val < k} :=
    hnat measurableSet_Iio
  have ha : Measurable (fun h : Transcript N => A.action t seed h) :=
    (A.action_measurable t).comp (measurable_const.prodMk measurable_id)
  exact Measurable.ite hset ha measurable_const

/-- The real finite stopped policy, with no post-stop scalar replies. -/
def stoppedObserver (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) : OracleAlgorithm d N Unit where
  action t _ h := stopAction A weight tape seed k hkd t h
  action_measurable t := (measurable_stopAction A weight tape seed k hkd t).comp measurable_snd
  past_only := by
    intro t u h h' hpast
    have hf := frameFromTranscript_past_only A weight tape seed k hkd t.val h h' hpast
    simp only [stopAction, hf, A.past_only t seed h h' hpast]
  output _ h := A.output seed h
  output_measurable := by
    have ho : Measurable (fun h : Transcript N => A.output seed h) :=
      A.output_measurable.comp (measurable_const.prodMk measurable_id)
    exact ho.comp measurable_snd

/-- Counterfactual frames are identical: after rank k both recursions freeze,
while the observer writes only zero/none replies. -/
theorem stoppedObserver_frame_eq (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (h : Transcript N) :
    frameFromTranscript (stoppedObserver A weight tape seed k hkd) weight tape () k hkd t h =
      frameFromTranscript A weight tape seed k hkd t h := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [frameFromTranscript, frameFromTranscript]
    split_ifs with ht
    · rw [ih]
      change stateStep k hkd (frameFromTranscript A weight tape seed k hkd t h)
          (effectiveVector weight tape (stopAction A weight tape seed k hkd ⟨t,ht⟩ h)) = _
      by_cases hr : (frameFromTranscript A weight tape seed k hkd t h).1.val < k
      · simp only [stopAction, if_pos hr]
      · simp only [stopAction, if_neg hr, stateStep, dif_neg hr]
    · exact ih

/-- A policy property, not an assumed posterior law. -/
def RankStopped (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) : Prop :=
  ∀ t : Fin N, ∀ h : Transcript N,
    k ≤ (frameFromTranscript A weight tape seed k hkd t.val h).1.val → A.action t seed h = none

/-- The explicitly constructed observer really stops according to its OWN frame. -/
theorem stoppedObserver_rankStopped (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) :
    RankStopped (stoppedObserver A weight tape seed k hkd) weight tape () k hkd := by
  intro t h hstop
  rw [stoppedObserver_frame_eq] at hstop
  change stopAction A weight tape seed k hkd t h = none
  simp only [stopAction, if_neg (not_lt.mpr hstop)]

#print axioms measurable_stopAction
#print axioms stoppedObserver_frame_eq
#print axioms stoppedObserver_rankStopped

end
end Task006.AdaptiveSphereStopped
