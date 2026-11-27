import AdaptiveSphereMeasurementProjection
import AdaptiveSphereStoppedCoupling

/-! Relating stopped frame rank to the original protocol's actual measurement
span, and identifying centers on the literal event dim(V) < k. -/

open MeasureTheory Set
namespace Task006.AdaptiveSphereStoppedSpan
open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereFrame Task006.AdaptiveSphereState
open Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereStopped
open Task006.AdaptiveSphereStoppedCoupling Task006.AdaptiveSphereSpan
open Task006.AdaptiveSphereAction Task006.AdaptiveSphereMean Task006.PosteriorCenter
noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

theorem stateStep_cap_eq_full_of_rank_lt (k : ℕ) (hkd : k ≤ d) (state : FrameState d) (q : E d)
    (hr : state.1.val < k) : stateStep k hkd state q = stateStep d le_rfl state q := by
  have hrd : state.1.val < d := hr.trans_le hkd
  simp only [stateStep, dif_pos hr, dif_pos hrd]

theorem rankStopped_frame_cap_eq_full (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (hstop : RankStopped A weight tape seed k hkd) (t : ℕ) (h : Transcript N) :
    frameFromTranscript A weight tape seed k hkd t h =
      frameFromTranscript A weight tape seed d le_rfl t h := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [frameFromTranscript, frameFromTranscript]
    split_ifs with ht
    · rw [← ih]
      by_cases hr : (frameFromTranscript A weight tape seed k hkd t h).1.val < k
      · exact stateStep_cap_eq_full_of_rank_lt k hkd _ _ hr
      · have ha := hstop ⟨t, ht⟩ h (Nat.le_of_not_gt hr)
        rw [ha]
        simp only [effectiveVector, stateStep_zero]
    · exact ih

theorem frame_cap_eq_full_of_rank_lt (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (h : Transcript N)
    (hr : (frameFromTranscript A weight tape seed k hkd t h).1.val < k) :
    frameFromTranscript A weight tape seed k hkd t h =
      frameFromTranscript A weight tape seed d le_rfl t h := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hprev : (frameFromTranscript A weight tape seed k hkd t h).1.val < k :=
      (frame_rank_mono A weight tape seed k hkd h (Nat.le_succ t)).trans_lt hr
    rw [frameFromTranscript, frameFromTranscript]
    split_ifs with ht
    · rw [← ih hprev]
      exact stateStep_cap_eq_full_of_rank_lt k hkd _ _ hprev
    · exact ih hprev

theorem stopped_measurementSpan_le_original (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (θ : Space d) :
    measurementSpanBefore (stoppedObserver A weight tape seed k hkd) weight tape () t θ ≤
      measurementSpanBefore A weight tape seed t θ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change effectiveVector weight tape
    ((stoppedObserver A weight tape seed k hkd).executedAction (linearSample weight θ) tape () i.val) ∈
      measurementSpanBefore A weight tape seed t θ
  by_cases hn : (stoppedObserver A weight tape seed k hkd).executedAction (linearSample weight θ) tape () i.val = none
  · rw [hn]
    exact Submodule.zero_mem _
  · have he := stopped_nonempty_action_eq_original A weight tape seed k hkd θ i.val hn
    rw [← he]
    exact Submodule.subset_span (Set.mem_range_self i)

theorem stopped_final_rank_eq_span_finrank (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (θ : Space d) :
    (frameFromTranscript A weight tape seed k hkd N
      ((stoppedObserver A weight tape seed k hkd).finalTranscript (linearSample weight θ) tape ())).1.val =
      Module.finrank ℝ (measurementSpanBefore (stoppedObserver A weight tape seed k hkd) weight tape () N θ) := by
  let B := stoppedObserver A weight tape seed k hkd
  have hs := stoppedObserver_rankStopped A weight tape seed k hkd
  have hf := rankStopped_frame_cap_eq_full B weight tape () k hkd hs N
    (B.finalTranscript (linearSample weight θ) tape ())
  rw [stoppedObserver_frame_eq] at hf
  have hd := actual_measurementSpan_finrank B weight tape () N le_rfl θ
  change Module.finrank ℝ (measurementSpanBefore B weight tape () N θ) =
    (frameFromTranscript B weight tape () d le_rfl N (B.finalTranscript (linearSample weight θ) tape ())).1.val at hd
  exact (congrArg (fun state : FrameState d => state.1.val) hf).trans hd.symm

theorem stopped_final_rank_le_original_span_finrank (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (θ : Space d) :
    (frameFromTranscript A weight tape seed k hkd N
      ((stoppedObserver A weight tape seed k hkd).finalTranscript (linearSample weight θ) tape ())).1.val ≤
      Module.finrank ℝ (measurementSpanBefore A weight tape seed N θ) := by
  rw [stopped_final_rank_eq_span_finrank]
  exact Submodule.finrank_mono (stopped_measurementSpan_le_original A weight tape seed k hkd N θ)

theorem below_dimension_stop_rank_lt (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (θ : Space d)
    (hdim : Module.finrank ℝ (measurementSpanBefore A weight tape seed N θ) < k) :
    (frameFromTranscript A weight tape seed k hkd N
      ((stoppedObserver A weight tape seed k hkd).finalTranscript (linearSample weight θ) tape ())).1.val < k :=
  (stopped_final_rank_le_original_span_finrank A weight tape seed k hkd θ).trans_lt hdim

theorem below_dimension_transcript_eq (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (θ : Space d)
    (hdim : Module.finrank ℝ (measurementSpanBefore A weight tape seed N θ) < k) :
    A.finalTranscript (linearSample weight θ) tape seed =
      (stoppedObserver A weight tape seed k hkd).finalTranscript (linearSample weight θ) tape () :=
  finalTranscript_eq_of_rank_lt A weight tape seed k hkd θ
    (below_dimension_stop_rank_lt A weight tape seed k hkd θ hdim)

theorem below_dimension_center_eq (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (j : Fin d) (Q : OrthogonalGroup d)
    (hdim : Module.finrank ℝ (measurementSpanBefore A weight tape seed N (column Q j)) < k) :
    actualCenter A weight tape seed d le_rfl N j Q =
      actualCenter (stoppedObserver A weight tape seed k hkd) weight tape () k hkd N j Q := by
  let B := stoppedObserver A weight tape seed k hkd
  have hr := below_dimension_stop_rank_lt A weight tape seed k hkd (column Q j) hdim
  have hh := finalTranscript_eq_of_rank_lt A weight tape seed k hkd (column Q j) hr
  have hf := frame_cap_eq_full_of_rank_lt A weight tape seed k hkd N
    (B.finalTranscript (linearSample weight (column Q j)) tape ()) hr
  rw [actualCenter_eq_projected A weight tape seed d le_rfl N le_rfl j Q,
    actualCenter_eq_projected B weight tape () k hkd N le_rfl j Q]
  change projectedCenter (frameFromTranscript A weight tape seed d le_rfl N
      (A.finalTranscript (linearSample weight (column Q j)) tape seed)) (column Q j) =
    projectedCenter (frameFromTranscript B weight tape () k hkd N
      (B.finalTranscript (linearSample weight (column Q j)) tape ())) (column Q j)
  rw [hh, ← hf, stoppedObserver_frame_eq]

#print axioms rankStopped_frame_cap_eq_full
#print axioms stopped_final_rank_le_original_span_finrank
#print axioms below_dimension_center_eq
end
end Task006.AdaptiveSphereStoppedSpan
