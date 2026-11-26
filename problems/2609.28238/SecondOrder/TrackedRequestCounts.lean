import SecondOrder.TrackedRequests

open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

theorem trackedStep_curvature_count {d L : ℕ} (Lip s τ : ℝ) (z : TrackedState d L)
    (r : CurvatureReply d) (b : Bool) :
    (trackedNext Lip s τ z r b).curvatureMoves+(if (trackedNext Lip s τ z r b).running then 0 else 1) =
      z.physical.curvatureMoves+(if z.physical.running then 0 else 1)+
        (if trackedCurvatureNeeded τ z then 1 else 0) := by
  cases hz : z.physical.running <;>
    by_cases hn : 4*τ < ‖trackerRead z.memory‖ <;> cases r <;>
      simp [trackedNext,trackedMove,decideMove,idealStep,hz,hn,trackedCurvatureNeeded,not_le.mpr,le_of_not_gt] <;>
      omega

theorem trackedStep_anchor_count {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (z : TrackedState d L)
    (r : CurvatureReply d) (b : Bool) :
    (trackedClock q τ z r).number = z.clock.number+
      (if (trackedNext Lip s τ z r b).running = true ∧ trackedRestart q τ z r then 1 else 0) := by
  have hg : isGradientMove z.physical (trackedMove τ z r) = true →
      (trackedNext Lip s τ z r b).running = true := by
    intro hgrad
    unfold trackedNext
    cases hz : z.physical.running <;> cases he : trackedMove τ z r <;> simp_all [isGradientMove,idealStep]
  unfold trackedRestart trackedClock
  cases hgrad : isGradientMove z.physical (trackedMove τ z r)
  · simp [epochClockStep,hgrad]
  · by_cases hc : z.clock.gradients+1=q <;> simp [epochClockStep,hgrad,hc,hg hgrad]

/-- Exact curvature-call count, including at most one final certificate
call. A physical cap reached while still running adds no extra call. -/
theorem trackedRequestTrace_curvature {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (source : TrackingSource d L)
    (t : ℕ) (w : Fin t → Bool) :
    requestCharge isCurvatureRequest (trackedRequestTrace q Lip s τ source t w) =
      (trackedRun q Lip s τ source t w).physical.curvatureMoves+
        (if (trackedRun q Lip s τ source t w).physical.running then 0 else 1) := by
  induction t with
  | zero => simp [trackedRequestTrace,requestCharge,isCurvatureRequest,trackedRun,trackedInitial,idealInitial]
  | succ t ih =>
    rw [trackedRequestTrace,requestCharge_append,trackedStepRequests_curvature,ih]
    rw [trackedRun,trackedStep_physical]
    exact (trackedStep_curvature_count Lip s τ _ _ _).symm

/-- One initial anchor and one anchor for each actual epoch reset. -/
theorem trackedRequestTrace_anchors {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (source : TrackingSource d L)
    (t : ℕ) (w : Fin t → Bool) :
    requestCharge isAnchorRequest (trackedRequestTrace q Lip s τ source t w) =
      1+(trackedRun q Lip s τ source t w).clock.number := by
  induction t with
  | zero => simp [trackedRequestTrace,requestCharge,isAnchorRequest,trackedRun,trackedInitial]
  | succ t ih =>
    rw [trackedRequestTrace,requestCharge_append,trackedStepRequests_anchor,ih]
    rw [trackedRun,trackedStep_clock,trackedStep_anchor_count q Lip s τ _ _ (w (Fin.last t))]
    omega

theorem trackedPath_extendSigns {d L M : ℕ} (q : ℕ) (Lip s τ : ℝ)
    (source : TrackingSource d L) (w : Fin M → Bool) :
    trackedPath q Lip s τ source (extendSigns w) M = trackedRun q Lip s τ source M w := by
  unfold trackedPath
  congr 1
  funext i
  simp [extendSigns,i.isLt]

theorem trackedRequestTrace_anchors_eq {d L q : ℕ} (hq : 0 < q) (Lip s τ : ℝ)
    (source : TrackingSource d L) (t : ℕ) (w : Fin t → Bool) :
    requestCharge isAnchorRequest (trackedRequestTrace q Lip s τ source t w) =
      1+(trackedRun q Lip s τ source t w).physical.gradientMoves/q := by
  rw [trackedRequestTrace_anchors,← trackedPath_extendSigns q Lip s τ source w,
    trackedPath_epoch_number hq]

theorem trackedRequestTrace_curvature_le {d L : ℕ} (q : ℕ) (Lip s τ : ℝ)
    (source : TrackingSource d L) (t : ℕ) (w : Fin t → Bool) :
    requestCharge isCurvatureRequest (trackedRequestTrace q Lip s τ source t w) ≤
      1+(trackedRun q Lip s τ source t w).physical.curvatureMoves := by
  rw [trackedRequestTrace_curvature]
  split_ifs <;> omega

theorem trackedRequestTrace_anchors_le {d L q : ℕ} (hq : 0 < q) (Lip s τ : ℝ)
    (source : TrackingSource d L) (t : ℕ) (w : Fin t → Bool) :
    requestCharge isAnchorRequest (trackedRequestTrace q Lip s τ source t w) ≤ t+1 := by
  rw [trackedRequestTrace_anchors_eq hq,trackedRun_physical]
  have hh := idealPhysicalLength_le Lip s (trackedPolicy q Lip s τ source) w
  have hd := Nat.div_le_self (idealRun Lip s (trackedPolicy q Lip s τ source) t w).gradientMoves q
  dsimp only [idealPhysicalLength,stateMoves] at hh
  omega

end
end SecondOrder
