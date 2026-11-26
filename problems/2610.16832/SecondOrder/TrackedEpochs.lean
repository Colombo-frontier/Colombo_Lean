import SecondOrder.TrackedBounds

open scoped Classical

namespace SecondOrder
noncomputable section

def trackedPath {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (source : TrackingSource d L)
    (w : ℕ → Bool) (t : ℕ) : TrackedState d L :=
  trackedRun q Lip s τ source t (fun i => w i.val)

theorem trackedPath_succ {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (source : TrackingSource d L)
    (w : ℕ → Bool) (t : ℕ) :
    trackedPath q Lip s τ source w (t+1) =
      let z := trackedPath q Lip s τ source w t
      let r := source.curvature t (fun i => w i.val) z
      trackedStep q Lip s τ z r (w t) (source.chords t (fun i => w i.val) z r)
        (source.refresh t (fun i => w i.val) z r) := rfl

theorem trackedPath_physical {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (source : TrackingSource d L)
    (w : ℕ → Bool) (t : ℕ) :
    (trackedPath q Lip s τ source w t).physical =
      idealPath Lip s (trackedPolicy q Lip s τ source) w t :=
  trackedRun_physical q Lip s τ source t _

theorem idealStep_stopped_gradientFlag {d : ℕ} (Lip s : ℝ) (z : IdealState d) (a : IdealMove d) (b : Bool)
    (hr : (idealStep Lip s z a b).running = false) : isGradientMove z a = false := by
  cases hz : z.running <;> cases a <;> simp_all [idealStep,isGradientMove]

theorem idealStep_running_moves {d : ℕ} (Lip s : ℝ) (z : IdealState d) (a : IdealMove d) (b : Bool)
    (hr : (idealStep Lip s z a b).running = true) :
    stateMoves (idealStep Lip s z a b) = stateMoves z+1 := by
  cases hz : z.running <;> cases a <;> simp_all [idealStep,stateMoves] <;> omega

theorem trackedStep_clock {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (z : TrackedState d L)
    (r : CurvatureReply d) (b : Bool) (packet : BinaryNode L → Point d) (anchor : Point d) :
    (trackedStep q Lip s τ z r b packet anchor).clock = trackedClock q τ z r := by
  by_cases hr : (trackedNext Lip s τ z r b).running = true
  · simp [trackedStep,hr]
  · have hg := idealStep_stopped_gradientFlag Lip s z.physical (trackedMove τ z r) b
      (Bool.eq_false_iff.mpr hr)
    simp [trackedStep,hr,trackedClock,hg,epochClockStep]

theorem trackedPath_clock {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (source : TrackingSource d L)
    (w : ℕ → Bool) (t : ℕ) :
    (trackedPath q Lip s τ source w t).clock =
      epochClock q (idealGradientFlag Lip s (trackedPolicy q Lip s τ source) w) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [trackedPath_succ,trackedStep_clock]
    let z := trackedPath q Lip s τ source w t
    let r := source.curvature t (fun i => w i.val) z
    have hg : isGradientMove z.physical (trackedMove τ z r) =
        idealGradientFlag Lip s (trackedPolicy q Lip s τ source) w t := by
      change isGradientMove (trackedPath q Lip s τ source w t).physical _ = _
      rw [trackedPath_physical]
      rfl
    have he : epochClockStep q (stateMoves z.physical) (isGradientMove z.physical (trackedMove τ z r)) z.clock =
        epochClockStep q t (isGradientMove z.physical (trackedMove τ z r)) z.clock := by
      cases hr : z.physical.running
      · simp [isGradientMove,hr,epochClockStep]
      · have hc := idealRun_running_count Lip s (trackedPolicy q Lip s τ source) t (fun i => w i.val)
          (by simpa only [z,trackedPath_physical] using hr)
        have hcount : stateMoves z.physical = t := by
          simpa only [z,trackedPath_physical,stateMoves,idealPath] using hc
        rw [hcount]
    change epochClockStep q (stateMoves z.physical) (isGradientMove z.physical (trackedMove τ z r)) z.clock = _
    rw [he,hg]
    change epochClockStep q t _ (trackedPath q Lip s τ source w t).clock = _
    rw [ih,epochClock]

theorem trackedClock_start_of_restart {d L : ℕ} (q : ℕ) (τ : ℝ)
    (z : TrackedState d L) (r : CurvatureReply d) (he : trackedRestart q τ z r) :
    (trackedClock q τ z r).start = stateMoves z.physical+1 := by
  unfold trackedRestart trackedClock at *
  cases hg : isGradientMove z.physical (trackedMove τ z r) <;>
    by_cases hc : z.clock.gradients+1=q <;> simp_all [epochClockStep]

theorem trackedClock_start_of_no_restart {d L : ℕ} (q : ℕ) (τ : ℝ)
    (z : TrackedState d L) (r : CurvatureReply d) (he : ¬ trackedRestart q τ z r) :
    (trackedClock q τ z r).start = z.clock.start := by
  unfold trackedRestart trackedClock at *
  cases hg : isGradientMove z.physical (trackedMove τ z r) <;>
    by_cases hc : z.clock.gradients+1=q <;> simp_all [epochClockStep]

theorem trackedStep_memory_offset {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (z : TrackedState d L)
    (r : CurvatureReply d) (b : Bool) (packet : BinaryNode L → Point d) (anchor : Point d)
    (hz : z.memory.length+z.clock.start = stateMoves z.physical) :
    let next := trackedStep q Lip s τ z r b packet anchor
    next.memory.length+next.clock.start = stateMoves next.physical := by
  dsimp only
  rw [trackedStep_physical,trackedStep_clock]
  by_cases hr : (trackedNext Lip s τ z r b).running = true
  · have hm := idealStep_running_moves Lip s z.physical (trackedMove τ z r) b hr
    change stateMoves (trackedNext Lip s τ z r b) = _ at hm
    rw [hm]
    by_cases he : trackedRestart q τ z r
    · simp [trackedStep,hr,he,trackerReset,trackedClock_start_of_restart q τ z r he]
    · simp only [trackedStep,hr,↓reduceIte,he,trackerPush,
        trackedClock_start_of_no_restart q τ z r he]
      omega
  · have hm := idealStep_stopped_moves Lip s z.physical (trackedMove τ z r) b (Bool.eq_false_iff.mpr hr)
    have hg := idealStep_stopped_gradientFlag Lip s z.physical (trackedMove τ z r) b (Bool.eq_false_iff.mpr hr)
    simp only [trackedStep,hr,↓reduceIte]
    simpa [trackedNext,hm,trackedClock,hg,epochClockStep] using hz

/-- The actual local tree length is the number of completed physical moves
since the stored epoch start, even after a halt. This is independent of
reply accuracy and the analytic corrected process. -/
theorem trackedPath_memory_offset {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (source : TrackingSource d L)
    (w : ℕ → Bool) (t : ℕ) :
    (trackedPath q Lip s τ source w t).memory.length+(trackedPath q Lip s τ source w t).clock.start =
      stateMoves (trackedPath q Lip s τ source w t).physical := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [trackedPath_succ]
    exact trackedStep_memory_offset q Lip s τ _ _ _ _ _ ih

theorem trackedPath_epoch_number {d L q : ℕ} (hq : 0 < q) (Lip s τ : ℝ) (source : TrackingSource d L)
    (w : ℕ → Bool) (t : ℕ) :
    (trackedPath q Lip s τ source w t).clock.number =
      (trackedPath q Lip s τ source w t).physical.gradientMoves/q := by
  rw [trackedPath_clock,epochClock_number hq,epochOfStep,idealGradientFlag_count,trackedPath_physical]

end
end SecondOrder
