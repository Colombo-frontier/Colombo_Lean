import SecondOrder.TrackedEpochs

open scoped Classical

namespace SecondOrder
noncomputable section

/-- Every stored point in the current epoch is the corresponding endpoint
of the physical path. Padded cells past the current local length are not
asserted to carry trajectory points. -/
theorem trackedPath_points {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (source : TrackingSource d L)
    (w : ℕ → Bool) (t k : ℕ) (hk : k ≤ (trackedPath q Lip s τ source w t).memory.length) :
    (trackedPath q Lip s τ source w t).memory.points k =
      (idealPath Lip s (trackedPolicy q Lip s τ source) w
        ((trackedPath q Lip s τ source w t).clock.start+k)).point := by
  induction t generalizing k with
  | zero =>
    have hk0 : k=0 := by change k ≤ 0 at hk; omega
    subst k
    rfl
  | succ t ih =>
    let z := trackedPath q Lip s τ source w t
    let r := source.curvature t (fun i => w i.val) z
    let packet := source.chords t (fun i => w i.val) z r
    let anchor := source.refresh t (fun i => w i.val) z r
    let p := trackedNext Lip s τ z r (w t)
    have hstep : trackedPath q Lip s τ source w (t+1) = trackedStep q Lip s τ z r (w t) packet anchor := rfl
    have hpp : p = idealPath Lip s (trackedPolicy q Lip s τ source) w (t+1) := by
      rw [← trackedPath_physical q Lip s τ source w (t+1),hstep,trackedStep_physical]
    have hoff : z.memory.length+z.clock.start = stateMoves z.physical :=
      trackedPath_memory_offset q Lip s τ source w t
    rw [hstep] at hk ⊢
    rw [trackedStep_clock]
    by_cases hr : p.running = true
    · have hpcount := idealRun_running_count Lip s (trackedPolicy q Lip s τ source) (t+1)
        (fun i => w i.val) (by simpa only [hpp,idealPath] using hr)
      have hpm := idealStep_running_moves Lip s z.physical (trackedMove τ z r) (w t) hr
      have hzt : stateMoves z.physical = t := by
        change stateMoves p = stateMoves z.physical+1 at hpm
        change stateMoves (idealPath Lip s (trackedPolicy q Lip s τ source) w (t+1)) = t+1 at hpcount
        rw [← hpp] at hpcount
        omega
      by_cases he : trackedRestart q τ z r
      · have hstart := trackedClock_start_of_restart q τ z r he
        rw [hzt] at hstart
        have hk0 : k=0 := by
          simpa only [trackedStep,show (trackedNext Lip s τ z r (w t)).running = true from hr,
            ↓reduceIte,he,trackerReset,Nat.le_zero] using hk
        subst k
        simpa only [trackedStep,show (trackedNext Lip s τ z r (w t)).running = true from hr,
          ↓reduceIte,he,trackerReset,hstart,Nat.add_zero] using congrArg IdealState.point hpp
      · have hstart := trackedClock_start_of_no_restart q τ z r he
        simp only [trackedStep,show (trackedNext Lip s τ z r (w t)).running = true from hr,
          ↓reduceIte,he,trackerPush,hstart] at hk ⊢
        by_cases hnew : k=z.memory.length+1
        · rw [hnew,trackerPushPoints_new]
          have ht : z.clock.start+(z.memory.length+1)=t+1 := by omega
          rw [ht]
          exact congrArg IdealState.point hpp
        · rw [trackerPushPoints_old z.memory p.point (by omega)]
          exact ih k (by change k ≤ z.memory.length; omega)
    · have hgrad := idealStep_stopped_gradientFlag Lip s z.physical (trackedMove τ z r) (w t)
        (Bool.eq_false_iff.mpr hr)
      have hclock : trackedClock q τ z r = z.clock := by simp [trackedClock,hgrad,epochClockStep]
      simp only [trackedStep,show ¬ (trackedNext Lip s τ z r (w t)).running = true from hr,
        ↓reduceIte,hclock] at hk ⊢
      exact ih k hk

/-- The temporary endpoint insertion used for all newly requested old-epoch
chords refers to the same physical path, including a step that will reset
the tracker immediately afterwards. -/
theorem trackedPath_pushPoints {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (source : TrackingSource d L)
    (w : ℕ → Bool) (t k : ℕ)
    (hr : (trackedPath q Lip s τ source w (t+1)).physical.running = true)
    (hk : k ≤ (trackedPath q Lip s τ source w t).memory.length+1) :
    trackerPushPoints (trackedPath q Lip s τ source w t).memory
      (trackedPath q Lip s τ source w (t+1)).physical.point k =
      (idealPath Lip s (trackedPolicy q Lip s τ source) w
        ((trackedPath q Lip s τ source w t).clock.start+k)).point := by
  let z := trackedPath q Lip s τ source w t
  change k ≤ z.memory.length+1 at hk
  by_cases hn : k=z.memory.length+1
  · rw [hn,trackerPushPoints_new]
    have hoff := trackedPath_memory_offset q Lip s τ source w t
    have hpcount := idealRun_running_count Lip s (trackedPolicy q Lip s τ source) (t+1)
      (fun i => w i.val) (by simpa only [trackedPath_physical,idealPath] using hr)
    have hpm : stateMoves (trackedPath q Lip s τ source w (t+1)).physical = stateMoves z.physical+1 := by
      rw [trackedPath_succ,trackedStep_physical]
      apply idealStep_running_moves
      simpa only [trackedPath_succ,trackedStep_physical] using hr
    rw [trackedPath_physical] at hpm
    have ht : z.clock.start+(z.memory.length+1)=t+1 := by
      change stateMoves (idealPath Lip s (trackedPolicy q Lip s τ source) w (t+1)) = t+1 at hpcount
      change z.memory.length+z.clock.start=stateMoves z.physical at hoff
      omega
    rw [trackedPath_physical]
    change _ = (idealPath Lip s (trackedPolicy q Lip s τ source) w (z.clock.start+(z.memory.length+1))).point
    rw [ht]
  · have hkold : k ≤ z.memory.length := by omega
    rw [trackerPushPoints_old z.memory _ hkold]
    exact trackedPath_points q Lip s τ source w t k hkold

/-- Each new direct chord ends at the new physical point and begins at the
stored old-epoch trajectory point. The statement includes reset-triggering
steps; their chord requests precede replacing the stored epoch. -/
theorem trackedPath_created_endpoints {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (source : TrackingSource d L)
    (w : ℕ → Bool) (t : ℕ) (i : BinaryNode L)
    (hr : (trackedPath q Lip s τ source w (t+1)).physical.running = true)
    (hi : i ∈ createdNodes L (trackedPath q Lip s τ source w t).memory.length) :
    let z := trackedPath q Lip s τ source w t
    let x := (trackedPath q Lip s τ source w (t+1)).physical.point
    trackerPushPoints z.memory x (nodeRight i) = x ∧
      trackerPushPoints z.memory x (nodeLeft i) =
        (idealPath Lip s (trackedPolicy q Lip s τ source) w (z.clock.start+nodeLeft i)).point := by
  have hir := (mem_createdNodes i).mp hi
  dsimp only
  constructor
  · rw [hir,trackerPushPoints_new]
  · apply trackedPath_pushPoints q Lip s τ source w t (nodeLeft i) hr
    exact (nodeLeft_lt_right i).le.trans hir.le

end
end SecondOrder
