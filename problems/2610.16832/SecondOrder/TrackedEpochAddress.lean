import SecondOrder.TrackedPoints
import SecondOrder.EpochLocalSum

open scoped Classical

namespace SecondOrder
noncomputable section

theorem trackedPath_move_time {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (source : TrackingSource d L)
    (w : ℕ → Bool) (t : ℕ) (hr : (trackedPath q Lip s τ source w (t+1)).physical.running = true) :
    stateMoves (trackedPath q Lip s τ source w t).physical = t := by
  have hc := idealRun_running_count Lip s (trackedPolicy q Lip s τ source) (t+1)
    (fun i => w i.val) (by simpa only [trackedPath_physical,idealPath] using hr)
  have hs : stateMoves (trackedPath q Lip s τ source w (t+1)).physical =
      stateMoves (trackedPath q Lip s τ source w t).physical+1 := by
    rw [trackedPath_succ,trackedStep_physical]
    apply idealStep_running_moves
    simpa only [trackedPath_succ,trackedStep_physical] using hr
  rw [trackedPath_physical,idealPath] at hs
  change stateMoves (idealRun Lip s (trackedPolicy q Lip s τ source) (t+1) (fun i => w i.val))=t+1 at hc
  omega

theorem trackedPath_active_running {d L M : ℕ} (q : ℕ) (Lip s τ : ℝ) (source : TrackingSource d L)
    (w : Fin M → Bool) (t : ℕ)
    (ht : t < idealPhysicalLength Lip s (trackedPolicy q Lip s τ source) w) :
    (trackedPath q Lip s τ source (extendSigns w) (t+1)).physical.running = true := by
  rw [trackedPath_physical]
  apply (idealPath_physical_prefix Lip s (trackedPolicy q Lip s τ source) (extendSigns w)
    (ht.trans_le (idealPhysicalLength_le Lip s _ w))).mpr
  simpa only [idealPath_extendSigns] using ht

theorem trackedPath_active_address {d L M q : ℕ} (hq : 0 < q) (Lip s τ : ℝ)
    (source : TrackingSource d L) (w : Fin M → Bool) (t : ℕ)
    (ht : t < idealPhysicalLength Lip s (trackedPolicy q Lip s τ source) w) :
    ((trackedPath q Lip s τ source (extendSigns w) t).clock.number,
      (trackedPath q Lip s τ source (extendSigns w) t).memory.length) =
      epochAddress q (idealGradientFlag Lip s (trackedPolicy q Lip s τ source) (extendSigns w)) t := by
  have hoff := trackedPath_memory_offset q Lip s τ source (extendSigns w) t
  have hc := trackedPath_move_time q Lip s τ source (extendSigns w) t
    (trackedPath_active_running q Lip s τ source w t ht)
  apply Prod.ext
  · rw [trackedPath_clock,epochClock_number hq]
    rfl
  · dsimp only [epochAddress]
    rw [← trackedPath_clock q Lip s τ source (extendSigns w) t]
    omega

theorem trackedPath_active_epoch {d L M q : ℕ} (hq : 0 < q) (Lip s τ : ℝ)
    (source : TrackingSource d L) (w : Fin M → Bool) (t : ℕ)
    (ht : t < idealPhysicalLength Lip s (trackedPolicy q Lip s τ source) w) :
    let z := trackedPath q Lip s τ source (extendSigns w) t
    idealEpochBegin q Lip s (trackedPolicy q Lip s τ source) w z.clock.number=z.clock.start ∧
      z.memory.length < idealEpochLength q Lip s (trackedPolicy q Lip s τ source) w z.clock.number := by
  have ha := trackedPath_active_address hq Lip s τ source w t ht
  have he := congrArg Prod.fst ha
  change (trackedPath q Lip s τ source (extendSigns w) t).clock.number =
    epochOfStep q (idealGradientFlag Lip s (trackedPolicy q Lip s τ source) (extendSigns w)) t at he
  have hb := epochBoundary_eq_clock hq ht he.symm
  have hl := (epochAddress_physical hq (idealGradientFlag Lip s (trackedPolicy q Lip s τ source) (extendSigns w)) ht).1
  rw [← ha] at hl
  refine ⟨?_,hl⟩
  simpa only [idealEpochBegin,trackedPath_clock] using hb

/-- A request generated from the stored point array has exactly the
endpoint used by the all-epoch tree energy and query-count analysis. -/
theorem trackedPath_request_point_epoch {d L M q : ℕ} (hq : 0 < q) (Lip s τ : ℝ)
    (source : TrackingSource d L) (w : Fin M → Bool) (t k : ℕ)
    (ht : t < idealPhysicalLength Lip s (trackedPolicy q Lip s τ source) w)
    (hk : k ≤ (trackedPath q Lip s τ source (extendSigns w) t).memory.length+1) :
    trackerPushPoints (trackedPath q Lip s τ source (extendSigns w) t).memory
      (trackedPath q Lip s τ source (extendSigns w) (t+1)).physical.point k =
        idealEpochPath q Lip s (trackedPolicy q Lip s τ source) w
          (trackedPath q Lip s τ source (extendSigns w) t).clock.number k := by
  have he := trackedPath_active_epoch hq Lip s τ source w t ht
  rw [trackedPath_pushPoints q Lip s τ source (extendSigns w) t k
    (trackedPath_active_running q Lip s τ source w t ht) hk,
    idealEpochPath_endpoint q Lip s (trackedPolicy q Lip s τ source) w _ k (by omega),he.1]

end
end SecondOrder
