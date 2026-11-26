import SecondOrder.TrackedRequestCounts
import SecondOrder.TrackedEpochAddress
import SecondOrder.EpochTreeCost

open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

def chordRequestCharge {d : ℕ} (c : Point d → Point d → ℕ) : TrackingRequest d → ℕ
  | .chord x y => c x y
  | _ => 0

theorem trackedStepRequests_chordCharge {d L : ℕ} (c : Point d → Point d → ℕ)
    (q : ℕ) (Lip s τ : ℝ) (z : TrackedState d L) (r : CurvatureReply d) (b : Bool) :
    requestCharge (chordRequestCharge c) (trackedStepRequests q Lip s τ z r b) =
      if (trackedNext Lip s τ z r b).running then
        ∑ i ∈ createdNodes L z.memory.length,
          c (trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeLeft i))
            (trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeRight i)) else 0 := by
  simp only [trackedStepRequests,requestCharge_append]
  dsimp only [trackedChordRequests,trackedRefreshRequests]
  split_ifs <;> simp [requestCharge,chordRequestCharge,List.map_map,Function.comp_def]

theorem trackedRequestTrace_charge_sum {d L : ℕ} (c : TrackingRequest d → ℕ)
    (q : ℕ) (Lip s τ : ℝ) (source : TrackingSource d L) (w : ℕ → Bool) (M : ℕ) :
    requestCharge c (trackedRequestTrace q Lip s τ source M (fun i => w i.val)) =
      c (.anchor 0)+∑ t ∈ Finset.range M,
        requestCharge c (trackedStepRequests q Lip s τ (trackedPath q Lip s τ source w t)
          (source.curvature t (fun i => w i.val) (trackedPath q Lip s τ source w t)) (w t)) := by
  induction M with
  | zero => simp [trackedRequestTrace,requestCharge]
  | succ M ih =>
    rw [trackedRequestTrace,requestCharge_append,Finset.sum_range_succ]
    change requestCharge c (trackedRequestTrace q Lip s τ source M (fun i => w i.val))+_ = _
    rw [ih,Nat.add_assoc]
    rfl

theorem trackedRequestTrace_extendSigns {d L M : ℕ} (q : ℕ) (Lip s τ : ℝ)
    (source : TrackingSource d L) (w : Fin M → Bool) :
    trackedRequestTrace q Lip s τ source M (fun i => extendSigns w i.val) =
      trackedRequestTrace q Lip s τ source M w := by
  congr 1
  funext i
  simp [extendSigns,i.isLt]

/-- Exact correspondence between the chronological chord request trace and
the sum over all actually created nodes in all epochs. Requests on the last
step of an epoch remain in the trace even when their table is then cleared. -/
theorem trackedRequestTrace_chord_schedule {d L M q : ℕ} (hq : 0 < q) (Lip s τ : ℝ)
    (source : TrackingSource d L) (w : Fin M → Bool) (c : Point d → Point d → ℕ) :
    requestCharge (chordRequestCharge c) (trackedRequestTrace q Lip s τ source M w) =
      ∑ e : Fin M, ∑ k ∈ Finset.range (idealEpochLength q Lip s (trackedPolicy q Lip s τ source) w e.val),
        ∑ i ∈ createdNodes L k,
          c (idealEpochPath q Lip s (trackedPolicy q Lip s τ source) w e.val (nodeLeft i))
            (idealEpochPath q Lip s (trackedPolicy q Lip s τ source) w e.val (nodeRight i)) := by
  let policy := trackedPolicy q Lip s τ source
  let N := idealPhysicalLength Lip s policy w
  let g := idealGradientFlag Lip s policy (extendSigns w)
  let cost := fun e k => ∑ i ∈ createdNodes L k,
    c (idealEpochPath q Lip s policy w e (nodeLeft i)) (idealEpochPath q Lip s policy w e (nodeRight i))
  rw [← trackedRequestTrace_extendSigns q Lip s τ source w,trackedRequestTrace_charge_sum]
  simp only [chordRequestCharge,Nat.zero_add]
  have hstep (t : ℕ) (ht : t < M) :
      requestCharge (chordRequestCharge c)
        (trackedStepRequests q Lip s τ (trackedPath q Lip s τ source (extendSigns w) t)
          (source.curvature t (fun i => extendSigns w i.val) (trackedPath q Lip s τ source (extendSigns w) t))
          (extendSigns w t)) = if t < N then cost (epochAddress q g t).1 (epochAddress q g t).2 else 0 := by
    rw [trackedStepRequests_chordCharge]
    have hr : (trackedNext Lip s τ (trackedPath q Lip s τ source (extendSigns w) t)
        (source.curvature t (fun i => extendSigns w i.val) (trackedPath q Lip s τ source (extendSigns w) t))
        (extendSigns w t)).running = true ↔ t < N := by
      have hpath := congrArg TrackedState.physical (trackedPath_succ q Lip s τ source (extendSigns w) t)
      simp only [trackedStep_physical] at hpath
      rw [← hpath,trackedPath_physical]
      simpa only [idealPath_extendSigns] using
        (idealPath_physical_prefix Lip s policy (extendSigns w) (M := M) ht)
    by_cases htn : t < N
    · rw [if_pos (hr.mpr htn),if_pos htn]
      have ha := trackedPath_active_address hq Lip s τ source w t htn
      change _ = cost (epochAddress q g t).1 (epochAddress q g t).2
      rw [← ha]
      unfold cost
      apply Finset.sum_congr rfl
      intro i hi
      have hir := (mem_createdNodes i).mp hi
      have hl : nodeLeft i ≤ (trackedPath q Lip s τ source (extendSigns w) t).memory.length+1 :=
        (nodeLeft_lt_right i).le.trans hir.le
      have hright := trackedPath_request_point_epoch hq Lip s τ source w t (nodeRight i) htn hir.le
      have hleft := trackedPath_request_point_epoch hq Lip s τ source w t (nodeLeft i) htn hl
      rw [trackedPath_succ,trackedStep_physical] at hright hleft
      rw [hright,hleft]
    · rw [if_neg (mt hr.mp htn),if_neg htn]
  calc
    _ = ∑ t ∈ Finset.range M, if t < N then cost (epochAddress q g t).1 (epochAddress q g t).2 else 0 :=
      Finset.sum_congr rfl (fun t ht => hstep t (Finset.mem_range.mp ht))
    _ = ∑ t ∈ Finset.range N, cost (epochAddress q g t).1 (epochAddress q g t).2 := by
      rw [← Finset.sum_filter]
      congr 1
      ext t
      have hn : N ≤ M := idealPhysicalLength_le Lip s policy w
      simp only [Finset.mem_filter,Finset.mem_range]
      omega
    _ = _ := sum_epoch_local (idealPhysicalLength_le Lip s policy w) hq g cost

theorem trackedRequestTrace_chord_count {d L M q : ℕ} (hq : 0 < q) (Lip s τ : ℝ)
    (source : TrackingSource d L) (w : Fin M → Bool) :
    requestCharge isChordRequest (trackedRequestTrace q Lip s τ source M w) ≤
      2*idealPhysicalLength Lip s (trackedPolicy q Lip s τ source) w := by
  have hh := trackedRequestTrace_chord_schedule hq Lip s τ source w (fun _ _ => 1)
  change requestCharge isChordRequest _ = _ at hh
  rw [hh]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  calc
    _ ≤ ∑ e : Fin M, 2*idealEpochLength q Lip s (trackedPolicy q Lip s τ source) w e.val := by
      apply Finset.sum_le_sum
      intro e he
      exact total_created_nodes L (idealEpochLength q Lip s (trackedPolicy q Lip s τ source) w e.val)
    _ = _ := by rw [← Finset.mul_sum,sum_idealEpochLength]

theorem trackedRequestTrace_chord_cost {d L M q : ℕ} (P : Parameters) (hq : 0 < q) (Lip s τ ρ δ : ℝ)
    (source : TrackingSource d L) (w : Fin M → Bool) :
    requestCharge (requestChordCost P ρ δ) (trackedRequestTrace q Lip s τ source M w) =
      idealEpochTreeQueries P q Lip s (trackedPolicy q Lip s τ source) w L ρ δ := by
  exact (trackedRequestTrace_chord_schedule hq Lip s τ source w
    (fun x y => localQueryCount (chordVariance P x y) ρ δ)).trans
      (idealEpochTreeQueries_created P q Lip s (trackedPolicy q Lip s τ source) w L ρ δ)

end
end SecondOrder
