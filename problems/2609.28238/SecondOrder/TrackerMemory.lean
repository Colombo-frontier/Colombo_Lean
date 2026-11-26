import SecondOrder.BinaryTracker
import SecondOrder.MoveDecision

open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

/-- One live epoch's actual stored points, anchor and direct chord table. -/
structure TrackerMemory (d L : ℕ) where
  length : ℕ
  points : ℕ → Point d
  anchor : Point d
  table : BinaryNode L → Option (Point d)

def trackerRead {d L : ℕ} (z : TrackerMemory d L) : Point d :=
  z.anchor+∑ l : Fin L, if binaryActive z.length l.val then
    (z.table (activeNode z.length l)).getD 0 else 0

def trackerReset {d L : ℕ} (x anchor : Point d) : TrackerMemory d L :=
  ⟨0,fun _ => x,anchor,fun _ => none⟩

def trackerPushPoints {d L : ℕ} (z : TrackerMemory d L) (x : Point d) : ℕ → Point d :=
  Function.update z.points (z.length+1) x

/-- A move inserts its endpoint and samples only the newly created nodes.
Old direct estimates are retained exactly, with no error accumulation. -/
def trackerPush {d L : ℕ} (z : TrackerMemory d L) (x : Point d)
    (packet : BinaryNode L → Point d) : TrackerMemory d L :=
  ⟨z.length+1,trackerPushPoints z x,z.anchor,
    fun i => if i ∈ createdNodes L z.length then some (packet i) else z.table i⟩

theorem trackerPushPoints_old {d L : ℕ} (z : TrackerMemory d L) (x : Point d)
    {k : ℕ} (hk : k ≤ z.length) : trackerPushPoints z x k = z.points k := by
  simp [trackerPushPoints,show k ≠ z.length+1 by omega]

@[simp] theorem trackerPushPoints_new {d L : ℕ} (z : TrackerMemory d L) (x : Point d) :
    trackerPushPoints z x (z.length+1) = x := by simp [trackerPushPoints]

theorem trackerRead_eq_binaryTracker {d L : ℕ} (z : TrackerMemory d L) :
    trackerRead z = binaryTracker z.anchor (fun _ i => (z.table i).getD 0) z.length := by
  unfold trackerRead binaryTracker
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  by_cases ha : binaryActive z.length l.val
  · rw [if_pos ha,levelEstimate_active _ _ _ ha]
  · simp [levelEstimate,ha]

def TrackerAccurate {d L : ℕ} (F : Point d → ℝ) (τ ρ : ℝ) (z : TrackerMemory d L) : Prop :=
  ‖z.anchor-gradient F (z.points 0)‖ ≤ τ/4 ∧
    ∀ i ∈ completedNodes L z.length,
      ‖(z.table i).getD 0-(gradient F (z.points (nodeRight i))-gradient F (z.points (nodeLeft i)))‖ ≤ ρ

theorem trackerRead_accurate {d L : ℕ} {F : Point d → ℝ} {τ ρ : ℝ}
    (z : TrackerMemory d L) (hz : TrackerAccurate F τ ρ z) (hρ : 0 ≤ ρ)
    (hL : (L : ℝ)*ρ ≤ τ/4) (hn : z.length < 2^L) :
    ‖trackerRead z-gradient F (z.points z.length)‖ ≤ τ/2 := by
  rw [trackerRead_eq_binaryTracker]
  exact binaryTracker_accuracy (fun t => gradient F (z.points t)) z.anchor
    (fun _ i => (z.table i).getD 0) hn hρ hz.1 hz.2 hL

theorem trackerReset_accurate {d L : ℕ} {F : Point d → ℝ} {τ ρ : ℝ}
    (x anchor : Point d) (ha : ‖anchor-gradient F x‖ ≤ τ/4) :
    TrackerAccurate F τ ρ (trackerReset (L := L) x anchor) := by
  constructor
  · exact ha
  · intro i hi
    simpa [trackerReset,completedNodes_zero] using hi

/-- Accurate newly sampled chords preserve the entire stored-table
invariant. Existing intervals refer only to earlier, unchanged points. -/
theorem trackerPush_accurate {d L : ℕ} {F : Point d → ℝ} {τ ρ : ℝ}
    (z : TrackerMemory d L) (hz : TrackerAccurate F τ ρ z) (x : Point d)
    (packet : BinaryNode L → Point d)
    (hc : ∀ i ∈ createdNodes L z.length,
      ‖packet i-(gradient F (trackerPushPoints z x (nodeRight i))-
        gradient F (trackerPushPoints z x (nodeLeft i)))‖ ≤ ρ) :
    TrackerAccurate F τ ρ (trackerPush z x packet) := by
  constructor
  · change ‖z.anchor-gradient F (trackerPushPoints z x 0)‖ ≤ τ/4
    rw [trackerPushPoints_old z x (Nat.zero_le _)]
    exact hz.1
  · intro i hi
    by_cases hn : i ∈ createdNodes L z.length
    · simpa only [trackerPush,if_pos hn,Option.getD_some] using hc i hn
    · have hright : nodeRight i ≤ z.length := by
        have hh := (mem_completedNodes i).mp hi
        have hn' := mt (mem_createdNodes i).mpr hn
        change nodeRight i ≤ z.length+1 at hh
        omega
      change ‖(if i ∈ createdNodes L z.length then some (packet i) else z.table i).getD 0-
        (gradient F (trackerPushPoints z x (nodeRight i))-
          gradient F (trackerPushPoints z x (nodeLeft i)))‖ ≤ ρ
      rw [if_neg hn,trackerPushPoints_old z x hright,
        trackerPushPoints_old z x ((nodeLeft_lt_right i).le.trans hright)]
      exact hz.2 i ((mem_completedNodes i).mpr hright)

theorem trackerPush_table_created {d L : ℕ} (z : TrackerMemory d L) (x : Point d)
    (packet : BinaryNode L → Point d) (i : BinaryNode L) (hi : i ∈ createdNodes L z.length) :
    (trackerPush z x packet).table i = some (packet i) := if_pos hi

theorem trackerPush_table_retained {d L : ℕ} (z : TrackerMemory d L) (x : Point d)
    (packet : BinaryNode L → Point d) (i : BinaryNode L) (hi : i ∉ createdNodes L z.length) :
    (trackerPush z x packet).table i = z.table i := if_neg hi

end
end SecondOrder
