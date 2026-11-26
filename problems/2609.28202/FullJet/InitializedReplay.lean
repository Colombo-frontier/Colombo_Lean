import FullJet.ReplayProtocol
import FullJet.InitializedRows

open scoped InnerProductSpace

namespace FullJet

noncomputable def initializedRowState {State : Type*} {n D k : ℕ}
    (initialIndex : Fin n) (initState : (Fin D → Bool) → State)
    (query : State → Fin n) (update : State → (Fin D → Bool) → State)
    (x : FixedTableSample n D k) (t : ℕ) : State :=
  rowStateRun query update
    (initState (fun l => decide (initialIndex ∈ fixedObservedColumns x.1 x.2 l))) x t

def initializedStateAlignmentEvent {State : Type*} {n D k : ℕ} {κ : Type*}
    (initialIndex : Fin n) (initState : (Fin D → Bool) → State)
    (query : State → Fin n) (update : State → (Fin D → Bool) → State)
    (direction : ℕ → State → κ → EuclideanSpace ℝ (Fin D)) (q : ℕ) (a : ℝ) :
    Set (FixedTableSample n D k) := {x | ∃ t ≤ q, ∃ l,
      a ≤ ⟪sampledDirection x, direction t
        (initializedRowState initialIndex initState query update x t) l⟫_ℝ}

theorem initializedRowState_eq_replay {State : Type*} {n D k : ℕ}
    (initialIndex : Fin n) (initState : (Fin D → Bool) → State)
    (query : State → Fin n) (update : State → (Fin D → Bool) → State)
    (x : FixedTableSample n D k) (q t : ℕ) (ht : t ≤ q) :
    let v := initializedTableRun initialIndex
      (fun b hist => query (replayState update (initState b) hist)) q x
    initializedRowState initialIndex initState query update x t =
      replayState update (initState v.1) ((List.ofFn v.2).take t) := by
  exact rowStateRun_eq_replay query update _ x q t ht

theorem initializedStateAlignmentEvent_eq {State : Type*} {n D k : ℕ} {κ : Type*}
    (initialIndex : Fin n) (initState : (Fin D → Bool) → State)
    (query : State → Fin n) (update : State → (Fin D → Bool) → State)
    (direction : ℕ → State → κ → EuclideanSpace ℝ (Fin D)) (q : ℕ) (a : ℝ) :
    (initializedStateAlignmentEvent initialIndex initState query update direction q a :
      Set (FixedTableSample n D k)) =
    initializedAlignmentEvent initialIndex
      (fun b hist => query (replayState update (initState b) hist)) q
      (fun b v (c : Fin (q + 1) × κ) => direction c.1.val
        (replayState update (initState b) ((List.ofFn v).take c.1.val)) c.2) a := by
  ext x
  constructor
  · rintro ⟨t, ht, l, hh⟩
    refine ⟨⟨⟨t, by omega⟩, l⟩, ?_⟩
    simpa only [initializedRowState_eq_replay initialIndex initState query update x q t ht] using hh
  · rintro ⟨⟨t, l⟩, hh⟩
    refine ⟨t.val, by omega, l, ?_⟩
    simpa only [initializedRowState_eq_replay initialIndex initState query update x q t.val (by omega)] using hh

/-- One free row may determine the entire starting state. The actual paid
run and every intermediate or output direction still obey the row bound. -/
theorem initialized_state_alignment_quarter {State : Type*} {n D k : ℕ}
    {κ : Type*} [Fintype κ] (hn : 0 < n) (hD : 0 < D) (hk : k ≤ n)
    (m : ℝ) (hm : 0 ≤ m) (hbalance : 2 * (k : ℝ) = n + m)
    (initialIndex : Fin n) (initState : (Fin D → Bool) → State)
    (query : State → Fin n) (update : State → (Fin D → Bool) → State)
    (direction : ℕ → State → κ → EuclideanSpace ℝ (Fin D))
    (hdirection : ∀ t s l, ‖direction t s l‖ ≤ 1)
    (q : ℕ) (hbudget : 8 * m + 9 * (q + 1 : ℕ) ≤ n) (a : ℝ) (ha : 0 < a)
    (hqueries : (q + 1 : ℕ) * (m / n) ^ 2 ≤ a ^ 2 / 1024)
    (hdim : 32 * Real.log 2 ≤ a ^ 2 * D)
    (hfamily : ((q + 1 : ℕ) * Fintype.card κ : ℝ) ≤ Real.exp (a ^ 2 * D / 4)) :
    ((fixedTableLaw n D k hk).toOuterMeasure
      (initializedStateAlignmentEvent initialIndex initState query update direction q a)).toReal ≤ 1 / 4 := by
  rw [initializedStateAlignmentEvent_eq]
  exact initialized_row_alignment_quarter (κ := Fin (q + 1) × κ)
    hn hD hk m hm hbalance _ _ q hbudget _ (fun b v c => hdirection c.1.val _ c.2)
      a ha hqueries hdim (by simpa using hfamily)

end FullJet
