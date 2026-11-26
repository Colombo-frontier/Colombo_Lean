import FullJet.FirstHitCoupling
import FullJet.RandomizedRows

open scoped InnerProductSpace

namespace FullJet

def replayState {State Reply : Type*} (update : State → Reply → State) (initial : State)
    (past : List Reply) : State := past.foldl update initial

theorem replayState_snoc {State Reply : Type*} (update : State → Reply → State)
    (initial : State) (past : List Reply) (b : Reply) :
    replayState update initial (past ++ [b]) = update (replayState update initial past) b := by
  simp [replayState, List.foldl_append]

theorem oracleRun_start_step {State Query Reply : Type*}
    (query : State → Query) (update : State → Reply → State) (oracle : Query → Reply)
    (initial : State) (q : ℕ) :
    oracleRun query update oracle initial (q + 1) =
      oracleRun query update oracle (update initial (oracle (query initial))) q := by
  induction q with
  | zero => rfl
  | succ q ih => exact congrArg (fun s => update s (oracle (query s))) ih

theorem runReplies_replay {Ω State Query Reply : Type*}
    (query : State → Query) (update : State → Reply → State) (observe : Ω → Query → Reply)
    (initial : State) (ω : Ω) (past : List Reply) (q : ℕ) :
    replayState update initial (past ++ List.ofFn
      (runReplies (fun ω hist => observe ω (query (replayState update initial hist))) ω past q)) =
      oracleRun query update (observe ω) (replayState update initial past) q := by
  induction q generalizing past with
  | zero => simp [runReplies, oracleRun]
  | succ q ih =>
    rw [runReplies, List.ofFn_cons, oracleRun_start_step]
    have hlist (b : Reply) (xs : List Reply) : past ++ b :: xs = (past ++ [b]) ++ xs := by
      simp [List.append_assoc]
    rw [hlist, ih, replayState_snoc]

theorem runReplies_take {Ω Reply : Type*} (reply : Ω → List Reply → Reply)
    (ω : Ω) (past : List Reply) (q t : ℕ) (ht : t ≤ q) :
    (List.ofFn (runReplies reply ω past q)).take t = List.ofFn (runReplies reply ω past t) := by
  induction t generalizing q past with
  | zero => simp [runReplies]
  | succ t ih =>
    cases q with
    | zero => omega
    | succ q =>
      simp only [runReplies, List.ofFn_cons, List.take_succ_cons]
      rw [ih (past ++ [reply ω past]) q (by omega)]

noncomputable def rowStateRun {State : Type*} {n D k : ℕ}
    (query : State → Fin n) (update : State → (Fin D → Bool) → State)
    (initial : State) (ω : FixedTableSample n D k) (q : ℕ) : State :=
  oracleRun query update (fun i j => decide (i ∈ fixedObservedColumns ω.1 ω.2 j)) initial q

theorem rowStateRun_eq_replay {State : Type*} {n D k : ℕ}
    (query : State → Fin n) (update : State → (Fin D → Bool) → State)
    (initial : State) (ω : FixedTableSample n D k) (q t : ℕ) (ht : t ≤ q) :
    rowStateRun query update initial ω t = replayState update initial
      ((List.ofFn (fixedTableTranscript (fun hist => query (replayState update initial hist)) [] q ω).2).take t) := by
  unfold fixedTableTranscript
  rw [runReplies_take _ _ [] q t ht]
  have h := runReplies_replay query update
    (fun (S : Fin D → Finset (Fin n)) i j => decide (i ∈ S j))
      initial (fixedObservedColumns ω.1 ω.2) [] t
  simpa only [List.nil_append, replayState, List.foldl_nil] using h.symm

def stateAlignmentEvent {State : Type*} {n D k : ℕ}
    (query : State → Fin n) (update : State → (Fin D → Bool) → State)
    (initial : State) (direction : ℕ → State → EuclideanSpace ℝ (Fin D)) (q : ℕ) (a : ℝ) :
    Set (FixedTableSample n D k) := {ω | ∃ t ≤ q,
      a ≤ ⟪sampledDirection ω, direction t (rowStateRun query update initial ω t)⟫_ℝ}

/-- An arbitrary row-oracle state machine is represented exactly by the
finite history model used in the information proof, at every prefix. -/
theorem stateAlignmentEvent_eq {State : Type*} {n D k : ℕ}
    (query : State → Fin n) (update : State → (Fin D → Bool) → State)
    (initial : State) (direction : ℕ → State → EuclideanSpace ℝ (Fin D)) (q : ℕ) (a : ℝ) :
    (stateAlignmentEvent query update initial direction q a : Set (FixedTableSample n D k)) =
      tableAlignmentEvent (fun hist => query (replayState update initial hist)) [] q
        (fun v (t : Fin (q + 1)) => direction t (replayState update initial ((List.ofFn v).take t))) a := by
  ext ω
  constructor
  · rintro ⟨t, ht, hhit⟩
    refine ⟨⟨t, by omega⟩, ?_⟩
    simpa only [rowStateRun_eq_replay query update initial ω q t ht] using hhit
  · rintro ⟨t, hhit⟩
    refine ⟨t.val, by omega, ?_⟩
    simpa only [rowStateRun_eq_replay query update initial ω q t.val (by omega)] using hhit

/-- The one-stage probability bound now applies directly to an arbitrary
adaptive state machine, including a direction selected in its final state. -/
theorem rowStateRun_alignment_quarter {State : Type*} {n D k : ℕ}
    (hn : 0 < n) (hD : 0 < D) (hk : k ≤ n)
    (m : ℝ) (hm : 0 ≤ m) (hbalance : 2 * (k : ℝ) = n + m)
    (query : State → Fin n) (update : State → (Fin D → Bool) → State) (initial : State)
    (direction : ℕ → State → EuclideanSpace ℝ (Fin D)) (hdirection : ∀ t s, ‖direction t s‖ ≤ 1)
    (q : ℕ) (hbudget : 8 * m + 9 * (q : ℝ) ≤ n) (a : ℝ) (ha : 0 < a)
    (hqueries : (q : ℝ) * (m / n) ^ 2 ≤ a ^ 2 / 1024)
    (hdim : 32 * Real.log 2 ≤ a ^ 2 * D)
    (hfamily : (q + 1 : ℕ) ≤ Real.exp (a ^ 2 * D / 4)) :
    ((fixedTableLaw n D k hk).toOuterMeasure
      (stateAlignmentEvent query update initial direction q a)).toReal ≤ 1 / 4 := by
  rw [stateAlignmentEvent_eq]
  exact fixedTable_alignment_quarter (κ := Fin (q + 1)) hn hD hk m hm hbalance _ [] q hbudget
    _ (fun v t => hdirection t _) a ha hqueries hdim (by simpa using hfamily)

end FullJet
