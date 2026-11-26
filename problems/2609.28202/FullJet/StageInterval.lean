import FullJet.StageEntry

namespace FullJet

theorem oracleRun_add {State Query Reply : Type*} (query : State → Query)
    (update : State → Reply → State) (oracle : Query → Reply) (initial : State) (a b : ℕ) :
    oracleRun query update oracle initial (a + b) =
      oracleRun query update oracle (oracleRun query update oracle initial a) b := by
  induction b with
  | zero => simp [oracleRun]
  | succ b ih => exact congrArg (fun s => update s (oracle (query s))) ih

/-- Restarting at any actual state before the current stage completes is
exactly simulated by its row protocol for the whole remaining prefix. -/
theorem actual_interval_eq_rows {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (x : Fin (T + 1) → FixedTableSample n D k) (ρ lam : ℝ) (N : ℕ)
    (hgood : x ∉ prematureAlignmentEvent query update output initial ρ lam N)
    (j : Fin (T + 1)) (start q : ℕ)
    (hfinish : start + q ≤ actualCrossingTime query update initial x ρ lam N j)
    (hN : start + q ≤ N) :
    oracleRun query update (sampledChainOracle x ρ lam p) initial (start + q) =
      rowStateRun (fun s => (query s).1)
        (prefixRowUpdate query update j (fun l => x l) ρ lam)
        (oracleRun query update (sampledChainOracle x ρ lam p) initial start) (x j) q := by
  rw [← prefixRun_eq_rowRun]
  rw [oracleRun_add]
  symm
  apply oracleRun_eq_of_agree
  intro t ht
  rw [← oracleRun_add]
  symm
  apply componentChain_fullJet_eq_truncated
  intro l hl
  exact tail_closed_before_first_crossing query update output initial x ρ lam N hgood j
    (start + t) (by omega) (by omega) l.castSucc (by
      have hv : j.val ≤ l.val := by simpa only [mem_prefixLinks, not_lt] using hl
      exact hv)

noncomputable def stageInitialIndex {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (initial : State) (ρ lam : ℝ) (N : ℕ) (j : Fin (T + 1)) :
    OtherStageSamples n D k (T + 1) j → Fin n :=
  Fin.cases (fun _ => (query initial).1)
    (fun h y => (query (erasedEntryState query update initial h y ρ lam N)).1) j

noncomputable def stageInitialState {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (initial : State) (ρ lam : ℝ) (N : ℕ) (j : Fin (T + 1)) :
    OtherStageSamples n D k (T + 1) j → (Fin D → Bool) → State :=
  Fin.cases (fun _ _ => initial) (fun h y => stageEntryInit query update initial h y ρ lam N) j

noncomputable def actualStageStart {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (initial : State) (x : Fin (T + 1) → FixedTableSample n D k) (ρ lam : ℝ) (N : ℕ)
    (j : Fin (T + 1)) : ℕ :=
  Fin.cases 0 (fun h => actualCrossingTime query update initial x ρ lam N h.castSucc + 1) j

theorem stageInitialState_exact {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (x : Fin (T + 1) → FixedTableSample n D k) (ρ lam : ℝ) (N : ℕ)
    (hgood : x ∉ prematureAlignmentEvent query update output initial ρ lam N)
    (j : Fin (T + 1)) (hstart : actualStageStart query update initial x ρ lam N j ≤ N) :
    stageInitialState query update initial ρ lam N j (fun l => x l)
      (observedRow (x j) (stageInitialIndex query update initial ρ lam N j (fun l => x l))) =
      oracleRun query update (sampledChainOracle x ρ lam p) initial
        (actualStageStart query update initial x ρ lam N j) := by
  cases j using Fin.cases with
  | zero => rfl
  | succ h =>
    apply stageEntryInit_eq_actual query update output initial x ρ lam N hgood h
    by_contra he
    have hn : actualCrossingTime query update initial x ρ lam N h.castSucc = N + 1 := by
      simp only [actualCrossingTime, firstCrossingTime, dif_neg he]
    change actualCrossingTime query update initial x ρ lam N h.castSucc + 1 ≤ N at hstart
    omega

/-- The candidate's actual state throughout a stage, including its first
completion state, equals the initialized row state used by the probability
bound. Only the independent entry data and one initial row are supplied. -/
theorem actual_stage_eq_initialized_rows {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (x : Fin (T + 1) → FixedTableSample n D k) (ρ lam : ℝ) (N : ℕ)
    (hgood : x ∉ prematureAlignmentEvent query update output initial ρ lam N)
    (j : Fin (T + 1)) (q : ℕ)
    (hfinish : actualStageStart query update initial x ρ lam N j + q ≤
      actualCrossingTime query update initial x ρ lam N j)
    (hN : actualStageStart query update initial x ρ lam N j + q ≤ N) :
    oracleRun query update (sampledChainOracle x ρ lam p) initial
      (actualStageStart query update initial x ρ lam N j + q) =
      initializedRowState (stageInitialIndex query update initial ρ lam N j (fun l => x l))
        (stageInitialState query update initial ρ lam N j (fun l => x l))
        (fun s => (query s).1) (prefixRowUpdate query update j (fun l => x l) ρ lam) (x j) q := by
  rw [actual_interval_eq_rows query update output initial x ρ lam N hgood j _ q hfinish hN]
  unfold initializedRowState
  change rowStateRun _ _ _ _ _ = rowStateRun _ _
    (stageInitialState query update initial ρ lam N j (fun l => x l)
      (observedRow (x j) (stageInitialIndex query update initial ρ lam N j (fun l => x l)))) _ _
  rw [stageInitialState_exact query update output initial x ρ lam N hgood j (by omega)]

end FullJet
