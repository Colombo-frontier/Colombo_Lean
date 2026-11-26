import FullJet.FirstCrossingTime
import FullJet.PrefixRowDecoder
import FullJet.InitializedReplay

namespace FullJet

noncomputable def erasedEntryTime {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (initial : State) (h : Fin T) (y : OtherStageSamples n D k (T + 1) h.succ)
    (ρ lam : ℝ) (N : ℕ) : ℕ :=
  firstCrossingTime (fun t => 5 / 32 < alignment (erasedDirection h.succ y h.castSucc)
    ((query (oracleRun query update (erasedPrefixOracle h.succ y ρ lam p h.val) initial t)).2 h.castSucc)) N

noncomputable def erasedEntryState {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (initial : State) (h : Fin T) (y : OtherStageSamples n D k (T + 1) h.succ)
    (ρ lam : ℝ) (N : ℕ) : State :=
  oracleRun query update (erasedPrefixOracle h.succ y ρ lam p h.val) initial
    (erasedEntryTime query update initial h y ρ lam N)

/-- The entry clock is selected using only other stages. Off the premature
event, it equals the actual first query crossing of the predecessor. -/
theorem erasedEntryTime_eq_actual {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (x : Fin (T + 1) → FixedTableSample n D k) (ρ lam : ℝ) (N : ℕ)
    (hgood : x ∉ prematureAlignmentEvent query update output initial ρ lam N) (h : Fin T)
    (he : ∃ t, t ≤ N ∧ 5 / 32 < alignment (sampledDirection (x h.castSucc))
      ((query (oracleRun query update (sampledChainOracle x ρ lam p) initial t)).2 h.castSucc)) :
    erasedEntryTime query update initial h (fun l => x l) ρ lam N =
      actualCrossingTime query update initial x ρ lam N h.castSucc := by
  let τ := actualCrossingTime query update initial x ρ lam N h.castSucc
  have ht : τ ≤ N := (firstCrossingTime_spec he).1
  have hθ : erasedDirection h.succ (fun l => x l) h.castSucc = sampledDirection (x h.castSucc) := by
    simp [erasedDirection, show h.castSucc ≠ h.succ by intro heq; have := congrArg Fin.val heq; simp at this]
  have heq (s : ℕ) (hs : s ≤ τ) :
      oracleRun query update (sampledChainOracle x ρ lam p) initial s =
        oracleRun query update (erasedPrefixOracle h.succ (fun l => x l) ρ lam p h.val) initial s := by
    apply sampledRun_eq_erased_before_crossing query update initial x h.succ (by simp)
    intro r hr l hl
    exact tail_closed_before_first_crossing query update output initial x ρ lam N hgood h.castSucc r
      (by omega) (by omega) l.castSucc hl
  apply firstCrossingTime_eq_of_first ht
  · rw [hθ, ← heq τ le_rfl]
    exact (firstCrossingTime_spec he).2
  · intro s hs
    rw [hθ, ← heq s hs.le]
    exact firstCrossingTime_min hs (by omega)

theorem erasedEntryState_eq_actual {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (x : Fin (T + 1) → FixedTableSample n D k) (ρ lam : ℝ) (N : ℕ)
    (hgood : x ∉ prematureAlignmentEvent query update output initial ρ lam N) (h : Fin T)
    (he : ∃ t, t ≤ N ∧ 5 / 32 < alignment (sampledDirection (x h.castSucc))
      ((query (oracleRun query update (sampledChainOracle x ρ lam p) initial t)).2 h.castSucc)) :
    erasedEntryState query update initial h (fun l => x l) ρ lam N =
      oracleRun query update (sampledChainOracle x ρ lam p) initial
        (actualCrossingTime query update initial x ρ lam N h.castSucc) := by
  unfold erasedEntryState
  rw [erasedEntryTime_eq_actual query update output initial x ρ lam N hgood h he]
  symm
  apply sampledRun_eq_erased_before_crossing query update initial x h.succ (by simp)
  intro r hr l hl
  exact tail_closed_before_first_crossing query update output initial x ρ lam N hgood h.castSucc r hr
    (hr.le.trans (firstCrossingTime_spec he).1) l.castSucc hl

noncomputable def stageEntryInit {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (initial : State) (h : Fin T) (y : OtherStageSamples n D k (T + 1) h.succ)
    (ρ lam : ℝ) (N : ℕ) (b : Fin D → Bool) : State :=
  let s := erasedEntryState query update initial h y ρ lam N
  update s (prefixRowDecoder h.succ y ρ lam p (query s) b)

/-- The actual completion reply initializes the next stage through exactly
one row. Its index and pre-reply state are fixed without that stage's sample. -/
theorem stageEntryInit_eq_actual {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (x : Fin (T + 1) → FixedTableSample n D k) (ρ lam : ℝ) (N : ℕ)
    (hgood : x ∉ prematureAlignmentEvent query update output initial ρ lam N) (h : Fin T)
    (he : ∃ t, t ≤ N ∧ 5 / 32 < alignment (sampledDirection (x h.castSucc))
      ((query (oracleRun query update (sampledChainOracle x ρ lam p) initial t)).2 h.castSucc)) :
    stageEntryInit query update initial h (fun l => x l) ρ lam N
      (observedRow (x h.succ) (query (erasedEntryState query update initial h (fun l => x l) ρ lam N)).1) =
      oracleRun query update (sampledChainOracle x ρ lam p) initial
        (actualCrossingTime query update initial x ρ lam N h.castSucc + 1) := by
  unfold stageEntryInit
  rw [erasedEntryState_eq_actual query update output initial x ρ lam N hgood h he]
  simp only [oracleRun]
  congr 1
  rw [← prefixRowDecoder_exact]
  symm
  apply componentChain_fullJet_eq_truncated
  intro l hl
  exact later_closed_at_first_crossing query update output initial x ρ lam N hgood h.castSucc
    (firstCrossingTime_spec he).1 l.castSucc (by
      simp only [mem_prefixLinks, Fin.val_succ] at hl
      change h.val < l.val
      omega)

end FullJet
