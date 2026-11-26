import FullJet.StageInterval

open scoped BigOperators InnerProductSpace

namespace FullJet

theorem sum_interval_cost_le {T : ℕ} (start finish : Fin (T + 1) → ℕ)
    (hvalid : ∀ j, start j ≤ finish j)
    (hprev : ∀ h : Fin T, finish h.castSucc ≤ start h.succ) :
    ∑ j, (finish j - start j) ≤ finish (Fin.last T) := by
  have hsum : (∑ j, (finish j - start j)) + ∑ j, start j = ∑ j, finish j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => Nat.sub_add_cancel (hvalid j))
  have hstart : ∑ h : Fin T, finish h.castSucc ≤ ∑ j, start j := by
    rw [Fin.sum_univ_succ]
    exact (Finset.sum_le_sum (fun h _ => hprev h)).trans (Nat.le_add_left _ _)
  have hend := Fin.sum_univ_castSucc finish
  omega

noncomputable def actualStageFinish {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (initial : State) (x : Fin (T + 1) → FixedTableSample n D k) (ρ lam : ℝ) (N : ℕ)
    (j : Fin (T + 1)) : ℕ := min (actualCrossingTime query update initial x ρ lam N j) N

noncomputable def actualStageCost {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (initial : State) (x : Fin (T + 1) → FixedTableSample n D k) (ρ lam : ℝ) (N : ℕ)
    (j : Fin (T + 1)) : ℕ :=
  actualStageFinish query update initial x ρ lam N j - actualStageStart query update initial x ρ lam N j

theorem actualStageFinish_hit {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (x : Fin (T + 1) → FixedTableSample n D k) (ρ lam : ℝ) (N : ℕ)
    (j : Fin (T + 1))
    (hout : 5 / 32 < alignment (sampledDirection (x j))
      (output (oracleRun query update (sampledChainOracle x ρ lam p) initial N) j)) :
    ∃ b, 5 / 32 < alignment (sampledDirection (x j))
      (inspectedPoint query output b (oracleRun query update (sampledChainOracle x ρ lam p) initial
        (actualStageFinish query update initial x ρ lam N j)) j) := by
  by_cases ht : actualCrossingTime query update initial x ρ lam N j ≤ N
  · refine ⟨false, ?_⟩
    simpa only [actualStageFinish, min_eq_left ht, inspectedPoint, Bool.false_eq_true, if_false]
      using firstCrossingTime_hit_of_le ht
  · refine ⟨true, ?_⟩
    simpa only [actualStageFinish, min_eq_right (le_of_not_ge ht), inspectedPoint, if_true] using hout

theorem actualStageStart_le_finish {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (x : Fin (T + 1) → FixedTableSample n D k) (ρ lam : ℝ) (N : ℕ)
    (hgood : x ∉ prematureAlignmentEvent query update output initial ρ lam N)
    (j : Fin (T + 1))
    (hout : 5 / 32 < alignment (sampledDirection (x j))
      (output (oracleRun query update (sampledChainOracle x ρ lam p) initial N) j)) :
    actualStageStart query update initial x ρ lam N j ≤ actualStageFinish query update initial x ρ lam N j := by
  cases j using Fin.cases with
  | zero => exact Nat.zero_le _
  | succ h =>
    obtain ⟨b, hh⟩ := actualStageFinish_hit query update output initial x ρ lam N h.succ hout
    have hfin : actualStageFinish query update initial x ρ lam N h.succ ≤ N := min_le_right _ _
    obtain ⟨s, hs, hh'⟩ := no_premature_predecessor query update output initial x ρ lam N hgood
      _ hfin h.castSucc h.succ (by simp) b hh
    have hle : actualCrossingTime query update initial x ρ lam N h.castSucc ≤ s :=
      firstCrossingTime_le (hs.le.trans hfin) hh'
    change actualCrossingTime query update initial x ρ lam N h.castSucc + 1 ≤ _
    exact Nat.succ_le_of_lt (lt_of_le_of_lt hle hs)

/-- These costs are computed from the actual trajectory. Completion queries
belong to the preceding transition; the granted initialization is not charged
again. The total paid interval length is at most the original budget. -/
theorem actualStageCost_sum_le {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (x : Fin (T + 1) → FixedTableSample n D k) (ρ lam : ℝ) (N : ℕ)
    (hgood : x ∉ prematureAlignmentEvent query update output initial ρ lam N)
    (hout : ∀ j, 5 / 32 < alignment (sampledDirection (x j))
      (output (oracleRun query update (sampledChainOracle x ρ lam p) initial N) j)) :
    ∑ j, actualStageCost query update initial x ρ lam N j ≤ N := by
  apply (sum_interval_cost_le _ _
    (fun j => actualStageStart_le_finish query update output initial x ρ lam N hgood j (hout j)) ?_).trans
      (min_le_right _ _)
  intro h
  exact (min_le_left _ _).trans (Nat.le_succ _)

def actualStageFastEvent {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (ρ lam : ℝ) (N q : ℕ) (j : Fin (T + 1)) :
    Set (Fin (T + 1) → FixedTableSample n D k) := {x |
      x j ∈ initializedStateAlignmentEvent
        (stageInitialIndex query update initial ρ lam N j (fun l => x l))
        (stageInitialState query update initial ρ lam N j (fun l => x l))
        (fun s => (query s).1) (prefixRowUpdate query update j (fun l => x l) ρ lam)
        (fun _ s b => radial (inspectedPoint query output b s j)) q (5 / 32)}

/-- A genuinely fast completed stage is contained in the independent-entry
row event. The conclusion follows from the actual interval simulation. -/
theorem actual_fast_stage_mem {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (x : Fin (T + 1) → FixedTableSample n D k) (ρ lam : ℝ) (N q : ℕ)
    (hgood : x ∉ prematureAlignmentEvent query update output initial ρ lam N)
    (j : Fin (T + 1))
    (hout : 5 / 32 < alignment (sampledDirection (x j))
      (output (oracleRun query update (sampledChainOracle x ρ lam p) initial N) j))
    (hcost : actualStageCost query update initial x ρ lam N j ≤ q) :
    x ∈ actualStageFastEvent query update output initial ρ lam N q j := by
  have hvalid := actualStageStart_le_finish query update output initial x ρ lam N hgood j hout
  have hsum : actualStageStart query update initial x ρ lam N j + actualStageCost query update initial x ρ lam N j =
      actualStageFinish query update initial x ρ lam N j := Nat.add_sub_of_le hvalid
  obtain ⟨b, hh⟩ := actualStageFinish_hit query update output initial x ρ lam N j hout
  have heq := actual_stage_eq_initialized_rows query update output initial x ρ lam N hgood j
    (actualStageCost query update initial x ρ lam N j)
    (by rw [hsum]; exact min_le_left _ _) (by rw [hsum]; exact min_le_right _ _)
  rw [hsum] at heq
  refine ⟨actualStageCost query update initial x ρ lam N j, hcost, b, ?_⟩
  rw [heq] at hh
  exact hh.le

end FullJet
