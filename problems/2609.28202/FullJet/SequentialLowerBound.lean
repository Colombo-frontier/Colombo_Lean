import FullJet.ActualStageCosts

open scoped BigOperators InnerProductSpace

namespace FullJet

/-- The fast-stage event uses the explicit independent entry and actual
row decoder constructed from the original complete-jet algorithm. -/
theorem actual_fast_stage_probability {State : Type*} {n D k T p : ℕ}
    (hn : 0 < n) (hD : 0 < D) (hk : k ≤ n)
    (m : ℝ) (hm : 0 ≤ m) (hbalance : 2 * (k : ℝ) = n + m)
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (ρ lam : ℝ) (N q : ℕ) (j : Fin (T + 1))
    (hbudget : 8 * m + 9 * (q + 1 : ℕ) ≤ n)
    (hqueries : (q + 1 : ℕ) * (m / n) ^ 2 ≤ (5 / 32 : ℝ) ^ 2 / 1024)
    (hdim : 32 * Real.log 2 ≤ (5 / 32 : ℝ) ^ 2 * D)
    (hfamily : (2 : ℝ) * (q + 1 : ℕ) ≤ Real.exp ((5 / 32 : ℝ) ^ 2 * D / 4)) :
    ((fixedChainLaw n D k (T + 1) hk).toOuterMeasure
      (actualStageFastEvent query update output initial ρ lam N q j)).toReal ≤ 1 / 4 := by
  letI := fixedColumn_nonempty hk
  apply uniform_coordinate_event_le j (fun y : OtherStageSamples n D k (T + 1) j =>
    initializedStateAlignmentEvent
      (stageInitialIndex query update initial ρ lam N j y)
      (stageInitialState query update initial ρ lam N j y)
      (fun s => (query s).1) (prefixRowUpdate query update j y ρ lam)
      (fun _ s b => radial (inspectedPoint query output b s j)) q (5 / 32))
  intro y
  exact initialized_state_alignment_quarter (κ := Bool) hn hD hk m hm hbalance _ _ _ _ _
    (fun _ _ _ => radial_norm_le_one _) q hbudget (5 / 32) (by norm_num)
    hqueries hdim (by simpa [mul_comm] using hfamily)

theorem actual_short_budget_probability {State : Type*} {n D k T p : ℕ}
    (hn : 0 < n) (hD : 0 < D) (hk : k ≤ n)
    (m : ℝ) (hm : 0 ≤ m) (hbalance : 2 * (k : ℝ) = n + m)
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (ρ lam : ℝ) (N q : ℕ)
    (hbudget : 8 * m + 9 * (q + 1 : ℕ) ≤ n) (hN : 2 * N ≤ (q + 1) * (T + 1))
    (hqueries : (q + 1 : ℕ) * (m / n) ^ 2 ≤ (5 / 32 : ℝ) ^ 2 / 1024)
    (hdim : 32 * Real.log 2 ≤ (5 / 32 : ℝ) ^ 2 * D)
    (hfamily : (2 : ℝ) * (q + 1 : ℕ) ≤ Real.exp ((5 / 32 : ℝ) ^ 2 * D / 4)) :
    ((fixedChainLaw n D k (T + 1) hk).toOuterMeasure (shortAlignmentBudgetEvent
      (actualStageFastEvent query update output initial ρ lam N q) (q + 1) N)).toReal ≤ 1 / 2 := by
  apply (pmf_event_mono_toReal _ _ _
    (shortAlignmentBudgetEvent_subset _ (q + 1) N (by omega) hN)).trans
  have hh := pmf_many_events_le (fixedChainLaw n D k (T + 1) hk)
    (actualStageFastEvent query update output initial ρ lam N q)
    (1 / 4) ((T + 1 : ℕ) / 2) (by positivity)
    (fun j => actual_fast_stage_probability hn hD hk m hm hbalance query update output initial
      ρ lam N q j hbudget hqueries hdim hfamily)
  convert hh using 1
  simp only [Fintype.card_fin]
  field_simp
  <;> ring

def outputAlignedEvent {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (ρ lam : ℝ) (N : ℕ) : Set (Fin (T + 1) → FixedTableSample n D k) :=
  {x | ∀ j, 5 / 32 < alignment (sampledDirection (x j))
    (output (oracleRun query update (sampledChainOracle x ρ lam p) initial N) j)}

/-- Completion of the real algorithm yields the actual cost witnesses.
This discharges the previously missing budget-event containment. -/
theorem outputAlignedEvent_subset {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (ρ lam : ℝ) (N q : ℕ) :
    outputAlignedEvent (k := k) query update output initial ρ lam N ⊆
      shortAlignmentBudgetEvent (actualStageFastEvent query update output initial ρ lam N q) (q + 1) N ∪
        prematureAlignmentEvent query update output initial ρ lam N := by
  intro x hout
  by_cases hb : x ∈ prematureAlignmentEvent query update output initial ρ lam N
  · exact Or.inr hb
  · apply Or.inl
    refine ⟨actualStageCost query update initial x ρ lam N,
      actualStageCost_sum_le query update output initial x ρ lam N hb hout, ?_⟩
    intro j hcost
    exact actual_fast_stage_mem query update output initial x ρ lam N q hb j (hout j) (by omega)

/-- Sequential revelation for the actual finite complete-jet hard chain.
It applies at every jet order and to arbitrary adaptive states and output
maps. The only probabilistic premises are the explicit numeric bounds. -/
theorem actual_chain_gradient_failure_probability {State : Type*} {n D k T p : ℕ}
    (hn : 0 < n) (hD : 0 < D) (hk : k ≤ n)
    (m : ℝ) (hm : 0 ≤ m) (hbalance : 2 * (k : ℝ) = n + m)
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (ρ : ℝ) (N q : ℕ)
    (hbudget : 8 * m + 9 * (q + 1 : ℕ) ≤ n) (hN : 2 * N ≤ (q + 1) * (T + 1))
    (hqueries : (q + 1 : ℕ) * (m / n) ^ 2 ≤ (5 / 32 : ℝ) ^ 2 / 1024)
    (hdim : 32 * Real.log 2 ≤ (5 / 32 : ℝ) ^ 2 * D)
    (hfamily : (2 : ℝ) * (q + 1 : ℕ) ≤ Real.exp ((5 / 32 : ℝ) ^ 2 * D / 4)) :
    1 / 2 - 2 * (T + 1 : ℕ) ^ 2 * (N + 1 : ℕ) * Real.exp (-((5 / 32 : ℝ) ^ 2 * D / 2)) ≤
      ((fixedChainLaw n D k (T + 1) hk).toOuterMeasure {x |
        (1 / 4 : ℝ) ≤ ‖fderiv ℝ (baseChain (fun j => sampledDirection (x j)) (33 / 16))
          (output (oracleRun query update (sampledChainOracle x ρ (33 / 16) p) initial N))‖}).toReal := by
  let A := shortAlignmentBudgetEvent
    (actualStageFastEvent (k := k) query update output initial ρ (33 / 16) N q) (q + 1) N
  let B := prematureAlignmentEvent (k := k) query update output initial ρ (33 / 16) N
  have hA := actual_short_budget_probability hn hD hk m hm hbalance query update output initial
    ρ (33 / 16) N q hbudget hN hqueries hdim hfamily
  have hB := actual_premature_alignment_tail hk hD query update output initial ρ (33 / 16) N
  have hprob := pmf_avoid_two_events (fixedChainLaw n D k (T + 1) hk) A B _ _ hA hB
  have hsub : (A ∪ B)ᶜ ⊆ {x |
      (1 / 4 : ℝ) ≤ ‖fderiv ℝ (baseChain (fun j => sampledDirection (x j)) (33 / 16))
        (output (oracleRun query update (sampledChainOracle x ρ (33 / 16) p) initial N))‖} := by
    intro x hx
    have hout : x ∉ outputAlignedEvent query update output initial ρ (33 / 16) N :=
      fun hh => hx (outputAlignedEvent_subset query update output initial ρ (33 / 16) N q hh)
    change ¬ ∀ j, 5 / 32 < _ at hout
    push_neg at hout
    obtain ⟨j, hj⟩ := hout
    exact baseChain_fderiv_lower_bound _ (fun j => sampledDirection_norm hD (x j)) _
      ⟨j, by linarith⟩
  have hh := hprob.trans (pmf_event_mono_toReal _ _ _ hsub)
  linarith

end FullJet
