import FullJet.PrefixCoupling

open scoped InnerProductSpace

namespace FullJet

def inspectedPoint {State E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {T n : ℕ}
    (query : State → Fin n × BlockSpace T E) (output : State → BlockSpace T E)
    (b : Bool) (state : State) : BlockSpace T E := if b then output state else (query state).2

noncomputable def erasedPrefixDirection {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (ρ lam : ℝ) (N : ℕ) (j : Fin (T + 1))
    (y : OtherStageSamples n D k (T + 1) j)
    (c : Fin (T + 1) × Fin (N + 1) × Bool) : EuclideanSpace ℝ (Fin D) :=
  if c.1.val < j.val then radial (inspectedPoint query output c.2.2
    (oracleRun query update (erasedPrefixOracle j y ρ lam p c.1.val) initial c.2.1.val) j) else 0

theorem erasedPrefixDirection_norm {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (ρ lam : ℝ) (N : ℕ) (j : Fin (T + 1))
    (y : OtherStageSamples n D k (T + 1) j) (c : Fin (T + 1) × Fin (N + 1) × Bool) :
    ‖erasedPrefixDirection query update output initial ρ lam N j y c‖ ≤ 1 := by
  unfold erasedPrefixDirection
  split_ifs
  · exact radial_norm_le_one _
  · simp

/-- A future block crosses the opacity threshold while no earlier query
has opened any gate at or beyond the chosen current stage. The inspected
point can be a query or a separately chosen output. -/
def prematureAlignmentEvent {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (ρ lam : ℝ) (N : ℕ) : Set (Fin (T + 1) → FixedTableSample n D k) :=
  {x | ∃ (j h : Fin (T + 1)) (t : ℕ) (b : Bool), h.val < j.val ∧ t ≤ N ∧
    (∀ s < t, ∀ l : Fin T, h.val ≤ l.val →
      alignment (sampledDirection (x l.castSucc))
        ((query (oracleRun query update (sampledChainOracle x ρ lam p) initial s)).2 l.castSucc) ≤ 5 / 32) ∧
    5 / 32 < alignment (sampledDirection (x j))
      (inspectedPoint query output b (oracleRun query update (sampledChainOracle x ρ lam p) initial t) j)}

theorem prematureAlignmentEvent_subset {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (ρ lam : ℝ) (N : ℕ) :
    prematureAlignmentEvent (k := k) query update output initial ρ lam N ⊆
      {x | ∃ j, x ∈ stageUnobservedAlignment j
        (erasedPrefixDirection query update output initial ρ lam N j) (5 / 32)} := by
  rintro x ⟨j, h, t, b, hj, ht, hclosed, hhit⟩
  refine ⟨j, ⟨h, ⟨t, by omega⟩, b⟩, ?_⟩
  have heq := sampledRun_eq_erased_before_crossing query update initial x j hj ρ lam t hclosed
  rw [heq] at hhit
  simpa only [erasedPrefixDirection, if_pos hj, alignment] using hhit.le

/-- This bound concerns the actual complete-jet algorithm. No independence
of its adaptive history is assumed: the erased prefix constructs the
independent comparison directions used in the finite product argument. -/
theorem actual_premature_alignment_tail {State : Type*} {n D k T p : ℕ}
    (hk : k ≤ n) (hD : 0 < D)
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (ρ lam : ℝ) (N : ℕ) :
    ((fixedChainLaw n D k (T + 1) hk).toOuterMeasure
      (prematureAlignmentEvent query update output initial ρ lam N)).toReal ≤
      2 * (T + 1 : ℕ) ^ 2 * (N + 1 : ℕ) * Real.exp (-((5 / 32 : ℝ) ^ 2 * D / 2)) := by
  apply (pmf_event_mono_toReal (fixedChainLaw n D k (T + 1) hk) _ _
    (prematureAlignmentEvent_subset query update output initial ρ lam N)).trans
  have h := chain_unobserved_alignment_tail hk hD
    (erasedPrefixDirection query update output initial ρ lam N)
    (erasedPrefixDirection_norm query update output initial ρ lam N) (5 / 32) (by norm_num)
  convert h using 1 <;> simp [Fintype.card_prod] <;> ring

end FullJet
