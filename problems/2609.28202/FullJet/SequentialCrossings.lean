import FullJet.PrematureAlignment

namespace FullJet

/-- A deterministic no-skipping principle. If every later-stage hit needs
an earlier hit somewhere in the unfinished tail, then it needs an earlier
hit at each intervening stage. Time induction rules out circular dependence. -/
theorem predecessor_hit_of_tail_hit {T : ℕ}
    (H : ℕ → Fin (T + 1) → Bool → Prop) (N : ℕ)
    (hstep : ∀ t ≤ N, ∀ h j : Fin (T + 1), h.val < j.val → ∀ b, H t j b →
      ∃ s < t, ∃ l : Fin (T + 1), h.val ≤ l.val ∧ H s l false)
    (t : ℕ) (ht : t ≤ N) (h j : Fin (T + 1)) (hj : h.val < j.val)
    (b : Bool) (hhit : H t j b) : ∃ s < t, H s h false := by
  induction t using Nat.strong_induction_on generalizing h j b with
  | h t ih =>
    obtain ⟨s, hs, l, hl, hh⟩ := hstep t ht h j hj b hhit
    by_cases heq : l = h
    · subst l
      exact ⟨s, hs, hh⟩
    · have hlt : h.val < l.val := lt_of_le_of_ne hl (fun hv => heq (Fin.ext hv.symm))
      obtain ⟨r, hr, hhr⟩ := ih s hs (by omega) h l hlt false hh
      exact ⟨r, by omega, hhr⟩

/-- Off the proved premature-alignment event, every actual query or output
alignment at a later block has a strictly earlier query alignment at each
predecessor. This supplies actual ordered completion times. -/
theorem no_premature_predecessor {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (x : Fin (T + 1) → FixedTableSample n D k) (ρ lam : ℝ) (N : ℕ)
    (hgood : x ∉ prematureAlignmentEvent query update output initial ρ lam N)
    (t : ℕ) (ht : t ≤ N) (h j : Fin (T + 1)) (hj : h.val < j.val) (b : Bool)
    (hhit : 5 / 32 < alignment (sampledDirection (x j))
      (inspectedPoint query output b (oracleRun query update (sampledChainOracle x ρ lam p) initial t) j)) :
    ∃ s < t, 5 / 32 < alignment (sampledDirection (x h))
      ((query (oracleRun query update (sampledChainOracle x ρ lam p) initial s)).2 h) := by
  let H : ℕ → Fin (T + 1) → Bool → Prop := fun t j b => 5 / 32 < alignment (sampledDirection (x j))
    (inspectedPoint query output b (oracleRun query update (sampledChainOracle x ρ lam p) initial t) j)
  have hstep : ∀ t ≤ N, ∀ h j : Fin (T + 1), h.val < j.val → ∀ b, H t j b →
      ∃ s < t, ∃ l : Fin (T + 1), h.val ≤ l.val ∧ H s l false := by
    intro t ht h j hj b hh
    by_contra he
    apply hgood
    refine ⟨j, h, t, b, hj, ht, ?_, hh⟩
    intro s hs l hl
    apply le_of_not_gt
    intro hhit'
    exact he ⟨s, hs, l.castSucc, hl, hhit'⟩
  exact predecessor_hit_of_tail_hit H N hstep t ht h j hj b hhit

/-- The index of a stage aligned on a query or output cannot exceed the
number of replies already received, unless premature alignment occurred. -/
theorem no_premature_stage_index_le_time {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (x : Fin (T + 1) → FixedTableSample n D k) (ρ lam : ℝ) (N : ℕ)
    (hgood : x ∉ prematureAlignmentEvent query update output initial ρ lam N)
    (j : Fin (T + 1)) (t : ℕ) (ht : t ≤ N) (b : Bool)
    (hhit : 5 / 32 < alignment (sampledDirection (x j))
      (inspectedPoint query output b (oracleRun query update (sampledChainOracle x ρ lam p) initial t) j)) :
    j.val ≤ t := by
  induction j using Fin.induction generalizing t b with
  | zero => exact Nat.zero_le t
  | succ j ih =>
    obtain ⟨s, hs, hh⟩ := no_premature_predecessor query update output initial x ρ lam N hgood
      t ht j.castSucc j.succ (by simp) b hhit
    have hprev := ih s (by omega) false hh
    simpa only [Fin.val_succ] using Nat.succ_le_of_lt (lt_of_le_of_lt hprev hs)

/-- A concrete, weaker chain-length lower bound already follows from the
coupling: fewer than T calls leave a block below the gradient threshold. -/
theorem short_run_unfinished {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (x : Fin (T + 1) → FixedTableSample n D k) (ρ lam : ℝ) (N : ℕ)
    (hgood : x ∉ prematureAlignmentEvent query update output initial ρ lam N) (hN : N < T) :
    ∃ j, alignment (sampledDirection (x j))
      (output (oracleRun query update (sampledChainOracle x ρ lam p) initial N) j) < 9 / 32 := by
  refine ⟨Fin.last T, ?_⟩
  have hclosed : alignment (sampledDirection (x (Fin.last T)))
      (output (oracleRun query update (sampledChainOracle x ρ lam p) initial N) (Fin.last T)) ≤ 5 / 32 := by
    apply le_of_not_gt
    intro hh
    have hb := no_premature_stage_index_le_time query update output initial x ρ lam N hgood
      (Fin.last T) N le_rfl true hh
    simp only [Fin.val_last] at hb
    omega
  linarith

end FullJet
