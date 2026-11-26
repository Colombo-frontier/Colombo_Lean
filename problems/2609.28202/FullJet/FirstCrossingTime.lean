import FullJet.SequentialCrossings

namespace FullJet

noncomputable def firstCrossingTime (P : ℕ → Prop) (N : ℕ) : ℕ := by
  classical
  exact if h : ∃ t, t ≤ N ∧ P t then Nat.find h else N + 1

theorem firstCrossingTime_le {P : ℕ → Prop} {N t : ℕ} (ht : t ≤ N) (hhit : P t) :
    firstCrossingTime P N ≤ t := by
  classical
  have he : ∃ s, s ≤ N ∧ P s := ⟨t, ht, hhit⟩
  rw [firstCrossingTime, dif_pos he]
  exact Nat.find_min' he ⟨ht, hhit⟩

theorem firstCrossingTime_spec {P : ℕ → Prop} {N : ℕ}
    (he : ∃ t, t ≤ N ∧ P t) :
    firstCrossingTime P N ≤ N ∧ P (firstCrossingTime P N) := by
  classical
  rw [firstCrossingTime, dif_pos he]
  exact Nat.find_spec he

theorem firstCrossingTime_min {P : ℕ → Prop} {N t : ℕ}
    (ht : t < firstCrossingTime P N) (hN : t ≤ N) : ¬ P t := by
  intro hh
  exact (not_le_of_gt ht) (firstCrossingTime_le hN hh)

theorem firstCrossingTime_hit_of_le {P : ℕ → Prop} {N : ℕ}
    (ht : firstCrossingTime P N ≤ N) : P (firstCrossingTime P N) := by
  classical
  by_cases he : ∃ t, t ≤ N ∧ P t
  · exact (firstCrossingTime_spec he).2
  · simp only [firstCrossingTime, dif_neg he] at ht
    omega

theorem firstCrossingTime_eq_of_first {P : ℕ → Prop} {N t : ℕ}
    (ht : t ≤ N) (hhit : P t) (hbefore : ∀ s < t, ¬ P s) : firstCrossingTime P N = t := by
  apply le_antisymm (firstCrossingTime_le ht hhit)
  apply le_of_not_gt
  intro hlt
  exact hbefore _ hlt (firstCrossingTime_spec ⟨t, ht, hhit⟩).2

noncomputable def actualCrossingTime {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (initial : State) (x : Fin (T + 1) → FixedTableSample n D k) (ρ lam : ℝ)
    (N : ℕ) (h : Fin (T + 1)) : ℕ :=
  firstCrossingTime (fun t => 5 / 32 < alignment (sampledDirection (x h))
    ((query (oracleRun query update (sampledChainOracle x ρ lam p) initial t)).2 h)) N

/-- Until the first query crossing at h, every gate in its unfinished tail
is closed. This is derived from no premature alignment, not assumed. -/
theorem tail_closed_before_first_crossing {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (x : Fin (T + 1) → FixedTableSample n D k) (ρ lam : ℝ) (N : ℕ)
    (hgood : x ∉ prematureAlignmentEvent query update output initial ρ lam N)
    (h : Fin (T + 1)) (s : ℕ) (hs : s < actualCrossingTime query update initial x ρ lam N h)
    (hN : s ≤ N) (l : Fin (T + 1)) (hl : h.val ≤ l.val) :
    alignment (sampledDirection (x l))
      ((query (oracleRun query update (sampledChainOracle x ρ lam p) initial s)).2 l) ≤ 5 / 32 := by
  apply le_of_not_gt
  intro hh
  by_cases heq : l = h
  · subst l
    exact firstCrossingTime_min hs hN hh
  · have hlt : h.val < l.val := lt_of_le_of_ne hl (fun hv => heq (Fin.ext hv.symm))
    obtain ⟨r, hr, hhit⟩ := no_premature_predecessor query update output initial x ρ lam N hgood
      s hN h l hlt false hh
    exact firstCrossingTime_min (by omega : r < actualCrossingTime query update initial x ρ lam N h)
      (by omega) hhit

/-- At h's first crossing query, later gates are still closed. The reply
can therefore expose the next row, but no later-stage data. -/
theorem later_closed_at_first_crossing {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : State) (x : Fin (T + 1) → FixedTableSample n D k) (ρ lam : ℝ) (N : ℕ)
    (hgood : x ∉ prematureAlignmentEvent query update output initial ρ lam N)
    (h : Fin (T + 1)) (ht : actualCrossingTime query update initial x ρ lam N h ≤ N)
    (l : Fin (T + 1)) (hl : h.val < l.val) :
    alignment (sampledDirection (x l)) ((query (oracleRun query update (sampledChainOracle x ρ lam p) initial
      (actualCrossingTime query update initial x ρ lam N h))).2 l) ≤ 5 / 32 := by
  apply le_of_not_gt
  intro hh
  obtain ⟨s, hs, hhit⟩ := no_premature_predecessor query update output initial x ρ lam N hgood
    _ ht h l hl false hh
  exact firstCrossingTime_min hs (by omega) hhit

end FullJet
