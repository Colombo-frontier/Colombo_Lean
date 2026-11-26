import FullJet.SequentialLowerBound

open MeasureTheory
open scoped BigOperators

namespace FullJet

def chainSeedSuccess {Ω State : Type*} {n D k T p : ℕ}
    (query : Ω → State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : Ω → State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : Ω → State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : Ω → State) (ρ : ℝ) (N : ℕ) (x : Fin (T + 1) → FixedTableSample n D k) : Set Ω :=
  {s | ‖fderiv ℝ (baseChain (fun j => sampledDirection (x j)) (33 / 16))
    (output s (oracleRun (query s) (update s) (sampledChainOracle x ρ (33 / 16) p) (initial s) N))‖ < 1 / 4}

/-- Arbitrary private randomness is averaged over the actual finite hard
chain distribution. With the explicit tail bound, success is at most 3/4. -/
theorem randomized_chain_success_le {Ω State : Type*} [MeasurableSpace Ω] {n D k T p : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (hn : 0 < n) (hD : 0 < D) (hk : k ≤ n)
    (m : ℝ) (hm : 0 ≤ m) (hbalance : 2 * (k : ℝ) = n + m)
    (query : Ω → State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : Ω → State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : Ω → State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : Ω → State) (ρ : ℝ) (N q : ℕ)
    (hbudget : 8 * m + 9 * (q + 1 : ℕ) ≤ n) (hN : 2 * N ≤ (q + 1) * (T + 1))
    (hqueries : (q + 1 : ℕ) * (m / n) ^ 2 ≤ (5 / 32 : ℝ) ^ 2 / 1024)
    (hdim : 32 * Real.log 2 ≤ (5 / 32 : ℝ) ^ 2 * D)
    (hfamily : (2 : ℝ) * (q + 1 : ℕ) ≤ Real.exp ((5 / 32 : ℝ) ^ 2 * D / 4))
    (htail : 2 * (T + 1 : ℕ) ^ 2 * (N + 1 : ℕ) * Real.exp (-((5 / 32 : ℝ) ^ 2 * D / 2)) ≤ 1 / 4)
    (hmeas : ∀ x : Fin (T + 1) → FixedTableSample n D k, MeasurableSet (chainSeedSuccess query update output initial ρ N x)) :
    ∑ x, (fixedChainLaw n D k (T + 1) hk x).toReal *
      P.real (chainSeedSuccess query update output initial ρ N x) ≤ 3 / 4 := by
  apply pmf_seed_event_average_le P (fixedChainLaw n D k (T + 1) hk) _ hmeas
  intro s
  have hfail := actual_chain_gradient_failure_probability hn hD hk m hm hbalance
    (query s) (update s) (output s) (initial s) ρ N q hbudget hN hqueries hdim hfamily
  have hcomp := pmf_event_compl_toReal (fixedChainLaw n D k (T + 1) hk)
    {x | s ∈ chainSeedSuccess query update output initial ρ N x}
  have heq : {x : Fin (T + 1) → FixedTableSample n D k | s ∈ chainSeedSuccess query update output initial ρ N x}ᶜ =
      {x | (1 / 4 : ℝ) ≤ ‖fderiv ℝ (baseChain (fun j => sampledDirection (x j)) (33 / 16))
        (output s (oracleRun (query s) (update s) (sampledChainOracle x ρ (33 / 16) p) (initial s) N))‖} := by
    ext x
    simp [chainSeedSuccess]
  rw [heq] at hcomp
  linarith

/-- A single fixed chain defeats the randomized algorithm. The seed space
need not be finite, and no minimax or Yao principle is assumed. -/
theorem randomized_chain_fixed_failure {Ω State : Type*} [MeasurableSpace Ω] {n D k T p : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (hn : 0 < n) (hD : 0 < D) (hk : k ≤ n)
    (m : ℝ) (hm : 0 ≤ m) (hbalance : 2 * (k : ℝ) = n + m)
    (query : Ω → State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : Ω → State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : Ω → State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : Ω → State) (ρ : ℝ) (N q : ℕ)
    (hbudget : 8 * m + 9 * (q + 1 : ℕ) ≤ n) (hN : 2 * N ≤ (q + 1) * (T + 1))
    (hqueries : (q + 1 : ℕ) * (m / n) ^ 2 ≤ (5 / 32 : ℝ) ^ 2 / 1024)
    (hdim : 32 * Real.log 2 ≤ (5 / 32 : ℝ) ^ 2 * D)
    (hfamily : (2 : ℝ) * (q + 1 : ℕ) ≤ Real.exp ((5 / 32 : ℝ) ^ 2 * D / 4))
    (htail : 2 * (T + 1 : ℕ) ^ 2 * (N + 1 : ℕ) * Real.exp (-((5 / 32 : ℝ) ^ 2 * D / 2)) ≤ 1 / 4)
    (hmeas : ∀ x : Fin (T + 1) → FixedTableSample n D k, MeasurableSet (chainSeedSuccess query update output initial ρ N x)) :
    ∃ x : Fin (T + 1) → FixedTableSample n D k,
      1 / 4 ≤ P.real (chainSeedSuccess query update output initial ρ N x)ᶜ := by
  have havg := randomized_chain_success_le P hn hD hk m hm hbalance query update output initial
    ρ N q hbudget hN hqueries hdim hfamily htail hmeas
  obtain ⟨x, _, hx⟩ := pmf_exists_low_probability P (fixedChainLaw n D k (T + 1) hk)
    (chainSeedSuccess query update output initial ρ N) (3 / 4) havg
  refine ⟨x, ?_⟩
  rw [measureReal_compl (hmeas x), measureReal_univ_eq_one]
  linarith

end FullJet
