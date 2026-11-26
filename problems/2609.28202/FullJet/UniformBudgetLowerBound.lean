import FullJet.AlgorithmModel
import FullJet.RateParameters
import FullJet.DiscreteRowBudget

open MeasureTheory

namespace FullJet

theorem successful_family_exceeds_capacity {Ω : Type*} [MeasurableSpace Ω]
    {n k m T p N q : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] (A : UniformJetAlgorithm Ω n p)
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n) (hbalance : 2 * k = n + m) (hp : 2 ≤ p)
    (Δ L ε δ : ℝ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) (hδ : δ < 1 / 4)
    (hA : A.succeeds P N Δ L ε δ)
    (hT : (T + 1 : ℕ) ≤ chainStageCapacity p Δ L ((m : ℝ) / n) ε)
    (hbudget : 8 * (m : ℝ) + 9 * (q + 1 : ℕ) ≤ n)
    (hqueries : (q + 1 : ℕ) * ((m : ℝ) / n) ^ 2 ≤ (5 / 32 : ℝ) ^ 2 / 1024) :
    (q + 1) * (T + 1) < 2 * N := by
  by_contra h
  have hN : 2 * N ≤ (q + 1) * (T + 1) := by omega
  obtain ⟨D, hD, hhard⟩ := chain_capacity_lower_bound P hn hm hmn hbalance hp Δ L ε hΔ hL hε
    hT hbudget hN hqueries
  let E := BlockSpace T (EuclideanSpace ℝ (Fin D))
  let B := A E
  have hB := hA E
  obtain ⟨f, hf, hh⟩ := hhard B.State B.query B.update B.output B.initial hB.1
  exact (not_le_of_gt hδ) (hh.trans (hB.2 f hf))

/-- The floor of a feasible real stage capacity converts the actual lower
bound into a real rate without replacing the algorithmic event by a premise. -/
theorem successful_family_large_capacity {Ω : Type*} [MeasurableSpace Ω]
    {n k m p N q : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] (A : UniformJetAlgorithm Ω n p)
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n) (hbalance : 2 * k = n + m) (hp : 2 ≤ p)
    (Δ L ε δ : ℝ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) (hδ : δ < 1 / 4)
    (hA : A.succeeds P N Δ L ε δ)
    (hcap : 2 ≤ chainStageCapacity p Δ L ((m : ℝ) / n) ε)
    (hbudget : 8 * (m : ℝ) + 9 * (q + 1 : ℕ) ≤ n)
    (hqueries : (q + 1 : ℕ) * ((m : ℝ) / n) ^ 2 ≤ (5 / 32 : ℝ) ^ 2 / 1024) :
    (q + 1 : ℕ) * chainStageCapacity p Δ L ((m : ℝ) / n) ε / 4 ≤ (N : ℝ) := by
  let C := chainStageCapacity p Δ L ((m : ℝ) / n) ε
  obtain ⟨hfloorlo, hfloorhi⟩ := floor_stage_budget C hcap
  have hfpos : 0 < ⌊C⌋₊ := by
    have hh : (0 : ℝ) < (⌊C⌋₊ : ℝ) := lt_of_lt_of_le (by dsimp [C]; linarith only [hcap]) hfloorlo
    exact_mod_cast hh
  have hT : ⌊C⌋₊ - 1 + 1 = ⌊C⌋₊ := by omega
  have hh := successful_family_exceeds_capacity (T := ⌊C⌋₊ - 1) P A hn hm hmn hbalance hp
    Δ L ε δ hΔ hL hε hδ hA (by rw [hT]; exact hfloorhi) hbudget hqueries
  rw [hT] at hh
  have hh' : (q + 1 : ℕ) * (⌊C⌋₊ : ℝ) < 2 * (N : ℝ) := by exact_mod_cast hh
  have hmul := mul_le_mul_of_nonneg_left hfloorlo (show (0 : ℝ) ≤ (q + 1 : ℕ) by positivity)
  change (q + 1 : ℕ) * C / 4 ≤ (N : ℝ)
  nlinarith only [hh', hmul]

end FullJet
