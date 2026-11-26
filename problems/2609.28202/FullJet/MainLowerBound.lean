import FullJet.UniformBudgetLowerBound

open MeasureTheory

namespace FullJet

theorem rate_lower_from_capacity (n Q A C K R : ℝ)
    (hn : 0 ≤ n) (hK : 0 < K) (hR : 1 ≤ R)
    (hlinear : n ≤ 2 * Q) (haccuracy : K * A ≤ n * C)
    (hlarge : 2 ≤ C → n * C / (4 * R) ≤ Q) :
    K / (8 * R * (K + 1)) * (n + A) ≤ Q := by
  have hQ : 0 ≤ Q := by linarith
  have hden : 0 < 8 * R * (K + 1) := by positivity
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  by_cases hC : 2 ≤ C
  · have hbig := (div_le_iff₀ (by positivity : 0 < 4 * R)).mp (hlarge hC)
    have hkn := mul_le_mul_of_nonneg_left hlinear hK.le
    have hcoef : 0 ≤ 8 * R * (K + 1) - (2 * K + 4 * R) := by
      nlinarith only [hR, hK, mul_nonneg (sub_nonneg.mpr hR) hK.le]
    have hprod := mul_nonneg hcoef hQ
    nlinarith only [hbig, haccuracy, hkn, hprod]
  · have hsmall := mul_le_mul_of_nonneg_left (le_of_not_ge hC) hn
    have hkn := mul_le_mul_of_nonneg_left hlinear (by positivity : 0 ≤ K + 2)
    have hcoef : 0 ≤ 8 * R * (K + 1) - 2 * (K + 2) := by
      nlinarith only [hR, hK, mul_nonneg (sub_nonneg.mpr hR) hK.le]
    have hprod := mul_nonneg hcoef hQ
    nlinarith only [hsmall, haccuracy, hkn, hprod]

noncomputable def mainLowerConstant (p : ℕ) : ℝ :=
  capacityConstant p / (8 * (largeSampleThreshold : ℝ) * (capacityConstant p + 1))

theorem mainLowerConstant_pos (p : ℕ) : 0 < mainLowerConstant p := by
  have hK := capacityConstant_pos p
  unfold mainLowerConstant largeSampleThreshold rowBudgetDivisor
  positivity

/-- The manuscript's full accuracy-dependent lower rate, with all actual
algorithm, probability, function-class, integer-bias, and dimension choices
discharged. Constants depend only on the fixed derivative order. -/
theorem main_lower_bound_for_algorithm {Ω : Type*} [MeasurableSpace Ω] {n p N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (A : UniformJetAlgorithm Ω n p)
    (hp : 2 ≤ p) (hn : largeSampleThreshold ≤ n)
    (Δ L ε δ : ℝ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) (hδ : δ < 1 / 4)
    (hA : A.succeeds P N Δ L ε δ) :
    mainLowerConstant p * fullRate p n Δ L ε ≤ (N : ℝ) := by
  have hn0 : 0 < n := by norm_num [largeSampleThreshold, rowBudgetDivisor] at hn; omega
  have hlin := scalar_algorithm_budget_lower P (A ℝ) hn0 hp Δ L ε δ hΔ hL.le hε hδ (hA ℝ)
  have hlinear : (n : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hlin.le
  obtain ⟨m, k, q, hm, hmn, hbalance, hlow, hhigh, hbudget, hqueries, hr⟩ :=
    exists_discrete_row_budget n hn
  have hρ : 0 < (m : ℝ) / n := by positivity
  have hC := chainStageCapacity_pos p Δ L ((m : ℝ) / n) ε hΔ hL hρ hε
  have hacc := capacity_dominates_accuracy p n m (by omega) hn0 hm hlow Δ L ε hΔ hL hε
  apply rate_lower_from_capacity (n : ℝ) (N : ℝ) (accuracyRate p n Δ L ε)
    (chainStageCapacity p Δ L ((m : ℝ) / n) ε) (capacityConstant p) (largeSampleThreshold : ℝ)
    (Nat.cast_nonneg _) (capacityConstant_pos p) (by norm_num [largeSampleThreshold, rowBudgetDivisor])
    hlinear hacc
  intro hlarge
  have hbound := successful_family_large_capacity P A hn0 hm hmn hbalance hp Δ L ε δ
    hΔ hL hε hδ hA hlarge hbudget hqueries
  have hmul := mul_le_mul_of_nonneg_right hr hC.le
  calc
    _ = ((n : ℝ) / largeSampleThreshold * chainStageCapacity p Δ L ((m : ℝ) / n) ε) / 4 := by ring
    _ ≤ (q + 1 : ℕ) * chainStageCapacity p Δ L ((m : ℝ) / n) ε / 4 :=
      div_le_div_of_nonneg_right hmul (by norm_num)
    _ ≤ _ := hbound

/-- This is the expanded rate exactly in the manuscript's exponent notation. -/
theorem main_lower_bound_expanded {Ω : Type*} [MeasurableSpace Ω] {n p N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (A : UniformJetAlgorithm Ω n p)
    (hp : 2 ≤ p) (hn : largeSampleThreshold ≤ n)
    (Δ L ε δ : ℝ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) (hδ : δ < 1 / 4)
    (hA : A.succeeds P N Δ L ε δ) :
    mainLowerConstant p * ((n : ℝ) + (n : ℝ) ^ (1 - 1 / (2 * (p : ℝ))) *
      (Δ * L ^ (1 / (p : ℝ)) * ε ^ (-((p : ℝ) + 1) / p))) ≤ (N : ℝ) := by
  have h := main_lower_bound_for_algorithm P A hp hn Δ L ε δ hΔ hL hε hδ hA
  simpa only [fullRate, accuracyRate, accuracyWork_eq_manuscript p (by omega)] using h

end FullJet
