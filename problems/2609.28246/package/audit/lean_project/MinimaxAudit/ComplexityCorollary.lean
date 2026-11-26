import MinimaxAudit.ComplexityUpper
import MinimaxAudit.ComplexityLower
import MinimaxAudit.ComplexityMeasurability

/-! Full revised source complexity corollary, on the actual global Borel
policy classes and their extended-natural infima. Every rate inequality is
obtained from the constructed scalar policies/instances, not a rate contract. -/
namespace MinimaxAudit
open MeasureTheory
open scoped ENNReal
universe u

/-- One set of positive p-only constants works for both source criteria,
all positive public parameters and all sufficiently large ratios. The chain
is stated in extended nonnegative reals to retain the empty-budget infinity
convention, and the middle step is the proved Borel policy inclusion. -/
theorem complexity_corollary_source (p : ℕ) (hp : 2 ≤ p) :
    ∃ c C Q0 : ℝ, 0 < c ∧ 0 < C ∧ 0 < Q0 ∧
      ∀ (E : OracleErrorCriterion) (L D eps : ℝ), 0 < L → 0 < D → 0 < eps →
      Q0 ≤ criterionRatio E p L D eps →
      ENNReal.ofReal (c * (criterionRatio E p L D eps) ^ (2 / (3 * (p : ℝ)-1))) ≤
        (randOracleComplexity.{u} E p L D eps : ℝ≥0∞) ∧
      (randOracleComplexity.{u} E p L D eps : ℝ≥0∞) ≤
        (detOracleComplexity E p L D eps : ℝ≥0∞) ∧
      (detOracleComplexity E p L D eps : ℝ≥0∞) ≤
        ENNReal.ofReal (C * (criterionRatio E p L D eps) ^ (2 / (3 * (p : ℝ)-1)) *
          (1 + Real.log (3 + criterionRatio E p L D eps)) ^ (6 * (p-1))) := by
  obtain ⟨C0,hC0,hupper⟩ := detOracleComplexity_upper p hp
  refine ⟨complexityLowerConstant p,2*C0,max 1 (complexityLowerThreshold p),
    complexityLowerConstant_pos p,by positivity,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro E L D eps hL hD heps hQ
  have hQlower : complexityLowerThreshold p ≤ criterionRatio E p L D eps :=
    (le_max_right _ _).trans hQ
  have hQone : 1 ≤ criterionRatio E p L D eps := (le_max_left _ _).trans hQ
  refine ⟨randOracleComplexity_lower.{u} E hp hL hD heps hQlower,
    ENat.toENNReal_mono (randOracleComplexity_le_det.{u} E p L D eps),?_⟩
  exact (hupper E L D eps hL hD heps).trans
    (ENNReal.ofReal_le_ofReal (criterionUpperCost_asymptotic E hp hC0.le hQone))
end MinimaxAudit
