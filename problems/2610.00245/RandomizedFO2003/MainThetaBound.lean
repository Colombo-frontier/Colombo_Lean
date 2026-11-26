import RandomizedFO2003.MainLowerBound
import RandomizedFO2003.MainUpperBound

namespace RandomizedFO2003.Model

open MeasureTheory
open scoped ENNReal

/-- Matching dimension-uniform oracle bounds on one common parameter
regime. The lower bound permits arbitrary measurable random seeds and
queries; the upper bound is attained by a deterministic first-order method. -/
def MainThetaBound : Prop :=
  ∃ c C K : ℝ, 0 < c ∧ 0 < C ∧ 0 < K ∧
    ∀ ε Δ L₁ L₂ : ℝ, 0 < ε → 0 < Δ → 0 < L₁ → 0 < L₂ →
      ε ≤ c * L₁ ^ 2 / L₂ →
      C ≤ Δ * L₂ ^ (1 / 2 : ℝ) * ε ^ (-(3 / 2 : ℝ)) →
      (∀ T : ℕ, (T : ℝ) < c * rate ε Δ L₁ L₂ →
        ∃ d : ℕ, ∀ (Seed : Type) [MeasurableSpace Seed]
          (ν : Measure Seed) [IsProbabilityMeasure ν] (A : Algorithm d Seed),
          ∃ f : Space d → ℝ,
            InFunctionClass f Δ L₁ L₂ ∧ ν (Success A f ε T) < (2 / 3 : ℝ≥0∞)) ∧
      (∀ d : ℕ, ∃ T : ℕ, ∃ A : Algorithm d Unit,
        (T : ℝ) ≤ K * rate ε Δ L₁ L₂ ∧
          ∀ f : Space d → ℝ, InFunctionClass f Δ L₁ L₂ →
            ‖gradient f (A.output T () (transcript A f () T))‖ ≤ ε)

/-- The complete matching upper/lower conclusion, in its operational
minimax form, with unchanged original function class and first-order oracle. -/
theorem main_theta_bound : MainThetaBound := by
  obtain ⟨c, C, hc, hC, hlower⟩ := main_lower_bound
  obtain ⟨K, hK, hupper⟩ := main_upper_bound
  refine ⟨min c 1, max C 1, K, lt_min hc (by norm_num), lt_max_of_lt_left hC, hK, ?_⟩
  intro ε Δ L₁ L₂ hε hΔ hL₁ hL₂ haccuracy hmass
  have hclower : min c 1 * L₁ ^ 2 / L₂ ≤ c * L₁ ^ 2 / L₂ :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left c 1) (sq_nonneg L₁)) hL₂.le
  have hcupper : min c 1 * L₁ ^ 2 / L₂ ≤ L₁ ^ 2 / L₂ := by
    simpa only [one_mul] using div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_right c 1) (sq_nonneg L₁)) hL₂.le
  have hrate : 0 ≤ rate ε Δ L₁ L₂ := by unfold rate; positivity
  constructor
  · intro T hT
    exact hlower ε Δ L₁ L₂ hε hΔ hL₁ hL₂ (haccuracy.trans hclower)
      ((le_max_left C 1).trans hmass) T
      (hT.trans_le (mul_le_mul_of_nonneg_right (min_le_left c 1) hrate))
  · exact hupper ε Δ L₁ L₂ hε hΔ hL₁ hL₂ (haccuracy.trans hcupper)
      ((le_max_right C 1).trans hmass)

end RandomizedFO2003.Model
