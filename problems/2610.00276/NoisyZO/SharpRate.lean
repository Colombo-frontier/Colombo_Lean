import NoisyZO.Minimax
import NoisyZO.RateArithmetic
import Mathlib.Basic.ENNReal.Inv

/-!
# Sharp minimax-rate statement

This is the order-theoretic final theorem in the exact saturated scale used by
the manuscript.  Analytic lower and algorithmic upper certificates plug into
it independently.
-/

open scoped ENNReal

namespace NoisyZO

noncomputable section

/-- The saturated rate `min {1, (d²/T)^((β-1)/β)}` as a nonnegative extended
real, the natural complete lattice for minimax risks. -/
def minimaxScale (β : ℝ) (d T : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (min 1 (((d : ℝ) ^ 2 / T) ^ rateExponent β))

/-- The manuscript's sharp minimax theorem follows immediately once the
lower hard-instance certificate and one uniform algorithm certificate have
been established with dimension- and budget-independent constants. -/
theorem sharp_minimax_rate_of_certificates
    {Algorithm Objective : Type*}
    (risk : Algorithm → Objective → ℝ≥0∞)
    (β : ℝ) (d T : ℕ) (c C : ℝ≥0∞)
    (hlower : ∀ algorithm, ∃ objective,
      c * minimaxScale β d T ≤ risk algorithm objective)
    (algorithm : Algorithm)
    (hupper : ∀ objective,
      risk algorithm objective ≤ C * minimaxScale β d T) :
    c * minimaxScale β d T ≤ minimaxRisk risk ∧
      minimaxRisk risk ≤ C * minimaxScale β d T :=
  minimaxRisk_between risk
    (c * minimaxScale β d T) (C * minimaxScale β d T)
    hlower algorithm hupper

end

end NoisyZO
