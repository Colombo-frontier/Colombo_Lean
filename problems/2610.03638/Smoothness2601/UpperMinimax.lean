import Smoothness2601.UpperAlgorithm
import Smoothness2601.UpperSource

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Smoothness2601
/-- The upper half of the source uniform theorem, simultaneously for every
finite smoothness order and p=∞, with constants independent of dimension. -/
theorem uniform_minimax_upper (b : Budgets) {M Λ β : ℝ}
    (hgap : b.μ < b.L₁) (hM : 0 < M) (hΛ : 0 < Λ) (hβ : 0 ≤ β) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ p : WithTop ℕ, 1 ≤ p → ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        minimaxComplexity b p (derivativeEnvelope b M Λ β) ε ≤
          ENNReal.ofReal (C * ε ^ (-4 : ℝ) * orderTradeoff p β ε ^ 2) := by
  refine ⟨UpperSource.constant b M Λ β, UpperSource.accuracyThreshold b,
    UpperSource.constant_pos b hgap M Λ β, UpperSource.accuracyThreshold_pos b, ?_⟩
  intro p hp ε hε hs
  obtain ⟨r,hr,hrp,hN⟩ := UpperSource.finite_order_budget (M := M) (Λ := Λ) b hgap hp hβ hε hs.le
  have hworks := fixed_order_budgetWorks b hgap hM hΛ hβ
    (UpperSource.biasCoefficient_pos b) (UpperSource.biasCoefficient_small b) hε r hr hrp
  refine (minimax_le_budget hworks).trans ?_
  exact_mod_cast ENNReal.ofReal_le_ofReal hN

end Smoothness2601
