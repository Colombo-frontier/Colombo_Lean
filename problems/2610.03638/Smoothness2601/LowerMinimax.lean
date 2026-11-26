import Smoothness2601.HardLower
import Smoothness2601.HardHorizon
import Smoothness2601.CoordinateMinimax
import Smoothness2601.MinimaxLower

/-! The genuine lower minimax theorem: the constructed globally admissible
scalar-inner family defeats every unrestricted randomized algorithm below
the uniform sample threshold. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Smoothness2601
open HardProfiles

theorem hard_budget_obstruction {b : Budgets} {M Λ β : ℝ}
    (W : WidthConstants b M Λ β) (hM : 0 < M) (hΛ : 0 < Λ)
    {p : WithTop ℕ} (hp : 1 ≤ p) (hβ : 0 ≤ β) {ε : ℝ} (hε : 0 < ε)
    (hεs : 16*ε ≤ W.chainThreshold) (N : ℕ)
    (hN : (N : ℝ) ≤ W.finalRateConstant*ε^(-4:ℝ)*orderTradeoff p β ε ^ 2) :
    ¬ BudgetWorks b p (derivativeEnvelope b M Λ β) ε N := by
  have hs : 0 < 16*ε := by positivity
  have hsδ := (W.chainThreshold_conditions hs hεs).1
  obtain ⟨n,hlo,_hhi,hgap⟩ := W.choose_chain hs hεs
  have hbudget := W.budget_reveal hp hβ hs hεs hlo (W.scaled_budget hp hβ hε hεs hN)
  intro hworks
  obtain ⟨A,hA⟩ := CoordinateMinimax.budgetWorks_scalar hworks (hardDimension N n)
  obtain ⟨U,hU,hfail⟩ := fixed_frame_expected_norm_chosen_dimension W hp hβ hs hsδ n N hbudget A
  let I := FrameTruncation.frameIsometry U hU
  have hsuccess := hA (population W hp hβ hs hsδ I) (regularity W hp hβ hs hsδ I hM hΛ)
    0 0 (initialized W hp hβ hs hsδ I hgap) Unit inferInstance (oracle W hp hβ hs hsδ I) ()
  have hbad := hfail.trans hsuccess
  have hreal := (ENNReal.ofReal_le_ofReal_iff hε.le).mp hbad
  linarith

theorem uniform_minimax_lower (b : Budgets) {M Λ β : ℝ}
    (hgap : b.μ < b.L₁) (hM : 0 < M) (hΛ : 0 < Λ) (hβ : 0 ≤ β) :
    ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧
      ∀ p : WithTop ℕ, 1 ≤ p → ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ENNReal.ofReal (c * ε ^ (-4 : ℝ) * orderTradeoff p β ε ^ 2) ≤
          minimaxComplexity b p (derivativeEnvelope b M Λ β) ε := by
  obtain ⟨W⟩ := widthConstants_nonempty (β := β) b hgap hM hΛ
  refine ⟨W.finalRateConstant,W.chainThreshold/16,W.finalRateConstant_pos,
    div_pos W.chainThreshold_pos (by norm_num),?_⟩
  intro p hp ε hε hs
  have hεs : 16*ε ≤ W.chainThreshold := by linarith
  apply minimax_lower_of_budget_obstruction
  intro N hN
  exact hard_budget_obstruction W hM hΛ hp hβ hε hεs N hN.le

end Smoothness2601
