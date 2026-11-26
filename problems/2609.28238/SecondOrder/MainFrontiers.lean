import SecondOrder.UniformUpperFeasible
import SecondOrder.MinimaxLowerRates

open scoped ENNReal

namespace SecondOrder
noncomputable section

/-- An explicit two-tolerance form of the manuscript's soft Theta notation.
The thresholds are independent and only logarithmic factors are suppressed. -/
def TolerancePolylogTheta (complexity : ℝ → ℝ → ℝ≥0∞) (rate : ℝ → ℝ → ℝ) : Prop :=
  ∃ c C ε₀ γ₀ : ℝ, 0<c ∧ 0<C ∧ 0<ε₀ ∧ 0<γ₀ ∧
    ∀ ε γ : ℝ, 0<ε → ε≤ε₀ → 0<γ → γ≤γ₀ →
      ENNReal.ofReal (c/(toleranceLog ε γ)^2*rate ε γ)≤complexity ε γ ∧
      complexity ε γ≤ENNReal.ofReal (C*(toleranceLog ε γ)^6*rate ε γ)

/-- Main theorem `main:holder`, for the actual uniform-algorithm minimax
quantity and the manuscript's ceiling dimension envelope. -/
theorem holderHessian_frontier (P : Parameters) {ν κ : ℝ}
    (hν : 0<ν) (hν1 : ν≤1) (hκ : 1+2/ν<κ) :
    TolerancePolylogTheta (hvpEnvelopeComplexity P ν κ) (holderEndpointRate ν) := by
  have hκ0 : 0≤κ := by have hp := div_pos (show (0:ℝ)<2 by norm_num) hν; linarith
  obtain ⟨ε₀,γ₀,hε₀,hγ₀,hlo⟩ := holderEnvelope_minimax_polylog_lower P hν hν1 hκ
  refine ⟨holderMinimaxLowerCoefficient P ν,stochasticEnvelopeCoefficient P ν κ,
    min ε₀ 1,min γ₀ 1,holderMinimaxLowerCoefficient_pos P hν,
    stochasticEnvelopeCoefficient_pos P hν hκ0,lt_min hε₀ (by norm_num),
    lt_min hγ₀ (by norm_num),?_⟩
  intro ε γ hε hεsmall hγ hγsmall
  exact ⟨hlo ε γ hε (hεsmall.trans (min_le_left _ _)) hγ (hγsmall.trans (min_le_left _ _)),
    holderEnvelope_minimax_polylog_upper P hν hκ0 hε (hεsmall.trans (min_le_right _ _))
      hγ (hγsmall.trans (min_le_right _ _))⟩

/-- Main theorem `main:baseline`: the exponents are three and five, with
no relation imposed between the two positive tolerances. -/
theorem lipschitzHessian_frontier (P : Parameters) {κ : ℝ} (hκ : 3<κ) :
    TolerancePolylogTheta (hvpEnvelopeComplexity P 1 κ) (fun ε γ => 1/ε^3+1/γ^5) := by
  have hκ0 : 0≤κ := by linarith
  obtain ⟨ε₀,γ₀,hε₀,hγ₀,hlo⟩ := lipschitzEnvelope_minimax_polylog_lower P hκ
  refine ⟨holderMinimaxLowerCoefficient P 1,stochasticEnvelopeCoefficient P 1 κ,
    min ε₀ 1,min γ₀ 1,holderMinimaxLowerCoefficient_pos P (by norm_num),
    stochasticEnvelopeCoefficient_pos P (by norm_num) hκ0,lt_min hε₀ (by norm_num),
    lt_min hγ₀ (by norm_num),?_⟩
  intro ε γ hε hεsmall hγ hγsmall
  exact ⟨hlo ε γ hε (hεsmall.trans (min_le_left _ _)) hγ (hγsmall.trans (min_le_left _ _)),
    lipschitzEnvelope_minimax_polylog_upper P hκ0 hε (hεsmall.trans (min_le_right _ _))
      hγ (hγsmall.trans (min_le_right _ _))⟩

/-- Main theorem `main:rich`, with a positive value-noise budget and joint
value, gradient and full-Hessian observations in its lower witnesses. -/
theorem richResponse_frontier (P : Parameters) {σ₀ κ : ℝ} (hσ₀ : 0<σ₀) (hκ : 3<κ) :
    TolerancePolylogTheta (richEnvelopeComplexity P σ₀ κ) (fun ε γ => 1/ε^3+1/γ^5) := by
  have hκ0 : 0≤κ := by linarith
  obtain ⟨ε₀,γ₀,hε₀,hγ₀,hlo⟩ := richEnvelope_minimax_polylog_lower P hσ₀ hκ
  refine ⟨richMinimaxLowerCoefficient P σ₀,stochasticEnvelopeCoefficient P 1 κ,
    min ε₀ 1,min γ₀ 1,richMinimaxLowerCoefficient_pos P hσ₀,
    stochasticEnvelopeCoefficient_pos P (by norm_num) hκ0,lt_min hε₀ (by norm_num),
    lt_min hγ₀ (by norm_num),?_⟩
  intro ε γ hε hεsmall hγ hγsmall
  exact ⟨hlo ε γ hε (hεsmall.trans (min_le_left _ _)) hγ (hγsmall.trans (min_le_left _ _)),
    richEnvelope_minimax_polylog_upper P σ₀ hκ0 hε (hεsmall.trans (min_le_right _ _))
      hγ (hγsmall.trans (min_le_right _ _))⟩

end
end SecondOrder
