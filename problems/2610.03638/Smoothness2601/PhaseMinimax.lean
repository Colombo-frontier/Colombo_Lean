import Smoothness2601.UniformMinimax
import Smoothness2601.PhaseRates

/-! The saturated growing-order regime and infinite-order factorial envelopes,
including the analytic logarithmic-square endpoint. -/
noncomputable section
open scoped ENNReal
namespace Smoothness2601

theorem infinite_factorial_minimax (b : Budgets) {M Λ β : ℝ}
    (hgap : b.μ < b.L₁) (hM : 0 < M) (hΛ : 0 < Λ) (hβ : 0 < β) :
    ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ENNReal.ofReal (c*ε^(-4:ℝ)*(Real.log (1/ε))^(2*β)) ≤
          minimaxComplexity b ⊤ (derivativeEnvelope b M Λ β) ε ∧
        minimaxComplexity b ⊤ (derivativeEnvelope b M Λ β) ε ≤
          ENNReal.ofReal (C*ε^(-4:ℝ)*(Real.log (1/ε))^(2*β)) := by
  obtain ⟨c,C,δ,hc,hC,hδ,h⟩ := uniform_minimax b hgap hM hΛ hβ.le
  have hphaseC := phaseCoefficient_pos hβ
  refine ⟨c*phaseCoefficient β,C*(2^β)^2*phaseCoefficient β,min δ (Real.exp (-β)),
    mul_pos hc hphaseC,by positivity,lt_min hδ (Real.exp_pos _),?_⟩
  intro ε hε hs
  have hph := phase_threshold hβ hε (hs.le.trans (min_le_right _ _))
  have ht : 0 ≤ Real.log (1/ε) := by
    have hh := (le_div_iff₀ hβ).mp hph
    linarith
  obtain ⟨hl,hu⟩ := orderTradeoff_infinite_phase hβ hε hph
  have hcl := (phase_rate_bounds hβ ht hc.le hε.le hl hu).1
  have hcu := (phase_rate_bounds hβ ht hC.le hε.le hl hu).2
  have hh := h ⊤ le_top ε hε (hs.trans_le (min_le_left _ _))
  exact ⟨(ENNReal.ofReal_le_ofReal hcl).trans hh.1,hh.2.trans (ENNReal.ofReal_le_ofReal hcu)⟩

theorem growing_order_after_phase (b : Budgets) {M Λ β : ℝ}
    (hgap : b.μ < b.L₁) (hM : 0 < M) (hΛ : 0 < Λ) (hβ : 0 < β) :
    ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧
      ∀ p : ℕ, 1 ≤ p → ∀ ε : ℝ, 0 < ε → ε < δ → Real.log (1/ε)/β ≤ p →
        ENNReal.ofReal (c*ε^(-4:ℝ)*(Real.log (1/ε))^(2*β)) ≤
          minimaxComplexity b p (derivativeEnvelope b M Λ β) ε ∧
        minimaxComplexity b p (derivativeEnvelope b M Λ β) ε ≤
          ENNReal.ofReal (C*ε^(-4:ℝ)*(Real.log (1/ε))^(2*β)) := by
  obtain ⟨c,C,δ,hc,hC,hδ,h⟩ := uniform_minimax b hgap hM hΛ hβ.le
  have hphaseC := phaseCoefficient_pos hβ
  refine ⟨c*phaseCoefficient β,C*(2^β)^2*phaseCoefficient β,min δ (Real.exp (-β)),
    mul_pos hc hphaseC,by positivity,lt_min hδ (Real.exp_pos _),?_⟩
  intro p hp ε hε hs hcap
  have hph := phase_threshold hβ hε (hs.le.trans (min_le_right _ _))
  have ht : 0 ≤ Real.log (1/ε) := by
    have hh := (le_div_iff₀ hβ).mp hph
    linarith
  obtain ⟨hl,hu⟩ := orderTradeoff_finite_phase hβ hε hph hcap
  have hcl := (phase_rate_bounds hβ ht hc.le hε.le hl hu).1
  have hcu := (phase_rate_bounds hβ ht hC.le hε.le hl hu).2
  have hh := h p (by exact_mod_cast hp) ε hε (hs.trans_le (min_le_left _ _))
  exact ⟨(ENNReal.ofReal_le_ofReal hcl).trans hh.1,hh.2.trans (ENNReal.ofReal_le_ofReal hcu)⟩

theorem infinite_analytic_minimax (b : Budgets) {M Λ : ℝ}
    (hgap : b.μ < b.L₁) (hM : 0 < M) (hΛ : 0 < Λ) :
    ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ENNReal.ofReal (c*ε^(-4:ℝ)*(Real.log (1/ε))^2) ≤
          minimaxComplexity b ⊤ (derivativeEnvelope b M Λ 1) ε ∧
        minimaxComplexity b ⊤ (derivativeEnvelope b M Λ 1) ε ≤
          ENNReal.ofReal (C*ε^(-4:ℝ)*(Real.log (1/ε))^2) := by
  simpa using infinite_factorial_minimax b hgap hM hΛ (by norm_num : (0:ℝ) < 1)

end Smoothness2601
