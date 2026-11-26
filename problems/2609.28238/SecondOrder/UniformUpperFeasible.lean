import SecondOrder.UniformUpperOutputLaw
import SecondOrder.UpperEnvelopeBudget
import SecondOrder.MinimaxSimulation

open MeasureTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

/-- A single measurable algorithm, chosen before the sample space, sample
law and loss, meets the success requirement on every common-loss instance. -/
theorem uniformUpperAlgorithm_solves (P : Parameters) (ν : ℝ) (d : ℕ)
    {ε γ : ℝ} (hε : 0<ε) (hγ : 0<γ) :
    HvpSolves (uniformUpperSeedLaw P ν d ε hγ) (uniformUpperAlgorithm P ν d ε γ)
      P ν ε γ (stochasticUpperCap P ν d ε γ) := by
  intro Ω mΩ η hη F f h
  obtain ⟨a₀,_⟩ := nonempty_of_measure_ne_zero (by simp : η Set.univ≠0)
  exact (by norm_num : (2:ℝ)/3≤29/32).trans (h.uniformUpperAlgorithm_success a₀ hε hγ)

theorem uniformUpperBudgetFeasible (P : Parameters) (ν : ℝ) (d : ℕ)
    {ε γ : ℝ} (hε : 0<ε) (hγ : 0<γ) :
    HvpBudgetFeasible P ν d ε γ (stochasticUpperCap P ν d ε γ) := by
  exact ⟨UniformUpperSeed P ν d ε γ,ℕ → Point d,inferInstance,inferInstance,
    uniformUpperSeedLaw P ν d ε hγ,inferInstance,uniformUpperAlgorithm P ν d ε γ,
    uniformUpperAlgorithm_measurable P ν d ε γ,uniformUpperAlgorithm_solves P ν d hε hγ⟩

theorem hvpMinimaxComplexity_upper_cap (P : Parameters) (ν : ℝ) (d : ℕ)
    {ε γ : ℝ} (hε : 0<ε) (hγ : 0<γ) :
    hvpMinimaxComplexity P ν d ε γ≤(stochasticUpperCap P ν d ε γ : ℝ≥0∞) :=
  hvpMinimaxComplexity_le_budget P ν d ε γ _ (uniformUpperBudgetFeasible P ν d hε hγ)

theorem holderEnvelope_minimax_polylog_upper (P : Parameters) {ν κ ε γ : ℝ}
    (hν : 0<ν) (hκ : 0≤κ) (hε : 0<ε) (hε1 : ε≤1) (hγ : 0<γ) (hγ1 : γ≤1) :
    hvpEnvelopeComplexity P ν κ ε γ≤
      ENNReal.ofReal (stochasticEnvelopeCoefficient P ν κ*(toleranceLog ε γ)^6*
        holderEndpointRate ν ε γ) := by
  apply iSup_le
  intro d
  apply iSup_le
  intro hd
  apply (hvpMinimaxComplexity_upper_cap P ν d hε hγ).trans
  simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal
    (stochasticUpperCap_envelope_rate P hν hκ hε hε1 hγ hγ1 (by omega) hd.2).le

theorem lipschitzEnvelope_minimax_polylog_upper (P : Parameters) {κ ε γ : ℝ}
    (hκ : 0≤κ) (hε : 0<ε) (hε1 : ε≤1) (hγ : 0<γ) (hγ1 : γ≤1) :
    hvpEnvelopeComplexity P 1 κ ε γ≤
      ENNReal.ofReal (stochasticEnvelopeCoefficient P 1 κ*(toleranceLog ε γ)^6*
        (1/ε^3+1/γ^5)) := by
  simpa only [holderEndpointRate_lipschitz ε hγ.le] using
    holderEnvelope_minimax_polylog_upper P (show (0:ℝ)<1 by norm_num) hκ hε hε1 hγ hγ1

theorem richEnvelope_minimax_polylog_upper (P : Parameters) (σ₀ : ℝ) {κ ε γ : ℝ}
    (hκ : 0≤κ) (hε : 0<ε) (hε1 : ε≤1) (hγ : 0<γ) (hγ1 : γ≤1) :
    richEnvelopeComplexity P σ₀ κ ε γ≤
      ENNReal.ofReal (stochasticEnvelopeCoefficient P 1 κ*(toleranceLog ε γ)^6*
        (1/ε^3+1/γ^5)) :=
  (richEnvelopeComplexity_le_hvp P σ₀ κ ε γ).trans
    (lipschitzEnvelope_minimax_polylog_upper P hκ hε hε1 hγ hγ1)

end
end SecondOrder
