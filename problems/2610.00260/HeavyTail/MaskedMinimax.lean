import HeavyTail.MaskedAmbientLower
import HeavyTail.MaskedRateCalibration
import HeavyTail.ModelQuantile

/-! The masked heavy-tail statistical component in the full ambient minimax
class, valid at all positive call budgets. -/

open MeasureTheory
open scoped ENNReal
namespace HeavyTail.MaskedLower
noncomputable section

theorem masked_fixedCallMinimax_lower_large_budget {d : ℕ} (θ : OracleParameters)
    (hT : 0 < θ.T) (hdim : Nat.ceil (θ.L ^ 2 / θ.s ^ 2) ≤ d)
    (hkT : Nat.ceil (θ.L ^ 2 / θ.s ^ 2) ≤ θ.T) :
    ENNReal.ofReal (heavyRate θ.μ θ.D θ.G θ.L θ.s θ.p θ.T) ≤ fixedCallMinimax (HardSpace d) θ := by
  let k := Nat.ceil (θ.L ^ 2 / θ.s ^ 2)
  let e := firstCoordinatesEmbedding hdim
  let π := 1 / (8 * (θ.T : ℝ))
  have hk : 0 < k := (activeDimension_bounds θ.s_pos θ.s_le_L).1
  have hvariance : θ.L ^ 2 ≤ (k : ℝ) * θ.s ^ 2 := activeDimension_variance θ.s_pos
  obtain ⟨hπ, hπ1, hkπ, hbudget⟩ := masked_sampling_budget hT hkT
  have hrate := maskedAmplitude_heavy_envelope θ.μ_nonneg θ.D_pos.le θ.G_pos.le
    θ.s_pos θ.s_le_L θ.p_gt_one θ.p_le_two hT
  apply fixedCallMinimax_lower
  intro A
  let B := quadraticPublicProblem (HardSpace d) θ
  obtain ⟨v, hv⟩ := ambientMasked_objective_probability_lower θ e hk hvariance π hπ hπ1 hkπ hbudget (A B)
  refine ⟨B, embeddedPrivateInstance e (maskedPrivateInstance θ hk hvariance π hπ hkπ v), ?_⟩
  have hδ : θ.δ < 1 / 4 := θ.δ_lt_tenth.trans (by norm_num)
  apply hδ.trans_le (hv.trans ?_)
  apply measureReal_mono (μ := PublicPolicy.outputLaw (A B)
    (embeddedPrivateInstance e (maskedPrivateInstance θ hk hvariance π hπ hkπ v))) _ (measure_ne_top _ _)
  intro x hx
  exact (ENNReal.ofReal_le_ofReal hrate).trans hx

/-- `eq:lb-heavy` at every positive budget, including the Gaussian-dominated
range T<ceil(L²/s²). The universal constant here is 1/16384. -/
theorem masked_fixedCallMinimax_lower {d : ℕ} (θ : OracleParameters)
    (hT : 0 < θ.T) (hdim : Nat.ceil (θ.L ^ 2 / θ.s ^ 2) ≤ d) :
    ENNReal.ofReal (heavyRate θ.μ θ.D θ.G θ.L θ.s θ.p θ.T) ≤ fixedCallMinimax (HardSpace d) θ := by
  by_cases hkT : Nat.ceil (θ.L ^ 2 / θ.s ^ 2) ≤ θ.T
  · exact masked_fixedCallMinimax_lower_large_budget θ hT hdim hkT
  · apply le_trans _ (GaussianLower.gaussian_fixedCallMinimax_lower_of_dimension θ hT hdim)
    apply ENNReal.ofReal_le_ofReal
    unfold heavyRate GaussianLower.traceRate
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply envelope_mono θ.μ_nonneg θ.D_pos.le
    · have hcoef : 0 ≤ heavyCoefficient θ.L θ.s θ.p θ.T := by
        unfold heavyCoefficient
        exact mul_nonneg θ.s_pos.le (Real.rpow_nonneg (by positivity) _)
      exact le_min θ.G_pos.le hcoef
    · exact min_le_min_left θ.G (heavyCoefficient_le_trace_small_budget θ.s_pos θ.s_le_L
        θ.p_gt_one θ.p_le_two hT (Nat.lt_of_not_ge hkT))

end
end HeavyTail.MaskedLower
