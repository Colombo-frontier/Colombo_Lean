import FreshGradientMinimax.GaussianOracleLaw
import FreshGradientMinimax.GaussianKL
import FreshGradientMinimax.KLEmbedding
import FreshGradientMinimax.TestingFamily

/-! The one-query KL bound applies to the full original oracle response at
every joint query, including dense or unbounded adaptive queries. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory InformationTheory
open scoped NNReal ENNReal

theorem gaussianDualKernel_klDiv {dx : ℕ} {L μ : ℝ} (F H : NCObjective dx 1 L μ)
    {v : ℝ≥0} (hv : v ≠ 0) (z : Joint dx 1) (hx : F.gradX z.1 z.2 = H.gradX z.1 z.2) :
    klDiv (gaussianDualKernel F v z) (gaussianDualKernel H v z) =
      ENNReal.ofReal (‖F.gradY z.1 z.2 - H.gradY z.1 z.2‖ ^ 2 / (2 * (v : ℝ))) := by
  rw [gaussianDualKernel_scalar_law, gaussianDualKernel_scalar_law, ← hx,
    klDiv_map_embedding (scalarResponseEmbed_measurableEmbedding _)
      (gaussianReal_mutual_ac _ _ hv) (gaussianReal_llr_integrable _ _ hv), gaussianReal_klDiv _ _ hv]
  rw [← realCoord_norm, realCoord_sub, sq_abs]

theorem testingOracle_one_query_kl (p : Parameters) (hκ : 1120 * p.μ ≤ p.L) (hσ : 0 < p.σ)
    (z : Joint 1 1) :
    klDiv ((FreshOracle.gaussianDual (testingHardObjective p hκ 1 (by norm_num)) p.σ).kernel z)
      ((FreshOracle.gaussianDual (testingHardObjective p hκ (-1) (by norm_num)) p.σ).kernel z) ≤
        ENNReal.ofReal (903168 * p.ε ^ 2 / (p.κ ^ 2 * p.σ ^ 2)) := by
  have hL : 0 < p.L := p.μ_pos.trans_le p.μ_le_L
  have hv : (⟨p.σ ^ 2, sq_nonneg p.σ⟩ : ℝ≥0) ≠ 0 := by
    intro he
    have h := congrArg (fun t : ℝ≥0 => (t : ℝ)) he
    change p.σ ^ 2 = 0 at h
    nlinarith only [h, sq_pos_of_pos hσ]
  change klDiv (gaussianDualKernel _ _ z) (gaussianDualKernel _ _ z) ≤ _
  rw [gaussianDualKernel_klDiv _ _ hv z (testingHardObjective_gradX_equal p hκ z.1 z.2)]
  apply ENNReal.ofReal_le_ofReal
  have h := div_le_div_of_nonneg_right (testingHardObjective_mean_separation p hκ z.1 z.2)
    (show 0 ≤ 2 * p.σ ^ 2 by positivity)
  calc
    _ ≤ (1806336 * p.μ ^ 2 * p.ε ^ 2 / p.L ^ 2) / (2 * p.σ ^ 2) := h
    _ = 903168 * p.ε ^ 2 / (p.κ ^ 2 * p.σ ^ 2) := by
      unfold Parameters.κ
      field_simp [ne_of_gt p.μ_pos, ne_of_gt hL, ne_of_gt hσ]
      ring

end FreshGradientMinimax
