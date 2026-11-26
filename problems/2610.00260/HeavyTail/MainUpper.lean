import HeavyTail.LocalizationUpper
import HeavyTail.ZeroQueryModel
import HeavyTail.AtMostModel

/-! Full all-budget statistical upper bounds. Every branch is an actual public
algorithm; all branch comparisons use public scalar parameters only. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace HeavyTail
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def fixedThresholdUpperConstant (p : ℝ) : ℝ :=
  max 128 (2 * max 2 (max (8 * acceptedStageConstant p) (localizationUpperConstant p)))

def unifiedUpperConstant (p : ℝ) : ℝ := fixedThresholdUpperConstant p * (1024 : ℝ) ^ 2

theorem ofReal_min_eq (a b : ℝ) : ENNReal.ofReal (min a b) = min (ENNReal.ofReal a) (ENNReal.ofReal b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (ENNReal.ofReal_le_ofReal h)]
  · rw [min_eq_right h, min_eq_right (ENNReal.ofReal_le_ofReal h)]

theorem fixedThresholdUpperConstant_pos (p : ℝ) : 0 < fixedThresholdUpperConstant p :=
  (by norm_num : (0 : ℝ) < 128).trans_le (le_max_left _ _)

theorem unifiedUpperConstant_pos (p : ℝ) : 0 < unifiedUpperConstant p := by
  unfold unifiedUpperConstant
  exact mul_pos (fixedThresholdUpperConstant_pos p) (by norm_num)

theorem fixedThreshold_fixedCallMinimax_upper (θ : OracleParameters) (hT : 0 < θ.T)
    {τ : ℝ} (hτ : 64 * (4 * θ.G + θ.L) ≤ τ) :
    fixedCallMinimax E θ ≤ ENNReal.ofReal (fixedThresholdUpperConstant θ.p *
      envelope θ.μ θ.D (min θ.G (fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ τ θ.T))) := by
  let v := fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ τ θ.T
  have hL : 0 < θ.L := θ.s_pos.trans_le θ.s_le_L
  have hG := θ.G_pos
  have hτpos : 0 < τ := (by positivity : 0 < 64 * (4 * θ.G + θ.L)).trans_le hτ
  have hv : 0 < v := (fixedThresholdAmplitude_components θ hτpos hT).1
  have henv : 0 ≤ envelope θ.μ θ.D (min θ.G v) :=
    envelope_nonneg θ.μ_nonneg θ.D_pos.le (le_min θ.G_pos.le hv.le)
  have hcap := zero_query_fixedCallMinimax_cap (E := E) θ
  by_cases hbudget : 8 * confidenceLog θ.δ ≤ θ.T
  · have hlin := single_stage_fixedCallMinimax_upper (E := E) hτ hbudget
    have hb : fixedCallMinimax E θ ≤ ENNReal.ofReal
        (parameterBranchMinimum θ.μ θ.D θ.G v 2 (8 * acceptedStageConstant θ.p)
          (localizationUpperConstant θ.p)) := by
      unfold parameterBranchMinimum
      rw [ofReal_min_eq]
      apply le_min hcap
      by_cases hμzero : θ.μ = 0
      · rw [if_pos hμzero]
        simpa only [v, mul_assoc] using hlin
      · rw [if_neg hμzero, ofReal_min_eq]
        apply le_min
        · simpa only [v, mul_assoc] using hlin
        · exact localized_fixedCallMinimax_upper (lt_of_le_of_ne θ.μ_nonneg (Ne.symm hμzero)) hτ hbudget
    apply hb.trans
    apply ENNReal.ofReal_le_ofReal
    exact (parameterBranchMinimum_le_envelope θ.μ_nonneg θ.D_pos.le θ.G_pos.le hv.le
      (by norm_num) (mul_nonneg (by norm_num) (acceptedStageConstant_pos θ.p).le)
      (localizationUpperConstant_pos θ.p).le).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) henv)
  · apply hcap.trans
    apply ENNReal.ofReal_le_ofReal
    have hs := small_budget_envelope_cap θ hτpos hT (lt_of_not_ge hbudget)
    have hc : 128 ≤ fixedThresholdUpperConstant θ.p := le_max_left _ _
    nlinarith only [hs, mul_le_mul_of_nonneg_right hc henv]

theorem fixedThreshold_atMostCallMinimax_upper (θ : OracleParameters) (hT : 0 < θ.T)
    {τ : ℝ} (hτ : 64 * (4 * θ.G + θ.L) ≤ τ) :
    atMostCallMinimax E θ ≤ ENNReal.ofReal (fixedThresholdUpperConstant θ.p *
      envelope θ.μ θ.D (min θ.G (fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ τ θ.T))) := by
  rw [atMostCallMinimax_eq_fixedCallMinimax]
  exact fixedThreshold_fixedCallMinimax_upper θ hT hτ

theorem unified_fixedCallMinimax_upper (θ : OracleParameters) (hT : 0 < θ.T) :
    fixedCallMinimax E θ ≤ ENNReal.ofReal (unifiedUpperConstant θ.p *
      envelope θ.μ θ.D (min θ.G (optimizationAmplitude θ.G θ.L θ.s θ.p θ.δ θ.T))) := by
  have hL : 0 < θ.L := θ.s_pos.trans_le θ.s_le_L
  apply (fixedThreshold_fixedCallMinimax_upper (E := E) θ hT
    (commonThreshold_admissible θ.G_pos.le hL.le θ.T)).trans
  apply ENNReal.ofReal_le_ofReal
  have hh := mul_le_mul_of_nonneg_left (commonThreshold_envelope_bound θ hT)
    (fixedThresholdUpperConstant_pos θ.p).le
  convert hh using 1 <;> unfold unifiedUpperConstant <;> ring

theorem unified_atMostCallMinimax_upper (θ : OracleParameters) (hT : 0 < θ.T) :
    atMostCallMinimax E θ ≤ ENNReal.ofReal (unifiedUpperConstant θ.p *
      envelope θ.μ θ.D (min θ.G (optimizationAmplitude θ.G θ.L θ.s θ.p θ.δ θ.T))) := by
  rw [atMostCallMinimax_eq_fixedCallMinimax]
  exact unified_fixedCallMinimax_upper θ hT

end HeavyTail
