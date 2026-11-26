import HeavyTail.SampleComplexityLower
import HeavyTail.MainUpper

/-! The source sample-complexity upper and lower bounds for the full oracle
model, with natural-number budget rounding and explicit zero-query exclusion. -/

noncomputable section
open scoped ENNReal
namespace HeavyTail

def sampleUpperConstant (p : ℝ) : ℝ :=
  localizationBudgetConstant (1 - 1 / p) (unifiedUpperConstant p) + 1

theorem sampleUpperConstant_pos (p : ℝ) : 0 < sampleUpperConstant p := by
  have h := (localizationBudgetConstant_bounds (q := 1 - 1 / p) (unifiedUpperConstant_pos p).le).1
  unfold sampleUpperConstant
  linarith

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- A concrete finite budget attains the desired minimax error. This upper
bound is valid for every ε>0, without the nonsaturation restriction. -/
theorem sample_complexity_upper (θ : OracleParameters) {ε : ℝ} (hε : 0 < ε) :
    sampleComplexity E θ ε ≤ ENNReal.ofReal
      (sampleUpperConstant θ.p * sampleUpperCost θ.G θ.L θ.s θ.p θ.δ
        (envelopeInverse θ.μ θ.D ε)) := by
  let a := envelopeInverse θ.μ θ.D ε
  let C := unifiedUpperConstant θ.p
  let B := localizationBudgetConstant (1 - 1 / θ.p) C
  let W := sampleUpperCost θ.G θ.L θ.s θ.p θ.δ a
  let T : ℕ := ⌈B * W⌉₊
  have ha : 0 < a := envelopeInverse_pos θ.μ_nonneg θ.D_pos hε
  have hC : 0 < C := unifiedUpperConstant_pos θ.p
  have hB : 2 ≤ B := (localizationBudgetConstant_bounds (q := 1 - 1 / θ.p) hC.le).1
  have hB0 : 0 ≤ B := (by norm_num : (0 : ℝ) ≤ 2).trans hB
  have hW : 1 ≤ W := sampleUpperCost_ge_one θ ha
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hBW : 2 ≤ B * W := by
    have hh := mul_le_mul hB hW (by norm_num : (0 : ℝ) ≤ 1) hB0
    simpa only [mul_one] using hh
  have hbudget : B * W ≤ (T : ℝ) := Nat.le_ceil _
  have hT : 0 < T := Nat.cast_pos.mp ((by norm_num : (0 : ℝ) < 2).trans_le (hBW.trans hbudget))
  have hamp := sample_budget_controls_amplitude θ ha hC.le hT hbudget
  have hG := θ.G_pos
  have hs := θ.s_pos
  have hL : 0 < θ.L := θ.s_pos.trans_le θ.s_le_L
  have hell : 0 < Real.log (3 / θ.δ) := confidenceLog_pos θ.δ_pos θ.δ_lt_tenth
  have hell' : 0 < confidenceLog θ.δ := hell
  have hv : 0 ≤ optimizationAmplitude θ.G θ.L θ.s θ.p θ.δ T := by
    unfold optimizationAmplitude statisticalAmplitude
    positivity
  have henv := sample_scaled_envelope θ.μ_nonneg θ.D_pos.le θ.G_pos.le ha.le hv hC.le hamp
  have hinverse : envelope θ.μ θ.D a = ε := envelope_right_inverse θ.μ_nonneg θ.D_pos hε.le
  rw [hinverse] at henv
  have hsuccess : atMostCallMinimax E (θ.atBudget T) ≤ ENNReal.ofReal ε :=
    (unified_atMostCallMinimax_upper (E := E) (θ.atBudget T) hT).trans
      (ENNReal.ofReal_le_ofReal henv)
  apply (sampleComplexity_le_budget E θ ε T hsuccess).trans
  have hceil : (T : ℝ) < B * W + 1 := Nat.ceil_lt_add_one (mul_nonneg hB0 hW0)
  have hTbound : (T : ℝ) ≤ (B + 1) * W := by nlinarith only [hceil, hW]
  simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hTbound

/-- The appendix's two-sided sample-complexity statement, with the same
positive p-only lower constant in the nonsaturation condition and lower rate. -/
theorem sample_complexity_bounds {d : ℕ} (θ : OracleParameters)
    {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ sampleLowerConstant θ.p * envelope θ.μ θ.D θ.G)
    (hdim : Nat.ceil (θ.L ^ 2 / θ.s ^ 2) ≤ d) :
    ENNReal.ofReal (sampleLowerConstant θ.p * sampleLowerCost θ.L θ.s θ.p θ.δ
      (envelopeInverse θ.μ θ.D ε)) ≤ sampleComplexity (HardSpace d) θ ε ∧
    sampleComplexity (HardSpace d) θ ε ≤ ENNReal.ofReal
      (sampleUpperConstant θ.p * sampleUpperCost θ.G θ.L θ.s θ.p θ.δ
        (envelopeInverse θ.μ θ.D ε)) :=
  ⟨sample_complexity_lower θ hε hsmall hdim, sample_complexity_upper (HardSpace d) θ hε⟩

theorem sample_complexity_constants :
    (∀ p : ℝ, 0 < sampleLowerConstant p ∧ 0 < sampleUpperConstant p) :=
  fun p => ⟨sampleLowerConstant_pos p, sampleUpperConstant_pos p⟩

end HeavyTail
