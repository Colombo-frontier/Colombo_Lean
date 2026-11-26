import HeavyTail.SampleComplexityCosts
import HeavyTail.ZeroQueryModel

/-! Sample complexity is the actual infimum over all nonnegative integer
raw-call budgets. The nonsaturated lower bound explicitly excludes zero calls. -/

noncomputable section
open scoped ENNReal
namespace HeavyTail

def OracleParameters.atBudget (θ : OracleParameters) (T : ℕ) : OracleParameters :=
  { θ with T := T }

def sampleLowerConstant (p : ℝ) : ℝ :=
  min (1 / 294912) ((1 / 147456 : ℝ) ^ (1 / (1 - 1 / p)))

theorem sampleLowerConstant_pos (p : ℝ) : 0 < sampleLowerConstant p := by
  unfold sampleLowerConstant
  exact lt_min (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def sampleComplexity (θ : OracleParameters) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ T : ℕ, ⨅ (_ : atMostCallMinimax E (θ.atBudget T) ≤ ENNReal.ofReal ε), (T : ℝ≥0∞)

theorem sampleComplexity_le_budget (θ : OracleParameters) (ε : ℝ) (T : ℕ)
    (h : atMostCallMinimax E (θ.atBudget T) ≤ ENNReal.ofReal ε) :
    sampleComplexity E θ ε ≤ T := iInf_le_of_le T (iInf_le_of_le h le_rfl)

variable {E}

theorem sample_complexity_zero_query_excluded {d : ℕ} (θ : OracleParameters)
    {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ sampleLowerConstant θ.p * envelope θ.μ θ.D θ.G)
    (hdim : Nat.ceil (θ.L ^ 2 / θ.s ^ 2) ≤ d) :
    ¬ atMostCallMinimax (HardSpace d) (θ.atBudget 0) ≤ ENNReal.ofReal ε := by
  have hd : 0 < d := lt_of_lt_of_le (MaskedLower.activeDimension_bounds θ.s_pos θ.s_le_L).1 hdim
  let e : HardSpace d := EuclideanSpace.single ⟨0, hd⟩ (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  have hlower := confidence_zero_query_fixedCallMinimax_lower (θ.atBudget 0) e he rfl
  rw [← atMostCallMinimax_eq_fixedCallMinimax] at hlower
  intro hsuccess
  have hreal : envelope θ.μ θ.D θ.G ≤ ε :=
    (ENNReal.ofReal_le_ofReal_iff hε.le).mp (hlower.trans hsuccess)
  have henv := envelope_pos θ.μ_nonneg θ.D_pos θ.G_pos
  have hc : sampleLowerConstant θ.p ≤ 1 / 294912 := min_le_left _ _
  have hh := mul_le_mul_of_nonneg_right hc henv.le
  nlinarith only [hreal, hsmall, hh, henv]

theorem successful_budget_lower_cost {d : ℕ} (θ : OracleParameters)
    {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ sampleLowerConstant θ.p * envelope θ.μ θ.D θ.G)
    (hdim : Nat.ceil (θ.L ^ 2 / θ.s ^ 2) ≤ d) (T : ℕ)
    (hsuccess : atMostCallMinimax (HardSpace d) (θ.atBudget T) ≤ ENNReal.ofReal ε) :
    sampleLowerConstant θ.p * sampleLowerCost θ.L θ.s θ.p θ.δ
      (envelopeInverse θ.μ θ.D ε) ≤ T := by
  have hT : 0 < T := by
    by_contra h
    have hz : T = 0 := by omega
    subst T
    exact sample_complexity_zero_query_excluded θ hε hsmall hdim hsuccess
  have hlower := unified_atMostCallMinimax_lower (θ.atBudget T) hT hdim
  have hrisk : (1 / 147456 : ℝ) * envelope θ.μ θ.D
      (min θ.G (statisticalAmplitude θ.L θ.s θ.p θ.δ T)) ≤ ε :=
    (ENNReal.ofReal_le_ofReal_iff hε.le).mp (hlower.trans hsuccess)
  have henv := envelope_pos θ.μ_nonneg θ.D_pos θ.G_pos
  have hsmall' : ε ≤ ((1 / 147456 : ℝ) / 2) * envelope θ.μ θ.D θ.G := by
    have hc : sampleLowerConstant θ.p ≤ 1 / 294912 := min_le_left _ _
    have hh := hsmall.trans (mul_le_mul_of_nonneg_right hc henv.le)
    convert hh using 1 <;> norm_num
  have hL : 0 < θ.L := θ.s_pos.trans_le θ.s_le_L
  have hs := θ.s_pos
  have hell : 0 < Real.log (3 / θ.δ) := confidenceLog_pos θ.δ_pos θ.δ_lt_tenth
  have hw : 0 ≤ statisticalAmplitude θ.L θ.s θ.p θ.δ T := by
    unfold statisticalAmplitude
    positivity
  have hamp := nonsaturated_amplitude_inverse θ.μ_nonneg θ.D_pos θ.G_pos hw hε
    (by norm_num : (0 : ℝ) < 1 / 147456) (by norm_num : (1 / 147456 : ℝ) ≤ 1) hsmall' hrisk
  have ha := envelopeInverse_pos θ.μ_nonneg θ.D_pos hε
  have hcost := sample_lower_cost_of_amplitude θ ha
    (by norm_num : (0 : ℝ) < 1 / 147456) (by norm_num : (1 / 147456 : ℝ) ≤ 1) hT hamp
  have hcost0 : 0 ≤ sampleLowerCost θ.L θ.s θ.p θ.δ (envelopeInverse θ.μ θ.D ε) := by
    unfold sampleLowerCost
    apply le_trans _ (le_max_left _ _)
    positivity
  exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hcost0).trans hcost

theorem sample_complexity_lower {d : ℕ} (θ : OracleParameters)
    {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ sampleLowerConstant θ.p * envelope θ.μ θ.D θ.G)
    (hdim : Nat.ceil (θ.L ^ 2 / θ.s ^ 2) ≤ d) :
    ENNReal.ofReal (sampleLowerConstant θ.p * sampleLowerCost θ.L θ.s θ.p θ.δ
      (envelopeInverse θ.μ θ.D ε)) ≤ sampleComplexity (HardSpace d) θ ε := by
  apply le_iInf
  intro T
  apply le_iInf
  intro hsuccess
  have h := successful_budget_lower_cost θ hε hsmall hdim T hsuccess
  simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal h

theorem one_le_sampleComplexity {d : ℕ} (θ : OracleParameters)
    {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ sampleLowerConstant θ.p * envelope θ.μ θ.D θ.G)
    (hdim : Nat.ceil (θ.L ^ 2 / θ.s ^ 2) ≤ d) :
    1 ≤ sampleComplexity (HardSpace d) θ ε := by
  apply le_iInf
  intro T
  apply le_iInf
  intro hsuccess
  have hT : 1 ≤ T := by
    by_contra h
    have hz : T = 0 := by omega
    subst T
    exact sample_complexity_zero_query_excluded θ hε hsmall hdim hsuccess
  exact_mod_cast hT

end HeavyTail
