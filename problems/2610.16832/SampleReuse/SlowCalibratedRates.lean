import SampleReuse.SlowCalibratedLoss

open SecondOrder

namespace SampleReuse
noncomputable section

def slowQueryConstant : ℝ := firstOrderGradientConstant*slowBiasConstant^2/20971520
def slowQueryThreshold (P : Parameters) (ε : ℝ) : ℝ :=
  slowQueryConstant*P.gap*(slowModelScale P)^2/(ε^3*slowAlpha (slowBlockSize P ε))

theorem slowQueryConstant_pos : 0 < slowQueryConstant := by
  have hg := firstOrderGradientConstant_pos
  have hb := slowBiasConstant_pos
  unfold slowQueryConstant
  positivity

theorem slowBiasConstant_le_one : slowBiasConstant ≤ 1 := by
  have hC : 1 ≤ slowRegularityConstant := by
    unfold slowRegularityConstant
    linarith [firstOrderGeometryConstant_pos,firstOrderNoiseConstant_pos,sampleNoiseThirdConstant_pos]
  unfold slowBiasConstant
  apply (div_le_iff₀ (mul_pos (by norm_num) slowRegularityConstant_bounds.1)).mpr
  linarith [firstOrderGradientConstant_le_one]

theorem slowQueryConstant_le_one : slowQueryConstant ≤ 1 := by
  have hb := pow_le_pow_left₀ slowBiasConstant_pos.le slowBiasConstant_le_one 2
  have hh := mul_le_mul firstOrderGradientConstant_le_one hb
    (sq_nonneg _) zero_le_one
  norm_num only [one_pow,one_mul] at hh
  unfold slowQueryConstant
  linarith

theorem slowAmplitude_ge_tolerance {d : ℕ} (hd : 0 < d) {ε : ℝ} (hε : 0 < ε) :
    ε ≤ slowAmplitude d ε := by
  have hA := slowAmplitude_pos hd hε
  have hβ : 0 ≤ slowDilation d := inv_nonneg.mpr (slowAlpha_pos hd).le
  have h₁ := mul_le_mul_of_nonneg_left (slowDilation_le_one hd) hA.le
  have h₂ := mul_le_mul_of_nonneg_left firstOrderGradientConstant_le_one (mul_nonneg hA.le hβ)
  rw [slowAmplitude_scale hd] at h₂
  nlinarith only [h₁,h₂,hε]

theorem slowQueryThreshold_pos (P : Parameters) {ε : ℝ} (hε : 0 < ε) :
    0 < slowQueryThreshold P ε := by
  have hc := slowQueryConstant_pos
  have hΔ := P.gap_pos
  have hs := slowModelScale_pos P
  have hd := slowAlpha_pos (slowBlockSize_pos P hε)
  unfold slowQueryThreshold
  positivity

theorem slowQueryThreshold_le_envelope (P : Parameters) {ε : ℝ} (hε : 0 < ε) :
    slowQueryThreshold P ε ≤ P.gap*(slowModelScale P)^2/ε^3 := by
  have hd := slowAlpha_ge_one (slowBlockSize_pos P hε)
  have hpow := pow_pos hε 3
  have hnum : 0 ≤ P.gap*(slowModelScale P)^2 := by have := P.gap_pos; positivity
  have hm := mul_le_mul_of_nonneg_right slowQueryConstant_le_one hnum
  unfold slowQueryThreshold
  calc
    _ ≤ (P.gap*(slowModelScale P)^2)/(ε^3*slowAlpha (slowBlockSize P ε)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith only [hm]
    _ ≤ _ := div_le_div_of_nonneg_left hnum hpow (by nlinarith only [hd,hpow])

theorem slow_query_integer_budget (P : Parameters) {ε : ℝ} (hc : SlowCalibratedConditions P ε) :
    slowQueryThreshold P ε ≤
      ((slowLinks P ε:ℝ)*(firstOrderResponseCap (slowCoefficientRadius P ε):ℝ))/2 := by
  have hd := slowBlockSize_pos P hc.tolerance_pos
  have hA := slowAmplitude_pos hd hc.tolerance_pos
  have hr := hc.radius_large
  have hcap : 32768 ≤ (slowCoefficientRadius P ε)^2 := by nlinarith
  have hb := firstOrderIntegerBudget_lower hA hc.amplitude_small hcap
  change P.gap*(slowCoefficientRadius P ε)^2/(5242880*slowAmplitude (slowBlockSize P ε) ε) ≤
    ((slowLinks P ε:ℝ)*(firstOrderResponseCap (slowCoefficientRadius P ε):ℝ))/2 at hb
  convert hb using 1
  unfold slowQueryThreshold slowQueryConstant slowCoefficientRadius slowAmplitude
  field_simp [hc.tolerance_pos.ne',(slowAlpha_pos hd).ne',firstOrderGradientConstant_pos.ne']
  ring_nf
  field_simp [hc.tolerance_pos.ne',(slowAlpha_pos hd).ne']
  ring

theorem slow_query_nat_budget (P : Parameters) {ε : ℝ} (hc : SlowCalibratedConditions P ε)
    (N : ℕ) (hN : (N:ℝ) ≤ slowQueryThreshold P ε) :
    2*N ≤ slowLinks P ε*firstOrderResponseCap (slowCoefficientRadius P ε) := by
  have hh := slow_query_integer_budget P hc
  have hn : (2:ℝ)*N ≤ (slowLinks P ε:ℝ)*(firstOrderResponseCap (slowCoefficientRadius P ε):ℝ) := by
    linarith
  exact_mod_cast hn

theorem slow_chain_envelope (P : Parameters) {ε : ℝ} (hc : SlowCalibratedConditions P ε) :
    (slowLinks P ε+1:ℕ) ≤ P.gap/ε := by
  apply (le_div_iff₀ hc.tolerance_pos).mpr
  have ha := mul_le_mul_of_nonneg_right
    (slowAmplitude_ge_tolerance (slowBlockSize_pos P hc.tolerance_pos) hc.tolerance_pos)
    (Nat.cast_nonneg (α := ℝ) (slowLinks P ε+1))
  nlinarith only [ha,hc.chain_budget,P.gap_pos]

/-- The precise manuscript logarithmic block size dominates every horizon
condition of the persistent information argument over the claimed query range. -/
theorem slow_calibrated_horizon (P : Parameters) {ε : ℝ} (hc : SlowCalibratedConditions P ε)
    (N : ℕ) (hN : (N:ℝ) ≤ slowQueryThreshold P ε) :
    256*Real.log (2*(N+1:ℕ)) ≤ (slowBlockSize P ε:ℝ) ∧
    16384*Real.log 2 ≤ (slowBlockSize P ε:ℝ) ∧
    128*Real.log (32*(N+1:ℕ)*(slowLinks P ε+1:ℕ)) ≤ (slowBlockSize P ε:ℝ) := by
  have hε := hc.tolerance_pos
  have hn := hN.trans (slowQueryThreshold_le_envelope P hε)
  have ht := slow_chain_envelope P hc
  have hd := (firstOrderEndpointBlockSize_bounds (s := slowModelScale P) P.gap_pos.le hε).2.1
  apply firstOrderHorizon_of_envelope (firstOrderEndpointEnvelope_ge_two P.gap_pos.le hε)
    hd N (slowLinks P ε)
  · unfold firstOrderEndpointEnvelope
    rw [Nat.cast_add,Nat.cast_one]
    have hq : 0 ≤ P.gap/ε := div_nonneg P.gap_pos.le hε.le
    linarith
  · unfold firstOrderEndpointEnvelope
    have hw : 0 ≤ P.gap*(slowModelScale P)^2/ε^3 := by have := P.gap_pos; positivity
    linarith

end
end SampleReuse
