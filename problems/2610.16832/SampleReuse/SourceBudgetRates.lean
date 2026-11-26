import SampleReuse.CurvatureFirstCostCalibration

namespace SampleReuse
noncomputable section

def sourceHorizonRateConstant (P : Parameters) : ℝ :=
  3+48*P.gap*(32*P.gradientLip/3+12*P.hessianLip^2)

/-- An explicit logarithmic factor in dimension and the independent tolerances. -/
def sourceRateLog (P : Parameters) (d : ℕ) (ε γ : ℝ) : ℝ :=
  1+Real.log (sourceUpperConstant*sourceHorizonRateConstant P*(d+1)*(1/ε^3+1/γ^3))

def sourceGradientRateConstant (P : Parameters) : ℝ :=
  (48*sourceUpperConstant+1)*sourceGradientConstant P

def sourceHessianRateConstant (P : Parameters) : ℝ :=
  (48*sourceUpperConstant+1)*sourceHessianConstant P

def sourceTotalRateConstant (P : Parameters) : ℝ :=
  (48*sourceUpperConstant+1)*(2*sourceGradientConstant P+3*sourceHessianConstant P)

theorem sourceGradientRateConstant_pos (P : Parameters) : 0<sourceGradientRateConstant P := by
  have := sourceGradientConstant_pos P
  have := sourceUpperConstant_pos
  unfold sourceGradientRateConstant
  positivity

theorem sourceHessianRateConstant_pos (P : Parameters) : 0<sourceHessianRateConstant P := by
  have := sourceHessianConstant_pos P
  have := sourceUpperConstant_pos
  unfold sourceHessianRateConstant
  positivity

theorem sourceTotalRateConstant_pos (P : Parameters) : 0<sourceTotalRateConstant P := by
  have := sourceGradientConstant_pos P
  have := sourceHessianConstant_pos P
  have := sourceUpperConstant_pos
  unfold sourceTotalRateConstant
  positivity

theorem sourceGradientBudget_one_le (P : Parameters) {ε γ : ℝ} (hε : 0<ε) (hγ : 0<γ) :
    1≤sourceGradientBudget P ε γ := by
  have := P.gap_pos
  have := P.gradientLip_pos
  have := P.gradientNoise_pos
  unfold sourceGradientBudget
  have h : 0≤P.gap*P.gradientLip/ε^2+P.gradientNoise^2/ε^2+
      P.gradientNoise*P.gradientLip*P.gap/ε^3+P.gradientLip^2*P.gap/(ε^2*γ) := by positivity
  linarith

theorem sourceHessianBudget_one_le (P : Parameters) {ε γ : ℝ} (hε : 0<ε) (hγ : 0<γ) :
    1≤sourceHessianBudget P ε γ := by
  have := P.gap_pos
  have := P.gradientLip_pos
  have := P.hessianLip_pos
  have := P.hessianNoise_pos
  unfold sourceHessianBudget
  have h : 0≤P.gap*P.gradientLip/ε^2+P.hessianNoise^2/γ^2+
      P.hessianNoise*P.hessianLip*P.gap/(ε*γ^2)+2*P.hessianLip^2*P.gap/γ^3 := by positivity
  linarith

theorem sourceIterationCap_rate (P : Parameters) {ε γ : ℝ}
    (hε : 0<ε) (he : ε≤1) (hγ : 0<γ) :
    (sourceIterationCap P ε γ:ℝ)+1 ≤ sourceHorizonRateConstant P*(1/ε^3+1/γ^3) := by
  have hp := P.gap_pos
  have hgl := P.gradientLip_pos
  have hhl := P.hessianLip_pos
  have hc := (Nat.ceil_lt_add_one (show 0≤48*P.gap*
    (32*P.gradientLip/(3*ε^2)+12*P.hessianLip^2/γ^3) by positivity)).le
  have h1 := (one_le_inverse_square hε he).trans (inverse_square_le_cube hε he)
  have h2 := inverse_square_le_cube hε he
  have h3 : 0≤1/γ^3 := by positivity
  have heq : 32*P.gradientLip/(3*ε^2) = (32*P.gradientLip/3)*(1/ε^2) := by ring
  have hsplit : 12*P.hessianLip^2/γ^3 = (12*P.hessianLip^2)*(1/γ^3) := by ring
  have hg := mul_le_mul_of_nonneg_left h2 (by positivity : 0≤32*P.gradientLip/3)
  have hmix : (32*P.gradientLip/3)*(1/ε^3)+(12*P.hessianLip^2)*(1/γ^3) ≤
      (32*P.gradientLip/3+12*P.hessianLip^2)*(1/ε^3+1/γ^3) := by
    nlinarith [mul_nonneg (by positivity : 0≤32*P.gradientLip/3) h3,
      mul_nonneg (by positivity : 0≤12*P.hessianLip^2) (by positivity : 0≤1/ε^3)]
  have hsum : 32*P.gradientLip/(3*ε^2)+12*P.hessianLip^2/γ^3 ≤
      (32*P.gradientLip/3+12*P.hessianLip^2)*(1/ε^3+1/γ^3) := by
    rw [heq,hsplit]
    linarith
  have hh := mul_le_mul_of_nonneg_left hsum (by positivity : 0≤48*P.gap)
  unfold sourceIterationCap sourceHorizonRateConstant
  push_cast
  nlinarith

theorem sourceLogScale_rate (P : Parameters) (d : ℕ) {ε γ : ℝ}
    (hε : 0<ε) (he : ε≤1) (hγ : 0<γ) :
    sourceLogScale d (sourceIterationCap P ε γ) ≤ sourceRateLog P d ε γ := by
  have hc := sourceUpperConstant_pos
  have hT := sourceIterationCap_rate P hε he hγ
  have hh := mul_le_mul_of_nonneg_left hT (by positivity : 0≤sourceUpperConstant*(d+1:ℝ))
  have hl := Real.log_le_log (by positivity :
    0<sourceUpperConstant*(d+1:ℝ)*((sourceIterationCap P ε γ:ℝ)+1)) hh
  unfold sourceLogScale sourceRateLog
  convert add_le_add_left hl 1 using 1
  congr 1
  ring

theorem sourceRateLog_one_le (P : Parameters) (d : ℕ) {ε γ : ℝ}
    (hε : 0<ε) (he : ε≤1) (hγ : 0<γ) : 1≤sourceRateLog P d ε γ :=
  (sourceLogScale_one_le _ _).trans (sourceLogScale_rate P d hε he hγ)

private theorem rounded_scaled_budget {L B : ℝ} (hL : 1≤L) (hB : 1≤B) :
    (⌈48*sourceUpperConstant*L^4*B⌉₊:ℝ) ≤ (48*sourceUpperConstant+1)*L^4*B := by
  have hC := sourceUpperConstant_pos
  have hL0 : 0≤L := by linarith
  have hB0 : 0≤B := by linarith
  have hc := (Nat.ceil_lt_add_one (show 0≤48*sourceUpperConstant*L^4*B by positivity)).le
  have hp : 1≤L^4 := one_le_pow₀ hL
  have hmul := mul_le_mul hp hB (by norm_num : (0:ℝ)≤1) (by positivity : 0≤L^4)
  nlinarith

theorem source_gradient_cap_rate (P : Parameters) (d : ℕ) {ε γ : ℝ}
    (hε : 0<ε) (he : ε≤1) (hγ : 0<γ) :
    (⌈48*sourceUpperConstant*(sourceLogScale d (sourceIterationCap P ε γ))^4*
      sourceGradientBudget P ε γ⌉₊:ℝ) ≤
      sourceGradientRateConstant P*(sourceRateLog P d ε γ)^4*(1/ε^3+1/(ε^2*γ)) := by
  have hC := sourceUpperConstant_pos
  have hcg := sourceGradientConstant_pos P
  have hB := sourceGradientBudget_one_le P hε hγ
  have hceil := rounded_scaled_budget (sourceLogScale_one_le d (sourceIterationCap P ε γ)) hB
  have hlog := pow_le_pow_left₀ (by linarith [sourceLogScale_one_le d (sourceIterationCap P ε γ)] :
    0≤sourceLogScale d (sourceIterationCap P ε γ)) (sourceLogScale_rate P d hε he hγ) 4
  have hrate := sourceGradientBudget_rate P hε he hγ
  have hmul := mul_le_mul hlog hrate (by linarith : 0≤sourceGradientBudget P ε γ)
    (by positivity : 0≤(sourceRateLog P d ε γ)^4)
  have hh := mul_le_mul_of_nonneg_left hmul (by positivity : 0≤48*sourceUpperConstant+1)
  unfold sourceGradientRateConstant
  nlinarith

theorem source_hessian_cap_rate (P : Parameters) (d : ℕ) {ε γ : ℝ}
    (hε : 0<ε) (he : ε≤1) (hγ : 0<γ) (hg : γ≤1) :
    (⌈48*sourceUpperConstant*(sourceLogScale d (sourceIterationCap P ε γ))^4*
      sourceHessianBudget P ε γ⌉₊:ℝ) ≤
      sourceHessianRateConstant P*(sourceRateLog P d ε γ)^4*(1/ε^2+1/(ε*γ^2)+1/γ^3) := by
  have hC := sourceUpperConstant_pos
  have hch := sourceHessianConstant_pos P
  have hB := sourceHessianBudget_one_le P hε hγ
  have hceil := rounded_scaled_budget (sourceLogScale_one_le d (sourceIterationCap P ε γ)) hB
  have hlog := pow_le_pow_left₀ (by linarith [sourceLogScale_one_le d (sourceIterationCap P ε γ)] :
    0≤sourceLogScale d (sourceIterationCap P ε γ)) (sourceLogScale_rate P d hε he hγ) 4
  have hrate := sourceHessianBudget_rate P hε he hγ hg
  have hmul := mul_le_mul hlog hrate (by linarith : 0≤sourceHessianBudget P ε γ)
    (by positivity : 0≤(sourceRateLog P d ε γ)^4)
  have hh := mul_le_mul_of_nonneg_left hmul (by positivity : 0≤48*sourceUpperConstant+1)
  unfold sourceHessianRateConstant
  nlinarith

theorem source_total_cap_rate (P : Parameters) (d : ℕ) {ε γ : ℝ}
    (hε : 0<ε) (he : ε≤1) (hγ : 0<γ) (hg : γ≤1) :
    (⌈48*sourceUpperConstant*(sourceLogScale d (sourceIterationCap P ε γ))^4*
      sourceGradientBudget P ε γ⌉₊:ℝ)+
    (⌈48*sourceUpperConstant*(sourceLogScale d (sourceIterationCap P ε γ))^4*
      sourceHessianBudget P ε γ⌉₊:ℝ) ≤
      sourceTotalRateConstant P*(sourceRateLog P d ε γ)^4*(1/ε^3+1/γ^3) := by
  have hC := sourceUpperConstant_pos
  have hcg := sourceGradientConstant_pos P
  have hch := sourceHessianConstant_pos P
  have hBg := sourceGradientBudget_one_le P hε hγ
  have hBH := sourceHessianBudget_one_le P hε hγ
  have hG := rounded_scaled_budget (sourceLogScale_one_le d (sourceIterationCap P ε γ)) hBg
  have hH := rounded_scaled_budget (sourceLogScale_one_le d (sourceIterationCap P ε γ)) hBH
  have hlog := pow_le_pow_left₀ (by linarith [sourceLogScale_one_le d (sourceIterationCap P ε γ)] :
    0≤sourceLogScale d (sourceIterationCap P ε γ)) (sourceLogScale_rate P d hε he hγ) 4
  have hrate := sourceBudgets_total_rate P hε he hγ hg
  have hmul := mul_le_mul hlog hrate (by linarith : 0≤sourceGradientBudget P ε γ+sourceHessianBudget P ε γ)
    (by positivity : 0≤(sourceRateLog P d ε γ)^4)
  have hh := mul_le_mul_of_nonneg_left hmul (by positivity : 0≤48*sourceUpperConstant+1)
  unfold sourceTotalRateConstant
  nlinarith

end
end SampleReuse


