import SecondOrder.ToleranceLogBounds

namespace SecondOrder
noncomputable section

def endpointQueryCoefficient (P : Parameters) (ν E : ℝ) : ℝ :=
  25+24*(6144*trackingPolylogCoefficient P ν*endpointTrackingCoefficient P ν+
    E*(1+curvatureCountCoefficient P ν))

def epsilonQueryCoefficient (P : Parameters) (ν E : ℝ) : ℝ :=
  1000*(1+Real.log 10)^4*endpointQueryCoefficient P ν E

theorem endpointQueryCoefficient_pos (P : Parameters) {ν E : ℝ} (hν : 0 < ν) (hE : 0 ≤ E) :
    0 < endpointQueryCoefficient P ν E := by
  have hP := trackingPolylogCoefficient_pos P hν
  have hT := endpointTrackingCoefficient_pos P ν
  have hC := curvatureCountCoefficient_pos P ν
  unfold endpointQueryCoefficient
  positivity

theorem epsilonQueryCoefficient_pos (P : Parameters) {ν E : ℝ} (hν : 0 < ν) (hE : 0 ≤ E) :
    0 < epsilonQueryCoefficient P ν E := by
  have hC := endpointQueryCoefficient_pos P hν hE
  have hl : 0 < Real.log 10 := Real.log_pos (by norm_num)
  unfold epsilonQueryCoefficient
  positivity

/-- A quantitative endpoint rate, conditional on a separately verified
polylogarithmic κ/γ⁻² price. The coefficient is independent of tolerances. -/
theorem selectedQueryCap_polylog (P : Parameters) {ν τ γ E : ℝ}
    (hν : 0 < ν) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hE : 0 ≤ E)
    {κ : ℕ} (hκ : (κ : ℝ) ≤ E*(toleranceLog τ γ)^4/γ^2) :
    (selectedQueryCap P ν τ γ κ : ℝ) <
      endpointQueryCoefficient P ν E*(toleranceLog τ γ)^4*holderEndpointRate ν τ γ := by
  have hj := one_le_toleranceLog hτ hτ1 hγ hγ1
  have hj4 : (1 : ℝ) ≤ (toleranceLog τ γ)^4 := one_le_pow₀ hj
  have hp := tracking_log_product_tolerances P hν hτ hτ1 hγ hγ1
  have ht := mul_le_mul_of_nonneg_right hp (endpointTrackingCoefficient_pos P ν).le
  have he : 0 ≤ E*(toleranceLog τ γ)^4 := by positivity
  apply (selectedQueryCap_endpoint P hν hτ hτ1 hγ hγ1 he hκ).trans_le
  apply mul_le_mul_of_nonneg_right _ (holderEndpointRate_pos ν hτ hγ).le
  unfold endpointQueryCoefficient
  nlinarith

theorem toleranceLog_epsilon_eq {ε γ : ℝ} (hε : 0 < ε) :
    toleranceLog (ε/10) γ = toleranceLog ε γ+Real.log 10 := by
  have he : 1/(ε/10) = 10*(1/ε) := by field_simp
  unfold toleranceLog
  rw [he,Real.log_mul (by norm_num) (by positivity)]
  ring

theorem toleranceLog_epsilon_bounds {ε γ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    toleranceLog ε γ ≤ toleranceLog (ε/10) γ ∧
      toleranceLog (ε/10) γ ≤ (1+Real.log 10)*toleranceLog ε γ := by
  rw [toleranceLog_epsilon_eq hε]
  have hl : 0 ≤ Real.log 10 := Real.log_nonneg (by norm_num)
  have hj := one_le_toleranceLog hε hε1 hγ hγ1
  have hx := mul_nonneg hl (sub_nonneg.mpr hj)
  constructor <;> nlinarith

/-- Substituting τ=ε/10 only changes the fixed coefficient. Both the
endpoint powers and the fourth power of the tolerance logarithm now use ε. -/
theorem selectedQueryCap_epsilon_rate (P : Parameters) {ν ε γ E : ℝ}
    (hν : 0 < ν) (hε : 0 < ε) (hε1 : ε ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hE : 0 ≤ E)
    {κ : ℕ} (hκ : (κ : ℝ) ≤ E*(toleranceLog ε γ)^4/γ^2) :
    (selectedQueryCap P ν (ε/10) γ κ : ℝ) <
      epsilonQueryCoefficient P ν E*(toleranceLog ε γ)^4*holderEndpointRate ν ε γ := by
  have hτ : 0 < ε/10 := div_pos hε (by norm_num)
  have hτ1 : ε/10 ≤ 1 := by linarith
  have hj := one_le_toleranceLog hε hε1 hγ hγ1
  have hj0 : 0 ≤ toleranceLog ε γ := by linarith
  have hl := toleranceLog_epsilon_bounds hε hε1 hγ hγ1
  have hl4 := pow_le_pow_left₀ hj0 hl.1 4
  have hκ' : (κ : ℝ) ≤ E*(toleranceLog (ε/10) γ)^4/γ^2 :=
    hκ.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl4 hE) (sq_nonneg γ))
  have hJτ : 0 ≤ toleranceLog (ε/10) γ := hj0.trans hl.1
  have hJ4 := pow_le_pow_left₀ hJτ hl.2 4
  have hR := holderEndpointRate_epsilon (ν := ν) hε hγ
  have hC := endpointQueryCoefficient_pos P hν hE
  have hR0 := (holderEndpointRate_pos ν hτ hγ).le
  have hlog10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hprod := mul_le_mul hJ4 hR hR0
    (by positivity : 0 ≤ ((1+Real.log 10)*toleranceLog ε γ)^4)
  have hall := mul_le_mul_of_nonneg_left hprod hC.le
  apply (selectedQueryCap_polylog P hν hτ hτ1 hγ hγ1 hE hκ').trans_le
  calc
    _ = endpointQueryCoefficient P ν E*((toleranceLog (ε/10) γ)^4*holderEndpointRate ν (ε/10) γ) := by ring
    _ ≤ endpointQueryCoefficient P ν E*
        (((1+Real.log 10)*toleranceLog ε γ)^4*(1000*holderEndpointRate ν ε γ)) := hall
    _ = _ := by unfold epsilonQueryCoefficient; ring

/-- Specializing the same verified rate to ν=1 gives the ε⁻³+γ⁻⁵ endpoint. -/
theorem holderEndpointRate_lipschitz (ε : ℝ) {γ : ℝ} (hγ : 0 ≤ γ) :
    holderEndpointRate 1 ε γ = 1/ε^3+1/γ^5 := by
  norm_num [holderEndpointRate,holderRateExponent,Real.rpow_neg hγ,Real.rpow_natCast,one_div]
  norm_cast

end
end SecondOrder
