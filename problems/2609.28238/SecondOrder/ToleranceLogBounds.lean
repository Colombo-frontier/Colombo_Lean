import SecondOrder.EndpointBudget

namespace SecondOrder
noncomputable section

def toleranceLog (τ γ : ℝ) : ℝ := 1+Real.log (1/τ)+Real.log (1/γ)

def moveEndpointCoefficient (P : Parameters) (ν : ℝ) : ℝ :=
  P.gap*P.gradientLip+curvatureCountCoefficient P ν

def moveLogCoefficient (P : Parameters) (ν : ℝ) : ℝ :=
  Real.log (26+48*moveEndpointCoefficient P ν)+3+holderRateExponent ν

def depthToleranceCoefficient (P : Parameters) (ν : ℝ) : ℝ :=
  2+moveLogCoefficient P ν/Real.log 2

def confidenceToleranceCoefficient (P : Parameters) (ν : ℝ) : ℝ :=
  8*Real.log 384+8*moveLogCoefficient P ν+2

def trackingPolylogCoefficient (P : Parameters) (ν : ℝ) : ℝ :=
  (depthToleranceCoefficient P ν)^3*confidenceToleranceCoefficient P ν

theorem toleranceLog_terms {τ γ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    0 ≤ Real.log (1/τ) ∧ 0 ≤ Real.log (1/γ) := by
  constructor
  · exact Real.log_nonneg ((le_div_iff₀ hτ).mpr (by simpa using hτ1))
  · exact Real.log_nonneg ((le_div_iff₀ hγ).mpr (by simpa using hγ1))

theorem one_le_toleranceLog {τ γ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    1 ≤ toleranceLog τ γ := by
  have he := toleranceLog_terms hτ hτ1 hγ hγ1
  unfold toleranceLog
  linarith [he.1,he.2]

theorem moveEndpointCoefficient_pos (P : Parameters) (ν : ℝ) : 0 < moveEndpointCoefficient P ν := by
  have hΔ := P.gap_pos
  have hL := P.gradientLip_pos
  have hC := curvatureCountCoefficient_pos P ν
  unfold moveEndpointCoefficient
  positivity

theorem holderRateExponent_pos {ν : ℝ} (hν : 0 < ν) : 0 < holderRateExponent ν := by
  unfold holderRateExponent
  positivity

theorem moveLogCoefficient_pos (P : Parameters) {ν : ℝ} (hν : 0 < ν) : 0 < moveLogCoefficient P ν := by
  have hC := moveEndpointCoefficient_pos P ν
  have hl : 0 ≤ Real.log (26+48*moveEndpointCoefficient P ν) := Real.log_nonneg (by linarith)
  have hp := holderRateExponent_pos hν
  unfold moveLogCoefficient
  positivity

theorem depthToleranceCoefficient_pos (P : Parameters) {ν : ℝ} (hν : 0 < ν) :
    0 < depthToleranceCoefficient P ν := by
  have hC := moveLogCoefficient_pos P hν
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold depthToleranceCoefficient
  positivity

theorem confidenceToleranceCoefficient_pos (P : Parameters) {ν : ℝ} (hν : 0 < ν) :
    0 < confidenceToleranceCoefficient P ν := by
  have hC := moveLogCoefficient_pos P hν
  have hl : 0 ≤ Real.log 384 := Real.log_nonneg (by norm_num)
  unfold confidenceToleranceCoefficient
  positivity

theorem trackingPolylogCoefficient_pos (P : Parameters) {ν : ℝ} (hν : 0 < ν) :
    0 < trackingPolylogCoefficient P ν :=
  mul_pos (pow_pos (depthToleranceCoefficient_pos P hν) _) (confidenceToleranceCoefficient_pos P hν)

theorem moveLogArgument_bound (P : Parameters) {ν τ γ : ℝ}
    (hν : 0 < ν) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    26+24*idealMoveBudget P ν τ γ ≤
      (26+48*moveEndpointCoefficient P ν)*(1/τ^3)*γ^(-holderRateExponent ν) := by
  have hA : (1 : ℝ) ≤ 1/τ^3 := by
    apply (le_div_iff₀ (pow_pos hτ 3)).mpr
    simpa using pow_le_one₀ hτ.le hτ1
  have hB : (1 : ℝ) ≤ γ^(-holderRateExponent ν) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hγ hγ1 (neg_nonpos.mpr (holderRateExponent_pos hν).le)
  have hprod : (1 : ℝ) ≤ (1/τ^3)*γ^(-holderRateExponent ν) := by
    simpa using mul_le_mul hA hB (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ 1/τ^3)
  have hR : holderEndpointRate ν τ γ ≤ 2*(1/τ^3)*γ^(-holderRateExponent ν) := by
    have hab := mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)
    unfold holderEndpointRate
    nlinarith
  have hC := moveEndpointCoefficient_pos P ν
  have hm := idealMoveBudget_endpoint P (ν := ν) hτ hτ1 hγ hγ1
  change idealMoveBudget P ν τ γ ≤ moveEndpointCoefficient P ν*holderEndpointRate ν τ γ at hm
  have hm' := hm.trans (mul_le_mul_of_nonneg_left hR hC.le)
  nlinarith

/-- Converts the logarithm of the actual move budget into logarithms of
reciprocal tolerances, with a fixed-parameter coefficient. -/
theorem moveBudget_log_tolerances (P : Parameters) {ν τ γ : ℝ}
    (hν : 0 < ν) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    Real.log (26+24*idealMoveBudget P ν τ γ) ≤ moveLogCoefficient P ν*toleranceLog τ γ := by
  let K := 26+48*moveEndpointCoefficient P ν
  have hC := moveEndpointCoefficient_pos P ν
  have hK : 0 < K := by dsimp only [K]; positivity
  have hM := idealMoveBudget_nonneg P ν τ γ hγ
  have hp := holderRateExponent_pos hν
  have ha : (0 : ℝ) < 1/τ^3 := by positivity
  have hb := Real.rpow_pos_of_pos hγ (-holderRateExponent ν)
  have he : Real.log (K*(1/τ^3)*γ^(-holderRateExponent ν)) =
      Real.log K+3*Real.log (1/τ)+holderRateExponent ν*Real.log (1/γ) := by
    rw [Real.log_mul (mul_pos hK ha).ne' hb.ne',Real.log_mul hK.ne' ha.ne',
      Real.log_div one_ne_zero (pow_ne_zero 3 hτ.ne'),Real.log_one,Real.log_pow,Real.log_rpow hγ,
      Real.log_div one_ne_zero hτ.ne',Real.log_div one_ne_zero hγ.ne',Real.log_one]
    norm_num
  have hl := Real.log_le_log (show 0 < 26+24*idealMoveBudget P ν τ γ by positivity)
    (moveLogArgument_bound P hν hτ hτ1 hγ hγ1)
  change Real.log (26+24*idealMoveBudget P ν τ γ) ≤ Real.log (K*(1/τ^3)*γ^(-holderRateExponent ν)) at hl
  rw [he] at hl
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by dsimp only [K]; linarith)
  obtain ⟨ht,hg⟩ := toleranceLog_terms hτ hτ1 hγ hγ1
  have hcross₁ := mul_nonneg hlogK (add_nonneg ht hg)
  have hcross₂ := mul_nonneg hp.le (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) ht)
  change Real.log (26+24*idealMoveBudget P ν τ γ) ≤
    (Real.log K+3+holderRateExponent ν)*(1+Real.log (1/τ)+Real.log (1/γ))
  nlinarith

theorem depthLogEnvelope_tolerances (P : Parameters) {ν τ γ : ℝ}
    (hν : 0 < ν) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    depthLogEnvelope P ν τ γ ≤ depthToleranceCoefficient P ν*toleranceLog τ γ := by
  have hl := moveBudget_log_tolerances P hν hτ hτ1 hγ hγ1
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hj := one_le_toleranceLog hτ hτ1 hγ hγ1
  have hd := div_le_div_of_nonneg_right hl h2.le
  rw [show moveLogCoefficient P ν*toleranceLog τ γ/Real.log 2 =
    (moveLogCoefficient P ν/Real.log 2)*toleranceLog τ γ by ring] at hd
  unfold depthLogEnvelope depthToleranceCoefficient Real.logb
  nlinarith

theorem confidenceLogEnvelope_tolerances (P : Parameters) {ν τ γ : ℝ}
    (hν : 0 < ν) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    confidenceLogEnvelope P ν τ γ ≤ confidenceToleranceCoefficient P ν*toleranceLog τ γ := by
  have hl := moveBudget_log_tolerances P hν hτ hτ1 hγ hγ1
  have hj := one_le_toleranceLog hτ hτ1 hγ hγ1
  have hc : 0 ≤ 8*Real.log 384+2 := by have hh := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 384); linarith
  have hx := mul_nonneg hc (sub_nonneg.mpr hj)
  unfold confidenceLogEnvelope confidenceToleranceCoefficient
  nlinarith

theorem tracking_log_product_tolerances (P : Parameters) {ν τ γ : ℝ}
    (hν : 0 < ν) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    (depthLogEnvelope P ν τ γ)^3*confidenceLogEnvelope P ν τ γ ≤
      trackingPolylogCoefficient P ν*(toleranceLog τ γ)^4 := by
  have hd := depthLogEnvelope_tolerances P hν hτ hτ1 hγ hγ1
  have hc := confidenceLogEnvelope_tolerances P hν hτ hτ1 hγ hγ1
  have hj : 0 ≤ toleranceLog τ γ := (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_toleranceLog hτ hτ1 hγ hγ1)
  have hd0 := (depthLogEnvelope_pos P ν τ hγ).le
  have hc0 := confidenceLogEnvelope_nonneg P ν τ hγ
  have hconst := (depthToleranceCoefficient_pos P hν).le
  have hp := mul_le_mul (pow_le_pow_left₀ hd0 hd 3) hc hc0 (by positivity : 0 ≤ (depthToleranceCoefficient P ν*toleranceLog τ γ)^3)
  unfold trackingPolylogCoefficient
  exact hp.trans_eq (by ring)

end
end SecondOrder
