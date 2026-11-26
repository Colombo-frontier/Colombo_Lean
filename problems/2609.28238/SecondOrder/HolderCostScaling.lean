import SecondOrder.TrackingLogFactors

namespace SecondOrder
noncomputable section

def holderRateExponent (ν : ℝ) : ℝ := 3+2/ν

def holderEndpointRate (ν τ γ : ℝ) : ℝ := 1/τ^3+γ^(-holderRateExponent ν)

def curvatureCountCoefficient (P : Parameters) (ν : ℝ) : ℝ :=
  (16*P.gap/3)*(8*P.hessianHolder)^(2/ν)

theorem curvatureCountCoefficient_pos (P : Parameters) (ν : ℝ) : 0 < curvatureCountCoefficient P ν := by
  have hΔ := P.gap_pos
  have hH := P.hessianHolder_pos
  unfold curvatureCountCoefficient
  positivity

theorem curvatureRadius_sq {H γ ν : ℝ} (hH : 0 < H) (hγ : 0 < γ) :
    (curvatureRadius H ν γ)^2 = γ^(2/ν)/(8*H)^(2/ν) := by
  have hb : 0 ≤ γ/(8*H) := by positivity
  rw [curvatureRadius,← Real.rpow_mul_natCast hb (1/ν) 2]
  norm_num only [Nat.cast_ofNat]
  rw [show (1/ν)*2 = 2/ν by ring,Real.div_rpow hγ.le (by positivity)]

/-- The actual chosen step size gives the exact Hölder move exponent,
with a coefficient depending only on the fixed problem parameters. -/
theorem curvatureCountScale_eq (P : Parameters) (ν : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    16*P.gap/(3*γ*(curvatureRadius P.hessianHolder ν γ)^2) =
      curvatureCountCoefficient P ν*γ^(-(1+2/ν)) := by
  have hH := P.hessianHolder_pos
  have hgpow := Real.rpow_pos_of_pos hγ (2/ν)
  have hHpow := Real.rpow_pos_of_pos (show 0 < 8*P.hessianHolder by positivity) (2/ν)
  rw [curvatureRadius_sq hH hγ,Real.rpow_neg hγ.le,Real.rpow_add hγ,Real.rpow_one]
  unfold curvatureCountCoefficient
  field_simp [hγ.ne',hgpow.ne',hHpow.ne']
  <;> ring <;> simp

theorem idealMoveBudget_scale (P : Parameters) (ν τ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    idealMoveBudget P ν τ γ = P.gap*P.gradientLip/τ^2+
      curvatureCountCoefficient P ν*γ^(-(1+2/ν)) := by
  rw [idealMoveBudget,div_div_eq_mul_div,div_div_eq_mul_div]
  rw [show P.gap*16 = 16*P.gap by ring,curvatureCountScale_eq P ν hγ]

theorem holderEndpointRate_pos (ν : ℝ) {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) :
    0 < holderEndpointRate ν τ γ := by
  unfold holderEndpointRate
  positivity

theorem one_le_holderEndpointRate (ν : ℝ) {τ γ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hγ : 0 < γ) :
    1 ≤ holderEndpointRate ν τ γ := by
  have he : (1 : ℝ) ≤ 1/τ^3 := by
    apply (le_div_iff₀ (pow_pos hτ 3)).mpr
    simpa using pow_le_one₀ hτ.le hτ1
  exact he.trans (le_add_of_nonneg_right (Real.rpow_nonneg hγ.le _))

theorem inv_sq_le_holderEndpointRate (ν : ℝ) {τ γ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hγ : 0 < γ) :
    1/τ^2 ≤ holderEndpointRate ν τ γ := by
  have hp : τ^3 ≤ τ^2 := by nlinarith [mul_le_mul_of_nonneg_left hτ1 (sq_nonneg τ)]
  exact (one_div_le_one_div_of_le (pow_pos hτ 3) hp).trans
    (le_add_of_nonneg_right (Real.rpow_nonneg hγ.le _))

theorem curvatureMovePower_le_endpoint (ν : ℝ) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    γ^(-(1+2/ν)) ≤ γ^(-holderRateExponent ν) :=
  Real.rpow_le_rpow_of_exponent_ge hγ hγ1 (by unfold holderRateExponent; linarith)

theorem inv_gamma_sq_le_endpoint {ν γ : ℝ} (hν : 0 < ν) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    1/γ^2 ≤ γ^(-holderRateExponent ν) := by
  have hp : γ^(-2 : ℝ) ≤ γ^(-holderRateExponent ν) :=
    Real.rpow_le_rpow_of_exponent_ge hγ hγ1 (by
      have hn : 0 < 2/ν := div_pos (by norm_num) hν
      unfold holderRateExponent
      linarith)
  simpa only [Real.rpow_neg hγ.le,Real.rpow_two,one_div] using hp

theorem curvatureMovePower_div_sq (ν : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    γ^(-(1+2/ν))/γ^2 = γ^(-holderRateExponent ν) := by
  rw [← Real.rpow_natCast γ 2,← Real.rpow_sub hγ]
  congr 1
  unfold holderRateExponent
  norm_num
  ring

end
end SecondOrder
