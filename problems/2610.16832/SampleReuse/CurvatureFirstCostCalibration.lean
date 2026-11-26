import SampleReuse.CurvatureFirstBudgetCalibration

open SecondOrder

namespace SampleReuse
noncomputable section

private theorem calibrated_cost_polynomial {a b c e q s L : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hq : 0 ≤ q) (hL : 1 ≤ L)
    (hqd : q ≤ 2*L) (hscale : s ≤ 16384*L^3) :
    1+(64/3:ℝ)*a+24*e+s*(b+4*q*((8/3:ℝ)*c+12*e)) ≤
      sourceUpperConstant*L^4*(1+a+b+c+e) := by
  let B := 1+a+b+c+e
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbase : 1+(64/3:ℝ)*a+24*e ≤ 24*B := by dsimp [B]; linarith
  have hinner : b+4*q*((8/3:ℝ)*c+12*e) ≤ 97*L*B := by
    have hbB : b ≤ B := by dsimp [B]; linarith
    have hcB : (8/3:ℝ)*c+12*e ≤ 12*B := by dsimp [B]; linarith
    have ht := mul_le_mul_of_nonneg_left hcB (by positivity : 0≤4*q)
    have hqB := mul_le_mul_of_nonneg_right hqd hB
    have hLB := mul_le_mul_of_nonneg_right hL hB
    nlinarith
  have hsinner := mul_le_mul hscale hinner (by positivity : 0≤b+4*q*((8/3:ℝ)*c+12*e))
    (by positivity : 0≤16384*L^3)
  have hL4 : 1 ≤ L^4 := one_le_pow₀ hL
  have hBL := mul_le_mul_of_nonneg_right hL4 hB
  have hrest : 0 ≤ L^4*B := mul_nonneg (pow_nonneg (by linarith) _) hB
  dsimp [sourceUpperConstant]
  change _ ≤ 2097152*L^4*B
  nlinarith

theorem source_gradient_expected_budget (P : Parameters) (d T : ℕ) {ε γ : ℝ}
    (hε : 0 < ε) (hγ : 0 < γ) :
    1+2*(32*P.gradientLip*P.gap/(3*ε^2)) + sourceConfidenceScale d T ε *
      (P.gradientNoise^2+4*(binaryDepth T:ℝ)*
        (P.gradientNoise*P.gradientLip*(8*P.gap/(3*ε))+P.gradientLip^2*(12*P.gap/γ))) ≤
      sourceUpperConstant*(sourceLogScale d T)^4*sourceGradientBudget P ε γ := by
  let a := P.gap*P.gradientLip/ε^2
  let b := P.gradientNoise^2/ε^2
  let c := P.gradientNoise*P.gradientLip*P.gap/ε^3
  let e := P.gradientLip^2*P.gap/(ε^2*γ)
  have hp := P.gap_pos
  have hgl := P.gradientLip_pos
  have hgn := P.gradientNoise_pos
  have ha : 0≤a := by dsimp [a]; positivity
  have hb : 0≤b := by dsimp [b]; positivity
  have hc : 0≤c := by dsimp [c]; positivity
  have he : 0≤e := by dsimp [e]; positivity
  have hscale : sourceConfidenceScale d T ε*ε^2 ≤16384*(sourceLogScale d T)^3 :=
    (le_div_iff₀ (sq_pos_of_pos hε)).mp (sourceConfidenceScale_bound d T hε)
  have hq : (binaryDepth T:ℝ) ≤2*sourceLogScale d T := by
    have := binaryDepth_log_bound d T
    linarith
  have hbound := calibrated_cost_polynomial ha hb hc he (Nat.cast_nonneg _)
    (sourceLogScale_one_le d T) hq hscale
  have hid : 1+2*(32*P.gradientLip*P.gap/(3*ε^2)) + sourceConfidenceScale d T ε *
      (P.gradientNoise^2+4*(binaryDepth T:ℝ)*
        (P.gradientNoise*P.gradientLip*(8*P.gap/(3*ε))+P.gradientLip^2*(12*P.gap/γ))) =
      1+(64/3:ℝ)*a+(sourceConfidenceScale d T ε*ε^2)*(b+4*(binaryDepth T:ℝ)*((8/3:ℝ)*c+12*e)) := by
    dsimp [a,b,c,e]
    field_simp
    all_goals ring
  rw [hid]
  change _ ≤ sourceUpperConstant*(sourceLogScale d T)^4*(1+a+b+c+e)
  linarith

theorem source_hessian_expected_budget (P : Parameters) (d T : ℕ) {ε γ : ℝ}
    (hε : 0 < ε) (hγ : 0 < γ) :
    1+2*((32*P.gradientLip/(3*ε^2)+12*P.hessianLip^2/γ^3)*P.gap) + sourceConfidenceScale d T γ *
      (P.hessianNoise^2+4*(binaryDepth T:ℝ)*
        (P.hessianNoise*P.hessianLip*(8*P.gap/(3*ε))+P.hessianLip^2*(12*P.gap/γ))) ≤
      sourceUpperConstant*(sourceLogScale d T)^4*sourceHessianBudget P ε γ := by
  let a := P.gap*P.gradientLip/ε^2
  let b := P.hessianNoise^2/γ^2
  let c := P.hessianNoise*P.hessianLip*P.gap/(ε*γ^2)
  let e := P.hessianLip^2*P.gap/γ^3
  have hp := P.gap_pos
  have hgl := P.gradientLip_pos
  have hhl := P.hessianLip_pos
  have hhn := P.hessianNoise_pos
  have ha : 0≤a := by dsimp [a]; positivity
  have hb : 0≤b := by dsimp [b]; positivity
  have hc : 0≤c := by dsimp [c]; positivity
  have he : 0≤e := by dsimp [e]; positivity
  have hscale : sourceConfidenceScale d T γ*γ^2 ≤16384*(sourceLogScale d T)^3 :=
    (le_div_iff₀ (sq_pos_of_pos hγ)).mp (sourceConfidenceScale_bound d T hγ)
  have hq : (binaryDepth T:ℝ) ≤2*sourceLogScale d T := by
    have := binaryDepth_log_bound d T
    linarith
  have hbound := calibrated_cost_polynomial ha hb hc he (Nat.cast_nonneg _)
    (sourceLogScale_one_le d T) hq hscale
  have hid : 1+2*((32*P.gradientLip/(3*ε^2)+12*P.hessianLip^2/γ^3)*P.gap) + sourceConfidenceScale d T γ *
      (P.hessianNoise^2+4*(binaryDepth T:ℝ)*
        (P.hessianNoise*P.hessianLip*(8*P.gap/(3*ε))+P.hessianLip^2*(12*P.gap/γ))) =
      1+(64/3:ℝ)*a+24*e+(sourceConfidenceScale d T γ*γ^2)*(b+4*(binaryDepth T:ℝ)*((8/3:ℝ)*c+12*e)) := by
    dsimp [a,b,c,e]
    field_simp
    all_goals ring
  rw [hid]
  apply hbound.trans
  have hC := sourceUpperConstant_pos
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0≤sourceUpperConstant*(sourceLogScale d T)^4)
  dsimp [sourceHessianBudget,a,b,c,e]
  have he' : 2*P.hessianLip^2*P.gap/γ^3 = 2*(P.hessianLip^2*P.gap/γ^3) := by ring
  rw [he']
  dsimp [e] at he
  linarith

end
end SampleReuse

