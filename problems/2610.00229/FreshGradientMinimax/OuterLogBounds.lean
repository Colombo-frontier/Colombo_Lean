import FreshGradientMinimax.OuterRateParameters

/-! Coarse and fine logarithms share a G-independent envelope. Only the
single cold initialization logarithm retains the localization parameter. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax

theorem outer_coarse_noise_le (p : Parameters) :
    p.σ ^ 2 / (p.μ * outerCoarseTolerance p.L p.ε) ≤ 1000000 * p.testing := by
  rw [outer_coarse_noise_identity]
  have hk := p.condition_ge_one
  have hk2 : p.κ ≤ p.κ ^ 2 := by nlinarith
  have h := mul_le_mul_of_nonneg_right hk2 (show 0 ≤ p.σ ^ 2 / p.ε ^ 2 by positivity)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  simpa only [Parameters.testing, mul_div_assoc] using h

theorem outer_valueLogFactor_bound (p : Parameters) {η : ℝ} (hη : 0 < η)
    (hn : p.σ ^ 2 / (p.μ * η) ≤ 1000000 * p.testing) :
    valueLogFactor (3 * p.L) p.σ p.μ η ≤ 10000000 * logarithmicEnvelope p := by
  have hμ := p.μ_pos
  have hk : 0 ≤ p.κ := by linarith [p.condition_ge_one]
  have hU : 0 ≤ p.testing := by unfold Parameters.testing; positivity
  have hΛ := logarithmicEnvelope_bounds p
  have hfirst := log_scaled_add_two (by norm_num : (1 : ℝ) ≤ 3) hk
  have hnoise := Real.log_le_log (by positivity : 0 < 2 + p.σ ^ 2 / (p.μ * η)) (add_le_add_left hn 2)
  have hs := log_scaled_add_two (by norm_num : (1 : ℝ) ≤ 1000000) hU
  have h3 : Real.log 3 ≤ 2 := by exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)).trans (by norm_num)
  have hC : Real.log 1000000 ≤ 999999 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1000000)).trans (by norm_num)
  unfold valueLogFactor
  rw [show (3 * p.L) / p.μ = 3 * p.κ by unfold Parameters.κ; ring]
  linarith only [hfirst, hnoise, hs, h3, hC, hΛ.1, hΛ.2.1, hΛ.2.2.2]

theorem outer_coarse_logfactor (p : Parameters) :
    valueLogFactor (3 * p.L) p.σ p.μ (outerCoarseTolerance p.L p.ε) ≤ 10000000 * logarithmicEnvelope p :=
  outer_valueLogFactor_bound p (outerCoarseTolerance_pos (parameter_L_pos p) p.ε_pos) (outer_coarse_noise_le p)

theorem outer_fine_logfactor (p : Parameters) :
    valueLogFactor (3 * p.L) p.σ p.μ (outerFineTolerance p.L p.μ p.ε) ≤ 10000000 * logarithmicEnvelope p :=
  outer_valueLogFactor_bound p (outerFineTolerance_pos (parameter_L_pos p) p.μ_pos p.ε_pos)
    (outer_fine_noise_identity p).le

theorem outer_warm_log (p : Parameters) (hreg : p.ε ^ 2 ≤ p.L * p.gap) :
    Real.log (2 + ((3 * p.L) / p.μ) *
      outerWarmEnvelope p.gap (outerCoarseTolerance p.L p.ε) (outerStepCount p.L p.gap p.ε) /
        outerCoarseTolerance p.L p.ε) ≤ 300000000 * logarithmicEnvelope p := by
  have hL := parameter_L_pos p
  have hμ := p.μ_pos
  have hη := outerCoarseTolerance_pos hL p.ε_pos
  have hk : 0 ≤ p.κ := by linarith [p.condition_ge_one]
  have hA := outerGapRatio_nonneg p
  have hΛ := logarithmicEnvelope_bounds p
  have hE := outerWarmEnvelope_nontrivial_bound hL p.gap_nonneg p.ε_pos hreg
  have hr := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hE (show 0 ≤ (3 * p.L) / p.μ by positivity)) hη.le
  have he : ((3 * p.L) / p.μ) * (84 * p.gap) / outerCoarseTolerance p.L p.ε =
      252000000 * (p.κ * outerGapRatio p) := by
    unfold outerCoarseTolerance Parameters.κ outerGapRatio
    field_simp
    ring
  rw [he] at hr
  have hE0 := NCObjective.outerWarmEnvelope_pos p.gap_nonneg hη (outerStepCount p.L p.gap p.ε)
  have hlog := Real.log_le_log (by positivity : 0 < 2 + ((3 * p.L) / p.μ) *
      outerWarmEnvelope p.gap (outerCoarseTolerance p.L p.ε) (outerStepCount p.L p.gap p.ε) /
        outerCoarseTolerance p.L p.ε) (add_le_add_left hr 2)
  have hs := log_scaled_add_two (by norm_num : (1 : ℝ) ≤ 252000000) (mul_nonneg hk hA)
  have hp := log_two_mul_bound hk hA
  have hC : Real.log 252000000 ≤ 251999999 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 252000000)).trans (by norm_num)
  linarith only [hlog, hs, hp, hC, hΛ.1, hΛ.2.1, hΛ.2.2.1]

theorem outer_fine_log (p : Parameters) :
    Real.log (2 + ((3 * p.L) / p.μ) * (6 * outerCoarseTolerance p.L p.ε) /
      outerFineTolerance p.L p.μ p.ε) ≤ 100 * logarithmicEnvelope p := by
  have hk : 0 ≤ p.κ := by linarith [p.condition_ge_one]
  have hΛ := logarithmicEnvelope_bounds p
  have he : ((3 * p.L) / p.μ) * (6 * outerCoarseTolerance p.L p.ε) / outerFineTolerance p.L p.μ p.ε =
      18 * p.κ ^ 2 := by
    unfold outerCoarseTolerance outerFineTolerance Parameters.κ
    field_simp [ne_of_gt (parameter_L_pos p), ne_of_gt p.μ_pos, ne_of_gt p.ε_pos]
    ring
  rw [he]
  have hs := log_scaled_add_two (by norm_num : (1 : ℝ) ≤ 18) (sq_nonneg p.κ)
  have hp := log_two_mul_bound hk hk
  rw [← pow_two] at hp
  have hC : Real.log 18 ≤ 17 := by exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 18)).trans (by norm_num)
  linarith only [hs, hp, hC, hΛ.1, hΛ.2.1]

theorem outer_cold_log (p : Parameters) (hreg : p.ε ^ 2 ≤ p.L * p.gap) :
    Real.log (2 + ((3 * p.L) / p.μ) * outerColdEnvelope p.L p.μ p.gap p.G (outerCoarseTolerance p.L p.ε) /
      outerCoarseTolerance p.L p.ε) ≤ 40000000 * outerColdLog p := by
  have hL := parameter_L_pos p
  have hμ := p.μ_pos
  have hη := outerCoarseTolerance_pos hL p.ε_pos
  have hk := p.condition_ge_one
  have hA := outerGapRatio_one p hreg
  let V := p.G ^ 2 / p.ε ^ 2
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have he : ((3 * p.L) / p.μ) * outerColdEnvelope p.L p.μ p.gap p.G (outerCoarseTolerance p.L p.ε) /
      outerCoarseTolerance p.L p.ε =
      3000000 * p.κ * (3 + 2 * p.κ) * outerGapRatio p + 6000000 * p.κ ^ 2 * V + 3 * p.κ := by
    unfold outerColdEnvelope outerCoarseTolerance outerGapRatio Parameters.κ V
    field_simp [ne_of_gt hL, ne_of_gt hμ, ne_of_gt p.ε_pos]
    ring
  have hk2 : p.κ ≤ p.κ ^ 2 := by nlinarith
  have hka : p.κ ^ 2 ≤ p.κ ^ 2 * outerGapRatio p := by nlinarith only [mul_le_mul_of_nonneg_left hA (sq_nonneg p.κ)]
  have hkA := mul_le_mul_of_nonneg_right hk2 (by linarith only [hA] : 0 ≤ outerGapRatio p)
  have hkv : 0 ≤ p.κ ^ 2 * V := mul_nonneg (sq_nonneg _) hV
  have hr : 3000000 * p.κ * (3 + 2 * p.κ) * outerGapRatio p + 6000000 * p.κ ^ 2 * V + 3 * p.κ ≤
      20000000 * (p.κ ^ 2 * V + p.κ ^ 2 * outerGapRatio p) := by
    nlinarith only [hkA, hk2, hka, hkv]
  rw [he]
  have hR : 0 ≤ p.κ ^ 2 * V + p.κ ^ 2 * outerGapRatio p := by positivity
  have hlog := Real.log_le_log (by positivity : 0 < 2 +
      (3000000 * p.κ * (3 + 2 * p.κ) * outerGapRatio p + 6000000 * p.κ ^ 2 * V + 3 * p.κ))
      (add_le_add_left hr 2)
  have hs := log_scaled_add_two (by norm_num : (1 : ℝ) ≤ 20000000) hR
  have hI : Real.log (2 + (p.κ ^ 2 * V + p.κ ^ 2 * outerGapRatio p)) = outerColdLog p := by
    congr 1
    dsimp [V, outerColdLog]
    ring
  rw [hI] at hs
  have hC : Real.log 20000000 ≤ 19999999 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 20000000)).trans (by norm_num)
  have hhalf := outerColdLog_half p
  linarith only [hlog, hs, hC, hhalf]

end FreshGradientMinimax

