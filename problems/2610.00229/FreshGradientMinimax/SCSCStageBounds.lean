import FreshGradientMinimax.SCSCLogBounds

/-! The per-stage initialization, condition-number and noise factors in
F.5. The cold-start logarithm occurs only in the deterministic term. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax

theorem scsc_stage_initialization_bound {ℓ σ μ η E₀ : ℝ}
    (hμ : 0 < μ) (hμℓ : μ ≤ ℓ) (hη : 0 < η) (hE : 0 ≤ E₀) (j : ℕ) :
    Real.log (2 + recursiveInputEnvelope μ (scscGradientTolerance μ η) (recursiveLastIndex (5 * ℓ) μ)
      (3 * (ℓ / μ) * E₀) j / recursiveAccuracy μ (scscGradientTolerance μ η) (recursiveLastIndex (5 * ℓ) μ) j) ≤
      100000000 * valueLogFactor ℓ σ μ η * Real.log (2 + (ℓ / μ) * E₀ / η) := by
  let L := valueLogFactor ℓ σ μ η
  let T := Real.log (2 + (ℓ / μ) * E₀ / η)
  let J := scscStageCount ℓ μ
  have hℓ := hμ.trans_le hμℓ
  have hL : 1 ≤ L := (valueLogFactor_bounds (σ := σ) hℓ hμ hη).1
  have hX : 0 ≤ (ℓ / μ) * E₀ / η := by positivity
  have hT : (1 / 2 : ℝ) ≤ T := log_two_bounds.1.trans
    (Real.log_le_log (by norm_num) (by linarith only [hX]))
  have hLT : (1 / 2 : ℝ) ≤ L * T := by
    have h := mul_le_mul_of_nonneg_right hL (by linarith only [hT] : 0 ≤ T)
    nlinarith only [h, hT]
  have hLmul : L ≤ 2 * (L * T) := by
    have h := mul_le_mul_of_nonneg_left hT (by linarith only [hL] : 0 ≤ 2 * L)
    nlinarith only [h]
  have hTmul : T ≤ L * T := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hL (by linarith only [hT] : 0 ≤ T)
  cases j with
  | zero =>
    rw [recursiveInputEnvelope, scsc_cold_ratio hμ hη]
    have hJ : 1 ≤ J := scscStageCount_one ℓ μ
    have hJL : J ≤ 20 * L := scscStageCount_log_bound hμ hμℓ hη
    have hlog := log_scaled_add_two (show (1 : ℝ) ≤ 3000000 * J ^ 2 by nlinarith only [hJ]) hX
    rw [Real.log_mul (by norm_num : (3000000 : ℝ) ≠ 0) (by nlinarith only [hJ] : J ^ 2 ≠ 0), Real.log_pow] at hlog
    have hC : Real.log 3000000 ≤ 2999999 :=
      (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3000000)).trans (by norm_num)
    have hJlog : Real.log J ≤ J - 1 := Real.log_le_sub_one_of_pos (by linarith only [hJ])
    change Real.log (2 + 3000000 * J ^ 2 * ((ℓ / μ) * E₀ / η)) ≤ 100000000 * L * T
    change _ ≤ Real.log 3000000 + 2 * Real.log J + T at hlog
    nlinarith only [hlog, hC, hJlog, hJL, hLmul, hTmul, hLT]
  | succ j =>
    rw [SCObjective.recursive_warm_envelope_ratio hμ (scscGradientTolerance_pos hμ hη)]
    have hlog : Real.log (2 + (138 : ℝ)) ≤ 139 :=
      (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2 + 138)).trans (by norm_num)
    change _ ≤ 100000000 * L * T
    nlinarith only [hlog, hLT]

theorem scsc_stage_sqrt_bound {ℓ μ : ℝ} (hμ : 0 < μ) (hμℓ : μ ≤ ℓ)
    {j : ℕ} (hj : j ≤ recursiveLastIndex (5 * ℓ) μ) :
    Real.sqrt ((5 * ℓ + recursiveCurvature μ j) / recursiveMass μ j) ≤ 4 * Real.sqrt (ℓ / μ) := by
  have hℓ := hμ.trans_le hμℓ
  have hmass : μ ≤ recursiveMass μ j := by
    simpa only [recursiveMass, pow_zero, one_mul] using recursiveMass_monotone hμ.le (Nat.zero_le j)
  have hcurv := recursiveCurvature_stage_bound hμ hμℓ hj
  have hκ : 0 ≤ ℓ / μ := div_nonneg hℓ.le hμ.le
  have hratio : (5 * ℓ + recursiveCurvature μ j) / recursiveMass μ j ≤ 16 * (ℓ / μ) := by
    calc
      _ ≤ (15 * ℓ) / recursiveMass μ j := div_le_div_of_nonneg_right (by linarith only [hcurv]) (recursiveMass_pos hμ j).le
      _ ≤ (15 * ℓ) / μ := div_le_div_of_nonneg_left (by positivity) hμ hmass
      _ ≤ _ := by ring_nf at hκ ⊢; nlinarith only [hκ]
  calc
    _ ≤ Real.sqrt (16 * (ℓ / μ)) := Real.sqrt_le_sqrt hratio
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]; norm_num

theorem scsc_stage_noise_bound {ℓ σ μ η : ℝ} (hμ : 0 < μ) (hμℓ : μ ≤ ℓ) (hη : 0 < η) (j : ℕ) :
    σ ^ 2 / (recursiveMass μ j * recursiveAccuracy μ (scscGradientTolerance μ η) (recursiveLastIndex (5 * ℓ) μ) j) ≤
      400000000 * valueLogFactor ℓ σ μ η ^ 2 * (σ ^ 2 / (μ * η)) := by
  rw [scsc_noise_identity hμ hη]
  have hJ : 0 ≤ scscStageCount ℓ μ := le_trans (by norm_num) (scscStageCount_one ℓ μ)
  have hL := (valueLogFactor_bounds (σ := σ) (hμ.trans_le hμℓ) hμ hη).1
  have hs := (sq_le_sq₀ hJ (by linarith only [hL] : 0 ≤ 20 * valueLogFactor ℓ σ μ η)).mpr
    (scscStageCount_log_bound hμ hμℓ hη)
  have hU : 0 ≤ σ ^ 2 / (μ * η) := by positivity
  have hm := mul_le_mul_of_nonneg_right hs (show 0 ≤ 1000000 * (σ ^ 2 / (μ * η)) by positivity)
  change 1000000 * scscStageCount ℓ μ ^ 2 * (σ ^ 2 / (μ * η)) ≤ _
  nlinarith only [hm]

end FreshGradientMinimax
