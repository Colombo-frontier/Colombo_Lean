import FreshGradientMinimax.RecursiveCostRate

/-! Uniform logarithmic bounds in the SCSC primitive. All multipliers
are independent of the starting energy; the noise term is never charged
an initialization logarithm. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax

def scscStageCount (ℓ μ : ℝ) : ℝ := (recursiveLastIndex (5 * ℓ) μ + 1 : ℕ)

theorem scscStageCount_one (ℓ μ : ℝ) : 1 ≤ scscStageCount ℓ μ := by
  unfold scscStageCount
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)

theorem scscGradientTolerance_pos {μ η : ℝ} (hμ : 0 < μ) (hη : 0 < η) :
    0 < scscGradientTolerance μ η := Real.sqrt_pos.mpr (by positivity)

theorem scscGradientTolerance_sq {μ η : ℝ} (hμ : 0 < μ) (hη : 0 < η) :
    scscGradientTolerance μ η ^ 2 = μ * η / 100 := Real.sq_sqrt (by positivity)

theorem log_scaled_add_two {B x : ℝ} (hB : 1 ≤ B) (hx : 0 ≤ x) :
    Real.log (2 + B * x) ≤ Real.log B + Real.log (2 + x) := by
  have hb : 0 < B := by linarith
  have h := Real.log_le_log (by positivity : 0 < 2 + B * x)
    (show 2 + B * x ≤ B * (2 + x) by nlinarith only [hB])
  rwa [Real.log_mul hb.ne' (by positivity)] at h

theorem scscStageCount_log_bound {ℓ σ μ η : ℝ} (hμ : 0 < μ) (hμℓ : μ ≤ ℓ) (hη : 0 < η) :
    scscStageCount ℓ μ ≤ 20 * valueLogFactor ℓ σ μ η := by
  have hℓ := hμ.trans_le hμℓ
  have hL := valueLogFactor_bounds (σ := σ) hℓ hμ hη
  have hκ : 0 < ℓ / μ := div_pos hℓ hμ
  have hcount := recursiveLastIndex_count hμ (show μ ≤ 5 * ℓ by linarith)
  have hlog := Real.log_le_log (by positivity : 0 < 5 * ℓ / μ)
    (show 5 * ℓ / μ ≤ 5 * (2 + ℓ / μ) by ring_nf; linarith)
  rw [Real.log_mul (by norm_num) (by positivity)] at hlog
  have h5 : Real.log 5 ≤ 4 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)).trans (by norm_num)
  have hdiv : Real.log (5 * ℓ / μ) / Real.log 2 ≤ 2 * (4 + valueLogFactor ℓ σ μ η) := by
    apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    have hm := mul_le_mul_of_nonneg_left log_two_bounds.1
      (by linarith [hL.1] : 0 ≤ 2 * (4 + valueLogFactor ℓ σ μ η))
    nlinarith only [hlog, h5, hL.2.1, hm]
  change scscStageCount ℓ μ ≤ _ at hcount
  linarith only [hcount, hdiv, hL.1]

theorem scsc_noise_identity {σ μ η : ℝ} (hμ : 0 < μ) (hη : 0 < η) (N j : ℕ) :
    σ ^ 2 / (recursiveMass μ j * recursiveAccuracy μ (scscGradientTolerance μ η) N j) =
      1000000 * (N + 1 : ℕ) ^ 2 * (σ ^ 2 / (μ * η)) := by
  rw [recursiveAccuracy_scaled hμ, scscGradientTolerance_sq hμ hη]
  field_simp
  ring

theorem scsc_cold_ratio {ℓ μ η E₀ : ℝ} (hμ : 0 < μ) (hη : 0 < η) (N : ℕ) :
    (3 * (ℓ / μ) * E₀) / recursiveAccuracy μ (scscGradientTolerance μ η) N 0 =
      3000000 * (N + 1 : ℕ) ^ 2 * ((ℓ / μ) * E₀ / η) := by
  rw [recursiveAccuracy, scscGradientTolerance_sq hμ hη]
  simp only [recursiveMass, pow_zero, one_mul]
  field_simp
  ring

theorem scsc_stage_log_bound {ℓ σ μ η : ℝ} (hμ : 0 < μ) (hμℓ : μ ≤ ℓ) (hη : 0 < η) (j : ℕ) :
    valueLogFactor ℓ σ (recursiveMass μ j)
      (recursiveAccuracy μ (scscGradientTolerance μ η) (recursiveLastIndex (5 * ℓ) μ) j) ≤
        10000000 * valueLogFactor ℓ σ μ η := by
  let J := scscStageCount ℓ μ
  let L := valueLogFactor ℓ σ μ η
  have hℓ := hμ.trans_le hμℓ
  have hL := valueLogFactor_bounds (σ := σ) hℓ hμ hη
  have hJ : 1 ≤ J := scscStageCount_one ℓ μ
  have hJL : J ≤ 20 * L := scscStageCount_log_bound hμ hμℓ hη
  have hmass : μ ≤ recursiveMass μ j := by
    simpa only [recursiveMass, pow_zero, one_mul] using recursiveMass_monotone hμ.le (Nat.zero_le j)
  have hfirst := Real.log_le_log (by have := recursiveMass_pos hμ j; positivity : 0 < 2 + ℓ / recursiveMass μ j)
    (add_le_add_left (div_le_div_of_nonneg_left hℓ.le hμ hmass) 2)
  have hU : 0 ≤ σ ^ 2 / (μ * η) := by positivity
  have hnoise := log_scaled_add_two (show (1 : ℝ) ≤ 1000000 * J ^ 2 by nlinarith only [hJ]) hU
  rw [Real.log_mul (by norm_num : (1000000 : ℝ) ≠ 0) (by nlinarith only [hJ] : J ^ 2 ≠ 0), Real.log_pow] at hnoise
  have hC : Real.log 1000000 ≤ 999999 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1000000)).trans (by norm_num)
  have hlogJ : Real.log J ≤ J - 1 := Real.log_le_sub_one_of_pos (by linarith only [hJ])
  unfold valueLogFactor
  rw [scsc_noise_identity hμ hη]
  change 1 + Real.log (2 + ℓ / recursiveMass μ j) + Real.log (2 + 1000000 * J ^ 2 * (σ ^ 2 / (μ * η))) ≤ 10000000 * L
  have hL1 : 1 ≤ L := hL.1
  have hL2 : Real.log (2 + ℓ / μ) ≤ L := hL.2.1
  have hL3 : Real.log (2 + σ ^ 2 / (μ * η)) ≤ L := hL.2.2
  nlinarith only [hfirst, hnoise, hC, hlogJ, hJL, hL1, hL2, hL3]

end FreshGradientMinimax
