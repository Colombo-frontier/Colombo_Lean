import FreshGradientMinimax.PrimalHorizonLower

/-! Universal constants and exact parameter restoration for the primal
stochastic hard family. The constants are independent of every problem input. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def primalValueCoefficient : ℝ := 64 * primalScalingConstant / primalBarrierConstant ^ 2
def primalNoiseCoefficient : ℝ := 4 * (10 ^ 4) ^ 2 * primalValueCoefficient
def primalLowerCoefficient : ℝ := (768 * primalValueCoefficient * (1 + primalNoiseCoefficient))⁻¹
def primalGapThreshold : ℝ := 128 * primalValueCoefficient

theorem primalValueCoefficient_pos : 0 < primalValueCoefficient := by
  unfold primalValueCoefficient primalScalingConstant
  exact div_pos (by norm_num) (sq_pos_of_pos primalBarrierConstant_pos)

theorem primalNoiseCoefficient_pos : 0 < primalNoiseCoefficient := by
  unfold primalNoiseCoefficient
  exact mul_pos (by norm_num) primalValueCoefficient_pos

theorem primalLowerCoefficient_pos : 0 < primalLowerCoefficient := by
  unfold primalLowerCoefficient
  exact inv_pos.mpr (mul_pos (mul_pos (by norm_num) primalValueCoefficient_pos)
    (by linarith [primalNoiseCoefficient_pos]))

theorem primalGapThreshold_pos : 0 < primalGapThreshold := by
  unfold primalGapThreshold
  exact mul_pos (by norm_num) primalValueCoefficient_pos

theorem primalValueScale_coefficient (L ε : ℝ) :
    primalValueScale L ε = primalValueCoefficient * ε ^ 2 / L := by
  unfold primalValueScale primalValueCoefficient
  ring

theorem revealProbability_mul_noise_le {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    revealProbability r s * s ≤ r := by
  unfold revealProbability
  split_ifs with h
  · simpa only [h, mul_zero] using hr
  · have hs' : 0 < s := lt_of_le_of_ne hs (Ne.symm h)
    calc
      min 1 (r / s) * s ≤ (r / s) * s := mul_le_mul_of_nonneg_right (min_le_right _ _) hs
      _ = r := div_mul_cancel₀ _ hs'.ne'

theorem primal_noise_probability_bound (p : Parameters) :
    primalRevealProbability p.L p.ε p.μ p.σ * (p.κ * p.σ ^ 2 / p.ε ^ 2) ≤ primalNoiseCoefficient := by
  have hL := p.μ_pos.trans_le p.μ_le_L
  have hp := revealProbability_mul_noise_le
    (sq_nonneg (10 ^ 4 * primalInteractionScale p.L p.ε p.μ)) (sq_nonneg p.σ)
  have hk : 0 ≤ p.κ / p.ε ^ 2 := div_nonneg (div_nonneg hL.le p.μ_pos.le) (sq_nonneg p.ε)
  have h := mul_le_mul_of_nonneg_right hp hk
  have he : (10 ^ 4 * primalInteractionScale p.L p.ε p.μ) ^ 2 * (p.κ / p.ε ^ 2) = primalNoiseCoefficient := by
    rw [mul_pow, primalInteractionScale_sq hL p.ε_pos p.μ_pos, primalValueScale_coefficient]
    unfold Parameters.κ primalNoiseCoefficient
    field_simp [hL.ne', p.μ_pos.ne', p.ε_pos.ne']
    ring
  rw [he] at h
  change primalRevealProbability p.L p.ε p.μ p.σ * p.σ ^ 2 * (p.κ / p.ε ^ 2) ≤ _ at h
  convert h using 1; ring

theorem primal_stage_count_exists {lam Δ : ℝ} (hlam : 0 < lam) (hΔ : 128 * lam ≤ Δ) :
    ∃ n : ℕ, 0 < n ∧ n + 1 = ⌊Δ / (32 * lam)⌋₊ ∧ Δ / (64 * lam) ≤ (n : ℝ) := by
  have hq : (4 : ℝ) ≤ Δ / (32 * lam) :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith only [hΔ])
  have hT : 4 ≤ ⌊Δ / (32 * lam)⌋₊ := Nat.le_floor hq
  let n := ⌊Δ / (32 * lam)⌋₊ - 1
  have hn : n + 1 = ⌊Δ / (32 * lam)⌋₊ := by dsimp [n]; omega
  refine ⟨n, by dsimp [n]; omega, hn, ?_⟩
  have hq' := Nat.lt_floor_add_one (Δ / (32 * lam))
  rw [← hn] at hq'
  push_cast at hq'
  have he : Δ / (64 * lam) = (Δ / (32 * lam)) / 2 := by ring
  rw [he]
  linarith

theorem primal_gap_threshold_scale (p : Parameters)
    (hgap : primalGapThreshold * p.ε ^ 2 ≤ p.L * p.gap) :
    128 * primalValueScale p.L p.ε ≤ p.gap := by
  rw [primalValueScale_coefficient]
  have he : 128 * (primalValueCoefficient * p.ε ^ 2 / p.L) =
      primalGapThreshold * p.ε ^ 2 / p.L := by unfold primalGapThreshold; ring
  rw [he]
  exact (div_le_iff₀ (p.μ_pos.trans_le p.μ_le_L)).mpr (by simpa only [mul_comm] using hgap)

end FreshGradientMinimax
