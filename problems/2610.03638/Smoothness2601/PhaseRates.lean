import Smoothness2601.OrderRates

noncomputable section
namespace Smoothness2601

theorem phase_threshold {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε)
    (hs : ε ≤ Real.exp (-β)) : 1 ≤ Real.log (1/ε)/β := by
  have hl := Real.log_le_log hε hs
  rw [Real.log_exp] at hl
  apply (le_div_iff₀ hβ).mpr
  rw [one_div,Real.log_inv]
  linarith

theorem phase_rate_bounds {β t D C ε : ℝ} (hβ : 0 < β) (ht : 0 ≤ t)
    (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hl : (t/β)^β*Real.exp β ≤ D)
    (hu : D ≤ 2^β*((t/β)^β*Real.exp β)) :
    C*phaseCoefficient β*ε^(-4:ℝ)*t^(2*β) ≤ C*ε^(-4:ℝ)*D^2 ∧
    C*ε^(-4:ℝ)*D^2 ≤ (C*(2^β)^2*phaseCoefficient β)*ε^(-4:ℝ)*t^(2*β) := by
  have hφ : 0 ≤ (t/β)^β*Real.exp β := by positivity
  have hD := hφ.trans hl
  have hCl : 0 ≤ C*ε^(-4:ℝ) := mul_nonneg hC (Real.rpow_nonneg hε _)
  constructor
  · have hh := mul_le_mul_of_nonneg_left ((sq_le_sq₀ hφ hD).mpr hl) hCl
    rw [phase_rate_identity hβ ht] at hh
    convert hh using 1
    ring
  · have hh := mul_le_mul_of_nonneg_left ((sq_le_sq₀ hD (by positivity)).mpr hu) hCl
    rw [mul_pow,phase_rate_identity hβ ht] at hh
    convert hh using 1
    ring

end Smoothness2601
