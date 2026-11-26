import FreshGradientMinimax.PathThetaBounds

/-! The actual signal fits the prescribed dual localization throughout the
paper's logarithmic horizon. All constants refer to the already constructed
hard objective; the signal bound is proved from its exact inverse formula. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax

theorem pathHardSignal_formula {L μ : ℝ} (hL : 0 < L) (hμ : 0 < μ) (ε : ℝ) (n : ℕ) :
    pathHardSignal L μ ε n =
      ε * Real.sinh (((n : ℝ) + 2) * pathTheta μ (L / 8192)) /
        (512 * Real.sinh (pathTheta μ (L / 8192))) := by
  have hθ := pathTheta_pos hμ (by positivity : 0 < L / 8192)
  have hs : Real.sinh (pathTheta μ (L / 8192)) ≠ 0 := (Real.sinh_pos_iff.mpr hθ).ne'
  have hn : Real.sinh (((n : ℝ) + 2) * pathTheta μ (L / 8192)) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (by positivity)).ne'
  unfold pathHardSignal pathTransmission
  field_simp [hL.ne', hs, hn]
  ring

theorem path_horizon_exponent_bound {θ r b : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hθr : θ * r ≤ 128) (hb : 1 < b) {N : ℕ}
    (hN : (N : ℝ) ≤ r * Real.log b / 1024) :
    (4 * (N : ℝ) + 5) * θ ≤ Real.log b + 5 := by
  have hbLog : 0 < Real.log b := Real.log_pos hb
  have hN' := (le_div_iff₀ (by norm_num : (0 : ℝ) < 1024)).mp hN
  have hm := mul_le_mul_of_nonneg_right hN' hθ
  have hc := mul_le_mul_of_nonneg_right hθr hbLog.le
  nlinarith only [hm, hc, hθ1, hbLog]

theorem path_horizon_sinh_bound {θ r b : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hθr : θ * r ≤ 128) (hsr : 1 ≤ Real.sinh θ * r) (hb : 1 < b) {N : ℕ}
    (hN : (N : ℝ) ≤ r * Real.log b / 1024) :
    Real.sinh ((4 * (N : ℝ) + 5) * θ) ≤ 512 * (Real.sinh θ * r) * b := by
  have hb0 : 0 ≤ b := by linarith
  have ht := path_horizon_exponent_bound hθ hθ1 hθr hb hN
  have he : Real.exp ((4 * (N : ℝ) + 5) * θ) ≤ b * 243 := by
    calc
      _ ≤ Real.exp (Real.log b + 5) := Real.exp_le_exp.mpr ht
      _ = b * Real.exp 5 := by rw [Real.exp_add, Real.exp_log (by linarith)]
      _ ≤ b * 243 := mul_le_mul_of_nonneg_left exp_five_le hb0
  have hs : Real.sinh ((4 * (N : ℝ) + 5) * θ) ≤ Real.exp ((4 * (N : ℝ) + 5) * θ) / 2 := by
    rw [Real.sinh_eq]
    linarith [Real.exp_pos (-((4 * (N : ℝ) + 5) * θ))]
  have hm := mul_le_mul_of_nonneg_right hsr hb0
  nlinarith only [he, hs, hm, hb0]

theorem pathHardSignal_horizon_le (p : Parameters) (hκ : 8192 ≤ p.κ)
    (hb : 1 < p.G / (p.ε * Real.sqrt p.κ)) {N : ℕ}
    (hN : (N : ℝ) ≤ Real.sqrt p.κ * Real.log (p.G / (p.ε * Real.sqrt p.κ)) / 1024) :
    pathHardSignal p.L p.μ p.ε (4 * N + 3) ≤ p.G := by
  have hL : 0 < p.L := p.μ_pos.trans_le p.μ_le_L
  have hk : 0 < p.κ := by linarith
  have hr : 0 < Real.sqrt p.κ := Real.sqrt_pos.mpr hk
  have hθ := pathTheta_pos p.μ_pos (by positivity : 0 < p.L / 8192)
  obtain ⟨hθ1, hθr, hsr⟩ := pathTheta_condition_bounds p hκ
  have hs := path_horizon_sinh_bound hθ.le hθ1 hθr hsr hb hN
  have hcal : p.ε * Real.sqrt p.κ * (p.G / (p.ε * Real.sqrt p.κ)) = p.G := by
    field_simp [p.ε_pos.ne', hr.ne']
  rw [pathHardSignal_formula hL p.μ_pos]
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 512) (Real.sinh_pos_iff.mpr hθ))).mpr
  have hi : (((4 * N + 3 : ℕ) : ℝ) + 2) = 4 * (N : ℝ) + 5 := by push_cast; ring
  rw [hi]
  calc
    _ ≤ p.ε * (512 * (Real.sinh (pathTheta p.μ (p.L / 8192)) * Real.sqrt p.κ) *
        (p.G / (p.ε * Real.sqrt p.κ))) := mul_le_mul_of_nonneg_left hs p.ε_pos.le
    _ = (p.ε * Real.sqrt p.κ * (p.G / (p.ε * Real.sqrt p.κ))) *
        (512 * Real.sinh (pathTheta p.μ (p.L / 8192))) := by ring
    _ = _ := by rw [hcal]

end FreshGradientMinimax
