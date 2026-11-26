import MatchingBounds1005.CUPGParameters
import MatchingBounds1005.CUPGEstimate

/-! The exact ε^(1/3) calibration, retaining the exponent 5/3. -/
noncomputable section

namespace MatchingBounds1005.CUPG

def rootParameter (ε : ℝ) : ℝ := ε ^ (1 / 3 : ℝ)

theorem rootParameter_pos {ε : ℝ} (hε : 0 < ε) : 0 < rootParameter ε :=
  Real.rpow_pos_of_pos hε _
theorem rootParameter_le_one {ε : ℝ} (hε : 0 ≤ ε) (hεone : ε ≤ 1) : rootParameter ε ≤ 1 :=
  Real.rpow_le_one hε hεone (by norm_num)
theorem rootParameter_cube {ε : ℝ} (hε : 0 ≤ ε) : (rootParameter ε) ^ 3 = ε := by
  rw [rootParameter, ← Real.rpow_natCast, ← Real.rpow_mul hε]
  norm_num
theorem rootParameter_rate {ε : ℝ} (hε : 0 ≤ ε) :
    ((rootParameter ε) ^ 5)⁻¹ = Model.rate ε := by
  rw [rootParameter, ← Real.rpow_natCast, ← Real.rpow_mul hε, ← Real.rpow_neg hε]
  norm_num [Model.rate]

theorem calibrated_totalCap {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) :
    ((epochCap (rootParameter ε) * (9 * phaseCap (rootParameter ε) ε + 3) : ℕ) : ℝ) ≤
      61920 * Model.rate ε * Real.log (2 / ε) := by
  have hh := totalCap_bound (rootParameter_pos hε) (rootParameter_le_one hε.le hεone) hε hεone
  simpa only [div_eq_mul_inv, rootParameter_rate hε.le] using hh

theorem calibrated_decrease {ε : ℝ} (hε : 0 < ε) :
    (rootParameter ε) ^ 4 / 256 ≤ ε ^ 2 / (5 * (rootParameter ε) ^ 2) := by
  have hr := rootParameter_pos hε
  have hc := rootParameter_cube hε.le
  apply (le_div_iff₀ (by positivity : 0 < 5 * (rootParameter ε) ^ 2)).2
  conv_rhs => rw [← hc]
  nlinarith [pow_nonneg hr.le 6]

theorem smoothUpper_mono {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {L M : ℝ} (h : SmoothUpper f L) (hLM : L ≤ M) :
    SmoothUpper f M := by
  intro x y
  have hm := mul_le_mul_of_nonneg_right hLM (sq_nonneg ‖y - x‖)
  have hh := h x y
  linarith

end MatchingBounds1005.CUPG
