import NCBall.GaussianMaximum
import NCBall.NoiseEmbedding

/-! # The original good event, with an explicit logarithmic dimension condition -/

noncomputable section
open MeasureTheory Set
namespace NCBall

theorem gaussian_size_from_log {n M : ℕ}
    (hlog : 2 * Real.log (8 * ((M : ℝ) + 1)) ≤ n) :
    (M : ℝ) * Real.exp (-(n : ℝ) / 2) ≤ 1 / 8 := by
  have hp : 0 < 8 * ((M : ℝ) + 1) := by positivity
  have he : 8 * ((M : ℝ) + 1) ≤ Real.exp ((n : ℝ) / 2) := by
    rw [← Real.exp_log hp]
    exact Real.exp_le_exp.mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-(n : ℝ) / 2)).le
  have hid : Real.exp ((n : ℝ) / 2) * Real.exp (-(n : ℝ) / 2) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [hid] at hm
  nlinarith [Real.exp_pos (-(n : ℝ) / 2)]

theorem roomNoise_good_iff {n M : ℕ} (z : Fin M → Fin n → ℝ) :
    (∀ j < M, ‖roomNoise z j‖ ≤ 2) ↔ ∀ j, coordinateNormSq (z j) ≤ 4 := by
  constructor
  · intro h j
    have hj := h j.val j.isLt
    simpa only [roomNoise, dif_pos j.isLt, transverseVector_norm_le_two_iff] using hj
  · intro h j hj
    simpa only [roomNoise, dif_pos hj, transverseVector_norm_le_two_iff] using h ⟨j, hj⟩

/-- Equation (7.3) for the same ambient vectors used by the constructed function. -/
theorem actual_good_event_probability {n M : ℕ} (hn : 0 < n)
    (hlog : 2 * Real.log (8 * ((M : ℝ) + 1)) ≤ n) :
    7 / 8 ≤ (gaussianRooms n M).real {z | ∀ j < M, ‖roomNoise z j‖ ≤ 2} := by
  simpa only [roomNoise_good_iff] using
    gaussianRooms_good_probability hn (gaussian_size_from_log hlog)

end NCBall
