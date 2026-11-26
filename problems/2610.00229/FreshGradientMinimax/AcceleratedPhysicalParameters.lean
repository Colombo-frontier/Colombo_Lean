import FreshGradientMinimax.AcceleratedCompressionParameters
import FreshGradientMinimax.RobinCoefficients

/-! The original physical length and value scales from E.4. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def acceleratedLengthScale (L ε : ℝ) : ℝ := 8 * acceleratedSmoothnessConstant * ε / (primalRidgeConstant * L)
def acceleratedValueScale (L ε : ℝ) : ℝ := 32 * acceleratedSmoothnessConstant * ε ^ 2 / (primalRidgeConstant ^ 2 * L)
def acceleratedValueCoefficient : ℝ := 32 * acceleratedSmoothnessConstant / primalRidgeConstant ^ 2

theorem acceleratedSmoothnessConstant_pos : 0 < acceleratedSmoothnessConstant := by norm_num [acceleratedSmoothnessConstant]

theorem acceleratedLengthScale_pos {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) : 0 < acceleratedLengthScale L ε :=
  div_pos (mul_pos (mul_pos (by norm_num) acceleratedSmoothnessConstant_pos) hε) (mul_pos primalRidgeConstant_pos hL)

theorem acceleratedValueScale_pos {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) : 0 < acceleratedValueScale L ε :=
  div_pos (mul_pos (mul_pos (by norm_num) acceleratedSmoothnessConstant_pos) (sq_pos_of_pos hε))
    (mul_pos (sq_pos_of_pos primalRidgeConstant_pos) hL)

theorem acceleratedValueCoefficient_pos : 0 < acceleratedValueCoefficient :=
  div_pos (mul_pos (by norm_num) acceleratedSmoothnessConstant_pos) (sq_pos_of_pos primalRidgeConstant_pos)

theorem acceleratedValueScale_coefficient (L ε : ℝ) :
    acceleratedValueScale L ε = acceleratedValueCoefficient * ε ^ 2 / L := by
  unfold acceleratedValueScale acceleratedValueCoefficient
  ring

theorem acceleratedScale_ratio {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    acceleratedValueScale L ε / acceleratedLengthScale L ε ^ 2 = L / (2 * acceleratedSmoothnessConstant) := by
  unfold acceleratedValueScale acceleratedLengthScale
  field_simp [hL.ne', hε.ne', primalRidgeConstant_pos.ne', acceleratedSmoothnessConstant_pos.ne']
  ring

theorem acceleratedScale_gradient_ratio {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    acceleratedValueScale L ε / acceleratedLengthScale L ε = 4 * ε / primalRidgeConstant := by
  unfold acceleratedValueScale acceleratedLengthScale
  field_simp [hL.ne', hε.ne', primalRidgeConstant_pos.ne', acceleratedSmoothnessConstant_pos.ne']
  ring

theorem acceleratedScale_smoothness {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    acceleratedValueScale L ε * acceleratedSmoothnessConstant / acceleratedLengthScale L ε ^ 2 = L / 2 := by
  rw [mul_div_right_comm, acceleratedScale_ratio hL hε]
  field_simp [acceleratedSmoothnessConstant_pos.ne']
  ring

theorem acceleratedScale_strongConcavity {n : ℕ} {L ε μ : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hn : (n + 2 : ℝ) ^ 2 ≤ L / (4 * acceleratedSmoothnessConstant * μ)) :
    2 * μ ≤ acceleratedValueScale L ε * robinStep (n + 2) ^ 2 / acceleratedLengthScale L ε ^ 2 := by
  have hN : 0 < (n + 2 : ℝ) := by positivity
  have hA := acceleratedSmoothnessConstant_pos
  have he : acceleratedValueScale L ε * robinStep (n + 2) ^ 2 / acceleratedLengthScale L ε ^ 2 =
      L / (2 * acceleratedSmoothnessConstant * (n + 2 : ℝ) ^ 2) := by
    rw [mul_div_right_comm, acceleratedScale_ratio hL hε]
    unfold robinStep
    push_cast
    simp only [div_eq_mul_inv, inv_pow, mul_inv_rev]
    ring
  rw [he]
  apply (le_div_iff₀ (by positivity)).mpr
  have h := (le_div_iff₀ (by positivity : 0 < 4 * acceleratedSmoothnessConstant * μ)).mp hn
  nlinarith only [h]

end FreshGradientMinimax
