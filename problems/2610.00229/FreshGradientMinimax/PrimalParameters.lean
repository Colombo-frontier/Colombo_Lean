import FreshGradientMinimax.RadialCompression
import FreshGradientMinimax.CoreLemma

/-! The numerical choices in (28), keeping the paper's constants. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def primalBarrierConstant : ℝ := Real.exp (-(1 / 2 : ℝ))
def primalRidgeConstant : ℝ := primalBarrierConstant / 100
def primalRadiusConstant : ℝ := 10 ^ 9 / primalBarrierConstant
def primalScalingConstant : ℝ := 10 ^ 8
def primalLengthScale (L ε : ℝ) : ℝ := 16 * primalScalingConstant * ε / (primalBarrierConstant * L)
def primalValueScale (L ε : ℝ) : ℝ := 64 * primalScalingConstant * ε ^ 2 / (primalBarrierConstant ^ 2 * L)
def primalCompressionRadius (n : ℕ) (L ε : ℝ) : ℝ :=
  primalRadiusConstant * primalLengthScale L ε * Real.sqrt (n + 1 : ℝ)
def primalRidgeCoefficient (L ε : ℝ) : ℝ :=
  primalValueScale L ε * primalRidgeConstant / primalLengthScale L ε ^ 2

theorem primalBarrierConstant_pos : 0 < primalBarrierConstant := Real.exp_pos _

theorem primalBarrierConstant_le_one : primalBarrierConstant ≤ 1 :=
  Real.exp_le_one_iff.mpr (by norm_num)

theorem primalRidgeConstant_pos : 0 < primalRidgeConstant := div_pos primalBarrierConstant_pos (by norm_num)

theorem primalRidgeConstant_le_one : primalRidgeConstant ≤ 1 := by
  unfold primalRidgeConstant
  linarith only [primalBarrierConstant_le_one]

theorem primalRadiusConstant_lower : 10 ^ 9 ≤ primalRadiusConstant := by
  unfold primalRadiusConstant
  exact (le_div_iff₀ primalBarrierConstant_pos).mpr
    (by nlinarith only [primalBarrierConstant_le_one])

theorem primalRadiusConstant_pos : 0 < primalRadiusConstant := lt_of_lt_of_le (by norm_num) primalRadiusConstant_lower

theorem primalLengthScale_pos {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) : 0 < primalLengthScale L ε := by
  unfold primalLengthScale primalScalingConstant
  exact div_pos (by positivity) (mul_pos primalBarrierConstant_pos hL)

theorem primalValueScale_pos {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) : 0 < primalValueScale L ε := by
  unfold primalValueScale primalScalingConstant
  exact div_pos (by positivity) (mul_pos (sq_pos_of_pos primalBarrierConstant_pos) hL)

theorem primalCompressionRadius_pos (n : ℕ) {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    0 < primalCompressionRadius n L ε := by
  unfold primalCompressionRadius
  exact mul_pos (mul_pos primalRadiusConstant_pos (primalLengthScale_pos hL hε)) (Real.sqrt_pos.mpr (by positivity))

theorem primalRidgeCoefficient_pos {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    0 < primalRidgeCoefficient L ε :=
  div_pos (mul_pos (primalValueScale_pos hL hε) primalRidgeConstant_pos) (sq_pos_of_pos (primalLengthScale_pos hL hε))

theorem primalScale_ratio {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    primalValueScale L ε / primalLengthScale L ε ^ 2 = L / (4 * primalScalingConstant) := by
  unfold primalValueScale primalLengthScale primalScalingConstant
  field_simp [hL.ne', hε.ne', primalBarrierConstant_pos.ne']
  ring

theorem primalScale_gradient_ratio {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    primalValueScale L ε / primalLengthScale L ε = 4 * ε / primalBarrierConstant := by
  unfold primalValueScale primalLengthScale primalScalingConstant
  field_simp [hL.ne', hε.ne', primalBarrierConstant_pos.ne']
  ring

theorem primalScale_xx_bound (n : ℕ) {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    10 ^ 6 * primalValueScale L ε / primalLengthScale L ε ^ 2 +
      24000 * primalValueScale L ε * Real.sqrt (n + 1 : ℝ) /
        (primalLengthScale L ε * primalCompressionRadius n L ε) + primalRidgeCoefficient L ε ≤ L / 4 := by
  have hs : Real.sqrt (n + 1 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity : 0 < (n + 1 : ℝ))).ne'
  have hr := primalLengthScale_pos hL hε
  have hc := primalRadiusConstant_pos
  have he : 24000 * primalValueScale L ε * Real.sqrt (n + 1 : ℝ) /
      (primalLengthScale L ε * primalCompressionRadius n L ε) =
      (24000 / primalRadiusConstant) * (primalValueScale L ε / primalLengthScale L ε ^ 2) := by
    unfold primalCompressionRadius
    field_simp
    ring
  rw [he, show 10 ^ 6 * primalValueScale L ε / primalLengthScale L ε ^ 2 =
    10 ^ 6 * (primalValueScale L ε / primalLengthScale L ε ^ 2) by ring,
    primalRidgeCoefficient, show primalValueScale L ε * primalRidgeConstant / primalLengthScale L ε ^ 2 =
    primalRidgeConstant * (primalValueScale L ε / primalLengthScale L ε ^ 2) by ring,
    primalScale_ratio hL hε]
  have h1 : 24000 / primalRadiusConstant ≤ 24000 :=
    (div_le_iff₀ hc).mpr (by nlinarith only [primalRadiusConstant_lower])
  have h2 := mul_le_mul_of_nonneg_right h1 (by unfold primalScalingConstant; positivity : 0 ≤ L / (4 * primalScalingConstant))
  have h3 := mul_le_mul_of_nonneg_right primalRidgeConstant_le_one
    (by unfold primalScalingConstant; positivity : 0 ≤ L / (4 * primalScalingConstant))
  unfold primalScalingConstant at *
  nlinarith only [h2, h3, hL]

theorem primalScale_xy_bound {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 ≤ μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) :
    2000 * Real.sqrt (μ * primalValueScale L ε) / primalLengthScale L ε ≤ L / 4 := by
  have hr := primalLengthScale_pos hL hε
  have hlam := primalValueScale_pos hL hε
  have he : (Real.sqrt (μ * primalValueScale L ε) / primalLengthScale L ε) ^ 2 =
      μ * (L / (4 * primalScalingConstant)) := by
    rw [div_pow, Real.sq_sqrt (mul_nonneg hμ hlam.le), mul_div_assoc, primalScale_ratio hL hε]
  have h1 := mul_le_mul_of_nonneg_right hm (by unfold primalScalingConstant; positivity : 0 ≤ L / (4 * primalScalingConstant))
  have h2 : Real.sqrt (μ * primalValueScale L ε) / primalLengthScale L ε ≤ L / (4 * primalScalingConstant) := by
    apply (sq_le_sq₀ (by positivity) (by unfold primalScalingConstant; positivity)).mp
    nlinarith only [he, h1]
  unfold primalScalingConstant at h2
  rw [mul_div_assoc]
  nlinarith only [h2, hL]

theorem primalScale_yy_bound {L μ : ℝ} (hL : 0 < L)
    (hm : μ ≤ L / (4 * primalScalingConstant)) : 50 * μ ≤ L / 4 := by
  unfold primalScalingConstant at hm
  linarith only [hm, hL]

end FreshGradientMinimax
