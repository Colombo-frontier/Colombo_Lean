import RandomizedFO2003.SmoothSaturation
import RandomizedFO2003.GradientCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace RandomizedFO2003.Cascade

open Primitives Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def forcingReadout (b : E) (D : ℝ) (x : E) : ℝ := inner (𝕜 := ℝ) b x / D

noncomputable def forcing (b : E) (D C₀ K : ℝ) (x : E) : ℝ :=
  D * (C₀ + saturation K (forcingReadout b D x))

theorem forcing_contDiff (b : E) (D C₀ K : ℝ) (n : ℕ) : ContDiff ℝ n (forcing b D C₀ K) :=
  contDiff_const.mul (contDiff_const.add ((saturation_contDiff K n).comp
    ((contDiff_const.inner ℝ contDiff_id).div_const D)))

theorem forcing_bounds (b : E) {D C₀ K : ℝ} (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hC : K + 2 ≤ C₀) (x : E) : D ≤ forcing b D C₀ K x ∧ forcing b D C₀ K x ≤ D * (C₀ + K + 1) := by
  have hs := abs_le.mp (Primitives.saturation_bound hK (forcingReadout b D x))
  dsimp only [forcing]
  constructor
  · calc
      D = D * 1 := (mul_one D).symm
      _ ≤ D * (C₀ + saturation K (forcingReadout b D x)) := mul_le_mul_of_nonneg_left (by linarith) hD
  · apply mul_le_mul_of_nonneg_left _ hD
    linarith

@[simp] theorem forcing_zero (b : E) (D C₀ K : ℝ) : forcing b D C₀ K 0 = D * C₀ := by
  simp [forcing, forcingReadout]

theorem forcingReadout_hasFDerivAt (b : E) (D : ℝ) (x : E) :
    HasFDerivAt (forcingReadout b D) (D⁻¹ • innerSL ℝ b) x := by
  convert (D⁻¹ • innerSL ℝ b).hasFDerivAt (x := x) using 1
  ext y
  change inner (𝕜 := ℝ) b y / D = D⁻¹ * inner (𝕜 := ℝ) b y
  rw [div_eq_mul_inv, mul_comm]

variable [CompleteSpace E]

theorem forcing_hasGradientAt (b : E) {D : ℝ} (hD : D ≠ 0) (C₀ K : ℝ) (x : E) :
    HasGradientAt (forcing b D C₀ K)
      (saturationSlope K (forcingReadout b D x) • b) x := by
  have hs := (saturation_hasDerivAt K (forcingReadout b D x)).comp_hasFDerivAt x
    (forcingReadout_hasFDerivAt b D x)
  apply hasGradientAt_of_pairing ((hs.const_add C₀).const_mul D)
  intro v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, real_inner_smul_left]
  change D * (saturationSlope K (forcingReadout b D x) * (D⁻¹ * inner (𝕜 := ℝ) b v)) = _
  field_simp

theorem forcing_gradient (b : E) {D : ℝ} (hD : D ≠ 0) (C₀ K : ℝ) (x : E) :
    gradient (forcing b D C₀ K) x = saturationSlope K (forcingReadout b D x) • b :=
  (forcing_hasGradientAt b hD C₀ K x).gradient

theorem forcing_gradient_norm_le (b : E) {D K : ℝ} (hD : D ≠ 0) (hK : 0 ≤ K) (C₀ : ℝ) (x : E) :
    ‖gradient (forcing b D C₀ K) x‖ ≤ ‖b‖ := by
  rw [forcing_gradient b hD C₀ K x, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (saturationSlope_mem K hK _).1]
  exact mul_le_of_le_one_left (norm_nonneg b) (saturationSlope_mem K hK _).2

theorem forcing_gradient_linear_region (b : E) {D K : ℝ} (hD : D ≠ 0) (C₀ : ℝ) (x : E)
    (hx : |forcingReadout b D x| ≤ K) : gradient (forcing b D C₀ K) x = b := by
  rw [forcing_gradient b hD C₀ K x, saturationSlope_one hx, one_smul]

end RandomizedFO2003.Cascade
