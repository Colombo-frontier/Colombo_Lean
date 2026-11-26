import SecondOrder.SampledShiftedHessian

open MeasureTheory Filter
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

theorem shiftedHessian_apply_sub {d : ℕ} (B : ℝ) (H K : Point d →L[ℝ] Point d)
    (v : Point d) : shiftedHessian B H v - shiftedHessian B K v =
      -((2 * B)⁻¹ • ((H - K) v)) := by
  simp only [shiftedHessian_apply, ContinuousLinearMap.sub_apply, smul_sub]
  abel

theorem shiftedHessian_error_sq {d : ℕ} (B : ℝ) (H K : Point d →L[ℝ] Point d)
    (v : Point d) : ‖shiftedHessian B H v - shiftedHessian B K v‖^2 =
      ((2 * B)⁻¹)^2 * ‖(H - K) v‖^2 := by
  rw [shiftedHessian_apply_sub, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.shifted_hvp_error_integrable (h : CommonLoss μ P ν F f)
    (x v : Point d) : Integrable (fun z => ‖sampledShiftedHessian P f x z v -
      shiftedHessian (eigenHessianBound P) (hessian F x) v‖^2) μ := by
  simp only [sampledShiftedHessian, shiftedHessian_error_sq]
  exact (h.hvp_error_integrable x v).const_mul _

theorem CommonLoss.shifted_hvp_variance (h : CommonLoss μ P ν F f) (x v : Point d) :
    (∫ z, ‖sampledShiftedHessian P f x z v -
      shiftedHessian (eigenHessianBound P) (hessian F x) v‖^2 ∂μ) ≤
        (P.hessianNoise^2 / (4 * eigenHessianBound P ^ 2)) * ‖v‖^2 := by
  simp only [sampledShiftedHessian, shiftedHessian_error_sq]
  rw [integral_const_mul]
  calc
    _ ≤ ((2 * eigenHessianBound P)⁻¹)^2 * (P.hessianNoise^2 * ‖v‖^2) :=
      mul_le_mul_of_nonneg_left (h.hvp_variance x v) (sq_nonneg _)
    _ = _ := by ring

/-- The oracle's uniform error bound survives the shift with exact scaling. -/
theorem CommonLoss.shifted_hvp_error_bound (h : CommonLoss μ P ν F f) :
    ∀ᵐ z ∂μ, ∀ (x v : Point d),
      ‖sampledShiftedHessian P f x z v -
        shiftedHessian (eigenHessianBound P) (hessian F x) v‖ ≤
          (P.hessianBound / (2 * eigenHessianBound P)) * ‖v‖ := by
  filter_upwards [h.global_hessian_bound] with z hz
  intro x v
  have hB := eigenHessianBound_pos P
  rw [sampledShiftedHessian, shiftedHessian_apply_sub, norm_neg, norm_smul,
    Real.norm_of_nonneg (by positivity : 0 ≤ (2 * eigenHessianBound P)⁻¹)]
  have hv : ‖(hessian (f z) x - hessian F x) v‖ ≤ P.hessianBound * ‖v‖ :=
    ((hessian (f z) x - hessian F x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hz x) (norm_nonneg _))
  calc
    _ ≤ (2 * eigenHessianBound P)⁻¹ * (P.hessianBound * ‖v‖) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    _ = _ := by ring

/-- For every fixed past, the next unnormalized innovation has mean zero.
The point and direction may be arbitrary functions of that past. -/
theorem CommonLoss.shifted_hvp_fresh_centered {A : Type*}
    (h : CommonLoss μ P ν F f) (x v : A → Point d) (a : A) :
    (∫ z, (sampledShiftedHessian P f (x a) z (v a) -
      shiftedHessian (eigenHessianBound P) (hessian F (x a)) (v a)) ∂μ) = 0 := by
  rw [integral_sub (h.shifted_hvp_integrable (x a) (v a)) (integrable_const _),
    h.shifted_hvp_unbiased]
  simp

end
end SecondOrder
