import GradientHessian.GaussianConcentrationDerivative

/-! The weighted integral inequality used in the entropy argument.  It is
proved by integrating a nonnegative square, independently of any assumed
Gaussian concentration or functional inequality. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory

variable {Ω V : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem weighted_integral_norm_square_le {v : Ω → V} {g : Ω → ℝ}
    (hv : Integrable v μ) (hg : Integrable g μ) (hgpos : ∀ᵐ x ∂μ, 0 < g x)
    (hgm : 0 < ∫ x, g x ∂μ)
    (hq : Integrable (fun x => ‖v x‖ ^ 2 / g x) μ) :
    ‖∫ x, v x ∂μ‖ ^ 2 ≤ (∫ x, g x ∂μ) * (∫ x, ‖v x‖ ^ 2 / g x ∂μ) := by
  let A := ∫ x, g x ∂μ
  let B := ∫ x, ‖v x‖ ∂μ
  let C := ∫ x, ‖v x‖ ^ 2 / g x ∂μ
  let c := B / A
  have hA : 0 < A := hgm
  have hB : 0 ≤ B := integral_nonneg (fun x => norm_nonneg (v x))
  have hc : c * A = B := div_mul_cancel₀ B hA.ne'
  have hnonneg : 0 ≤ ∫ x, ‖v x‖ ^ 2 / g x - 2 * c * ‖v x‖ + c ^ 2 * g x ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hgpos] with x hx
    have he : ‖v x‖ ^ 2 / g x - 2 * c * ‖v x‖ + c ^ 2 * g x =
        (‖v x‖ - c * g x) ^ 2 / g x := by field_simp; ring
    rw [he]
    exact div_nonneg (sq_nonneg _) hx.le
  have hqsub : Integrable (fun x => ‖v x‖ ^ 2 / g x - 2 * c * ‖v x‖) μ :=
    hq.sub (hv.norm.const_mul (2 * c))
  rw [integral_add hqsub (hg.const_mul (c ^ 2)),
    integral_sub hq (hv.norm.const_mul (2 * c)), integral_const_mul,
    integral_const_mul] at hnonneg
  change 0 ≤ C - 2 * c * B + c ^ 2 * A at hnonneg
  have hmul := mul_nonneg hnonneg hA.le
  have he : (C - 2 * c * B + c ^ 2 * A) * A = A * C - B ^ 2 := by
    calc
      _ = A * C - 2 * (c * A) * B + (c * A) ^ 2 := by ring
      _ = _ := by rw [hc]; ring
  rw [he] at hmul
  have hbound : B ^ 2 ≤ A * C := by linarith only [hmul]
  exact ((sq_le_sq₀ (norm_nonneg _) hB).mpr (norm_integral_le_integral_norm v)).trans hbound

end GradientHessian.GaussianConcentration
