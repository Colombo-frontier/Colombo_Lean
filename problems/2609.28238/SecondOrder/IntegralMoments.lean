import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

open MeasureTheory
open scoped InnerProductSpace

namespace SecondOrder

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Squared-error integrability follows from the original second moment. -/
theorem integrable_norm_sub_sq {X : Ω → E} (hX : Integrable X μ)
    (hX2 : Integrable (fun w => ‖X w‖^2) μ) (c : E) :
    Integrable (fun w => ‖X w-c‖^2) μ := by
  have h := (hX2.sub ((hX.inner_const c).const_mul 2)).add (integrable_const (‖c‖^2))
  simpa only [norm_sub_sq_real] using h

/-- Exact second-moment shift identity for arbitrary probability spaces. -/
theorem integral_norm_sub_sq {X : Ω → E} (hX : Integrable X μ)
    (hX2 : Integrable (fun w => ‖X w‖^2) μ) (c : E) :
    (∫ w, ‖X w-c‖^2 ∂μ) = (∫ w, ‖X w‖^2 ∂μ) -
      2*⟪c,∫ w, X w ∂μ⟫_ℝ+‖c‖^2 := by
  have hc (w : Ω) : ⟪X w,c⟫_ℝ = ⟪c,X w⟫_ℝ := real_inner_comm _ _
  simp_rw [norm_sub_sq_real, hc]
  have hcross : Integrable (fun w => 2*⟪c,X w⟫_ℝ) μ := (hX.const_inner c).const_mul 2
  have hsub : Integrable (fun w => ‖X w‖^2-2*⟪c,X w⟫_ℝ) μ := hX2.sub hcross
  rw [integral_add hsub (integrable_const (‖c‖^2)),
    integral_sub hX2 hcross, integral_const_mul, integral_inner hX]
  simp

theorem integral_variance_identity {X : Ω → E} (hX : Integrable X μ)
    (hX2 : Integrable (fun w => ‖X w‖^2) μ) :
    (∫ w, ‖X w-(∫ z, X z ∂μ)‖^2 ∂μ) =
      (∫ w, ‖X w‖^2 ∂μ)-‖∫ w, X w ∂μ‖^2 := by
  rw [integral_norm_sub_sq hX hX2, real_inner_self_eq_norm_sq]
  ring

/-- The Hilbert-space Jensen inequality needed for centered gradient differences. -/
theorem norm_integral_sq_le {X : Ω → E} (hX : Integrable X μ)
    (hX2 : Integrable (fun w => ‖X w‖^2) μ) :
    ‖∫ w, X w ∂μ‖^2 ≤ ∫ w, ‖X w‖^2 ∂μ := by
  have h := integral_nonneg (μ := μ) (fun w => sq_nonneg ‖X w-(∫ z, X z ∂μ)‖)
  rw [integral_variance_identity hX hX2] at h
  linarith

theorem integral_variance_le_second_moment {X : Ω → E} (hX : Integrable X μ)
    (hX2 : Integrable (fun w => ‖X w‖^2) μ) :
    (∫ w, ‖X w-(∫ z, X z ∂μ)‖^2 ∂μ) ≤ ∫ w, ‖X w‖^2 ∂μ := by
  rw [integral_variance_identity hX hX2]
  exact sub_le_self _ (sq_nonneg _)

/-- Recenter a square-integrable zero-mean error without losing its variance. -/
theorem integral_norm_add_sq_of_mean_zero {X : Ω → E} (hX : Integrable X μ)
    (hX2 : Integrable (fun w => ‖X w‖^2) μ) (hmean : (∫ w, X w ∂μ) = 0) (c : E) :
    (∫ w, ‖X w+c‖^2 ∂μ) = (∫ w, ‖X w‖^2 ∂μ)+‖c‖^2 := by
  simpa only [sub_neg_eq_add, hmean, inner_zero_right, mul_zero, sub_zero, norm_neg] using
    integral_norm_sub_sq hX hX2 (-c)

/-- Conditional variance identity with a specified conditional mean. -/
theorem integral_conditional_variance {X : Ω → E} {a c : E}
    (hX : Integrable X μ) (he : Integrable (fun w => ‖X w-a‖^2) μ)
    (hm : (∫ w, X w ∂μ) = a) :
    (∫ w, ‖X w-c‖^2 ∂μ) = (∫ w, ‖X w-a‖^2 ∂μ)+‖a-c‖^2 := by
  have hcenter : (∫ w, X w-a ∂μ) = 0 := by
    rw [integral_sub hX (integrable_const _),hm]
    simp
  have h := integral_norm_add_sq_of_mean_zero (hX.sub (integrable_const a)) he hcenter (a-c)
  simpa only [Pi.sub_apply, sub_add_sub_cancel] using h

end SecondOrder
