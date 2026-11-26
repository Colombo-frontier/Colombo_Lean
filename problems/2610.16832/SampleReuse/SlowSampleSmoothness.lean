import SampleReuse.SlowSamplePayload
import SampleReuse.SlowScale

/-! Uniform sample-wise smoothness of the actual slowly scaled conservative loss. -/

open SecondOrder
namespace SampleReuse
noncomputable section
variable {d T : ℕ}

theorem firstOrderRandomLoss_third_uniform (Θ : Fin (T + 1) → Fin d → Bool)
    (hd : 0 < d) (R : ℝ) (hR : 2 ≤ R) (z : FirstOrderCoefficients d T R)
    (x : FirstOrderSpace d T) :
    ‖iteratedFDeriv ℝ 3 (firstOrderRandomLoss Θ z) x‖ ≤
      (firstOrderGeometryConstant + sampleNoiseThirdConstant * (R + 1)) * Real.sqrt d := by
  change ‖iteratedFDeriv ℝ 3 (fun y => firstOrderChain Θ y + firstOrderChainNoise Θ z y) x‖ ≤ _
  rw [iteratedFDeriv_add_apply' (firstOrderChain_contDiff Θ).contDiffAt
    (firstOrderChainNoise_contDiff Θ z).contDiffAt]
  exact ((norm_add_le _ _).trans (add_le_add (firstOrderChain_third_bound Θ hd x)
    (firstOrderChainNoise_third_uniform Θ hd R hR z x))).trans_eq (by ring)

theorem scaledFirstOrderSample_third_uniform (Θ : Fin (T + 1) → Fin d → Bool)
    (hd : 0 < d) {A β : ℝ} (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (R : ℝ) (hR : 2 ≤ R) (z : FirstOrderCoefficients d T R)
    (x : Point (FirstOrderDimension d T)) :
    ‖iteratedFDeriv ℝ 3 (scaledFirstOrderSample Θ A β z) x‖ ≤
      A * β ^ 3 * ((firstOrderGeometryConstant + sampleNoiseThirdConstant * (R + 1)) * Real.sqrt d) := by
  have hRp : 0 ≤ R + 1 := by linarith
  have hgeom := firstOrderGeometryConstant_pos.le
  have hnoise := sampleNoiseThirdConstant_pos.le
  exact scalarLinearScaling_iterated_bound_of_le _ hA hβ (by positivity)
    (firstOrderDilation d T β)
    (by simpa only [abs_of_nonneg hβ] using firstOrderDilation_norm d T β) 3
    (firstOrderRandomLoss_contDiff Θ z) x
    (firstOrderRandomLoss_third_uniform Θ hd R hR z _)

theorem scaledFirstOrderSample_second_uniform (Θ : Fin (T + 1) → Fin d → Bool)
    (hd : 0 < d) {A β : ℝ} (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (R : ℝ) (hR : 2 ≤ R) (z : FirstOrderCoefficients d T R)
    (x : Point (FirstOrderDimension d T)) :
    ‖hessian (scaledFirstOrderSample Θ A β z) x‖ ≤
      A * β ^ 2 * (firstOrderGeometryConstant + firstOrderNoiseConstant * (R + 1)) := by
  have hh := (scaledFirstOrderSample_error_bounds Θ hd hA hβ R hR z x).2.2
  have hp := (scaledFirstOrderPopulation_derivative_bounds Θ hd hA hβ x).1
  calc
    _ = ‖(hessian (scaledFirstOrderSample Θ A β z) x - hessian (scaledFirstOrderPopulation Θ A β) x) +
        hessian (scaledFirstOrderPopulation Θ A β) x‖ := by rw [sub_add_cancel]
    _ ≤ _ := ((norm_add_le _ _).trans (add_le_add hh hp)).trans_eq (by ring)

/-- The slow dilation cancels sqrt(d) in the uniform third derivative after
amplitude scaling. This is the new sample-wise regularity mechanism. -/
theorem slow_sample_derivative_bounds (Θ : Fin (T + 1) → Fin d → Bool)
    (hd : 0 < d) {A : ℝ} (hA : 0 ≤ A) (R : ℝ) (hR : 2 ≤ R)
    (z : FirstOrderCoefficients d T R) (x : Point (FirstOrderDimension d T)) :
    ‖hessian (scaledFirstOrderSample Θ A (slowDilation d) z) x‖ ≤
      A * (Real.sqrt d)⁻¹ * (firstOrderGeometryConstant + firstOrderNoiseConstant * (R + 1)) ∧
    ‖iteratedFDeriv ℝ 3 (scaledFirstOrderSample Θ A (slowDilation d) z) x‖ ≤
      A * slowDilation d * (firstOrderGeometryConstant + sampleNoiseThirdConstant * (R + 1)) := by
  have hβ : 0 ≤ slowDilation d := inv_nonneg.mpr (slowAlpha_pos hd).le
  constructor
  · simpa only [slowDilation_sq] using scaledFirstOrderSample_second_uniform Θ hd hA hβ R hR z x
  · calc
      _ ≤ A * slowDilation d ^ 3 *
          ((firstOrderGeometryConstant + sampleNoiseThirdConstant * (R + 1)) * Real.sqrt d) :=
        scaledFirstOrderSample_third_uniform Θ hd hA hβ R hR z x
      _ = A * (slowDilation d ^ 3 * Real.sqrt d) *
          (firstOrderGeometryConstant + sampleNoiseThirdConstant * (R + 1)) := by ring
      _ = _ := by rw [slowDilation_cubic hd]

theorem slow_sample_gradient_lipschitz (Θ : Fin (T + 1) → Fin d → Bool)
    (hd : 0 < d) {A : ℝ} (hA : 0 ≤ A) (R : ℝ) (hR : 2 ≤ R)
    (z : FirstOrderCoefficients d T R) (x y : Point (FirstOrderDimension d T)) :
    ‖gradient (scaledFirstOrderSample Θ A (slowDilation d) z) x -
      gradient (scaledFirstOrderSample Θ A (slowDilation d) z) y‖ ≤
      (A * (Real.sqrt d)⁻¹ * (firstOrderGeometryConstant + firstOrderNoiseConstant * (R + 1))) * ‖x - y‖ := by
  apply gradient_lipschitz_of_second_bound
    ((scaledFirstOrderSample_contDiff Θ A (slowDilation d) z).of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)) _ y x
  intro w
  simpa only [hessian, norm_fderiv_gradient] using (slow_sample_derivative_bounds Θ hd hA R hR z w).1

theorem slow_sample_hessian_lipschitz (Θ : Fin (T + 1) → Fin d → Bool)
    (hd : 0 < d) {A : ℝ} (hA : 0 ≤ A) (R : ℝ) (hR : 2 ≤ R)
    (z : FirstOrderCoefficients d T R) (x y : Point (FirstOrderDimension d T)) :
    ‖hessian (scaledFirstOrderSample Θ A (slowDilation d) z) x -
      hessian (scaledFirstOrderSample Θ A (slowDilation d) z) y‖ ≤
      (A * slowDilation d * (firstOrderGeometryConstant + sampleNoiseThirdConstant * (R + 1))) * ‖x - y‖ :=
  fderiv_gradient_lipschitz_of_third_bound (scaledFirstOrderSample_contDiff Θ A (slowDilation d) z)
    (fun w => (slow_sample_derivative_bounds Θ hd hA R hR z w).2) y x

end
end SampleReuse
