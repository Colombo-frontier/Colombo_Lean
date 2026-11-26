import NCConcave16991.ConeSmoothRules
import NCConcave16991.DenseSmoothRadialGradient
import NCConcave16991.DenseSmoothRadialDerivativeBounds

/-! # An explicit admissible C∞ gate for the Appendix C radial chain

The gate has the paper's exact thresholds 5/32 and 9/32. We use the
already constructed concrete unit-mass density rather than the paper's
particular mollified triangular density; all quantitative bounds below
are proved for this actual function.
-/

noncomputable section

namespace NCConcave16991.DenseSmooth

open ConePrimitives ConeSmooth Set
open scoped ContDiff

def gate (s : ℝ) : ℝ := omega (8 * s - 5 / 4)
def gateD (s : ℝ) : ℝ := 8 * density (8 * s - 5 / 4)

theorem gate_contDiff : ContDiff ℝ ∞ gate := omega_contDiff.comp (by fun_prop)
theorem gateD_contDiff : ContDiff ℝ ∞ gateD := contDiff_const.mul (density_contDiff.comp (by fun_prop))

theorem gate_hasDerivAt (s : ℝ) : HasDerivAt gate (gateD s) s := by
  convert (omega_hasDerivAt (8 * s - 5 / 4)).comp s
    (((hasDerivAt_id s).const_mul 8).sub_const (5 / 4)) using 1
  · rfl
  · simp only [gateD]; ring

theorem gateD_hasDerivAt (s : ℝ) :
    HasDerivAt gateD (64 * deriv density (8 * s - 5 / 4)) s := by
  convert ((density_contDiff.differentiable (by simp) (8 * s - 5 / 4)).hasDerivAt.comp s
    (((hasDerivAt_id s).const_mul 8).sub_const (5 / 4))).const_mul 8 using 1
  · rfl
  · ring

theorem gate_mem_Icc (s : ℝ) : gate s ∈ Icc (0 : ℝ) 1 := ⟨omega_nonneg _, omega_le_one _⟩
theorem gateD_nonneg (s : ℝ) : 0 ≤ gateD s := mul_nonneg (by norm_num) (density_nonneg _)
theorem gateD_le (s : ℝ) : gateD s ≤ 16 := by
  have hh := density_le_two (8 * s - 5 / 4)
  unfold gateD
  linarith

theorem gate_zero {s : ℝ} (hs : s ≤ 5 / 32) : gate s = 0 := omega_zero (by linarith)
theorem gate_one {s : ℝ} (hs : 9 / 32 ≤ s) : gate s = 1 := omega_one (by linarith)
theorem gateD_zero_left {s : ℝ} (hs : s ≤ 5 / 32) : gateD s = 0 := by
  rw [gateD, density_zero_left (by linarith)]
  ring
theorem gateD_zero_right {s : ℝ} (hs : 9 / 32 ≤ s) : gateD s = 0 := by
  rw [gateD, density_zero_right (by linarith)]
  ring

theorem gateD_sub_bound (x y : ℝ) :
    |gateD x - gateD y| ≤ (64 * densitySlopeBound) * |x - y| := by
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (𝕜 := ℝ)
    (f := gateD) (fun t _ ↦ (gateD_hasDerivAt t).differentiableAt)
    (fun t _ ↦ by
      rw [(gateD_hasDerivAt t).deriv, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 64)]
      exact mul_le_mul_of_nonneg_left (density_deriv_bound _) (by norm_num))
    convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs] using hh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem radialCoordinate_contDiff (u : E) : ContDiff ℝ ∞ (radialCoordinate u) := by
  exact (contDiff_const.inner ℝ contDiff_id).div
    ((contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun x ↦ by positivity))
    (fun x ↦ by positivity)

theorem radialCoordinateGradient_sub_bound (u : E) (hu : ‖u‖ = 1) (x y : E) :
    ‖radialCoordinateGradient u x - radialCoordinateGradient u y‖ ≤ 2 * ‖x - y‖ := by
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (s := univ) (𝕜 := ℝ)
    (f := radialCoordinateGradient u)
    (fun z _ ↦ (hasFDerivAt_radialCoordinateGradient u z).differentiableAt)
    (fun z _ ↦ by
      rw [(hasFDerivAt_radialCoordinateGradient u z).fderiv]
      exact norm_radialHessian_le_two hu z) convex_univ (mem_univ y) (mem_univ x)

theorem radialCoordinate_derivativeBound (u : E) (hu : ‖u‖ = 1) :
    DerivativeBound (radialCoordinate u) 1 2 := by
  refine ⟨radialCoordinate_contDiff u, by norm_num, by norm_num, ?_, ?_⟩
  · intro x
    rw [(hasFDerivAt_radialCoordinate u x).fderiv, innerSL_apply_norm]
    exact norm_radialCoordinateGradient_le_one hu x
  · intro x y
    rw [(hasFDerivAt_radialCoordinate u x).fderiv, (hasFDerivAt_radialCoordinate u y).fderiv,
      ← map_sub, innerSL_apply_norm]
    exact radialCoordinateGradient_sub_bound u hu x y

end NCConcave16991.DenseSmooth
