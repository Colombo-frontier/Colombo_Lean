import Geode.Parameters
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The small-radius and large-radius interpretation of the curvature factor.
At zero the limit is punctured: the totalized quotient itself is zero at zero. -/
namespace Geode

open Filter
open scoped Topology

theorem curvatureFactor_punctured_zero :
    Tendsto curvatureFactor (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have hs : Tendsto (fun R : ℝ => Real.sinh R / R) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa only [Real.cosh_zero, Real.sinh_zero, zero_add, sub_zero, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using (Real.hasDerivAt_sinh 0).tendsto_slope_zero
  have hc : Tendsto Real.cosh (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa only [Real.cosh_zero] using
      (Real.continuous_cosh.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have h := hc.div hs (by norm_num : (1 : ℝ) ≠ 0)
  change Tendsto (fun R : ℝ => Real.cosh R / (Real.sinh R / R))
    (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 1)) at h
  have heq : (fun R : ℝ => Real.cosh R / (Real.sinh R / R)) = curvatureFactor := by
    funext R
    simp only [curvatureFactor, Real.tanh_eq_sinh_div_cosh, div_div_eq_mul_div]
    ring
  simpa only [heq, div_one] using h

theorem curvatureFactor_right_zero :
    Tendsto curvatureFactor (𝓝[>] (0 : ℝ)) (𝓝 1) :=
  curvatureFactor_punctured_zero.mono_left (nhdsGT_le_nhdsNE 0)

theorem radius_le_curvatureFactor {R : ℝ} (hR : 0 < R) : R ≤ curvatureFactor R := by
  have hs : 0 < Real.sinh R := Real.sinh_pos_iff.mpr hR
  have hsc : Real.sinh R ≤ Real.cosh R := by
    have he := Real.exp_pos (-R)
    have h := Real.cosh_sub_sinh R
    linarith only [he, h]
  rw [curvatureFactor, Real.tanh_eq_sinh_div_cosh, div_div_eq_mul_div, le_div_iff₀ hs]
  exact mul_le_mul_of_nonneg_left hsc hR.le

theorem curvatureFactor_ratio_atTop :
    Tendsto (fun R : ℝ => curvatureFactor R / R) atTop (𝓝 1) := by
  have hu : Tendsto (fun R : ℝ => 1 + R⁻¹) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0))
  apply tendsto_const_nhds.squeeze' hu
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact (one_le_div hR).mpr (radius_le_curvatureFactor hR)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    calc
      curvatureFactor R / R ≤ (R + 1) / R :=
        div_le_div_of_nonneg_right (curvatureFactor_le_radius_add_one hR) hR.le
      _ = 1 + R⁻¹ := by rw [add_div, div_self hR.ne', one_div]

end Geode
