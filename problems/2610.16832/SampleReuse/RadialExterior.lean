import SampleReuse.RadialGeometry
import SampleReuse.Model

open RandomizedFO2003.Calculus
open scoped InnerProductSpace Topology

namespace SampleReuse
noncomputable section

theorem radialCutoff_deriv_nonpos (r : ℝ) : deriv radialCutoff r ≤ 0 := by
  have hd := ((radialCutoff_contDiff 1).differentiable (by norm_num) r).hasDerivAt
  apply le_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht'.le)
    (sub_nonpos.mpr (radialCutoff_antitone (show r ≤ r+t by linarith)))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def radialUnit (x : E) : E := ‖x‖⁻¹ • x

omit [CompleteSpace E] in
theorem radialUnit_norm {x : E} (hx : x ≠ 0) : ‖radialUnit x‖ = 1 := by
  rw [radialUnit, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

omit [CompleteSpace E] in
theorem inner_radialUnit_self {x : E} (hx : x ≠ 0) : ⟪x,radialUnit x⟫_ℝ = ‖x‖ := by
  rw [radialUnit, real_inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp
  ring

theorem radialGlobalization_gradient {f : E → ℝ} (hf : Differentiable ℝ f)
    (b : ℝ) {R : ℝ} (hR : 0 < R) {x : E} (hx : x ≠ 0) :
    gradient (radialGlobalization f b R) x =
      radialCutoff (‖x‖/R) • gradient f x +
      f x • ((deriv radialCutoff (‖x‖/R)/R/‖x‖) • x) +
      (b*radialRise (‖x‖/R)/‖x‖) • x := by
  have hc := ((radialCutoffLoss_contDiff (E := E) hR 1).differentiable (by norm_num) x).hasGradientAt
  have hw := ((radialWallLoss_contDiff (E := E) b hR 1).differentiable (by norm_num) x).hasGradientAt
  have hh := (hasGradientAt_add (hasGradientAt_mul hc (hf x).hasGradientAt) hw).gradient
  rw [radialWallLoss_gradient b hR hx, radialCutoffLoss_gradient R hx] at hh
  exact hh

theorem radialGlobalization_radial_derivative {f : E → ℝ} (hf : Differentiable ℝ f)
    (b : ℝ) {R : ℝ} (hR : 0 < R) {x : E} (hx : x ≠ 0) :
    ⟪gradient (radialGlobalization f b R) x,radialUnit x⟫_ℝ =
      radialCutoff (‖x‖/R)*⟪gradient f x,radialUnit x⟫_ℝ +
      f x*deriv radialCutoff (‖x‖/R)/R + b*radialRise (‖x‖/R) := by
  rw [radialGlobalization_gradient hf b hR hx]
  simp only [inner_add_left, real_inner_smul_left, inner_radialUnit_self hx]
  field_simp
  ring

/-- Every exterior point has a large actual gradient; query norms are unrestricted. -/
theorem radialGlobalization_exterior_gradient {f : E → ℝ} (hf : Differentiable ℝ f)
    {b B R : ℝ} (hR : 0 < R) (hB : 0 ≤ B) {x : E} (hx : R ≤ ‖x‖)
    (hf0 : f x ≤ 0) (hgrad : ‖gradient f x‖ ≤ B) :
    b-B ≤ ‖gradient (radialGlobalization f b R) x‖ := by
  have hxn : x ≠ 0 := norm_pos_iff.mp (hR.trans_le hx)
  have hi : -B ≤ ⟪gradient f x,radialUnit x⟫_ℝ := by
    have hh := abs_real_inner_le_norm (gradient f x) (radialUnit x)
    rw [radialUnit_norm hxn, mul_one] at hh
    exact (abs_le.mp (hh.trans hgrad)).1
  have hc := radialCutoff_mem (‖x‖/R)
  have hm := mul_le_mul_of_nonneg_left hi hc.1
  have hcB := mul_le_mul_of_nonneg_right hc.2 hB
  have hcut : 0 ≤ f x*deriv radialCutoff (‖x‖/R)/R :=
    div_nonneg (mul_nonneg_of_nonpos_of_nonpos hf0 (radialCutoff_deriv_nonpos _)) hR.le
  have he := radialGlobalization_radial_derivative hf b hR hxn
  rw [radialRise_one ((le_div_iff₀ hR).mpr (by simpa using hx)), mul_one] at he
  have hh := real_inner_le_norm (gradient (radialGlobalization f b R) x) (radialUnit x)
  rw [radialUnit_norm hxn, mul_one] at hh
  linarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem radialGlobalization_lower {f : E → ℝ} {b R D : ℝ}
    (hb : 0 ≤ b) (hR : 0 < R) (hD : 0 ≤ D) (x : E) (hf : -D ≤ f x) :
    -D ≤ radialGlobalization f b R x := by
  have hc := radialCutoff_mem (‖x‖/R)
  have hw := radialWall_nonneg hb hR (norm_nonneg x)
  have hm := mul_le_mul_of_nonneg_left hf hc.1
  have hD' := mul_le_mul_of_nonneg_right hc.2 hD
  dsimp [radialGlobalization, radialCutoffLoss, radialWallLoss]
  nlinarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem radialGlobalization_zero {f : E → ℝ} (hf : f 0 = 0)
    (b : ℝ) {R : ℝ} (hR : 0 < R) : radialGlobalization f b R 0 = 0 := by
  simp only [radialGlobalization, radialCutoffLoss, radialWallLoss, norm_zero, hf, mul_zero,
    zero_add, radialWall_zero b hR (by positivity : (0:ℝ) ≤ R/2)]

end
end SampleReuse
