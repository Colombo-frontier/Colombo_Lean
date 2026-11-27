import Mathlib

/-!
Radial extension infrastructure for transferring the proved Gaussian Lipschitz
concentration theorem to the sphere. The extension is constructed by Mathlib's
proved real-valued Lipschitz extension theorem, with a derived radial constant.
-/

open Set Metric
open scoped NNReal ENNReal

namespace Task006.SphereConcentration
noncomputable section

/-- Normalization is locally Lipschitz away from zero, with an explicit
constant derived directly from the norm triangle inequality. -/
theorem norm_normalize_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤ (2 / ‖x‖) * ‖x - y‖ := by
  have ha : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hb : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hvec : ‖x‖⁻¹ • x - ‖y‖⁻¹ • y =
      ‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y := by module
  have hinv : ‖x‖⁻¹ - ‖y‖⁻¹ = (‖y‖ - ‖x‖) / (‖x‖ * ‖y‖) := by
    field_simp
  have habs : |‖x‖⁻¹ - ‖y‖⁻¹| * ‖y‖ = ‖x‖⁻¹ * |‖x‖ - ‖y‖| := by
    rw [hinv, abs_div, abs_mul, abs_of_pos ha, abs_of_pos hb, abs_sub_comm ‖y‖ ‖x‖]
    field_simp
  calc
    ‖NormedSpace.normalize x - NormedSpace.normalize y‖ =
        ‖‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y‖ := by
      rw [NormedSpace.normalize, NormedSpace.normalize, hvec]
    _ ≤ ‖‖x‖⁻¹ • (x - y)‖ + ‖(‖x‖⁻¹ - ‖y‖⁻¹) • y‖ := norm_add_le _ _
    _ = ‖x‖⁻¹ * ‖x - y‖ + ‖x‖⁻¹ * |‖x‖ - ‖y‖| := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_inv, abs_norm, habs]
    _ ≤ ‖x‖⁻¹ * ‖x - y‖ + ‖x‖⁻¹ * ‖x - y‖ := by
      have h := mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) (inv_nonneg.mpr ha.le)
      linarith only [h]
    _ = (2 / ‖x‖) * ‖x - y‖ := by ring

/-- A genuine Lipschitz map on a positive-radius outer annulus. -/
theorem normalize_lipschitzOn_annulus {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℝ} (hr : 0 < r) :
    LipschitzOnWith (Real.toNNReal (2 / r))
      (NormedSpace.normalize : E → E) {x | r ≤ ‖x‖} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (hr.trans_le hx))
  have hy0 : y ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (hr.trans_le hy))
  have h := (norm_normalize_sub_le x y hx0 hy0).trans
    (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hr hx) (norm_nonneg _))
  simpa only [dist_eq_norm, Real.coe_toNNReal (2 / r) (div_nonneg (by norm_num) hr.le)] using h

/-- A sphere-Lipschitz scalar function has an actual global extension of its
radialization outside radius r, with constant 2H/r. -/
theorem exists_radial_lipschitz_extension {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℝ} (hr : 0 < r)
    {H : ℝ≥0} {f : E → ℝ} (hf : LipschitzOnWith H f (sphere (0 : E) 1)) :
    ∃ g : E → ℝ,
      LipschitzWith ((Real.toNNReal (2 / r)) * H) g ∧
      EqOn (fun x => f (NormedSpace.normalize x)) g {x | r ≤ ‖x‖} := by
  have hrad : LipschitzOnWith ((Real.toNNReal (2 / r)) * H)
      (fun x => f (NormedSpace.normalize x)) {x | r ≤ ‖x‖} := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (hr.trans_le hx))
    have hy0 : y ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (hr.trans_le hy))
    have hxs : NormedSpace.normalize x ∈ sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm]
      exact NormedSpace.norm_normalize hx0
    have hys : NormedSpace.normalize y ∈ sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm]
      exact NormedSpace.norm_normalize hy0
    have h₁ := hf.dist_le_mul _ hxs _ hys
    have h₂ := (normalize_lipschitzOn_annulus (E := E) hr).dist_le_mul _ hx _ hy
    simp only [NNReal.coe_mul, Real.coe_toNNReal (2 / r) (div_nonneg (by norm_num) hr.le)] at *
    calc
      dist (f (NormedSpace.normalize x)) (f (NormedSpace.normalize y)) ≤ H * dist (NormedSpace.normalize x) (NormedSpace.normalize y) := h₁
      _ ≤ H * ((2 / r) * dist x y) := mul_le_mul_of_nonneg_left h₂ H.coe_nonneg
      _ = _ := by ring
  exact hrad.extend_real

end
end Task006.SphereConcentration
