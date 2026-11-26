import GradientHessian.ReadoutFilter
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Quantitative normalization and certificate stability with the manuscript's
literal delta and numerical constants, in the actual Hilbert-space norm. -/

namespace GradientHessian.ReadoutNormalization

open ReadoutFilter
open scoped InnerProductSpace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def direction (u : E) : E := ‖u‖⁻¹ • u

theorem direction_norm {u : E} (hu : 0 < ‖u‖) : ‖direction u‖ = 1 := by
  rw [direction, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu), inv_mul_cancel₀ hu.ne']

theorem normalization_distance {u v : E} (hu : 0 < ‖u‖) (hv : 0 < ‖v‖) :
    ‖direction u - direction v‖ ≤ 2 * ‖u - v‖ / ‖v‖ := by
  have he : direction u - direction v =
      (‖u‖⁻¹ - ‖v‖⁻¹) • u + ‖v‖⁻¹ • (u - v) := by
    simp only [direction, sub_smul, smul_sub]
    abel
  have hs : |‖u‖⁻¹ - ‖v‖⁻¹| * ‖u‖ = |‖v‖ - ‖u‖| / ‖v‖ := by
    calc
      _ = |(‖u‖⁻¹ - ‖v‖⁻¹) * ‖u‖| := by rw [abs_mul, abs_of_pos hu]
      _ = |(‖v‖ - ‖u‖) / ‖v‖| := by congr 1; field_simp; ring
      _ = _ := by rw [abs_div, abs_of_pos hv]
  rw [he]
  calc
    _ ≤ ‖(‖u‖⁻¹ - ‖v‖⁻¹) • u‖ + ‖‖v‖⁻¹ • (u - v)‖ := norm_add_le _ _
    _ = |‖v‖ - ‖u‖| / ‖v‖ + ‖u - v‖ / ‖v‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, hs, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hv)]
      ring
    _ ≤ ‖u - v‖ / ‖v‖ + ‖u - v‖ / ‖v‖ := by
      apply add_le_add_right
      apply div_le_div_of_nonneg_right _ hv.le
      simpa only [norm_sub_rev] using abs_norm_sub_norm_le v u
    _ = _ := by ring

theorem stable_readout_geometry {u v : E}
    (hl : Real.sqrt 2 / 3 ≤ ‖v‖) (hh : ‖v‖ ≤ 1 / 2) (he : ‖u - v‖ ≤ delta) :
    2 / 5 ≤ ‖u‖ ∧ ‖u‖ ≤ 3 / 5 ∧ ‖direction u‖ = 1 ∧
      ‖direction v‖ = 1 ∧ ‖direction u - direction v‖ ≤ 5 * delta := by
  have hs : (7 / 5 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hd : delta ≤ 1 / 1000 := delta_le_thousandth
  have hn1 := norm_sub_norm_le u v
  have hn2 := norm_sub_norm_le v u
  rw [norm_sub_rev] at hn2
  have hu : (2 / 5 : ℝ) ≤ ‖u‖ := by linarith
  have hv : (2 / 5 : ℝ) ≤ ‖v‖ := by linarith
  have hu0 : 0 < ‖u‖ := by linarith
  have hv0 : 0 < ‖v‖ := by linarith
  refine ⟨hu, by linarith, direction_norm hu0, direction_norm hv0, ?_⟩
  apply (normalization_distance hu0 hv0).trans
  apply (div_le_iff₀ hv0).mpr
  have hprod := mul_le_mul_of_nonneg_left hv
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) delta_pos.le)
  nlinarith

/-- Perturbing the ideal normalized readout by the exact filter tolerance
preserves the source's inverse certificate with margin. -/
theorem stable_inverse_certificate {u v q g : E}
    (hl : Real.sqrt 2 / 3 ≤ ‖v‖) (hh : ‖v‖ ≤ 1 / 2) (he : ‖u - v‖ ≤ delta)
    (hg : ‖g‖ ≤ 1) (hcomp : ‖g - q‖ ≤ 1 / 5)
    (hideal : ⟪direction v, q⟫_ℝ = ‖v‖) :
    1 / 4 ≤ ⟪direction u, g⟫_ℝ := by
  obtain ⟨_, _, _, hnv, hdiff⟩ := stable_readout_geometry hl hh he
  have htail := abs_real_inner_le_norm (direction v) (g - q)
  rw [hnv, one_mul] at htail
  have htail' : -(1 / 5 : ℝ) ≤ ⟪direction v, g - q⟫_ℝ :=
    (neg_le_neg hcomp).trans ((neg_le_neg htail).trans (neg_abs_le _))
  have herr := abs_real_inner_le_norm (direction u - direction v) g
  have herr' : |⟪direction u - direction v, g⟫_ℝ| ≤ 5 * delta :=
    herr.trans (by nlinarith [norm_nonneg (direction u - direction v), norm_nonneg g])
  have heq : ⟪direction u, g⟫_ℝ =
      ‖v‖ + ⟪direction v, g - q⟫_ℝ + ⟪direction u - direction v, g⟫_ℝ := by
    rw [inner_sub_right, inner_sub_left, hideal]
    ring
  have hs : (7 / 5 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hd := delta_le_thousandth
  have hlo := (abs_le.mp herr').1
  rw [heq]
  linarith

end
end GradientHessian.ReadoutNormalization
