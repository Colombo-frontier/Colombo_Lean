import Geode.Acosh
import Geode.Parameters
import Mathlib.Analysis.Convex.Deriv

/-!
# Scalar differential estimates for squared hyperbolic distance

The functions are the actual inverse-cosh square and curvature factor. These
results supply the scalar Hessian estimates for the projected upper algorithm.
-/

namespace Geode

open Set

theorem sinh_le_mul_cosh {r : ℝ} (hr : 0 ≤ r) : Real.sinh r ≤ r * Real.cosh r := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t => t * Real.cosh t - Real.sinh t)
      (t * Real.sinh t) t := by
    intro t
    convert ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub
      (Real.hasDerivAt_sinh t) using 1
    simp only [id_eq]
    ring
  have hm := monotone_of_hasDerivAt_nonneg hd (fun t => ?_)
  · have h := hm hr
    simp only [zero_mul, Real.sinh_zero, sub_zero] at h
    linarith
  · by_cases ht : 0 ≤ t
    · exact mul_nonneg ht (Real.sinh_nonneg_iff.mpr ht)
    · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge ht)
        (Real.sinh_nonpos_iff.mpr (le_of_not_ge ht))

theorem self_le_sinh_mul_cosh {r : ℝ} (hr : 0 ≤ r) :
    r ≤ Real.sinh r * Real.cosh r := by
  have h := Real.self_le_sinh_iff.mpr (show 0 ≤ 2 * r by linarith)
  rw [Real.sinh_two_mul] at h
  linarith

theorem curvatureFactor_eq_cosh_div_sinh (r : ℝ) :
    curvatureFactor r = r * Real.cosh r / Real.sinh r := by
  rw [curvatureFactor, Real.tanh_eq_sinh_div_cosh, div_div_eq_mul_div]

theorem one_le_curvatureFactor {r : ℝ} (hr : 0 < r) : 1 ≤ curvatureFactor r := by
  rw [curvatureFactor_eq_cosh_div_sinh, le_div_iff₀ (Real.sinh_pos_iff.mpr hr), one_mul]
  exact sinh_le_mul_cosh hr.le

theorem hasDerivAt_curvatureFactor {r : ℝ} (hr : 0 < r) :
    HasDerivAt curvatureFactor
      ((Real.cosh r * Real.sinh r - r) / Real.sinh r ^ 2) r := by
  have hs : Real.sinh r ≠ 0 := (Real.sinh_pos_iff.mpr hr).ne'
  have h := ((hasDerivAt_id r).mul (Real.hasDerivAt_cosh r)).div
    (Real.hasDerivAt_sinh r) hs
  have hn : (1 * Real.cosh r + r * Real.sinh r) * Real.sinh r -
      (r * Real.cosh r) * Real.cosh r = Real.cosh r * Real.sinh r - r := by
    have hh := Real.cosh_sq_sub_sinh_sq r
    linear_combination -r * hh
  rw [show curvatureFactor = (fun r : ℝ => r * Real.cosh r / Real.sinh r) from
    funext curvatureFactor_eq_cosh_div_sinh]
  simpa only [id_eq, hn] using h

theorem curvatureFactor_monotoneOn : MonotoneOn curvatureFactor (Ioi 0) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
    (fun r hr => (hasDerivAt_curvatureFactor hr).continuousAt.continuousWithinAt)
    (fun r hr => (hasDerivAt_curvatureFactor (interior_subset hr)).hasDerivWithinAt) ?_
  intro r hr
  apply div_nonneg _ (sq_nonneg _)
  have h := self_le_sinh_mul_cosh (le_of_lt (interior_subset hr))
  nlinarith

noncomputable def squaredArcosh (z : ℝ) : ℝ := arcosh z ^ 2 / 2
noncomputable def squaredArcoshSlope (z : ℝ) : ℝ := arcosh z / Real.sqrt (z ^ 2 - 1)
noncomputable def squaredArcoshSlopeDerivative (z : ℝ) : ℝ :=
  (Real.sqrt (z ^ 2 - 1) - z * arcosh z) / Real.sqrt (z ^ 2 - 1) ^ 3

theorem hasDerivAt_squaredArcosh {z : ℝ} (hz : 1 < z) :
    HasDerivAt squaredArcosh (squaredArcoshSlope z) z := by
  have h := ((hasDerivAt_arcosh hz).pow 2).div_const 2
  convert h using 1
  unfold squaredArcoshSlope
  ring

theorem hasDerivAt_squaredArcoshSlope {z : ℝ} (hz : 1 < z) :
    HasDerivAt squaredArcoshSlope (squaredArcoshSlopeDerivative z) z := by
  have hrad : 0 < z ^ 2 - 1 := by nlinarith
  have hs : Real.sqrt (z ^ 2 - 1) ≠ 0 := (Real.sqrt_pos.mpr hrad).ne'
  have h := (hasDerivAt_arcosh hz).mul (hasDerivAt_arcosh_slope hz)
  convert h using 1
  unfold squaredArcoshSlopeDerivative
  generalize hsqrt : Real.sqrt (z ^ 2 - 1) = s at *
  field_simp
  ring

theorem squaredArcoshSlope_nonneg {z : ℝ} (_hz : 1 ≤ z) :
    0 ≤ squaredArcoshSlope z := div_nonneg (arcosh_nonneg z) (Real.sqrt_nonneg _)

theorem squaredArcoshSlopeDerivative_nonpos {z : ℝ} (hz : 1 < z) :
    squaredArcoshSlopeDerivative z ≤ 0 := by
  have h := sinh_le_mul_cosh (arcosh_nonneg z)
  rw [sinh_arcosh, cosh_arcosh hz.le] at h
  unfold squaredArcoshSlopeDerivative
  apply div_nonpos_of_nonpos_of_nonneg _ (pow_nonneg (Real.sqrt_nonneg _) 3)
  nlinarith

theorem arcosh_mul_slope_eq_curvature {z : ℝ} (hz : 1 < z) :
    z * squaredArcoshSlope z = curvatureFactor (arcosh z) := by
  rw [curvatureFactor_eq_cosh_div_sinh, cosh_arcosh hz.le, sinh_arcosh]
  unfold squaredArcoshSlope
  ring

theorem squaredArcoshSlope_le_one {z : ℝ} (hz : 1 < z) :
    squaredArcoshSlope z ≤ 1 := by
  have hs : 0 < Real.sqrt (z ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
  have h := Real.self_le_sinh_iff.mpr (arcosh_nonneg z)
  rw [sinh_arcosh] at h
  unfold squaredArcoshSlope
  exact (div_le_one hs).mpr h

theorem squaredArcosh_second_bound {z g a δ : ℝ}
    (hz : 1 < z + δ) (hδ : 0 ≤ δ) :
    squaredArcoshSlopeDerivative (z + δ) * g ^ 2 +
      squaredArcoshSlope (z + δ) * (a ^ 2 * z) ≤
      a ^ 2 * curvatureFactor (arcosh (z + δ)) := by
  have hs := squaredArcoshSlope_nonneg hz.le
  have hn := mul_nonpos_of_nonpos_of_nonneg
    (squaredArcoshSlopeDerivative_nonpos hz) (sq_nonneg g)
  have hshift := mul_nonneg (mul_nonneg (sq_nonneg a) hs) hδ
  rw [← arcosh_mul_slope_eq_curvature hz]
  nlinarith

theorem hasDerivAt_squaredArcosh_comp {F : ℝ → ℝ} {g t δ : ℝ}
    (hF : HasDerivAt F g t) (hz : 1 < F t + δ) :
    HasDerivAt (fun s => squaredArcosh (F s + δ))
      (squaredArcoshSlope (F t + δ) * g) t := by
  have h := (hasDerivAt_squaredArcosh hz).comp t (hF.add_const δ)
  exact h

theorem hasDerivAt_squaredArcosh_comp_slope {F G : ℝ → ℝ} {h t δ : ℝ}
    (hF : HasDerivAt F (G t) t) (hG : HasDerivAt G h t) (hz : 1 < F t + δ) :
    HasDerivAt (fun s => squaredArcoshSlope (F s + δ) * G s)
      (squaredArcoshSlopeDerivative (F t + δ) * G t ^ 2 +
        squaredArcoshSlope (F t + δ) * h) t := by
  have hd := ((hasDerivAt_squaredArcoshSlope hz).comp t (hF.add_const δ)).mul hG
  convert hd using 1
  simp only [Function.comp_def]
  ring

theorem squaredArcosh_second_bound_uniform {z g a δ D : ℝ}
    (hz : 1 ≤ z) (hδ : 0 < δ) (hD : 0 < D)
    (hbound : z + δ ≤ Real.cosh D) :
    squaredArcoshSlopeDerivative (z + δ) * g ^ 2 +
      squaredArcoshSlope (z + δ) * (a ^ 2 * z) ≤ a ^ 2 * curvatureFactor D := by
  have hz' : 1 < z + δ := by linarith
  have hr : 0 < arcosh (z + δ) := (arcosh_pos_iff hz'.le).mpr hz'
  have hle : arcosh (z + δ) ≤ D := (arcosh_le_iff_le_cosh hz'.le hD.le).mpr hbound
  exact (squaredArcosh_second_bound hz' hδ.le).trans
    (mul_le_mul_of_nonneg_left (curvatureFactor_monotoneOn hr hD hle) (sq_nonneg a))

end Geode
