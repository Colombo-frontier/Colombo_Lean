import RandomizedFO2003.SphereUniqueness
import RandomizedFO2003.HaarExposure
import GradientHessian.SharpSphereTail

/-! The Haar exposure construction and the sharp spherical tail previously use
two concrete sphere measures. This file identifies those measures and transfers
the proved exponential bound. No concentration or uniformity hypothesis is added.
-/

noncomputable section

namespace SampleReuse.RandomFrame

open MeasureTheory ProbabilityTheory RandomizedFO2003
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianSphere_eq_exposureSphere :
    GradientHessian.SphereGaussian.sphereLaw E = Spherical.sphereLaw E := by
  apply Spherical.sphereLaw_unique E
  · exact GradientHessian.SphereGaussian.sphereLaw_unit
  · intro U
    exact ⟨U.continuous.measurable, GradientHessian.SphereGaussian.sphereLaw_isometry U⟩

theorem sphere_projection_tail (y : E) (hy : y ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    (Spherical.sphereLaw E).real {x | t ≤ |⟪y, x⟫_ℝ|} ≤
      2 * Real.exp (-(Module.finrank ℝ E : ℝ) * t ^ 2 / (2 * ‖y‖ ^ 2)) := by
  rw [← gaussianSphere_eq_exposureSphere]
  exact GradientHessian.SharpSphereTail.sphereLaw_sharp_tail y hy ht

theorem sphere_projection_tail_of_norm_le (y : E) {R t : ℝ}
    (hR : 0 < R) (ht : 0 < t) (hy : ‖y‖ ≤ R) :
    (Spherical.sphereLaw E).real {x | t ≤ |⟪y, x⟫_ℝ|} ≤
      2 * Real.exp (-(Module.finrank ℝ E : ℝ) * t ^ 2 / (2 * R ^ 2)) := by
  by_cases hy0 : y = 0
  · simp only [hy0, inner_zero_left, abs_zero, not_le_of_gt ht, Set.setOf_false,
      measureReal_empty]
    positivity
  · apply (sphere_projection_tail y hy0 ht.le).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hden : 2 * ‖y‖ ^ 2 ≤ 2 * R ^ 2 := by nlinarith
    have hquot := div_le_div_of_nonneg_left
      (show 0 ≤ (Module.finrank ℝ E : ℝ) * t ^ 2 by positivity)
      (show 0 < 2 * ‖y‖ ^ 2 by positivity) hden
    simpa only [neg_mul, neg_div] using neg_le_neg hquot

theorem haar_projection_tail (e y : E) (he : ‖e‖ = 1) {R t : ℝ}
    (hR : 0 < R) (ht : 0 < t) (hy : ‖y‖ ≤ R) :
    (Rotations.haarLaw E).real {U | t ≤ |⟪y, Rotations.isometry E U e⟫_ℝ|} ≤
      2 * Real.exp (-(Module.finrank ℝ E : ℝ) * t ^ 2 / (2 * R ^ 2)) := by
  have hm := Rotations.haar_unit_orbit_preserving E e he
  have hs : MeasurableSet {x : E | t ≤ |⟪y, x⟫_ℝ|} :=
    measurableSet_le measurable_const (continuous_const.inner continuous_id).abs.measurable
  have heq := hm.measure_preimage hs.nullMeasurableSet
  have hreal := congrArg ENNReal.toReal heq
  change (Rotations.haarLaw E).real {U | t ≤ |⟪y, Rotations.isometry E U e⟫_ℝ|} =
    (Spherical.sphereLaw E).real {x | t ≤ |⟪y, x⟫_ℝ|} at hreal
  rw [hreal]
  exact sphere_projection_tail_of_norm_le y hR ht hy

end SampleReuse.RandomFrame
