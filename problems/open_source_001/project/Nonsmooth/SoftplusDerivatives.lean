import Nonsmooth.SoftplusConvexity

open Set Filter
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def softplusSlope (t : ℝ) : ℝ := Real.exp t / (1 + Real.exp t)
def softplusCurvature (t : ℝ) : ℝ := Real.exp t / (1 + Real.exp t) ^ 2

theorem softplusSlope_bounds (t : ℝ) : 0 < softplusSlope t ∧ softplusSlope t < 1 := by
  constructor
  · unfold softplusSlope
    positivity
  · apply (div_lt_iff₀ (by positivity : 0 < 1 + Real.exp t)).mpr
    linarith

theorem softplusCurvature_bounds (t : ℝ) : 0 < softplusCurvature t ∧ softplusCurvature t ≤ 1 / 4 := by
  constructor
  · unfold softplusCurvature
    positivity
  · apply (div_le_iff₀ (by positivity : 0 < (1 + Real.exp t) ^ 2)).mpr
    nlinarith [sq_nonneg (Real.exp t - 1)]

theorem softplusSlope_contDiff : ContDiff ℝ ⊤ softplusSlope :=
  Real.contDiff_exp.div (contDiff_const.add Real.contDiff_exp) (fun t => by positivity)

theorem softplusCurvature_contDiff : ContDiff ℝ ⊤ softplusCurvature :=
  Real.contDiff_exp.div ((contDiff_const.add Real.contDiff_exp).pow 2) (fun t => by positivity)

theorem softplusSlope_hasDerivAt (t : ℝ) : HasDerivAt softplusSlope (softplusCurvature t) t := by
  convert! (Real.hasDerivAt_exp t).div ((Real.hasDerivAt_exp t).const_add 1)
    (by positivity : 1 + Real.exp t ≠ 0) using 1
  unfold softplusCurvature
  congr 1
  ring

theorem softplusCurvature_hasDerivAt (t : ℝ) :
    HasDerivAt softplusCurvature (softplusCurvature t * (1 - 2 * softplusSlope t)) t := by
  convert! (Real.hasDerivAt_exp t).div (((Real.hasDerivAt_exp t).const_add 1).pow 2)
    (by positivity : (1 + Real.exp t) ^ 2 ≠ 0) using 1
  unfold softplusCurvature softplusSlope
  simp only [Pi.pow_apply]
  field_simp <;> ring

theorem softplusCurvature_derivative_bound (t : ℝ) :
    |softplusCurvature t * (1 - 2 * softplusSlope t)| ≤ 1 / 4 := by
  have hs := softplusSlope_bounds t
  have hc := softplusCurvature_bounds t
  rw [abs_mul, abs_of_pos hc.1]
  have ha : |1 - 2 * softplusSlope t| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  exact (mul_le_of_le_one_right hc.1.le ha).trans hc.2

end
end Nonsmooth
