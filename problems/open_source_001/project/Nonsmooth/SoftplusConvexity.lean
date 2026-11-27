import Nonsmooth.SoftInequalityWeights
import Mathlib.Analysis.Convex.Deriv

open Set Filter
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def softplus (t : ℝ) : ℝ := Real.log (1 + Real.exp t)

theorem softplus_contDiff : ContDiff ℝ ⊤ softplus := by
  exact (contDiff_const.add Real.contDiff_exp).log (fun t => by positivity)

theorem softplus_hasDerivAt (t : ℝ) :
    HasDerivAt softplus (Real.exp t / (1 + Real.exp t)) t := by
  exact ((Real.hasDerivAt_exp t).const_add 1).log (by positivity)

theorem softplus_monotone : Monotone softplus := by
  intro a b hab
  exact Real.log_le_log (by positivity) (add_le_add le_rfl (Real.exp_le_exp.mpr hab))

theorem softplus_convex : ConvexOn ℝ univ softplus := by
  apply Monotone.convexOn_univ_of_deriv (softplus_contDiff.differentiable (by simp))
  intro a b hab
  rw [(softplus_hasDerivAt a).deriv, (softplus_hasDerivAt b).deriv]
  apply (div_le_div_iff₀ (by positivity : 0 < 1 + Real.exp a)
    (by positivity : 0 < 1 + Real.exp b)).mpr
  nlinarith [Real.exp_le_exp.mpr hab]

theorem softInequalityStep_exp (n : ℕ) (t : ℝ) :
    softInequalityStep n t = Real.exp (-softplus ((n : ℝ) * t)) := by
  rw [softInequalityStep, softplus, Real.exp_neg, Real.exp_log (by positivity), Real.exp_nat_mul]
  simp only [one_div]

end
end Nonsmooth
