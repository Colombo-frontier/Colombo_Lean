import Nonsmooth.ParametricRegressionIdentities
import Nonsmooth.SliceRegressionCurvature

open MeasureTheory ProbabilityTheory Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- The actual marginal curvature controls the actual regression derivative.
Local dominated differentiation, strict transverse curvature, and the Hessian
determinant are explicit; no derivative identity is assumed. -/
theorem regular_slice_regression_curvature
    (V dx dxx score mixed γ : ℝ → ℝ → ℝ) (t : ℝ)
    (hV : ∀ r, Measurable (V r)) (hi : ∀ r, Integrable (fun x => Real.exp (-V r x)))
    (hdx : Continuous (dx t)) (hdxx : Continuous (dxx t))
    (hscore : Continuous (score t)) (hmixed : Continuous (mixed t))
    (hDx : ∀ x, HasDerivAt (V t) (dx t x) x)
    (hDxx : ∀ x, HasDerivAt (dx t) (dxx t x) x)
    (hDmixed : ∀ x, HasDerivAt (score t) (mixed t x) x)
    (htransverse : ∀ x, 0 < dxx t x - 1)
    (hHessian : ∀ x, (mixed t x) ^ 2 ≤ (dxx t x - 1) * (γ t x - 1))
    (hmeanReg : PotentialMomentRegularAt V score (fun _ x => x) (fun _ _ => 0) t)
    (hscoreReg : PotentialMomentRegularAt V score score γ t)
    (hdenReg : ∀ r, PotentialMomentRegularAt V score (fun _ _ => 1) (fun _ _ => 0) r)
    (hscore2 : MemLp (score t) 2 (realDensityLaw (fun x => Real.exp (-V t x))))
    (hγ : Integrable (γ t) (realDensityLaw (fun x => Real.exp (-V t x)))) :
    1 + (deriv (potentialExpectation V (fun _ x => x)) t) ^ 2 ≤
      deriv (deriv (fun r => -Real.log (potentialPartition V r))) t := by
  have hmono : Monotone (fun x => dx t x - 1 * x) := by
    apply monotone_of_hasDerivAt_nonneg
      (fun x => (hDxx x).sub ((hasDerivAt_id x).const_mul 1))
    intro x
    simpa only [mul_one, Pi.zero_apply] using (htransverse x).le
  have hx2 := (strong_potential_law_probability_and_memLp (V t) (dx t) hdx
    (by norm_num : (0 : ℝ) < 1) hDx hmono).2
  have hM := potentialRegression_derivative V score t hV hi hmeanReg (hdenReg t) hx2 hscore2
  have hC := potentialNegativeLogPartition_secondDerivative V score γ t hV hi hscoreReg hdenReg hscore2 hγ
  apply scalar_slice_regression_curvature (V t) (dx t) (dxx t) (score t) (mixed t) (γ t)
    hdx hdxx hscore hmixed hDx hDxx hDmixed htransverse hHessian hscore2 hγ
    (deriv (potentialExpectation V (fun _ x => x)) t)
    (deriv (deriv (fun r => -Real.log (potentialPartition V r))) t)
  · exact hM.deriv
  · exact hC.deriv

end
end Nonsmooth
