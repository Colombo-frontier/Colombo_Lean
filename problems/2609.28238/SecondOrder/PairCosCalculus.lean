import SecondOrder.PairOperators
import SecondOrder.PeriodicFourier

open scoped BigOperators Classical InnerProductSpace

namespace SecondOrder
noncomputable section
variable {d : ℕ}

def pairCosGradient (a : UpperPair d → ℝ) (x : Point d) : Point d :=
  pairVectorSum (fun e => -a e*Real.sin (coordinateDifference e x))

def pairCosHessian (a : UpperPair d → ℝ) (x : Point d) : Point d →L[ℝ] Point d :=
  pairLaplacian (fun e => -a e*Real.cos (coordinateDifference e x))

theorem pairCosPotential_hasGradientAt (a : UpperPair d → ℝ) (x : Point d) :
    HasGradientAt (pairCosPotential a) (pairCosGradient a x) x := by
  have he (e : UpperPair d) : HasFDerivAt (fun y => a e*Real.cos (coordinateDifference e y))
      ((-a e*Real.sin (coordinateDifference e x)) • coordinateDifference e) x := by
    convert ((coordinateDifference e).hasFDerivAt.cos.const_mul (a e)) using 1
    ext v
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert HasFDerivAt.sum (fun e (_ : e ∈ Finset.univ) => he e) using 1
  simp only [pairCosGradient, pairVectorSum, map_sum, map_smul, pairDirection,
    LinearIsometryEquiv.apply_symm_apply]

theorem gradient_pairCosPotential (a : UpperPair d → ℝ) :
    gradient (pairCosPotential a) = pairCosGradient a :=
  funext (fun x => (pairCosPotential_hasGradientAt a x).gradient)

theorem pairCosGradient_hasFDerivAt (a : UpperPair d → ℝ) (x : Point d) :
    HasFDerivAt (pairCosGradient a) (pairCosHessian a x) x := by
  have he (e : UpperPair d) : HasFDerivAt
      (fun y => (-a e*Real.sin (coordinateDifference e y)) • pairDirection e)
      ((-a e*Real.cos (coordinateDifference e x)) •
        (coordinateDifference e).smulRight (pairDirection e)) x := by
    convert (((coordinateDifference e).hasFDerivAt.sin.const_mul (-a e)).smul_const (pairDirection e)) using 1
    ext v
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      smul_eq_mul, smul_smul]
  exact HasFDerivAt.sum (fun e (_ : e ∈ Finset.univ) => he e)

theorem hessian_pairCosPotential (a : UpperPair d → ℝ) (x : Point d) :
    hessian (pairCosPotential a) x = pairCosHessian a x := by
  rw [hessian, gradient_pairCosPotential]
  exact (pairCosGradient_hasFDerivAt a x).fderiv

/-- The centered Fourier field, used for each realized coefficient error. -/
def pairNoisePotential (a : UpperPair d → ℝ) (x : Point d) : ℝ :=
  -((d:ℝ)⁻¹)^2*pairCosPotential a x

theorem pairNoisePotential_contDiff (a : UpperPair d → ℝ) (k : WithTop ℕ∞) :
    ContDiff ℝ k (pairNoisePotential a) :=
  contDiff_const.mul (pairCosPotential_contDiff a k)

theorem gradient_pairNoisePotential (a : UpperPair d → ℝ) :
    gradient (pairNoisePotential a) = fun x => -((d:ℝ)⁻¹)^2 • pairCosGradient a x := by
  funext x
  have hd := ((pairCosPotential_hasGradientAt a x).hasFDerivAt.const_mul (-((d:ℝ)⁻¹)^2)).fderiv
  change (InnerProductSpace.toDual ℝ (Point d)).symm
    (fderiv ℝ (fun y => -((d:ℝ)⁻¹)^2*pairCosPotential a y) x) = _
  rw [hd, map_smul, LinearIsometryEquiv.symm_apply_apply]

theorem hessian_pairNoisePotential (a : UpperPair d → ℝ) (x : Point d) :
    hessian (pairNoisePotential a) x = -((d:ℝ)⁻¹)^2 • pairCosHessian a x := by
  rw [hessian, gradient_pairNoisePotential]
  exact ((pairCosGradient_hasFDerivAt a x).const_smul _).fderiv

end
end SecondOrder
