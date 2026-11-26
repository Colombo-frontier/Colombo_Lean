import SecondOrder.ScaledCurvatureGeometry

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ}

/-- An actual common random scalar loss on Point of the total dimension.
Every model field is proved; only explicit numerical scale inequalities remain
as hypotheses in this reusable parameterized form. -/
theorem scaledCurvatureCommonLoss (Θ : Fin (T+1) → BalancedVector m) (hm : 0<m)
    (P : Parameters) {A β ν : ℝ} (hA : 0≤A) (hβ : 0≤β) (hν : 0<ν) (hν1 : ν≤1)
    (R : ℝ) (hR : 2≤R)
    (hgap : A*(T+1:ℕ)≤P.gap)
    (hLip : A*β^2*(curvatureGeometryConstant/((2*m:ℕ):ℝ))≤P.gradientLip)
    (hHolder : (2*(A*β^2*(curvatureGeometryConstant/((2*m:ℕ):ℝ))))^(1-ν)*
      (A*β^3*(curvatureGeometryConstant/((2*m:ℕ):ℝ)))^ν≤P.hessianHolder)
    (hgerr : A*β*(curvatureNoiseConstant*(R+1)/Real.sqrt ((2*m:ℕ):ℝ))≤P.gradientNoise)
    (hHerr : A*β^2*(curvatureNoiseConstant*(R+1)/((2*m:ℕ):ℝ))≤min P.hessianNoise P.hessianBound) :
    CommonLoss (curvatureCoefficientLaw Θ R hR).toMeasure P ν
      (scaledCurvaturePopulation Θ A β) (scaledCurvatureSample Θ A β) := by
  apply finiteCommonLoss_of_uniformBounds _ P hν hν1
  · intro z
    exact (scaledCurvatureSample_contDiff Θ A β z).of_le (show (2:WithTop ℕ∞)≤3 by decide)
  · intro z
    exact (scaledCurvatureSample_C21 Θ hm A β R hR z).2
  · exact scaledCurvatureSample_mean Θ hm A β R hR
  · intro x
    exact (scaledCurvaturePopulation_gap Θ hA β x).trans hgap
  · intro x y
    exact (scaledCurvaturePopulation_gradient_lipschitz Θ hm hA hβ x y).trans
      (mul_le_mul_of_nonneg_right hLip (norm_nonneg _))
  · intro x y
    exact (scaledCurvaturePopulation_hessian_holder Θ hm hA hβ hν.le hν1 x y).trans
      (mul_le_mul_of_nonneg_right hHolder (Real.rpow_nonneg (norm_nonneg _) ν))
  · intro z x
    exact (scaledCurvatureSample_error_bounds Θ hm hA hβ R hR z x).2.1.trans hgerr
  · intro z x
    exact (scaledCurvatureSample_error_bounds Θ hm hA hβ R hR z x).2.2.trans hHerr

theorem scaledCurvatureRichCommonLoss (Θ : Fin (T+1) → BalancedVector m) (hm : 0<m)
    (P : Parameters) {A β σ₀ : ℝ} (hA : 0≤A) (hβ : 0≤β) (hσ₀ : 0<σ₀)
    (R : ℝ) (hR : 2≤R)
    (hgap : A*(T+1:ℕ)≤P.gap)
    (hLip : A*β^2*(curvatureGeometryConstant/((2*m:ℕ):ℝ))≤P.gradientLip)
    (hHolder : A*β^3*(curvatureGeometryConstant/((2*m:ℕ):ℝ))≤P.hessianHolder)
    (hverr : A*(curvatureNoiseConstant*(R+1))≤σ₀)
    (hgerr : A*β*(curvatureNoiseConstant*(R+1)/Real.sqrt ((2*m:ℕ):ℝ))≤P.gradientNoise)
    (hHerr : A*β^2*(curvatureNoiseConstant*(R+1)/((2*m:ℕ):ℝ))≤min P.hessianNoise P.hessianBound) :
    RichCommonLoss (curvatureCoefficientLaw Θ R hR).toMeasure P σ₀
      (scaledCurvaturePopulation Θ A β) (scaledCurvatureSample Θ A β) := by
  apply finiteRichCommonLoss_of_valueBound _ P hσ₀
  · apply scaledCurvatureCommonLoss Θ hm P hA hβ (by norm_num) le_rfl R hR hgap hLip _ hgerr hHerr
    simpa only [sub_self, Real.rpow_zero, Real.rpow_one, one_mul] using hHolder
  · intro z x
    exact (scaledCurvatureSample_error_bounds Θ hm hA hβ R hR z x).1.trans hverr

end
end SecondOrder
