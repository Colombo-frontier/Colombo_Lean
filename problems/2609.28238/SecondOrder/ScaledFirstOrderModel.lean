import SecondOrder.ScaledFirstOrderGeometry

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ}

/-- All common random loss clauses for the actual conservative first-order
family, under explicit numerical scale inequalities. -/
theorem scaledFirstOrderCommonLoss (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    (P : Parameters) {A β ν : ℝ} (hA : 0≤A) (hβ : 0≤β) (hν : 0<ν) (hν1 : ν≤1)
    (R : ℝ) (hR : 2≤R)
    (hgap : 20*A*(T+1:ℕ)≤P.gap)
    (hLip : A*β^2*firstOrderGeometryConstant≤P.gradientLip)
    (hHolder : (2*(A*β^2*firstOrderGeometryConstant))^(1-ν)*
      (A*β^3*(firstOrderGeometryConstant*Real.sqrt d))^ν≤P.hessianHolder)
    (hgerr : A*β*(firstOrderNoiseConstant*(R+1))≤P.gradientNoise)
    (hHerr : A*β^2*(firstOrderNoiseConstant*(R+1))≤min P.hessianNoise P.hessianBound) :
    CommonLoss (firstOrderChainCoefficientLaw Θ R hR).toMeasure P ν
      (scaledFirstOrderPopulation Θ A β) (scaledFirstOrderSample Θ A β) := by
  apply finiteCommonLoss_of_uniformBounds _ P hν hν1
  · intro z
    exact (scaledFirstOrderSample_contDiff Θ A β z).of_le (show (2:WithTop ℕ∞)≤3 by decide)
  · intro z
    exact (scaledFirstOrderSample_C21 Θ hd A β R hR z).2
  · exact scaledFirstOrderSample_mean Θ hd A β R hR
  · intro x
    exact (scaledFirstOrderPopulation_gap Θ hA β x).trans hgap
  · intro x y
    exact (scaledFirstOrderPopulation_gradient_lipschitz Θ hd hA hβ x y).trans
      (mul_le_mul_of_nonneg_right hLip (norm_nonneg _))
  · intro x y
    exact (scaledFirstOrderPopulation_hessian_holder Θ hd hA hβ hν.le hν1 x y).trans
      (mul_le_mul_of_nonneg_right hHolder (Real.rpow_nonneg (norm_nonneg _) ν))
  · intro z x
    exact (scaledFirstOrderSample_error_bounds Θ hd hA hβ R hR z x).2.1.trans hgerr
  · intro z x
    exact (scaledFirstOrderSample_error_bounds Θ hd hA hβ R hR z x).2.2.trans hHerr

theorem scaledFirstOrderRichCommonLoss (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    (P : Parameters) {A β σ₀ : ℝ} (hA : 0≤A) (hβ : 0≤β) (hσ₀ : 0<σ₀)
    (R : ℝ) (hR : 2≤R)
    (hgap : 20*A*(T+1:ℕ)≤P.gap)
    (hLip : A*β^2*firstOrderGeometryConstant≤P.gradientLip)
    (hHolder : A*β^3*(firstOrderGeometryConstant*Real.sqrt d)≤P.hessianHolder)
    (hverr : A*(firstOrderNoiseConstant*(R+1))≤σ₀)
    (hgerr : A*β*(firstOrderNoiseConstant*(R+1))≤P.gradientNoise)
    (hHerr : A*β^2*(firstOrderNoiseConstant*(R+1))≤min P.hessianNoise P.hessianBound) :
    RichCommonLoss (firstOrderChainCoefficientLaw Θ R hR).toMeasure P σ₀
      (scaledFirstOrderPopulation Θ A β) (scaledFirstOrderSample Θ A β) := by
  apply finiteRichCommonLoss_of_valueBound _ P hσ₀
  · apply scaledFirstOrderCommonLoss Θ hd P hA hβ (by norm_num) le_rfl R hR hgap hLip _ hgerr hHerr
    simpa only [sub_self,Real.rpow_zero,Real.rpow_one,one_mul] using hHolder
  · intro z x
    exact (scaledFirstOrderSample_error_bounds Θ hd hA hβ R hR z x).1.trans hverr

end
end SecondOrder
