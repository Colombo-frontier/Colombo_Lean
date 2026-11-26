import SecondOrder.CurvatureHolderScales

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

/-- The same conservative random scalar loss is admissible in the actual
Hölder model after checking its new scaling, not by class inclusion. -/
theorem curvatureHolderFamily_admissible {m T : ℕ} (Θ : Fin (T+1) → BalancedVector m)
    (hm : 0<m) (P : Parameters) {γ ν : ℝ} (hγ : 0<γ) (hν : 0<ν) (hν1 : ν≤1)
    (hsmall : 64*curvatureNoiseConstant*γ≤curvatureNoiseBudget P)
    (hLip : 8*curvatureGeometryConstant*γ≤P.gradientLip)
    (hgrad : curvatureNoiseBudget P*Real.sqrt ((2*m:ℕ):ℝ)≤
      P.gradientNoise*curvatureHolderInputScale P.hessianHolder γ ν)
    (hgap : curvatureOutputScale ((2*m:ℕ):ℝ) (curvatureHolderEffectiveL P.hessianHolder γ ν) γ*
      (T+1:ℕ)≤P.gap) :
    CommonLoss (curvatureCoefficientLaw Θ (curvatureCoefficientScale (curvatureNoiseBudget P) γ)
      (curvatureCoefficientScale_ge_two hγ hsmall)).toMeasure P ν
      (scaledCurvaturePopulation Θ
        (curvatureOutputScale ((2*m:ℕ):ℝ) (curvatureHolderEffectiveL P.hessianHolder γ ν) γ)
        (curvatureInputScale (curvatureHolderEffectiveL P.hessianHolder γ ν) γ))
      (scaledCurvatureSample Θ
        (curvatureOutputScale ((2*m:ℕ):ℝ) (curvatureHolderEffectiveL P.hessianHolder γ ν) γ)
        (curvatureInputScale (curvatureHolderEffectiveL P.hessianHolder γ ν) γ)) := by
  have hD : (0:ℝ)<(2*m:ℕ) := by exact_mod_cast Nat.mul_pos (by omega) hm
  have hL := curvatureHolderEffectiveL_pos (ν := ν) P.hessianHolder_pos hγ
  apply scaledCurvatureCommonLoss Θ hm P (curvatureOutputScale_pos hD hL hγ).le
    (curvatureInputScale_pos hL hγ).le hν hν1 _ _ hgap
  · rw [(curvatureScales_smoothness hD hL hγ).1]
    exact hLip
  · exact (curvatureHolderScales_smoothness hD P.hessianHolder_pos hγ hν hν1).trans
      (by linarith [P.hessianHolder_pos])
  · exact (curvatureHolderScales_gradient_noise hD P.hessianHolder_pos hγ hsmall).trans
      ((div_le_iff₀ (curvatureHolderInputScale_pos P.hessianHolder_pos hγ)).2 hgrad)
  · exact curvatureScales_hessian_noise hD hL hγ hsmall

theorem curvatureHolderBudgetFamily_admissible {m : ℕ} (hm : 0<m) (P : Parameters)
    {γ ν : ℝ} (hγ : 0<γ) (hν : 0<ν) (hν1 : ν≤1)
    (hsmall : 64*curvatureNoiseConstant*γ≤curvatureNoiseBudget P)
    (hLip : 8*curvatureGeometryConstant*γ≤P.gradientLip)
    (hgrad : curvatureNoiseBudget P*Real.sqrt ((2*m:ℕ):ℝ)≤
      P.gradientNoise*curvatureHolderInputScale P.hessianHolder γ ν)
    (hsize : 2*curvatureOutputScale ((2*m:ℕ):ℝ) (curvatureHolderEffectiveL P.hessianHolder γ ν) γ≤P.gap)
    (Θ : Fin (curvatureBudgetLinks P.gap
        (curvatureOutputScale ((2*m:ℕ):ℝ) (curvatureHolderEffectiveL P.hessianHolder γ ν) γ)+1) →
      BalancedVector m) :
    CommonLoss (curvatureCoefficientLaw Θ (curvatureCoefficientScale (curvatureNoiseBudget P) γ)
      (curvatureCoefficientScale_ge_two hγ hsmall)).toMeasure P ν
      (scaledCurvaturePopulation Θ
        (curvatureOutputScale ((2*m:ℕ):ℝ) (curvatureHolderEffectiveL P.hessianHolder γ ν) γ)
        (curvatureInputScale (curvatureHolderEffectiveL P.hessianHolder γ ν) γ))
      (scaledCurvatureSample Θ
        (curvatureOutputScale ((2*m:ℕ):ℝ) (curvatureHolderEffectiveL P.hessianHolder γ ν) γ)
        (curvatureInputScale (curvatureHolderEffectiveL P.hessianHolder γ ν) γ)) := by
  apply curvatureHolderFamily_admissible Θ hm P hγ hν hν1 hsmall hLip hgrad
  have hD : (0:ℝ)<(2*m:ℕ) := by exact_mod_cast Nat.mul_pos (by omega) hm
  have hA := curvatureOutputScale_pos hD (curvatureHolderEffectiveL_pos (ν := ν) P.hessianHolder_pos hγ) hγ
  exact (curvatureBudgetLinks_gap hA hsize).trans (by linarith [P.gap_pos])

end
end SecondOrder
