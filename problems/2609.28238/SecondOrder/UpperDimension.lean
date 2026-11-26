import SecondOrder.StochasticUpperAlgorithm

open MeasureTheory
open scoped ENNReal

namespace SecondOrder
noncomputable section

def ojaDimensionFreePriceCoefficient (P : Parameters) : ℝ :=
  400*(104976*(eigenHessianBound P)^2+4000*(2304*P.hessianBound^2+2))

def stochasticDimensionFreeCoefficient (P : Parameters) (ν : ℝ) : ℝ :=
  epsilonQueryCoefficient P ν
    (ojaDimensionFreePriceCoefficient P*(confidenceToleranceCoefficient P ν*(1+Real.log 10))^2)

theorem ojaDimensionFreePriceCoefficient_pos (P : Parameters) :
    0 < ojaDimensionFreePriceCoefficient P := by unfold ojaDimensionFreePriceCoefficient; positivity

theorem stochasticDimensionFreeCoefficient_pos (P : Parameters) {ν : ℝ} (hν : 0 < ν) :
    0 < stochasticDimensionFreeCoefficient P ν := by
  apply epsilonQueryCoefficient_pos P hν
  have hC := ojaDimensionFreePriceCoefficient_pos P
  positivity

theorem one_le_dimensionLog {d : ℕ} (hd : 0 < d) : 1 ≤ 1+Real.log (4*(d:ℝ)) := by
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hl := Real.log_nonneg (by linarith : (1:ℝ) ≤ 4*(d:ℝ))
  linarith

theorem ojaPriceCoefficient_dimension (P : Parameters) {d : ℕ} (hd : 0 < d) :
    ojaPriceCoefficient P d ≤ ojaDimensionFreePriceCoefficient P*(1+Real.log (4*(d:ℝ)))^2 := by
  have hD : (1:ℝ) ≤ (1+Real.log (4*(d:ℝ)))^2 := one_le_pow₀ (one_le_dimensionLog hd)
  have hc : 0 ≤ 4000*(2304*P.hessianBound^2+2) := by positivity
  have hm := mul_nonneg hc (sub_nonneg.mpr hD)
  unfold ojaPriceCoefficient ojaDimensionFreePriceCoefficient
  nlinarith

theorem affine_scale_bound {a b E E₀ D : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hD : 1 ≤ D) (hE : E ≤ E₀*D) : a+b*E ≤ (a+b*E₀)*D := by
  have he := mul_le_mul_of_nonneg_left hE hb
  have hd := mul_nonneg ha (sub_nonneg.mpr hD)
  nlinarith

/-- The displayed upper coefficient has only a squared logarithmic
dependence on dimension; its remaining coefficient is dimension-free. -/
theorem stochasticUpperCoefficient_dimension (P : Parameters) {ν : ℝ} (hν : 0 < ν)
    {d : ℕ} (hd : 0 < d) :
    stochasticUpperCoefficient P ν d ≤
      stochasticDimensionFreeCoefficient P ν*(1+Real.log (4*(d:ℝ)))^2 := by
  let D := (1+Real.log (4*(d:ℝ)))^2
  let E₀ := ojaDimensionFreePriceCoefficient P*(confidenceToleranceCoefficient P ν*(1+Real.log 10))^2
  have hE : ojaSelectedPriceCoefficient P ν d ≤ E₀*D := by
    have he := mul_le_mul_of_nonneg_right (ojaPriceCoefficient_dimension P hd)
      (sq_nonneg (confidenceToleranceCoefficient P ν*(1+Real.log 10)))
    exact he.trans_eq (by dsimp only [E₀,D]; ring)
  have hD : 1 ≤ D := one_le_pow₀ (one_le_dimensionLog hd)
  have hT := trackingPolylogCoefficient_pos P hν
  have hK := endpointTrackingCoefficient_pos P ν
  have hC := curvatureCountCoefficient_pos P ν
  have hb := affine_scale_bound
    (a := 25+24*(6144*trackingPolylogCoefficient P ν*endpointTrackingCoefficient P ν))
    (b := 24*(1+curvatureCountCoefficient P ν)) (by positivity) (by positivity) hD hE
  have he : endpointQueryCoefficient P ν (ojaSelectedPriceCoefficient P ν d) ≤
      endpointQueryCoefficient P ν E₀*D := by
    unfold endpointQueryCoefficient
    nlinarith [hb]
  have hm := mul_le_mul_of_nonneg_left he
    (show 0 ≤ 1000*(1+Real.log 10)^4 by positivity)
  exact hm.trans_eq (by
    unfold stochasticDimensionFreeCoefficient epsilonQueryCoefficient
    dsimp only [E₀,D]
    ring)

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- Fixed-parameter Hölder endpoint upper bound, with explicit logarithms
of both dimension and tolerances, for the actual permitted-query trace. -/
theorem CommonLoss.stochasticUpperRun_dimension_rate (h : CommonLoss μ P ν F f) (hd : 0 < d)
    {ε γ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    (∀ w : StochasticUpperTape Ω d P ν ε γ,
      ((stochasticUpperTrace P ν f ε γ w).length:ℝ) <
        stochasticDimensionFreeCoefficient P ν*(1+Real.log (4*(d:ℝ)))^2*
          (toleranceLog ε γ)^4*holderEndpointRate ν ε γ) ∧
    ENNReal.ofReal (29/32:ℝ) ≤ stochasticUpperLaw μ P ν d ε hγ
      {w | BudgetedSuccess F ε γ (stochasticUpperRun P ν f ε γ w)} := by
  obtain ⟨hcost,hs⟩ := h.stochasticUpperRun_rate hε hε1 hγ hγ1
  refine ⟨?_,hs⟩
  intro w
  have hc := stochasticUpperCoefficient_dimension P h.nu_pos hd
  have hp := mul_le_mul_of_nonneg_right hc (pow_nonneg (by
    have hj := one_le_toleranceLog hε hε1 hγ hγ1; linarith) 4)
  exact (hcost w).trans_le (mul_le_mul_of_nonneg_right hp (holderEndpointRate_pos ν hε hγ).le)

theorem CommonLoss.stochasticUpperRun_lipschitz_rate (h : CommonLoss μ P 1 F f) (hd : 0 < d)
    {ε γ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    (∀ w : StochasticUpperTape Ω d P 1 ε γ,
      ((stochasticUpperTrace P 1 f ε γ w).length:ℝ) <
        stochasticDimensionFreeCoefficient P 1*(1+Real.log (4*(d:ℝ)))^2*
          (toleranceLog ε γ)^4*(1/ε^3+1/γ^5)) ∧
    ENNReal.ofReal (29/32:ℝ) ≤ stochasticUpperLaw μ P 1 d ε hγ
      {w | BudgetedSuccess F ε γ (stochasticUpperRun P 1 f ε γ w)} := by
  simpa only [holderEndpointRate_lipschitz ε hγ.le] using
    h.stochasticUpperRun_dimension_rate hd hε hε1 hγ hγ1

end
end SecondOrder
