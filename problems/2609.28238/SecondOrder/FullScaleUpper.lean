import SecondOrder.OjaFullPrice
import SecondOrder.MinimumRequestBudget

open MeasureTheory
open scoped ENNReal

namespace SecondOrder
noncomputable section

/-- The original nonasymptotic scale, retaining the constrained minimum.
The curvature-count coefficient makes the constant depending on ν explicit. -/
def fullUpperScale (P : Parameters) (ν ε γ : ℝ) : ℝ :=
  minimumTrackingScale P ν ε γ+
    (1+curvatureCountCoefficient P ν*γ^(-(1+2/ν)))*(eigenHessianBound P)^2/γ^2

def fullUpperLogFactor (P : Parameters) (ν : ℝ) (d : ℕ) (ε γ : ℝ) : ℝ :=
  let M := physicalCap P ν (ε/10) γ
  let L := trackingTreeDepth M
  let δ := localFailureTolerance M
  25+24*(6144*10000*(L:ℝ)^3*(8*Real.log (1/δ)+2)+ojaFullPriceFactor d δ)

theorem fullUpperScale_expansion (P : Parameters) (ν ε : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    fullUpperScale P ν ε γ =
      1+P.gradientNoise^2/ε^2+P.gap*P.gradientLip/ε^2+
      curvatureCountCoefficient P ν*γ^(-(1+2/ν))+
      P.gap*chordVarianceScale P/(ε^2*γ)+epochMinimum P ε+
      (1+curvatureCountCoefficient P ν*γ^(-(1+2/ν)))*(eigenHessianBound P)^2/γ^2 := by
  unfold fullUpperScale minimumTrackingScale mixedTrackingCost
  rw [idealMoveBudget_scale P ν ε hγ]
  ring

theorem one_le_minimumTrackingScale (P : Parameters) (ν : ℝ) {ε γ : ℝ}
    (hε : 0 < ε) (hγ : 0 < γ) : 1 ≤ minimumTrackingScale P ν ε γ := by
  have hm := idealMoveBudget_nonneg P ν ε γ hγ
  have he := epochMinimum_nonneg P hε
  have hv := (mixedTrackingCost_pos P hε hγ).le
  have ha : 0 ≤ P.gradientNoise^2/ε^2 := by positivity
  unfold minimumTrackingScale
  linarith

theorem fullUpper_scale_collect {a F T E : ℝ}
    (ha : 0 ≤ a) (hF : 0 ≤ F) (hT : 1 ≤ T) (hE : 0 ≤ E) :
    25+24*(a*T+F*E) ≤ (25+24*(a+F))*(T+E) := by
  have hTE : 1 ≤ T+E := by linarith
  have hT0 : 0 ≤ T := by linarith
  nlinarith [mul_nonneg ha hE, mul_nonneg hF hT0]

/-- The actual deterministic cap has the full original parameter
dependence, for every positive tolerance. The multiplier displays all
dimension, depth and confidence logarithms. -/
theorem stochasticUpperCap_full_scale (P : Parameters) (ν : ℝ) (d : ℕ)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) :
    (stochasticUpperCap P ν d ε γ : ℝ) <
      fullUpperLogFactor P ν d ε γ*fullUpperScale P ν ε γ := by
  let M := physicalCap P ν (ε/10) γ
  let L := trackingTreeDepth M
  let δ := localFailureTolerance M
  let κ := branchedOjaQueryCount P d γ δ
  let K := curvatureCountCoefficient P ν*γ^(-(1+2/ν))
  let H := 6144*(L:ℝ)^3*(8*Real.log (1/δ)+2)
  let E := (1+K)*(eigenHessianBound P)^2/γ^2
  have hK : 0 ≤ K :=
    mul_nonneg (curvatureCountCoefficient_pos P ν).le (Real.rpow_nonneg hγ.le _)
  have hH : 0 ≤ H := by
    have hh := chordConfidenceFactor_nonneg (localFailureTolerance_pos M) (localFailureTolerance_le_one M)
    dsimp only [H, δ]
    positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hτ : 0 < ε/10 := by positivity
  have hc := selectedQueryCap_minimum_bound P ν hτ hγ κ
  change (stochasticUpperCap P ν d ε γ : ℝ) <
    25+24*(H*minimumTrackingScale P ν (ε/10) γ+(1+K)*(κ:ℝ)) at hc
  have ht := mul_le_mul_of_nonneg_left (minimumTrackingScale_epsilon P ν hε hγ) hH
  have hp := mul_le_mul_of_nonneg_left
    (branchedOjaQueryCount_full_bound P d hγ (localFailureTolerance_pos M) (localFailureTolerance_le_one M))
    (show 0 ≤ 1+K by linarith)
  have hp' : (1+K)*(κ:ℝ) ≤ ojaFullPriceFactor d δ*E := by
    exact hp.trans_eq (by dsimp only [E]; ring)
  have hs : (stochasticUpperCap P ν d ε γ : ℝ) <
      25+24*((H*10000)*minimumTrackingScale P ν ε γ+ojaFullPriceFactor d δ*E) := by
    nlinarith [hc, ht, hp']
  have hg := fullUpper_scale_collect (show 0 ≤ H*10000 by positivity)
    (ojaFullPriceFactor_nonneg d δ) (one_le_minimumTrackingScale P ν hε hγ) hE
  exact hs.trans_le (hg.trans_eq (by
    dsimp only [fullUpperLogFactor, fullUpperScale, H, E, K, L, M, δ]
    ring))

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- Full nonasymptotic gradient/HVP upper bound for the already
implemented algorithm and its actual permitted-query list. -/
theorem CommonLoss.stochasticUpperRun_full_scale (h : CommonLoss μ P ν F f)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) :
    (∀ w : StochasticUpperTape Ω d P ν ε γ,
      ((stochasticUpperTrace P ν f ε γ w).length : ℝ) <
        fullUpperLogFactor P ν d ε γ*fullUpperScale P ν ε γ) ∧
    ENNReal.ofReal (29/32:ℝ) ≤ stochasticUpperLaw μ P ν d ε hγ
      {w | BudgetedSuccess F ε γ (stochasticUpperRun P ν f ε γ w)} := by
  refine ⟨fun w => ?_, h.stochasticUpperRun_success hε hγ⟩
  exact (Nat.cast_le.mpr (stochasticUpperTrace_cap P ν f ε γ w)).trans_lt
    (stochasticUpperCap_full_scale P ν d hε hγ)

end
end SecondOrder
