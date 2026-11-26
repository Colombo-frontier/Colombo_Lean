import SecondOrder.OjaPriceLog
import SecondOrder.ConditionalUpperRate

namespace SecondOrder
noncomputable section

def ojaSelectedPriceCoefficient (P : Parameters) (ν : ℝ) (d : ℕ) : ℝ :=
  ojaPriceCoefficient P d*(confidenceToleranceCoefficient P ν*(1+Real.log 10))^2

theorem ojaSelectedPriceCoefficient_pos (P : Parameters) {ν : ℝ} (hν : 0 < ν) (d : ℕ) :
    0 < ojaSelectedPriceCoefficient P ν d := by
  have hC := confidenceToleranceCoefficient_pos P hν
  have hP := ojaPriceCoefficient_pos P d
  have h10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  unfold ojaSelectedPriceCoefficient
  positivity

theorem ojaSelected_confidenceLog (P : Parameters) {ν τ γ : ℝ}
    (hν : 0 < ν) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ojaConfidenceLog (localFailureTolerance (physicalCap P ν τ γ)) ≤
      confidenceToleranceCoefficient P ν*toleranceLog τ γ := by
  have hl := one_le_ojaConfidenceLog (localFailureTolerance_pos (physicalCap P ν τ γ))
    (localFailureTolerance_le_one _)
  have hc := (selectedConfidence_log_bound P ν τ hγ).trans
    (confidenceLogEnvelope_tolerances P hν hτ hτ1 hγ hγ1)
  unfold ojaConfidenceLog at *
  linarith

/-- The concrete curvature-query price satisfies exactly the price
contract required by the selected optimizer's tolerance-rate theorem. -/
theorem ojaSelectedQueryCount_rate (P : Parameters) {d : ℕ} (hd : 0 < d)
    {ν ε γ : ℝ} (hν : 0 < ν) (hε : 0 < ε) (hε1 : ε ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hγB : γ ≤ 4*eigenHessianBound P) :
    (ojaAmplifiedQueryCount P d γ (localFailureTolerance (physicalCap P ν (ε/10) γ)):ℝ) ≤
      ojaSelectedPriceCoefficient P ν d*(toleranceLog ε γ)^4/γ^2 := by
  let δ := localFailureTolerance (physicalCap P ν (ε/10) γ)
  let J := toleranceLog ε γ
  let C := confidenceToleranceCoefficient P ν*(1+Real.log 10)
  have hδ := localFailureTolerance_pos (physicalCap P ν (ε/10) γ)
  have hδ1 := localFailureTolerance_le_one (physicalCap P ν (ε/10) γ)
  have hJ : 1 ≤ J := one_le_toleranceLog hε hε1 hγ hγ1
  have hJ0 : 0 ≤ J := by linarith
  have hC : 0 ≤ C := by
    have hc := confidenceToleranceCoefficient_pos P hν
    have hl : 0 < Real.log 10 := Real.log_pos (by norm_num)
    dsimp only [C]; positivity
  have hL : 0 ≤ ojaConfidenceLog δ := (by norm_num : (0:ℝ) ≤ 1).trans (one_le_ojaConfidenceLog hδ hδ1)
  have hLC : ojaConfidenceLog δ ≤ C*J := by
    have ht := ojaSelected_confidenceLog P hν (show 0 < ε/10 by positivity)
      (show ε/10 ≤ 1 by linarith) hγ hγ1
    have he := mul_le_mul_of_nonneg_left (toleranceLog_epsilon_bounds hε hε1 hγ hγ1).2
      (confidenceToleranceCoefficient_pos P hν).le
    exact ht.trans (he.trans_eq (by dsimp only [C,J]; ring))
  have hJ24 : J^2 ≤ J^4 := by
    have hJ2 : (1:ℝ) ≤ J^2 := one_le_pow₀ hJ
    nlinarith [mul_nonneg (sq_nonneg J) (sub_nonneg.mpr hJ2)]
  have hP := ojaPriceCoefficient_pos P d
  calc
    _ ≤ ojaPriceCoefficient P d*(ojaConfidenceLog δ)^2/γ^2 :=
      ojaAmplifiedQueryCount_log_bound P hd hγ hγ1 hγB hδ hδ1
    _ ≤ ojaPriceCoefficient P d*(C*J)^2/γ^2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL hLC 2) hP.le) (sq_nonneg γ)
    _ = ojaSelectedPriceCoefficient P ν d*J^2/γ^2 := by
      unfold ojaSelectedPriceCoefficient
      dsimp only [C]
      ring
    _ ≤ ojaSelectedPriceCoefficient P ν d*J^4/γ^2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hJ24 (ojaSelectedPriceCoefficient_pos P hν d).le) (sq_nonneg γ)

end
end SecondOrder
