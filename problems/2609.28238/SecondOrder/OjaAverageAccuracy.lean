import SecondOrder.OjaIterationScale

open MeasureTheory
open scoped InnerProductSpace Classical

namespace SecondOrder
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- With a fully specified learning rate and integer horizon, the average
population Rayleigh value is within ε/4 of the top eigenvalue with constant
probability. Only the original model assumptions remain. -/
theorem CommonLoss.oja_average_accuracy (h : CommonLoss μ P ν F f) (hd : 0 < d)
    {ε : ℝ} (hε : 0 < ε) (x : Point d) :
    (1:ℝ)/48 ≤ (ojaRandomLaw μ d (ojaIterationCount d ε)).real {w |
      (topRayleigh (shiftedHessian (eigenHessianBound P) (hessian F x)) - ε/4) *
        (ojaIterationCount d ε : ℝ) ≤
          ojaRandomMeanRayleighSum P F f (ojaLearningRate d ε) x (ojaIterationCount d ε) w} := by
  let t : ℝ := ojaScale d ε
  let ℓ : ℝ := topRayleigh (shiftedHessian (eigenHessianBound P) (hessian F x))
  have ht0 : 0 < t := Nat.cast_pos.mpr (ojaScale_pos hd hε)
  have ht1 : 1 ≤ t := by
    change (1:ℝ) ≤ (ojaScale d ε : ℝ)
    exact_mod_cast (Nat.succ_le_iff.mpr (ojaScale_pos hd hε))
  have hℓ1 : ℓ ≤ 1 := (h.mean_shifted_top_eigenpair hd x).2.1
  have hη := (ojaLearningRate_pos hd hε).le
  have hη1 := ojaLearningRate_le_one hd hε
  have hscale : ojaLearningRate d ε ^ 2 * ℓ * (ojaIterationCount d ε : ℝ) ≤ (1/2:ℝ)/100 := by
    simpa only [ojaLearningRate,ojaIterationCount,Nat.cast_pow,t] using
      oja_square_scale_moment ht0 hℓ1
  have hr : 0 < 8*t := by positivity
  have hp := h.ojaRandomMeanRayleighSum_regret hd hη hη1
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (1/2:ℝ) ≤ 1 by norm_num) hr x
    (ojaIterationCount d ε) hscale
  have hprob : (1:ℝ)/48 ≤ (1-(1/2:ℝ))/12 - (ojaIterationCount d ε : ℝ)/(8*t)^2 := by
    simpa only [ojaIterationCount,Nat.cast_pow,t] using oja_square_scale_probability ht0
  refine (hprob.trans hp).trans ?_
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro w hw
  have hL := oja_log_dimension_nonneg hd
  have hreg : ℓ*t^2 - ojaRandomMeanRayleighSum P F f (ojaLearningRate d ε) x
      (ojaIterationCount d ε) w ≤ 20*(1+Real.log (4*(d:ℝ)))*t := by
    apply oja_square_scale_regret ht1 hL
    simpa only [Set.mem_setOf_eq,ojaLearningRate,ojaIterationCount,Nat.cast_pow,t,ℓ] using hw
  have htol := mul_le_mul_of_nonneg_right (ojaScale_lower d hε) ht0.le
  change (ℓ-ε/4)*(ojaIterationCount d ε : ℝ) ≤ _
  have hN : (ojaIterationCount d ε : ℝ) = t^2 := by simp only [ojaIterationCount,Nat.cast_pow,t]
  rw [hN]
  change 80*(1+Real.log (4*(d:ℝ)))*t ≤ ε*t*t at htol
  nlinarith

end
end SecondOrder
