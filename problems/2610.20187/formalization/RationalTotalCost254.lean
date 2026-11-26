import RationalRoundCost254

noncomputable section
open scoped BigOperators
namespace Paper254

theorem standardLiveCap_log_bound (T : ℕ) (hT : 0<T) :
    (standardLiveCap T (scaleCount T):ℝ)≤40*logFactor T^2 := by
  have ht : (1:ℝ)≤T := by exact_mod_cast hT
  have hp : (0:ℝ)<2*(T+1:ℝ) := by positivity
  have hb : 2*(T+1:ℝ)≤(2*T)^2 := by nlinarith
  have hl:=Real.log_le_log hp hb
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hplus : logFactor (T+1)≤2*logFactor T := by
    unfold logFactor
    push_cast
    linarith
  have h₁:=scaleDepth_log_bound (T+1) (by omega)
  have h₂:=scaleDepth_log_bound T hT
  have hL:=logFactor_ge_one T hT
  have hprod:=mul_le_mul (h₁.trans (mul_le_mul_of_nonneg_left hplus (by norm_num))) h₂
    (by positivity : (0:ℝ)≤scaleCount T+1) (by positivity : 0≤2*(2*logFactor T))
  unfold standardLiveCap
  push_cast
  change 5*(scaleCount (T+1)+1:ℝ)*(scaleCount T+1:ℝ)≤_
  nlinarith

theorem countedStandardRound_cost {d T K : ℕ} (hd : 0<d)
    (p roundCost projectionCost gradientCost : ℕ) (oracle : RationalProjectionProcedure d)
    (cfg : Fin ((T+1)*(K+1))→RationalHistoryParameters)
    (lam : ℚ) (S : RationalSparseData d ((T+1)*(K+1))) (query : RationalGradientQuery d)
    (t C : ℕ) (hcfg : ∀ e,historyStepCostBound d roundCost projectionCost (cfg e)≤C) :
    (countedRationalRound p roundCost projectionCost gradientCost oracle cfg
      ((standardRationalSchedule T K).live t) ((standardRationalSchedule T K).live (t+1))
      ((standardRationalSchedule T K).prior t) ((standardRationalSchedule T K).share t) lam S query).2≤
      standardLiveCap T K*(C+5*d+6*p+2*roundCost+65)+2*p+4+gradientCost := by
  apply (countedRationalRound_cost hd p roundCost projectionCost gradientCost oracle cfg _ _ _ _ lam S query C hcfg).trans
  have h₁:=Nat.mul_le_mul_right (C+5*d+3*p+roundCost+32)
    (standardRationalSchedule_uniform_card T K t)
  have h₂:=Nat.mul_le_mul_right (3*p+roundCost+33)
    (standardRationalSchedule_uniform_card T K (t+1))
  nlinarith

/-- Total charge of the complete round program along any state sequence;
the subsequent compact-state refinement supplies the actual trajectory. -/
theorem countedStandardRounds_total_cost {d T : ℕ} (hd : 0<d) (hT : 0<T)
    (p roundCost projectionCost gradientCost : ℕ) (oracle : RationalProjectionProcedure d)
    (cfg : Fin ((T+1)*(scaleCount T+1))→RationalHistoryParameters)
    (lam : ℚ) (states : ℕ→RationalSparseData d ((T+1)*(scaleCount T+1)))
    (query : ℕ→RationalGradientQuery d) (C : ℕ)
    (hcfg : ∀ e,historyStepCostBound d roundCost projectionCost (cfg e)≤C) :
    (∑ t∈Finset.range T,
      ((countedRationalRound p roundCost projectionCost gradientCost oracle cfg
        ((standardRationalSchedule T (scaleCount T)).live t)
        ((standardRationalSchedule T (scaleCount T)).live (t+1))
        ((standardRationalSchedule T (scaleCount T)).prior t)
        ((standardRationalSchedule T (scaleCount T)).share t) lam (states t) (query t)).2:ℝ))≤
      40*T*logFactor T^2*(C+5*d+6*p+2*roundCost+65:ℝ)+T*(2*p+4+gradientCost:ℝ) := by
  have hh:=Finset.sum_le_sum (s:=Finset.range T) (fun t ht=>
    countedStandardRound_cost hd p roundCost projectionCost gradientCost oracle cfg lam (states t)
      (query t) t C hcfg)
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hh
  have hr : (∑ t∈Finset.range T,
      ((countedRationalRound p roundCost projectionCost gradientCost oracle cfg
        ((standardRationalSchedule T (scaleCount T)).live t)
        ((standardRationalSchedule T (scaleCount T)).live (t+1))
        ((standardRationalSchedule T (scaleCount T)).prior t)
        ((standardRationalSchedule T (scaleCount T)).share t) lam (states t) (query t)).2:ℝ))≤
      T*((standardLiveCap T (scaleCount T):ℝ)*(C+5*d+6*p+2*roundCost+65:ℝ)+2*p+4+gradientCost) := by
    exact_mod_cast hh
  apply hr.trans
  have hb:=mul_le_mul_of_nonneg_right (standardLiveCap_log_bound T hT)
    (show (0:ℝ)≤C+5*d+6*p+2*roundCost+65 by positivity)
  have ht:=mul_le_mul_of_nonneg_left hb (show (0:ℝ)≤T by positivity)
  nlinarith

end Paper254
#print axioms Paper254.standardLiveCap_log_bound
#print axioms Paper254.countedStandardRounds_total_cost
