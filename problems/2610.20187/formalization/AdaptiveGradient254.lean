import GradientScale254
import OnlineAggregation254
import BasicBounds254

noncomputable section
namespace Paper254

theorem uniform_log_overhead (N : ℕ) (j : Fin (N+1)) :
    -Real.log ((uniformWeights N).weight j) = Real.log (N+1 : ℝ) := by
  change -Real.log (1/(N+1 : ℝ)) = _
  rw [Real.log_div (by norm_num) (ne_of_gt (show (0 : ℝ) < N+1 by positivity)), Real.log_one]
  ring

theorem gradient_grid_overhead (T : ℕ) (hT : 0 < T) (η : ℝ) (hη : 0 < η)
    (j : Fin (scaleCount T+1)) :
    -Real.log ((uniformWeights (scaleCount T)).weight j)/η ≤ logFactor T/η := by
  rw [uniform_log_overhead]
  apply div_le_div_of_nonneg_right _ hη.le
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hk : (scaleCount T : ℝ) ≤ T := by exact_mod_cast Nat.log_le_self 2 T
  have hh := Real.log_le_log (by positivity : (0 : ℝ) < scaleCount T+1)
    (show (scaleCount T+1 : ℝ) ≤ 2*T by linarith)
  unfold logFactor
  linarith

def adaptiveGradient {d T : ℕ} {D : ℝ} (W : Domain d D) (G η : ℝ)
    (w0 : W.carrier) : OnlineLearner W T :=
  aggregateOnline (uniformWeights (scaleCount T)) η w0
    (fun k => onlineProjectedGradient W G (dyadicScale (1+D) k.val) w0)

theorem adaptiveGradient_bound {d T : ℕ} {D G η : ℝ} (W : Domain d D)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (hT : 0 < T)
    (w0 : W.carrier) (f : Fin T → Loss d) (hf : ∀ t, AdmissibleLoss W G η (f t))
    (u : Fin T → W.carrier) :
    regret (adaptiveGradient W G η w0) f u ≤
      (D^2+2*D+G^2+G*D*(1+D))*Real.sqrt (T*(1+pathLength u))+logFactor T/η := by
  let P := pathLength u
  let R := Real.sqrt ((T : ℝ)*(1+P))
  have hP : 0 ≤ P := pathLength_nonneg u
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hL := logFactor_ge_one T hT
  have hlog : 0 ≤ logFactor T/η := by positivity
  have hA : 0 < 1+D := by positivity
  by_cases hlarge : (1+D)^2 ≤ (T : ℝ)
  · obtain ⟨hlo,hhi⟩ := gradient_scale_feasible D P hD hP T hT (pathLength_le_diameter hD.le u) hlarge
    obtain ⟨k,hkl,hkh⟩ := dyadic_scale_approx (1+D) hA T hT (R/T) hlo hhi
    have hmeta := aggregateOnline_regret (uniformWeights (scaleCount T)) hη w0
      (fun k => onlineProjectedGradient W G (dyadicScale (1+D) k.val) w0) f hf u k (by dsimp [uniformWeights]; positivity)
    have hbase := projectedGradient_online_bound W hT hη (dyadicScale_pos (1+D) hA k.val) w0 f hf u
    have hcost := gradient_scale_cost D G P hD hP T hT (dyadicScale (1+D) k.val) hkl hkh
    have hover := gradient_grid_overhead T hT η hη k
    change regret (adaptiveGradient W G η w0) f u ≤ _ at hmeta
    rw [sub_eq_add_neg, ← neg_div] at hmeta
    have hsum : regret (adaptiveGradient W G η w0) f u ≤ (D^2+2*D+G^2)*R+logFactor T/η := by
      linarith
    change _ ≤ (D^2+2*D+G^2+G*D*(1+D))*R+logFactor T/η
    nlinarith [mul_nonneg (show 0 ≤ G*D*(1+D) by positivity) hR]
  · have hb := linear_regret_bound (adaptiveGradient W G η w0) f u hG.le hf
    have hs : R^2 = (T : ℝ)*(1+P) := Real.sq_sqrt (by positivity)
    have ht : (T : ℝ) ≤ (1+D)*R := by
      have hm := mul_le_mul_of_nonneg_right (le_of_not_ge hlarge) hTr.le
      have hn := mul_nonneg (sq_nonneg (1+D)) (mul_nonneg hTr.le hP)
      have heq := congrArg (fun x : ℝ => (1+D)^2*x) hs
      by_contra hnot
      have hz := mul_pos (sub_pos.mpr (lt_of_not_ge hnot))
        (show 0 < (T : ℝ)+(1+D)*R by positivity)
      nlinarith
    have hm := mul_le_mul_of_nonneg_left ht (mul_nonneg hG.le hD.le)
    change _ ≤ (D^2+2*D+G^2+G*D*(1+D))*R+logFactor T/η
    nlinarith [mul_nonneg (show 0 ≤ D^2+2*D+G^2 by positivity) hR]

end Paper254
#print axioms Paper254.adaptiveGradient_bound
