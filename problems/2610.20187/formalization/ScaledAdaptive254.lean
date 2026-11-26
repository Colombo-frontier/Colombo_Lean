import ScaledGradient254

noncomputable section
namespace Paper254

def scaledAdaptiveGradient {d T : ℕ} {D : ℝ} (W : Domain d D) (G η : ℝ)
    (w0 : W.carrier) : OnlineLearner W T :=
  aggregateOnline (uniformWeights (scaleCount T)) η w0
    (fun k => onlineProjectedGradient W G (dyadicScale (2*D/G) k.val) w0)

theorem scaledAdaptiveGradient_bound {d T : ℕ} {D G η : ℝ} (W : Domain d D)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (hT : 0 < T)
    (w0 : W.carrier) (f : Fin T → Loss d) (hf : ∀ t, AdmissibleLoss W G η (f t))
    (u : Fin T → W.carrier) :
    regret (scaledAdaptiveGradient W G η w0) f u ≤
      2*gradientRate D G T (pathLength u)+logFactor T/η := by
  let P := pathLength u
  let R := gradientRate D G T P
  have hP : 0 ≤ P := pathLength_nonneg u
  have hR : 0 < R := by dsimp [R,gradientRate]; positivity
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hL := logFactor_ge_one T hT
  have hlog : 0 ≤ logFactor T/η := by positivity
  by_cases hlarge : (4 : ℝ) ≤ T
  · obtain ⟨hlo,hhi⟩ := scaled_gradient_feasible D G P T hD hG hP (pathLength_le_diameter hD.le u) hlarge
    obtain ⟨k,hkl,hkh⟩ := dyadic_scale_approx (2*D/G) (by positivity) T hT (R/(G^2*T)) hlo hhi
    have hmeta := aggregateOnline_regret (uniformWeights (scaleCount T)) hη w0
      (fun k => onlineProjectedGradient W G (dyadicScale (2*D/G) k.val) w0) f hf u k (by dsimp [uniformWeights]; positivity)
    have hbase := projectedGradient_online_bound W hT hη (dyadicScale_pos (2*D/G) (by positivity) k.val) w0 f hf u
    have hcost := scaled_gradient_cost D G P (dyadicScale (2*D/G) k.val) T hD hG hP hT hkl hkh
    have hover := gradient_grid_overhead T hT η hη k
    change regret (scaledAdaptiveGradient W G η w0) f u ≤ _ at hmeta
    rw [sub_eq_add_neg, ← neg_div] at hmeta
    linarith
  · have hb := linear_regret_bound (scaledAdaptiveGradient W G η w0) f u hG.le hf
    have hs : R^2 = G^2*T*(D^2+D*P) := gradientRate_square D G P T hD hG hP
    have hcap : G*D*T ≤ 2*R := by
      have ht : (T : ℝ)^2 ≤ 4*T := by nlinarith
      have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ G^2*D^2 by positivity)
      have hp := mul_nonneg (show 0 ≤ G^2*T*D by positivity) hP
      by_contra hh
      have hx := mul_pos (sub_pos.mpr (lt_of_not_ge hh)) (show 0 < G*D*T+2*R by positivity)
      nlinarith
    change _ ≤ 2*R+logFactor T/η
    linarith

end Paper254
#print axioms Paper254.scaledAdaptiveGradient_bound
