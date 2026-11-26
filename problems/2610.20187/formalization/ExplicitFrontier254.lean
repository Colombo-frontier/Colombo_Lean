import ExplicitCurved254
import ExplicitOutside254
import ScaledAdaptive254
import UpperMain254

noncomputable section
namespace Paper254

theorem explicit_full_frontier {d T : ℕ} {D G η : ℝ} (W : Domain d D)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (hd : 0 < d) (hT : 0 < T) :
    ∃ A : OnlineLearner W T, ∀ f : Fin T → Loss d,
      (∀ t, AdmissibleLoss W G η (f t)) → ∀ u : Fin T → W.carrier,
      regret A f u ≤ 8192*((d+1 : ℝ)*logFactor T^2/curvature D G η+
        min (explicitCurvedRate (curvature D G η) G d T (pathLength u))
          (min (gradientRate D G T (pathLength u)) (G*D*T))) := by
  obtain ⟨w,hw⟩ := W.nonempty
  let w0 : W.carrier := ⟨w,hw⟩
  let curved : OnlineLearner W T := dyadicLearner W hD hG hη w0
  let grad : OnlineLearner W T := scaledAdaptiveGradient W G η w0
  let experts : Fin 2 → OnlineLearner W T := fun j => if j.val = 0 then curved else grad
  let learner := aggregateOnline (uniformWeights 1) η w0 experts
  refine ⟨learner,?_⟩
  intro f hf u
  let γ := curvature D G η
  let S := (d+1 : ℝ)*logFactor T^2/γ
  let E := explicitCurvedRate γ G d T (pathLength u)
  let U := gradientRate D G T (pathLength u)
  have hγ := curvature_pos D G η hD hG hη
  have hL := logFactor_ge_one T hT
  have hP := pathLength_nonneg u
  have hS : 0 ≤ S := by dsimp [S,γ]; positivity
  have hE : 0 ≤ E := by dsimp [E,explicitCurvedRate]; positivity
  have hU : 0 ≤ U := by dsimp [U,gradientRate]; positivity
  have hcap : 0 ≤ G*D*T := by positivity
  have hmeta0 := aggregateOnline_regret (uniformWeights 1) hη w0 experts f hf u (0 : Fin 2) (by norm_num [uniformWeights])
  have hmeta1 := aggregateOnline_regret (uniformWeights 1) hη w0 experts f hf u (1 : Fin 2) (by norm_num [uniformWeights])
  change regret learner f u ≤ regret curved f u-Real.log ((uniformWeights 1).weight 0)/η at hmeta0
  change regret learner f u ≤ regret grad f u-Real.log ((uniformWeights 1).weight 1)/η at hmeta1
  rw [sub_eq_add_neg, ← neg_div] at hmeta0 hmeta1
  have ho0 := binary_overhead T hT η hη (0 : Fin 2)
  have ho1 := binary_overhead T hT η hη (1 : Fin 2)
  have hlog : logFactor T/η ≤ S := explicit_overhead_absorbed D G η d T hD hG hη hT
  have hgrad : regret grad f u ≤ 2*U+logFactor T/η := scaledAdaptiveGradient_bound W hD hG hη hT w0 f hf u
  have hUE : regret learner f u ≤ 8192*(S+E) := by
    by_cases hs : pathLength u ≤ γ^2*G^2*T*D^3/(Real.sqrt (d+1 : ℝ)*logFactor T^2)
    · have hc : regret curved f u ≤ 6144*(S+E) := explicit_curved_specialization W hD hG hη hd hT w0 f hf u hs
      linarith
    · have hu : U ≤ S+2*E := explicit_outside_bound D G η d T (pathLength u) hD hG hη hT hP (le_of_not_ge hs)
      linarith
  have hUU : regret learner f u ≤ 8192*(S+U) := by linarith
  have hUT : regret learner f u ≤ 8192*(S+G*D*T) := by
    have hh := linear_regret_bound learner f u hG.le hf
    linarith
  change regret learner f u ≤ 8192*(S+min E (min U (G*D*T)))
  by_cases he : E ≤ min U (G*D*T)
  · rwa [min_eq_left he]
  · rw [min_eq_right (le_of_not_ge he)]
    by_cases hu : U ≤ G*D*T
    · rwa [min_eq_left hu]
    · rwa [min_eq_right (le_of_not_ge hu)]

end Paper254
#print axioms Paper254.explicit_full_frontier
