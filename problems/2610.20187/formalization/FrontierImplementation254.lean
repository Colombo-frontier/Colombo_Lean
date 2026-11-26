import FrontierRuntime254

noncomputable section
open scoped BigOperators
namespace Paper254

def implementedFrontier {d T : ℕ} {D G eta : ℝ} (W : Domain d D)
    (hD : 0<D) (hG : 0<G) (heta : 0<eta) (w0 : W.carrier) : OnlineLearner W T :=
  frontierWithBase W G eta w0 (dyadicLearner W hD hG heta w0)

/-- The concrete nested learner refined by the cached frontier state has
the full statistical frontier; no regret bound is an input to this theorem. -/
theorem implementedFrontier_regret {d T : ℕ} {D G eta : ℝ} (W : Domain d D)
    (hD : 0<D) (hG : 0<G) (heta : 0<eta) (hd : 0<d) (hT : 0<T)
    (w0 : W.carrier) (f : Fin T → Loss d) (hf : ∀ t,AdmissibleLoss W G eta (f t))
    (u : Fin T → W.carrier) :
    regret (implementedFrontier W hD hG heta w0) f u≤
      8192*((d+1 : ℝ)*logFactor T^2/curvature D G eta+
        min (explicitCurvedRate (curvature D G eta) G d T (pathLength u))
          (min (gradientRate D G T (pathLength u)) (G*D*T))) := by
  let curved : OnlineLearner W T := dyadicLearner W hD hG heta w0
  let grad : OnlineLearner W T := scaledAdaptiveGradient W G eta w0
  let experts : Fin 2 → OnlineLearner W T := fun j => if j.val=0 then curved else grad
  let learner := aggregateOnline (uniformWeights 1) eta w0 experts
  change regret learner f u≤_
  let gamma := curvature D G eta
  let S := (d+1 : ℝ)*logFactor T^2/gamma
  let E := explicitCurvedRate gamma G d T (pathLength u)
  let U := gradientRate D G T (pathLength u)
  have hgamma := curvature_pos D G eta hD hG heta
  have hL := logFactor_ge_one T hT
  have hP := pathLength_nonneg u
  have hS : 0≤S := by dsimp [S,gamma]; positivity
  have hE : 0≤E := by dsimp [E,explicitCurvedRate]; positivity
  have hU : 0≤U := by dsimp [U,gradientRate]; positivity
  have hcap : 0≤G*D*T := by positivity
  have hmeta0 := aggregateOnline_regret (uniformWeights 1) heta w0 experts f hf u
    (0 : Fin 2) (by norm_num [uniformWeights])
  have hmeta1 := aggregateOnline_regret (uniformWeights 1) heta w0 experts f hf u
    (1 : Fin 2) (by norm_num [uniformWeights])
  change regret learner f u≤regret curved f u-Real.log ((uniformWeights 1).weight 0)/eta at hmeta0
  change regret learner f u≤regret grad f u-Real.log ((uniformWeights 1).weight 1)/eta at hmeta1
  rw [sub_eq_add_neg,←neg_div] at hmeta0 hmeta1
  have ho0 := binary_overhead T hT eta heta (0 : Fin 2)
  have ho1 := binary_overhead T hT eta heta (1 : Fin 2)
  have hlog : logFactor T/eta≤S := explicit_overhead_absorbed D G eta d T hD hG heta hT
  have hgrad : regret grad f u≤2*U+logFactor T/eta :=
    scaledAdaptiveGradient_bound W hD hG heta hT w0 f hf u
  have hUE : regret learner f u≤8192*(S+E) := by
    by_cases hs : pathLength u≤gamma^2*G^2*T*D^3/(Real.sqrt (d+1 : ℝ)*logFactor T^2)
    · have hc : regret curved f u≤6144*(S+E) :=
        explicit_curved_specialization W hD hG heta hd hT w0 f hf u hs
      linarith
    · have hu : U≤S+2*E := explicit_outside_bound D G eta d T (pathLength u)
        hD hG heta hT hP (le_of_not_ge hs)
      linarith
  have hUU : regret learner f u≤8192*(S+U) := by linarith
  have hUT : regret learner f u≤8192*(S+G*D*T) := by
    have hh := linear_regret_bound learner f u hG.le hf
    linarith
  change regret learner f u≤8192*(S+min E (min U (G*D*T)))
  by_cases he : E≤min U (G*D*T)
  · rwa [min_eq_left he]
  · rw [min_eq_right (le_of_not_ge he)]
    by_cases hu : U≤G*D*T
    · rwa [min_eq_left hu]
    · rwa [min_eq_right (le_of_not_ge hu)]

theorem implementedFrontier_prediction {d T : ℕ} {D G eta : ℝ} (W : Domain d D)
    (hD : 0<D) (hG : 0<G) (heta : 0<eta) (lc gc pc ec : ℕ)
    (w0 : W.carrier) (f : Fin T → Loss d) (t : Fin T) :
    let ff := extendFinite (fun _ => 0) f
    let curve := expertTrajectory (T := T) w0 (dyadicLearner W hD hG heta w0) ff
    (frontierStateRun W lc gc pc ec G eta
      (fun k : Fin (scaleCount T+1) => dyadicScale (2*D/G) k.val) w0 ff curve t.val).prediction (curve t.val)=
      predictions (implementedFrontier W hD hG heta w0) f t :=
  frontier_runtime_prediction W lc gc pc ec G eta w0 (dyadicLearner W hD hG heta w0) f t

/-- Additional real arithmetic and oracle work of the full-frontier wrapper.
The curved engine's separately certified cost is added to this expression. -/
theorem implementedFrontier_total_overhead {d T : ℕ} {D G eta : ℝ} (W : Domain d D)
    (hD : 0<D) (hG : 0<G) (heta : 0<eta) (hT : 0<T) (lc gc pc ec : ℕ)
    (w0 : W.carrier) (f : Fin T → Loss d) :
    let ff := extendFinite (fun _ => 0) f
    let curve := expertTrajectory (T := T) w0 (dyadicLearner W hD hG heta w0) ff
    ((∑ t : Fin T,((frontierStateRun W lc gc pc ec G eta
      (fun k : Fin (scaleCount T+1) => dyadicScale (2*D/G) k.val) w0 ff curve t.val).round
      lc gc pc ec G eta (fun k => dyadicScale (2*D/G) k.val) (ff t.val) (curve t.val)).2 : ℕ) : ℝ)≤
      20*T*logFactor T*((d+lc+gc+pc+ec+2 : ℕ) : ℝ) := by
  intro ff curve
  rw [frontierStateRun_total_overhead]
  push_cast
  have hh := mul_le_mul_of_nonneg_left (frontier_overhead_log_bound d T lc gc pc ec hT)
    (Nat.cast_nonneg T : (0 : ℝ)≤T)
  push_cast at hh
  nlinarith

end Paper254
#print axioms Paper254.implementedFrontier_regret
#print axioms Paper254.implementedFrontier_prediction
#print axioms Paper254.implementedFrontier_total_overhead
