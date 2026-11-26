import ClippedMain254
import FeasibleBalance254

noncomputable section
namespace Paper254

theorem main_curved : MainCurvedStatement := by
  intro D G η hD hG hη
  let γ := curvature D G η
  have hγ : 0 < γ := curvature_pos D G η hD hG hη
  let a := 2/γ+2*γ*G^2*D^2
  let b := 3*(1+2*G^2/γ)
  refine ⟨2048*(a+b), γ^2*G^2*D^3/2, by dsimp [a,b]; positivity, by positivity, ?_⟩
  intro d T hd hT W
  obtain ⟨w,hw⟩ := W.nonempty
  let w0 : W.carrier := ⟨w,hw⟩
  refine ⟨dyadicLearner W hD hG hη w0, ?_⟩
  intro f hf u hsmall
  let P := pathLength u
  let Λ := logFactor T
  let root := (Real.sqrt (d+1 : ℝ)*Λ^2*P/(γ^2*G^2*T))^(1/3 : ℝ)
  let τ := max (D/T) root
  have hP : 0 ≤ P := pathLength_nonneg u
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  obtain ⟨hr, _hrD, hbal, hlo, hhi⟩ := balanced_scale_feasible d T hd hT D G γ P hD hG hγ hP hsmall
  have hreg := dyadic_learner_clipped W hD hG hη hT w0 f hf u τ hlo hhi
  have hb : (Real.sqrt (d+1 : ℝ)*Λ^2/γ)*P = (γ*G^2*T)*root^3 := by
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff (ne_of_gt hγ)).mpr
    convert hbal.symm using 1 <;> ring
  have hcost := clipped_balance_cost (Real.sqrt (d+1 : ℝ)*Λ^2/γ)
    (γ*G^2*T) P (D/T) root (by positivity) (by positivity) hP (div_pos hD hTr) hr hb
  have hbalanced := balanced_curved_term d T hd hT γ G P root hγ hG hP hr hbal
  have hfloor := floor_smoothing_bound d T hd hT γ G D hγ
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hstatic : (d+1 : ℝ)*Λ^2/γ ≤ (2/γ)*((d : ℝ)*Λ^2) := by
    have hh := mul_le_mul_of_nonneg_right (show (d+1 : ℝ) ≤ 2*d by linarith)
      (show 0 ≤ Λ^2/γ by positivity)
    convert hh using 1 <;> ring
  have hS : 0 ≤ (d : ℝ)*Λ^2 := by positivity
  have hQ : 0 ≤ curvedRate d T P := curvedRate_nonneg d T P hP
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hbb : 0 ≤ b := by dsimp [b]; positivity
  have hm1 := mul_nonneg ha hQ
  have hm2 := mul_nonneg hbb hS
  change regret (dyadicLearner W hD hG hη w0) f u ≤
    2048*((d+1 : ℝ)*Λ^2/γ+Real.sqrt (d+1 : ℝ)*Λ^2/(γ*τ)*P+γ*G^2*T*τ^2) at hreg
  have he : (Real.sqrt (d+1 : ℝ)*Λ^2/γ)*P/τ = Real.sqrt (d+1 : ℝ)*Λ^2/(γ*τ)*P := by ring
  change (Real.sqrt (d+1 : ℝ)*Λ^2/γ)*P/τ+γ*G^2*T*τ^2 ≤
    3*(γ*G^2*T)*root^2+2*(γ*G^2*T)*(D/T)^2 at hcost
  rw [he] at hcost
  change regret (dyadicLearner W hD hG hη w0) f u ≤ 2048*(a+b)*((d : ℝ)*Λ^2+curvedRate d T P)
  change γ*G^2*T*(D/T)^2 ≤ γ*G^2*D^2*((d : ℝ)*Λ^2) at hfloor
  dsimp [a,b] at hm1 hm2 ⊢
  nlinarith

end Paper254
#print axioms Paper254.main_curved
