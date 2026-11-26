import ExplicitRate254

noncomputable section
namespace Paper254

/-- Parameter-uniform specialization of the clipped theorem. The constant
6144 is independent of D,G,eta,d,T and the comparator. -/
theorem explicit_curved_specialization {d T : ℕ} {D G η : ℝ} (W : Domain d D)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (hd : 0 < d) (hT : 0 < T) (w0 : W.carrier)
    (f : Fin T → Loss d) (hf : ∀ t, AdmissibleLoss W G η (f t)) (u : Fin T → W.carrier)
    (hsmall : pathLength u ≤ curvature D G η^2*G^2*T*D^3/(Real.sqrt (d+1 : ℝ)*logFactor T^2)) :
    regret (dyadicLearner W hD hG hη w0) f u ≤ 6144*
      ((d+1 : ℝ)*logFactor T^2/curvature D G η+
        explicitCurvedRate (curvature D G η) G d T (pathLength u)) := by
  let γ := curvature D G η
  let P := pathLength u
  let Λ := logFactor T
  let X := Real.sqrt (d+1 : ℝ)*Λ^2*P/(γ^2*G^2*T)
  let root := X^(1/3 : ℝ)
  let τ := max (D/T) root
  have hγ : 0 < γ := curvature_pos D G η hD hG hη
  have hP : 0 ≤ P := pathLength_nonneg u
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hL := logFactor_ge_one T hT
  have hden : 0 < γ^2*G^2*T := by positivity
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hr : 0 ≤ root := Real.rpow_nonneg hX0 _
  have hr3 : root^3 = X := third_rpow_cube X hX0
  have hXD : X ≤ D^3 := by
    have hs := (le_div_iff₀ (show 0 < Real.sqrt (d+1 : ℝ)*logFactor T^2 by positivity)).mp hsmall
    apply (div_le_iff₀ hden).mpr
    change P*(Real.sqrt (d+1 : ℝ)*Λ^2) ≤ γ^2*G^2*T*D^3 at hs
    nlinarith
  have hrD : root ≤ D := nonneg_le_of_cube_le _ _ hr hD.le (by rw [hr3]; exact hXD)
  have hlo : D/T ≤ τ := le_max_left _ _
  have hhi : τ ≤ D := max_le ((div_le_iff₀ hTr).mpr (by nlinarith)) hrD
  have hbal : γ^2*G^2*T*root^3 = Real.sqrt (d+1 : ℝ)*Λ^2*P := by
    rw [hr3]
    dsimp [X]
    field_simp
  have hb : (Real.sqrt (d+1 : ℝ)*Λ^2/γ)*P = (γ*G^2*T)*root^3 := by
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff (ne_of_gt hγ)).mpr
    convert hbal.symm using 1 <;> ring
  have hcost := clipped_balance_cost (Real.sqrt (d+1 : ℝ)*Λ^2/γ) (γ*G^2*T) P
    (D/T) root (by positivity) (by positivity) hP (div_pos hD hTr) hr hb
  have hexact := balanced_term_exact γ G root P d T hγ hG hT hP hr hbal
  have hfloor := explicit_floor_bound D G γ d T hD hG hγ hd hT
    (curvature_times_radius D G η hD hG)
  have hreg := dyadic_learner_clipped W hD hG hη hT w0 f hf u τ hlo hhi
  change regret (dyadicLearner W hD hG hη w0) f u ≤
    2048*((d+1 : ℝ)*Λ^2/γ+Real.sqrt (d+1 : ℝ)*Λ^2/(γ*τ)*P+γ*G^2*T*τ^2) at hreg
  change (Real.sqrt (d+1 : ℝ)*Λ^2/γ)*P/τ+γ*G^2*T*τ^2 ≤
    3*(γ*G^2*T)*root^2+2*(γ*G^2*T)*(D/T)^2 at hcost
  have he : (Real.sqrt (d+1 : ℝ)*Λ^2/γ)*P/τ = Real.sqrt (d+1 : ℝ)*Λ^2/(γ*τ)*P := by ring
  rw [he] at hcost
  change γ*G^2*T*(D/T)^2 ≤ (d+1 : ℝ)*Λ^2/γ at hfloor
  change regret (dyadicLearner W hD hG hη w0) f u ≤
    6144*((d+1 : ℝ)*Λ^2/γ+explicitCurvedRate γ G d T P)
  nlinarith

end Paper254
#print axioms Paper254.explicit_curved_specialization
