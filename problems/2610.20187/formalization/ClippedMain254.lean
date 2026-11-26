import NormalizedGrid254
import BasicBounds254

noncomputable section
namespace Paper254

theorem dyadic_learner_clipped {d T : ℕ} {D G η : ℝ} (W : Domain d D)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (hT : 0 < T) (w0 : W.carrier)
    (f : Fin T → Loss d) (hf : ∀ t, AdmissibleLoss W G η (f t))
    (u : Fin T → W.carrier) (τ : ℝ) (hlo : D/T ≤ τ) (hhi : τ ≤ D) :
    regret (dyadicLearner W hD hG hη w0) f u ≤ 2048*
      ((d+1 : ℝ)*logFactor T^2/curvature D G η+
        Real.sqrt (d+1 : ℝ)*logFactor T^2/(curvature D G η*τ)*pathLength u+
        curvature D G η*G^2*T*τ^2) := by
  obtain ⟨k, hklo, hkhi⟩ := dyadic_scale_approx D hD T hT τ hlo hhi
  have hh := normalized_grid_bound W hD hG hη hT w0 f hf u k
  let γ := curvature D G η
  let Λ := logFactor T
  let τk := dyadicScale D k.val
  have hγ : 0 < γ := curvature_pos D G η hD hG hη
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hτ : 0 < τ := lt_of_lt_of_le (div_pos hD hTr) hlo
  have hτk : 0 < τk := dyadicScale_pos D hD k.val
  have hp := pathLength_nonneg u
  have hm := div_le_div_of_nonneg_left
    (show 0 ≤ Real.sqrt (d+1 : ℝ)*Λ^2 by positivity) (mul_pos hγ hτ)
    (mul_le_mul_of_nonneg_left hklo hγ.le)
  have hmp := mul_le_mul_of_nonneg_right hm hp
  have hsq : τk^2 ≤ 4*τ^2 := by nlinarith
  have hsm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ γ*G^2*T/2 by positivity)
  have hs0 : 0 ≤ (d+1 : ℝ)*Λ^2/γ := by positivity
  have hm0 : 0 ≤ Real.sqrt (d+1 : ℝ)*Λ^2/(γ*τ)*pathLength u := by positivity
  have hsm0 : 0 ≤ γ*G^2*T*τ^2 := by positivity
  change regret (dyadicLearner W hD hG hη w0) f u ≤
    24*(d+1 : ℝ)*Λ^2/γ+1024*(Real.sqrt (d+1 : ℝ)*Λ^2/(γ*τk))*pathLength u+γ*G^2*T*τk^2/2 at hh
  change regret (dyadicLearner W hD hG hη w0) f u ≤
    2048*((d+1 : ℝ)*Λ^2/γ+Real.sqrt (d+1 : ℝ)*Λ^2/(γ*τ)*pathLength u+γ*G^2*T*τ^2)
  change Real.sqrt (d+1 : ℝ)*Λ^2/(γ*τk)*pathLength u ≤
    Real.sqrt (d+1 : ℝ)*Λ^2/(γ*τ)*pathLength u at hmp
  ring_nf at hh hmp hsm hs0 hm0 hsm0 ⊢
  nlinarith

/-- Parameter-explicit clipped main upper theorem. Every analytic and
algorithmic dependency is a proved theorem; no regret interface is assumed. -/
theorem main_clipped_upper : ClippedUpperStatement := by
  refine ⟨2048, by norm_num, ?_⟩
  intro D G η hD hG hη d T _hd hT W
  obtain ⟨w, hw⟩ := W.nonempty
  let w0 : W.carrier := ⟨w,hw⟩
  refine ⟨dyadicLearner W hD hG hη w0, ?_⟩
  intro f hf u
  refine ⟨linear_regret_bound _ f u hG.le hf, ?_⟩
  intro τ hlo hhi
  exact dyadic_learner_clipped W hD hG hη hT w0 f hf u τ hlo hhi

end Paper254
#print axioms Paper254.main_clipped_upper
