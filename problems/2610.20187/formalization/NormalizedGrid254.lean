import LogBudget254
import BudgetNormalization254

noncomputable section
namespace Paper254

def dyadicLearner {d T : ℕ} {D G η : ℝ} (W : Domain d D)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (w0 : W.carrier) : OnlineLearner W T :=
  sparseOnlineLearner W hD hG hη w0 (dyadicVariance D T) (dyadicVariance_pos D hD T)

theorem normalized_grid_bound {d T : ℕ} {D G η : ℝ} (W : Domain d D)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (hT : 0 < T) (w0 : W.carrier)
    (f : Fin T → Loss d) (hf : ∀ t, AdmissibleLoss W G η (f t))
    (u : Fin T → W.carrier) (k : Fin (scaleCount T+1)) :
    regret (dyadicLearner W hD hG hη w0) f u ≤
      24*(d+1 : ℝ)*logFactor T^2/curvature D G η+
      1024*(Real.sqrt (d+1 : ℝ)*logFactor T^2/(curvature D G η*dyadicScale D k.val))*pathLength u+
      curvature D G η*G^2*T*(dyadicScale D k.val)^2/2 := by
  let γ := curvature D G η
  let Λ := logFactor T
  let τ := dyadicScale D k.val
  let L := scaleCount T+1
  let a := masterOverhead T (scaleCount T) (γ/2)
  let B := birthBudget d D (τ^2)
  let H := restartThreshold L a B (γ/2)
  let V := variationThreshold L a B (γ/2) (τ^2)
  have hγ : 0 < γ := curvature_pos D G η hD hG hη
  have hlam : 0 < γ/2 := by positivity
  have hτ : 0 < τ := dyadicScale_pos D hD k.val
  have hΛ : 0 ≤ Λ := le_trans (by norm_num) (logFactor_ge_one T hT)
  have hL : (0 : ℝ) < L := by dsimp [L]; positivity
  have ha : 0 ≤ a := masterOverhead_nonneg T (scaleCount T) _ hlam
  have hB : 0 < B := birthBudget_positive d D (τ^2) hD (sq_pos_of_pos hτ)
  have hLmax : (L : ℝ) ≤ 2*Λ := by
    simpa only [L, Nat.cast_add, Nat.cast_one] using scaleDepth_log_bound T hT
  have haMax : a*(γ/2) ≤ 2*Λ := (le_div_iff₀ hlam).mp (masterOverhead_log_bound T hT _ hlam)
  have hrange := dyadicScale_range D hD T hT k
  have hBmax : B ≤ (d+1 : ℝ)*Λ := birthBudget_log_bound d T hT D τ hD hrange.1 hrange.2
  have hs := restart_static_normalization a B γ L Λ (d+1 : ℝ) ha hB.le hγ hL.le hΛ
    (by linarith [Nat.cast_nonneg d (α := ℝ)]) hLmax haMax hBmax
  have hm := restart_movement_normalization a B γ L Λ (d+1 : ℝ) τ ha hB hγ hL hΛ
    (by linarith [Nat.cast_nonneg d (α := ℝ)]) hτ hLmax haMax hBmax
  have hp := mul_le_mul_of_nonneg_right hm (pathLength_nonneg u)
  have hpow : T < 2^L := Nat.lt_pow_succ_log_self (by norm_num) T
  have hh := sparse_online_fixed_scale W hD hG hη w0 (dyadicVariance D T)
    (dyadicVariance_pos D hD T) f hf u k L (by dsimp [L]; omega) hpow
  change regret (dyadicLearner W hD hG hη w0) f u ≤ (H/64)*(1+pathLength u/V)+γ*G^2*T*τ^2/2 at hh
  have he : (H/64)*(1+pathLength u/V) = H/64+((H/64)/V)*pathLength u := by ring
  rw [he] at hh
  change H/64 ≤ _ at hs
  change ((H/64)/V)*pathLength u ≤ _ at hp
  have hp' : ((H/64)/V)*pathLength u ≤
      1024*(Real.sqrt (d+1 : ℝ)*Λ^2/(γ*τ))*pathLength u := by
    convert hp using 1 <;> ring
  change regret (dyadicLearner W hD hG hη w0) f u ≤
    24*(d+1 : ℝ)*Λ^2/γ+1024*(Real.sqrt (d+1 : ℝ)*Λ^2/(γ*τ))*pathLength u+γ*G^2*T*τ^2/2
  linarith

end Paper254
#print axioms Paper254.normalized_grid_bound
