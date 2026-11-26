import FreshGradientMinimax.SaddleGeometry

/-! Elimination of the strongly convex fast variable in F.1. The effective
gradient is the actual derivative of q(v) = -min_u g(u,v), and its smoothness
is at most 5ℓ when α ≥ ℓ/4. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem alpha_le_smooth_of_distinct (S : SCObjective dx dy ℓ μ α)
    (u w : Euclid dx) (huw : u ≠ w) : α ≤ ℓ := by
  have hs := S.saddle_operator_monotone u w 0 0
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero,
    inner_zero_right, sub_zero] at hs
  have hl := S.toNCObjective.gradX_lip_primal u w 0
  have hi := real_inner_le_norm (S.gradX u 0 - S.gradX w 0) (u - w)
  have hm := mul_le_mul_of_nonneg_right hl (norm_nonneg (u - w))
  have hn : 0 < ‖u - w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr huw))
  apply (mul_le_mul_right hn).mp
  nlinarith only [hs, hi, hm]

theorem alpha_le_smooth (S : SCObjective dx dy ℓ μ α) [Nontrivial (Euclid dx)] : α ≤ ℓ := by
  obtain ⟨u, hu⟩ := exists_ne (0 : Euclid dx)
  exact S.alpha_le_smooth_of_distinct u 0 hu

theorem slice_gradient_zero (v : Euclid dy) : S.gradX (S.sliceMin v) v = 0 :=
  gradient_zero_at_global_min (g := fun u => S.gradX u v) (S.sliceMin v)
    (S.toNCObjective.derivative_x (S.sliceMin v) v)
    (S.sliceMin_minimizes v)

theorem slice_residual_distance (u : Euclid dx) (v : Euclid dy) :
    α * ‖u - S.sliceMin v‖ ≤ ‖S.gradX u v‖ := by
  have hc : StrongConcaveGradient (fun x => -S.f x v) (fun x => -S.gradX x v) α := by
    intro x y
    have h := S.primal_strong v x y
    simp only [inner_neg_left]
    dsimp only at h
    linarith
  have hm := strong_concave_gradient_monotone hc u (S.sliceMin v)
  simp only [S.slice_gradient_zero, neg_zero, zero_sub, neg_neg] at hm
  exact residual_controls_distance α (S.gradX u v) (u - S.sliceMin v) hm

theorem sliceMin_lip (v v' : Euclid dy) : ‖S.sliceMin v - S.sliceMin v'‖ ≤ (ℓ / α) * ‖v - v'‖ := by
  have h1 := S.slice_residual_distance (S.sliceMin v') v
  have h2 := S.toNCObjective.gradX_lip_dual (S.sliceMin v') v v'
  rw [S.slice_gradient_zero, sub_zero] at h2
  rw [norm_sub_rev] at h1
  have h : ‖S.sliceMin v - S.sliceMin v'‖ ≤ (ℓ * ‖v - v'‖) / α := by
    apply (le_div_iff₀ S.α_pos).mpr
    nlinarith only [h1, h2]
  convert h using 1
  ring

theorem sliceMin_continuous : Continuous S.sliceMin := by
  have hp : 0 ≤ ℓ / α := div_nonneg S.toNCObjective.L_pos.le S.α_pos.le
  apply (show LipschitzWith ⟨ℓ / α, hp⟩ S.sliceMin from ?_).continuous
  apply LipschitzWith.of_dist_le_mul
  intro v v'
  simpa only [dist_eq_norm, NNReal.coe_mk] using S.sliceMin_lip v v'

def effectiveValue (v : Euclid dy) : ℝ := -S.dualValue v
def effectiveGradient (v : Euclid dy) : Euclid dy := -S.gradY (S.sliceMin v) v

theorem dualValue_hasFDerivAt (v : Euclid dy) :
    HasFDerivAt S.dualValue (innerSL ℝ (S.gradY (S.sliceMin v) v)) v := by
  let lift : Euclid dy → Joint dx dy := fun t => (S.sliceMin t, t)
  have hlift : Continuous lift := S.sliceMin_continuous.prodMk continuous_id
  have ho := (S.derivative (lift v)).isLittleO.comp_tendsto hlift.continuousAt
  have hb : (fun t => lift t - lift v) =O[nhds v] (fun t => t - v) := by
    apply Asymptotics.IsBigO.of_bound (1 + ℓ / α)
    apply Filter.Eventually.of_forall
    intro t
    change max ‖S.sliceMin t - S.sliceMin v‖ ‖t - v‖ ≤ (1 + ℓ / α) * ‖t - v‖
    apply max_le
    · have h := S.sliceMin_lip t v
      nlinarith [norm_nonneg (t - v)]
    · have hp : 0 ≤ ℓ / α := div_nonneg S.toNCObjective.L_pos.le S.α_pos.le
      nlinarith [norm_nonneg (t - v)]
  have h := ho.trans_isBigO hb
  apply HasFDerivAtFilter.of_isLittleO
  simpa only [lift, Function.comp_def, Prod.fst_sub, Prod.snd_sub,
    ContinuousLinearMap.coprod_apply, innerSL_apply, S.slice_gradient_zero,
    inner_zero_left, zero_add, ← S.dualValue_eq_min] using h

theorem effectiveValue_hasFDerivAt (v : Euclid dy) :
    HasFDerivAt S.effectiveValue (innerSL ℝ (S.effectiveGradient v)) v := by
  apply (S.dualValue_hasFDerivAt v).neg.congr_fderiv
  apply ContinuousLinearMap.ext
  intro h
  simp [effectiveGradient]

theorem true_effective_gradient (v : Euclid dy) : gradient S.effectiveValue v = S.effectiveGradient v := by
  have h : HasGradientAt S.effectiveValue (S.effectiveGradient v) v := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact S.effectiveValue_hasFDerivAt v
  exact h.gradient

theorem effective_strong : StrongConvexGradient S.effectiveValue S.effectiveGradient μ := by
  intro v w
  have hc := S.dual_strong (S.sliceMin v) v w
  have hv := S.dualValue_le w (S.sliceMin v)
  rw [← S.dualValue_eq_min v] at hc
  simp only [effectiveValue, effectiveGradient, inner_neg_left]
  linarith

theorem effectiveGradient_lip (v w : Euclid dy) :
    ‖S.effectiveGradient v - S.effectiveGradient w‖ ≤ (1 + ℓ / α) * ℓ * ‖v - w‖ := by
  have ht := norm_sub_le_norm_sub_add_norm_sub (S.gradY (S.sliceMin v) v)
    (S.gradY (S.sliceMin w) v) (S.gradY (S.sliceMin w) w)
  have hx := S.toNCObjective.gradY_lip_primal (S.sliceMin v) (S.sliceMin w) v
  have hy := S.toNCObjective.gradY_lip_dual (S.sliceMin w) v w
  have hs := S.sliceMin_lip v w
  have hℓ := S.toNCObjective.L_pos
  simp only [effectiveGradient, neg_sub_neg, norm_sub_rev]
  nlinarith

theorem effectiveGradient_lip_five (hfast : ℓ / 4 ≤ α) (v w : Euclid dy) :
    ‖S.effectiveGradient v - S.effectiveGradient w‖ ≤ 5 * ℓ * ‖v - w‖ := by
  have hk : ℓ / α ≤ 4 := (div_le_iff₀ S.α_pos).mpr (by linarith)
  have hc : (1 + ℓ / α) * ℓ ≤ 5 * ℓ := by nlinarith [S.toNCObjective.L_pos]
  exact (S.effectiveGradient_lip v w).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

end SCObjective
end FreshGradientMinimax
