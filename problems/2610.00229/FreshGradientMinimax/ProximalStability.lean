import FreshGradientMinimax.ProximalSaddle

/-! Stability of actual proximal saddles, including the warm-start energy bound
whose constant is independent of the initial dual localization parameter G. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace
namespace NCObjective
variable {dx dy : ℕ} {L μ : ℝ} (O : NCObjective dx dy L μ)

theorem regularizedX_at_proxPoint (c : Euclid dx) :
    O.regularizedX c (O.proxPoint c) (O.dualMax (O.proxPoint c)) = 0 :=
  O.prox_gradient_zero c

theorem regularizedX_shift (c c' u : Euclid dx) (v : Euclid dy) :
    O.regularizedX c u v = O.regularizedX c' u v + (2 * L) • (c' - c) := by
  unfold regularizedX
  module

theorem proximal_center_monotonicity (c c' : Euclid dx) :
    L * ‖O.proxPoint c - O.proxPoint c'‖ ^ 2 +
      μ * ‖O.dualMax (O.proxPoint c) - O.dualMax (O.proxPoint c')‖ ^ 2 ≤
        2 * L * ⟪c - c', O.proxPoint c - O.proxPoint c'⟫_ℝ := by
  have h := (O.proximalObjective c).saddle_operator_monotone
    (O.proxPoint c) (O.proxPoint c') (O.dualMax (O.proxPoint c)) (O.dualMax (O.proxPoint c'))
  change L * _ + μ * _ ≤
    ⟪O.regularizedX c (O.proxPoint c) (O.dualMax (O.proxPoint c)) -
      O.regularizedX c (O.proxPoint c') (O.dualMax (O.proxPoint c')), _⟫_ℝ -
    ⟪O.gradY (O.proxPoint c) (O.dualMax (O.proxPoint c)) -
      O.gradY (O.proxPoint c') (O.dualMax (O.proxPoint c')), _⟫_ℝ at h
  rw [O.regularizedX_at_proxPoint,
    O.regularizedX_shift c c' (O.proxPoint c'), O.regularizedX_at_proxPoint] at h
  simp only [O.dual_gradient_zero, zero_add, zero_sub, sub_self, inner_zero_left,
    sub_zero, inner_neg_left, real_inner_smul_left] at h
  calc
    _ ≤ _ := h
    _ = _ := by simp only [inner_sub_left]; ring

theorem proximal_center_stability (c c' : Euclid dx) :
    L / 2 * ‖O.proxPoint c - O.proxPoint c'‖ ^ 2 +
      μ * ‖O.dualMax (O.proxPoint c) - O.dualMax (O.proxPoint c')‖ ^ 2 ≤
        2 * L * ‖c - c'‖ ^ 2 := by
  have hm := O.proximal_center_monotonicity c c'
  have hy := inner_sub_quadratic_le O.L_pos ((2 * L) • (c - c'))
    (O.proxPoint c - O.proxPoint c')
  rw [real_inner_smul_left, norm_smul_sq] at hy
  have he : (2 * L) ^ 2 * ‖c - c'‖ ^ 2 / (2 * L) = 2 * L * ‖c - c'‖ ^ 2 := by
    have hL := ne_of_gt O.L_pos
    field_simp
    ring
  rw [he] at hy
  linarith

theorem proxPoint_lip (c c' : Euclid dx) : ‖O.proxPoint c - O.proxPoint c'‖ ≤ 2 * ‖c - c'‖ := by
  have h := O.proximal_center_stability c c'
  have hn := mul_nonneg O.μ_pos.le (sq_nonneg ‖O.dualMax (O.proxPoint c) - O.dualMax (O.proxPoint c')‖)
  have hsq : ‖O.proxPoint c - O.proxPoint c'‖ ^ 2 ≤ 4 * ‖c - c'‖ ^ 2 := by
    apply (mul_le_mul_left O.L_pos).mp
    nlinarith only [h, hn]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * ‖c - c'‖)).mp
  nlinarith only [hsq]

theorem proxPoint_continuous : Continuous O.proxPoint := by
  apply (show LipschitzWith 2 O.proxPoint from ?_).continuous
  apply LipschitzWith.of_dist_le_mul
  intro c c'
  simpa only [dist_eq_norm] using O.proxPoint_lip c c'

theorem proximal_saddle_energy_shift (c c' : Euclid dx) :
    3 * L * ‖O.proxPoint c - O.proxPoint c'‖ ^ 2 +
      μ * ‖O.dualMax (O.proxPoint c) - O.dualMax (O.proxPoint c')‖ ^ 2 ≤
        12 * L * ‖c - c'‖ ^ 2 := by
  have h := O.proximal_center_stability c c'
  have hn := mul_nonneg O.μ_pos.le (sq_nonneg ‖O.dualMax (O.proxPoint c) - O.dualMax (O.proxPoint c')‖)
  linarith

/-- A previous solve's genuine gap and the change of center suffice for a new
starting-energy envelope. No unobserved dual radius occurs on the right. -/
theorem proximal_warm_energy (c c' u : Euclid dx) (v : Euclid dy) :
    3 * L * ‖u - O.proxPoint c'‖ ^ 2 + μ * ‖v - O.dualMax (O.proxPoint c')‖ ^ 2 ≤
      12 * (O.proximalObjective c).gap u v + 24 * L * ‖c - c'‖ ^ 2 := by
  have hg := O.proximal_gap_controls_distance c u v
  have hs := O.proximal_saddle_energy_shift c c'
  have hx := norm_add_sq_le_two (u - O.proxPoint c) (O.proxPoint c - O.proxPoint c')
  have hy := norm_add_sq_le_two (v - O.dualMax (O.proxPoint c))
    (O.dualMax (O.proxPoint c) - O.dualMax (O.proxPoint c'))
  rw [sub_add_sub_cancel] at hx hy
  have hxL := mul_le_mul_of_nonneg_left hx (show 0 ≤ 3 * L by have := O.L_pos; positivity)
  have hyμ := mul_le_mul_of_nonneg_left hy O.μ_pos.le
  have hn := mul_nonneg O.μ_pos.le (sq_nonneg ‖v - O.dualMax (O.proxPoint c)‖)
  nlinarith only [hxL, hyμ, hg, hs, hn]

theorem initial_proximal_distance {Δ : ℝ} (hΔ : O.PrimalGapAtMost Δ) :
    L * ‖O.proxPoint 0‖ ^ 2 ≤ Δ := by
  have hm := O.proxPoint_minimizes 0 0
  have hg := hΔ (O.proxPoint 0)
  simp only [proximalValue, sub_zero, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero] at hm
  linarith

theorem primal_gradient_from_saddle_gap (c u : Euclid dx) (v : Euclid dy) :
    ‖gradient O.value u‖ ^ 2 ≤ 2 * ‖proximalResidual L c (O.proxPoint c)‖ ^ 2 +
      144 * (L / μ) * L * (O.proximalObjective c).gap u v := by
  have ht := O.true_gradient_from_prox c u
  have hp := O.prox_gradient_sq_le_gap c u
  have hg := O.proximal_gap_dominates_value c u v
  have hk : 0 ≤ 8 * (L / μ) * L := by have := O.L_pos; have := O.μ_pos; positivity
  have hg' := mul_le_mul_of_nonneg_left hg hk
  nlinarith only [ht, hp, hg']

/-- The single cold start has an explicit energy bound in the known parameters. -/
theorem initial_proximal_energy {Δ G : ℝ} (hΔ : O.PrimalGapAtMost Δ) (hG : O.DualLocalized G) :
    3 * L * ‖O.proxPoint 0‖ ^ 2 + μ * ‖O.dualMax (O.proxPoint 0)‖ ^ 2 ≤
      (3 + 2 * (L / μ)) * Δ + 2 * G ^ 2 / μ := by
  have hL := O.L_pos
  have hμ := O.μ_pos
  have hinit := O.initial_proximal_distance hΔ
  have hy0 := O.initial_dual_distance hG
  have hdiff := O.dualMax_lip (O.proxPoint 0) 0
  rw [sub_zero] at hdiff
  have hdiff2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (L / μ) * ‖O.proxPoint 0‖)).mpr hdiff
  rw [mul_pow] at hdiff2
  have hy02 := (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hy0)).mpr hy0
  have ht := norm_add_sq_le_two (O.dualMax (O.proxPoint 0) - O.dualMax 0) (O.dualMax 0)
  rw [sub_add_cancel] at ht
  have htμ := mul_le_mul_of_nonneg_left ht hμ.le
  have hdμ := mul_le_mul_of_nonneg_left hdiff2 hμ.le
  have hzμ := mul_le_mul_of_nonneg_left hy02 hμ.le
  calc
    _ ≤ 3 * L * ‖O.proxPoint 0‖ ^ 2 +
        2 * μ * ((L / μ) ^ 2 * ‖O.proxPoint 0‖ ^ 2) + 2 * μ * (G / μ) ^ 2 := by
      nlinarith only [htμ, hdμ, hzμ]
    _ = (3 + 2 * (L / μ)) * (L * ‖O.proxPoint 0‖ ^ 2) + 2 * G ^ 2 / μ := by
      field_simp
      ring
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left hinit (by positivity)) _

end NCObjective
end FreshGradientMinimax
