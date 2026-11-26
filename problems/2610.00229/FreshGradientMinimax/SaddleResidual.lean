import FreshGradientMinimax.RecursivePotential

/-! A true max-min gap certificate using the effective gradient and the
fast-variable error returned by the implemented solver. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem jointGap_continuous : Continuous (fun z : Joint dx dy => S.gap z.1 z.2) := by
  have hv : Continuous S.toNCObjective.value := continuous_iff_continuousAt.mpr
    (fun x => (S.toNCObjective.value_hasFDerivAt x).continuousAt)
  have hd : Continuous S.dualValue := continuous_iff_continuousAt.mpr
    (fun v => (S.dualValue_hasFDerivAt v).continuousAt)
  exact (hv.comp continuous_fst).sub (hd.comp continuous_snd)

theorem gap_effective_residual (hfast : ℓ / 4 ≤ α) (z : Joint dx dy) :
    μ * S.gap z.1 z.2 ≤ ‖gradient S.effectiveValue z.2‖ ^ 2 +
      3 * ℓ ^ 2 * ‖z.1 - S.sliceMin z.2‖ ^ 2 := by
  have hx := S.toNCObjective.gradX_lip_primal z.1 (S.sliceMin z.2) z.2
  rw [S.slice_gradient_zero, sub_zero] at hx
  have hxs := (sq_le_sq₀ (norm_nonneg _) (by have := S.L_pos; positivity)).mpr hx
  rw [mul_pow] at hxs
  have hy := S.toNCObjective.gradY_lip_primal z.1 (S.sliceMin z.2) z.2
  have hys := (sq_le_sq₀ (norm_nonneg _) (by have := S.L_pos; positivity)).mpr hy
  rw [mul_pow] at hys
  have ht := norm_add_sq_le_two (S.gradY z.1 z.2 - S.gradY (S.sliceMin z.2) z.2)
    (S.gradY (S.sliceMin z.2) z.2)
  rw [sub_add_cancel] at ht
  have hgrad : ‖gradient S.effectiveValue z.2‖ = ‖S.gradY (S.sliceMin z.2) z.2‖ := by
    rw [S.true_effective_gradient, effectiveGradient, norm_neg]
  have hgy : ‖S.gradY z.1 z.2‖ ^ 2 ≤ 2 * ℓ ^ 2 * ‖z.1 - S.sliceMin z.2‖ ^ 2 +
      2 * ‖gradient S.effectiveValue z.2‖ ^ 2 := by rw [hgrad]; linarith only [ht, hys]
  have hμa : μ ≤ 4 * α := by have := S.μ_le_L; linarith
  have hcert := mul_le_mul_of_nonneg_left (S.gap_le_residual z.1 z.2)
    (by have := S.α_pos; have := S.μ_pos; positivity : 0 ≤ 2 * α * μ)
  have heq (A B : ℝ) : 2 * α * μ * (A / (2 * α) + B / (2 * μ)) = μ * A + α * B := by
    field_simp [S.α_pos.ne', S.μ_pos.ne']
    ring
  rw [heq] at hcert
  have hμx := mul_le_mul_of_nonneg_right hμa (sq_nonneg ‖S.gradX z.1 z.2‖)
  have hxmul := mul_le_mul_of_nonneg_left hxs (by have := S.α_pos; positivity : 0 ≤ 4 * α)
  have hymul := mul_le_mul_of_nonneg_left hgy S.α_pos.le
  apply (mul_le_mul_left (by have := S.α_pos; positivity : 0 < 2 * α)).mp
  nlinarith only [hcert, hμx, hxmul, hymul]

theorem gap_le_fast_effective (hfast : ℓ / 4 ≤ α) {m : ℝ} (hscale : 5 * ℓ ≤ m) (z : Joint dx dy) :
    S.gap z.1 z.2 ≤ (‖gradient S.effectiveValue z.2‖ ^ 2 + m * S.fastError m z) / μ := by
  apply (le_div_iff₀ S.μ_pos).mpr
  have hL := S.L_pos
  have hm : 0 ≤ m := by linarith
  have hsq : 3 * ℓ ^ 2 ≤ m ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖z.1 - S.sliceMin z.2‖)
  have h := S.gap_effective_residual hfast z
  dsimp [fastError]
  nlinarith only [h, hmul]

end SCObjective
end FreshGradientMinimax
