import FreshGradientMinimax.QuadraticRestart
import FreshGradientMinimax.RecursiveParameters

/-! The first value solve starts from the given saddle-distance energy.
All minimizing points below are the already constructed actual extrema;
the initial linear coefficient is the known vector zero. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem sliceMin_saddleV : S.sliceMin S.saddleV = S.saddleU := by
  have h := S.slice_residual_distance S.saddleU S.saddleV
  rw [S.saddle_gradX_zero, norm_zero] at h
  have ha := S.α_pos
  have hz : ‖S.saddleU - S.sliceMin S.saddleV‖ = 0 := by nlinarith [norm_nonneg (S.saddleU - S.sliceMin S.saddleV)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

theorem effectiveValue_minimizes (v : Euclid dy) : S.effectiveValue S.saddleV ≤ S.effectiveValue v := by
  have h := (S.dualValue_le v S.saddleU).trans (S.saddle_left v)
  rw [← S.sliceMin_saddleV, ← S.dualValue_eq_min] at h
  exact neg_le_neg h

theorem dualQuadraticMin_zero (hfast : ℓ / 4 ≤ α) : S.dualQuadraticMin hfast 0 le_rfl 0 = S.saddleV := by
  apply Eq.symm
  apply (S.effective_model hfast).quadraticMin_unique
  intro y
  simpa only [quadraticFamily, zero_div, zero_mul, add_zero, inner_zero_left, sub_zero] using S.effectiveValue_minimizes y

def saddleStartEnergy (z : Joint dx dy) : ℝ :=
  ℓ * ‖z.1 - S.saddleU‖ ^ 2 + μ * ‖z.2 - S.saddleV‖ ^ 2

theorem saddleStartEnergy_continuous : Continuous S.saddleStartEnergy :=
  (continuous_const.mul ((continuous_fst.sub continuous_const).norm.pow 2)).add
    (continuous_const.mul ((continuous_snd.sub continuous_const).norm.pow 2))

theorem recursive_cold_energy (hfast : ℓ / 4 ≤ α) (z : Joint dx dy) :
    S.dualQuadraticEnergy hfast 0 le_rfl (0, z) ≤ 3 * (ℓ / μ) * S.saddleStartEnergy z := by
  have hg := ((S.effective_model hfast).gap_quadratic_bounds S.saddleV S.effectiveValue_minimizes z.2).2
  have hκ : 1 ≤ ℓ / μ := (le_div_iff₀ S.μ_pos).mpr (by simpa only [one_mul] using S.μ_le_L)
  have hℓ := S.L_pos
  have hμ := S.μ_pos
  have hμℓ := S.μ_le_L
  have hc : μ ≤ 3 * (ℓ / μ) * ℓ := by nlinarith
  have hcv : 5 * ℓ / 2 ≤ 3 * (ℓ / μ) * μ := by rw [mul_assoc, div_mul_cancel₀ _ hμ.ne']; linarith
  have hx := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖z.1 - S.saddleU‖)
  have hv := mul_le_mul_of_nonneg_right hcv (sq_nonneg ‖z.2 - S.saddleV‖)
  dsimp [dualQuadraticEnergy, parameterEnergy, solverEnergy]
  rw [S.dualQuadraticMin_zero hfast, S.sliceMin_saddleV]
  simp only [quadraticFamily, zero_div, zero_mul, add_zero, inner_zero_left, sub_zero]
  dsimp only [saddleStartEnergy]
  nlinarith only [hg, hx, hv]

theorem recursive_cold_energy_mean (hfast : ℓ / 4 ≤ α) (ν : Measure (Joint dx dy))
    (hInit : Integrable S.saddleStartEnergy ν) {E₀ : ℝ} (hE : (∫ z, S.saddleStartEnergy z ∂ν) ≤ E₀) :
    Integrable (S.dualQuadraticEnergy hfast 0 le_rfl) (ν.map (fun z => ((0 : Euclid dy), z))) ∧
    (∫ z, S.dualQuadraticEnergy hfast 0 le_rfl z ∂ν.map (fun z => ((0 : Euclid dy), z))) ≤ 3 * (ℓ / μ) * E₀ := by
  have hm := (S.dualQuadraticEnergy_measurable hfast 0 le_rfl).stronglyMeasurable
  have hi : Integrable (fun z : Joint dx dy => S.dualQuadraticEnergy hfast 0 le_rfl (0, z)) ν := by
    apply (hInit.const_mul (3 * (ℓ / μ))).mono' (hm.measurable.comp measurable_prodMk_left).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro z
    change ‖S.dualQuadraticEnergy hfast 0 le_rfl (0, z)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (S.dualQuadraticEnergy_nonneg hfast 0 le_rfl _)]
    exact S.recursive_cold_energy hfast z
  refine ⟨(integrable_map_measure hm.aestronglyMeasurable measurable_prodMk_left.aemeasurable).mpr hi, ?_⟩
  rw [integral_map measurable_prodMk_left.aemeasurable hm.aestronglyMeasurable]
  have h := integral_mono hi (hInit.const_mul (3 * (ℓ / μ))) (S.recursive_cold_energy hfast)
  rw [integral_const_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left hE (by have := S.L_pos; have := S.μ_pos; positivity))

end SCObjective
end FreshGradientMinimax
