import FreshGradientMinimax.LocalizedOuter

/-! The paper's explicit coarse precision and number of solves, including
the actual-program residual guarantee in (53). -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators

def outerCoarseTolerance (L ε : ℝ) : ℝ := ε ^ 2 / (1000000 * L)
def outerStepCount (L Δ ε : ℝ) : ℕ := ⌈1000000 * L * Δ / ε ^ 2⌉₊

theorem outerCoarseTolerance_pos {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    0 < outerCoarseTolerance L ε := by unfold outerCoarseTolerance; positivity

theorem outerStepCount_pos {L Δ ε : ℝ} (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) :
    0 < outerStepCount L Δ ε := by unfold outerStepCount; exact Nat.ceil_pos.mpr (by positivity)

theorem outerStepCount_energy_bounds {L Δ ε : ℝ} (hL : 0 < L) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    Δ ≤ outerStepCount L Δ ε * outerCoarseTolerance L ε ∧
    outerStepCount L Δ ε * outerCoarseTolerance L ε ≤ Δ + outerCoarseTolerance L ε := by
  have hη := outerCoarseTolerance_pos hL hε
  have he : (1000000 * L * Δ / ε ^ 2) * outerCoarseTolerance L ε = Δ := by
    unfold outerCoarseTolerance
    field_simp
  have hlo := mul_le_mul_of_nonneg_right (Nat.le_ceil (1000000 * L * Δ / ε ^ 2)) hη.le
  have hhi := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one
    (show 0 ≤ 1000000 * L * Δ / ε ^ 2 by positivity)).le hη.le
  rw [he] at hlo
  rw [add_mul, he, one_mul] at hhi
  exact ⟨hlo, hhi⟩

theorem outerWarmEnvelope_nontrivial_bound {L Δ ε : ℝ} (hL : 0 < L) (hΔ : 0 ≤ Δ)
    (hε : 0 < ε) (hreg : ε ^ 2 ≤ L * Δ) :
    outerWarmEnvelope Δ (outerCoarseTolerance L ε) (outerStepCount L Δ ε) ≤ 84 * Δ := by
  have hT := (outerStepCount_energy_bounds hL hΔ hε).2
  have hη : outerCoarseTolerance L ε ≤ Δ := by
    apply (div_le_iff₀ (by positivity : 0 < 1000000 * L)).mpr
    nlinarith
  unfold outerWarmEnvelope
  linarith

namespace NCObjective
variable {dx dy : ℕ} {L μ σ : ℝ} (F : NCObjective dx dy L μ)

theorem localizedOuter_residual_average (O : FreshOracle F σ) {Δ G η : ℝ}
    (hΔ : F.PrimalGapAtMost Δ) (hG : F.DualLocalized G) (hη : 0 < η) {T : ℕ} (hT : 0 < T) :
    (∑ j ∈ Finset.range T, ∫ p, ‖proximalResidual L p.1 (F.proxPoint p.1)‖ ^ 2
      ∂localizedOuterLaw L σ μ Δ G η T O.kernel (j + 1)) / T ≤ 8 * L * (Δ / T + η) := by
  have hb := F.localizedOuter_residual_bound O hΔ hG hη T
  have he (c : Euclid dx) : ‖proximalResidual L c (F.proxPoint c)‖ ^ 2 = 8 * L * F.proximalResidualEnergy c := by
    unfold proximalResidualEnergy
    field_simp [ne_of_gt F.L_pos]
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hL := F.L_pos
  simp_rw [he, integral_const_mul]
  rw [← Finset.mul_sum]
  apply (div_le_iff₀ hTr).mpr
  rw [show 8 * L * (Δ / T + η) * T = 8 * L * (Δ + T * η) by field_simp; ring]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

theorem localizedOuter_coarse_accuracy (O : FreshOracle F σ) {Δ G ε : ℝ}
    (hΔ : F.PrimalGapAtMost Δ) (hG : F.DualLocalized G) (hε : 0 < ε) (hreg : ε ^ 2 ≤ L * Δ) :
    (∑ j ∈ Finset.range (outerStepCount L Δ ε), ∫ p, ‖proximalResidual L p.1 (F.proxPoint p.1)‖ ^ 2
      ∂localizedOuterLaw L σ μ Δ G (outerCoarseTolerance L ε) (outerStepCount L Δ ε) O.kernel (j + 1)) /
        outerStepCount L Δ ε ≤ 16 * ε ^ 2 / 1000000 := by
  have hL := F.L_pos
  have hΔ0 := F.primalGap_parameter_nonneg hΔ
  have hΔp : 0 < Δ := by nlinarith [sq_pos_of_pos hε]
  have hT := outerStepCount_pos hL hΔp hε
  have hη := outerCoarseTolerance_pos hL hε
  have h := F.localizedOuter_residual_average O hΔ hG hη hT
  refine h.trans ?_
  have he := (outerStepCount_energy_bounds hL hΔ0 hε).1
  have ht : (0 : ℝ) < outerStepCount L Δ ε := Nat.cast_pos.mpr hT
  have hd : Δ / outerStepCount L Δ ε ≤ outerCoarseTolerance L ε := by
    apply (div_le_iff₀ ht).mpr
    simpa only [mul_comm] using he
  calc
    _ ≤ 8 * L * (2 * outerCoarseTolerance L ε) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by unfold outerCoarseTolerance; field_simp; ring

end NCObjective
end FreshGradientMinimax
