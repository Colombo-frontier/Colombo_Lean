import FreshGradientMinimax.OuterSelection
import FreshGradientMinimax.ProximalFine

/-! The paper's final genuine gradient guarantee for the uniform coarse
output followed by the implemented fine solver. The whole-program sampler
and fixed-budget realization are supplied in OuterComplete and OuterBudget. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

def outerFineTolerance (L μ ε : ℝ) : ℝ := ε ^ 2 / (1000000 * (L / μ) * L)

theorem outerFineTolerance_pos {L μ ε : ℝ} (hL : 0 < L) (hμ : 0 < μ) (hε : 0 < ε) :
    0 < outerFineTolerance L μ ε := by unfold outerFineTolerance; positivity

def refinedOuterLaw {dx dy : ℕ} (L σ μ Δ G ε : ℝ) (K : Kernel (Joint dx dy) (Joint dx dy)) :
    Measure (Euclid dx × Joint dx dy) :=
  (proximalSolverProgram dx dy L σ μ (outerFineTolerance L μ ε / 2) (6 * outerCoarseTolerance L ε)).resultKernel K ∘ₘ
    selectedOuterLaw L σ μ Δ G (outerCoarseTolerance L ε) (outerStepCount L Δ ε) K

namespace NCObjective
variable {dx dy : ℕ} {L μ σ : ℝ} (F : NCObjective dx dy L μ)

theorem refinedOuterLaw_probability (O : FreshOracle F σ) {Δ G ε : ℝ}
    (hε : 0 < ε) (hreg : ε ^ 2 ≤ L * Δ) : IsProbabilityMeasure (refinedOuterLaw L σ μ Δ G ε O.kernel) := by
  have hΔ : 0 < Δ := by have := F.L_pos; nlinarith [sq_pos_of_pos hε]
  letI := selectedOuterLaw_probability L σ μ Δ G (outerCoarseTolerance L ε)
    (outerStepCount_pos F.L_pos hΔ hε) O.kernel
  unfold refinedOuterLaw
  infer_instance

theorem refinedOuterLaw_gradient_accuracy (O : FreshOracle F σ) {Δ G ε : ℝ}
    (hΔ : F.PrimalGapAtMost Δ) (hG : F.DualLocalized G) (hε : 0 < ε) (hreg : ε ^ 2 ≤ L * Δ) :
    Integrable (fun p : Euclid dx × Joint dx dy => ‖gradient F.value p.2.1‖ ^ 2)
      (refinedOuterLaw L σ μ Δ G ε O.kernel) ∧
    (∫ p, ‖gradient F.value p.2.1‖ ^ 2 ∂refinedOuterLaw L σ μ Δ G ε O.kernel) ≤ ε ^ 2 / 12 := by
  have hL := F.L_pos
  have hμ := F.μ_pos
  have hΔp : 0 < Δ := by nlinarith [sq_pos_of_pos hε]
  have hT := outerStepCount_pos hL hΔp hε
  have hη := outerCoarseTolerance_pos hL hε
  have hηf := outerFineTolerance_pos hL hμ hε
  letI := selectedOuterLaw_probability L σ μ Δ G (outerCoarseTolerance L ε) hT O.kernel
  have hm := F.selectedOuterLaw_moments O hΔ hG hη hT
  have hg := F.proximalSolverProgram_fine_gradient O hηf
    (show 0 < 6 * outerCoarseTolerance L ε by positivity) _ hm.1 hm.2.1 hm.2.2.1
  refine ⟨hg.1, hg.2.trans ?_⟩
  have he := (outerStepCount_energy_bounds hL (F.primalGap_parameter_nonneg hΔ) hε).1
  have hd : Δ / outerStepCount L Δ ε ≤ outerCoarseTolerance L ε := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hT)).mpr
    simpa only [mul_comm] using he
  have hr : (∫ p, F.proximalResidualEnergy p.1
      ∂selectedOuterLaw L σ μ Δ G (outerCoarseTolerance L ε) (outerStepCount L Δ ε) O.kernel) ≤
      2 * outerCoarseTolerance L ε := by linarith [hm.2.2.2]
  calc
    _ ≤ 16 * L * (2 * outerCoarseTolerance L ε) + 144 * (L / μ) * L * outerFineTolerance L μ ε :=
      add_le_add_right (mul_le_mul_of_nonneg_left hr (by positivity)) _
    _ = 176 * ε ^ 2 / 1000000 := by
      unfold outerCoarseTolerance outerFineTolerance
      field_simp
      ring
    _ ≤ _ := by nlinarith [sq_nonneg ε]

end NCObjective
end FreshGradientMinimax
