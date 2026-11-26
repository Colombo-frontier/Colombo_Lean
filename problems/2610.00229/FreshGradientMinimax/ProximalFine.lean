import FreshGradientMinimax.OuterMoments

/-! A final fine solve yields a square-integrable genuine primal gradient.
Its bound is derived from the input center residual and its actual gap. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace NCObjective
variable {dx dy : ℕ} {L μ σ : ℝ} (F : NCObjective dx dy L μ)

theorem primal_gradient_square_continuous : Continuous (fun u => ‖gradient F.value u‖ ^ 2) := by
  simp_rw [F.true_primal_gradient]
  exact F.primalGradient_continuous.norm.pow 2

theorem proximal_gradient_energy_bound (p : Euclid dx × Joint dx dy) :
    ‖gradient F.value p.2.1‖ ^ 2 ≤
      16 * L * F.proximalResidualEnergy p.1 + 144 * (L / μ) * L * F.proximalGap p := by
  have h := F.primal_gradient_from_saddle_gap p.1 p.2.1 p.2.2
  have he : 16 * L * F.proximalResidualEnergy p.1 = 2 * ‖proximalResidual L p.1 (F.proxPoint p.1)‖ ^ 2 := by
    unfold proximalResidualEnergy
    field_simp [ne_of_gt F.L_pos]
    ring
  rw [he]
  exact h

theorem proximalSolverProgram_fine_gradient (O : FreshOracle F σ) {η E : ℝ}
    (hη : 0 < η) (hE : 0 < E) (ν : Measure (Euclid dx × Joint dx dy)) [IsProbabilityMeasure ν]
    (hi : Integrable F.proximalStartEnergy ν) (hb : (∫ p, F.proximalStartEnergy p ∂ν) ≤ E)
    (hr : Integrable (fun p : Euclid dx × Joint dx dy => F.proximalResidualEnergy p.1) ν) :
    Integrable (fun p : Euclid dx × Joint dx dy => ‖gradient F.value p.2.1‖ ^ 2)
      ((proximalSolverProgram dx dy L σ μ (η / 2) E).resultKernel O.kernel ∘ₘ ν) ∧
    (∫ p, ‖gradient F.value p.2.1‖ ^ 2 ∂(proximalSolverProgram dx dy L σ μ (η / 2) E).resultKernel O.kernel ∘ₘ ν) ≤
      16 * L * (∫ p, F.proximalResidualEnergy p.1 ∂ν) + 144 * (L / μ) * L * η := by
  have hg := F.proximalSolverProgram_result_accuracy O hη hE ν hi hb
  have hc := F.proximalSolverProgram_center_integrable O (η / 2) E ν F.proximalResidualEnergy
    F.proximalResidualEnergy_continuous.measurable hr
  have hgi := integrable_nonneg_envelope
    (F.primal_gradient_square_continuous.measurable.comp measurable_snd.fst)
    (fun p => sq_nonneg ‖gradient F.value p.2.1‖)
    ((hc.1.const_mul (16 * L)).add (hg.1.const_mul (144 * (L / μ) * L)))
    F.proximal_gradient_energy_bound
  refine ⟨hgi, ?_⟩
  have hm := integral_mono hgi ((hc.1.const_mul (16 * L)).add (hg.1.const_mul (144 * (L / μ) * L)))
    F.proximal_gradient_energy_bound
  simp only [Pi.add_apply, Function.comp_apply] at hm
  rw [integral_add (hc.1.const_mul (16 * L)) (hg.1.const_mul (144 * (L / μ) * L)),
    integral_const_mul, integral_const_mul, hc.2] at hm
  have hL := F.L_pos
  have hμ := F.μ_pos
  have hcoef : 0 ≤ 144 * (L / μ) * L := by positivity
  exact hm.trans (add_le_add_left (mul_le_mul_of_nonneg_left hg.2 hcoef) _)

end NCObjective
end FreshGradientMinimax
