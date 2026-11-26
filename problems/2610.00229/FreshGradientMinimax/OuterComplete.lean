import FreshGradientMinimax.OuterSample
import FreshGradientMinimax.OuterRefinement

/-! Coarse iteration, uniform selection, and fine refinement are one
original-query program, chosen without access to the objective or oracle.
Its stopped-history output has the proven genuine gradient guarantee. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

def refinedOuterProgram (dx dy : ℕ) (L σ μ Δ G ε : ℝ) (hT : 0 < outerStepCount L Δ ε) :
    OracleProgram dx dy (OuterTrace dx dy) (Euclid dx × Joint dx dy) :=
  (selectedOuterProgram dx dy L σ μ Δ G (outerCoarseTolerance L ε) hT).chain
    (proximalSolverProgram dx dy L σ μ (outerFineTolerance L μ ε / 2) (6 * outerCoarseTolerance L ε))

def refinedOuterWork (L σ μ Δ G ε : ℝ) : ℝ :=
  outerRunWork L σ μ (outerCoarseTolerance L ε) (outerColdEnvelope L μ Δ G (outerCoarseTolerance L ε))
    (outerWarmEnvelope Δ (outerCoarseTolerance L ε) (outerStepCount L Δ ε)) (outerStepCount L Δ ε) +
  scscSolverWork (3 * L) L σ μ (outerFineTolerance L μ ε / 2) (6 * outerCoarseTolerance L ε)

theorem refinedOuterProgram_result_law {dx dy : ℕ} (L σ μ Δ G ε : ℝ) (hT : 0 < outerStepCount L Δ ε)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] :
    (refinedOuterProgram dx dy L σ μ Δ G ε hT).resultKernel K ∘ₘ Measure.dirac 0 =
      refinedOuterLaw L σ μ Δ G ε K := by
  rw [refinedOuterProgram, OracleProgram.chain_result, ← Measure.comp_assoc, selectedOuterProgram_result_law]
  rfl

theorem refinedOuterProgram_original_law {dx dy : ℕ} (L σ μ Δ G ε : ℝ) (hT : 0 < outerStepCount L Δ ε)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] :
    ((refinedOuterProgram dx dy L σ μ Δ G ε hT).originalKernel K ∘ₘ Measure.dirac 0).map Prod.fst =
      refinedOuterLaw L σ μ Δ G ε K := by
  rw [OracleProgram.original_result_law, refinedOuterProgram_result_law]

namespace NCObjective
variable {dx dy : ℕ} {L μ σ : ℝ} (F : NCObjective dx dy L μ)

theorem refinedOuterProgram_cost (O : FreshOracle F σ) (Δ G ε : ℝ) (hT : 0 < outerStepCount L Δ ε)
    (t : OuterTrace dx dy) :
    Integrable costValue ((refinedOuterProgram dx dy L σ μ Δ G ε hT).lawKernel O.kernel t) ∧
    (∫ p, costValue p ∂(refinedOuterProgram dx dy L σ μ Δ G ε hT).lawKernel O.kernel t) =
      refinedOuterWork L σ μ Δ G ε := by
  have hc := F.selectedOuterProgram_cost O Δ G (outerCoarseTolerance L ε) hT t
  have hf (p : Euclid dx × Joint dx dy) := F.proximalSolverProgram_cost O
    (outerFineTolerance L μ ε / 2) (6 * outerCoarseTolerance L ε) p
  simp only [OracleProgram.originalKernel_eq_law] at hf
  rw [refinedOuterProgram, OracleProgram.chain_law]
  have h := costedCompose_cost _ _ t hc.1 (fun p => (hf p).1) _ (fun p => (hf p).2)
  simpa only [hc.2, refinedOuterWork] using h

theorem refinedOuterProgram_mean_calls (O : FreshOracle F σ) (Δ G ε : ℝ) (hT : 0 < outerStepCount L Δ ε) :
    Integrable costValue ((refinedOuterProgram dx dy L σ μ Δ G ε hT).originalKernel O.kernel ∘ₘ Measure.dirac 0) ∧
    (∫ p, costValue p ∂(refinedOuterProgram dx dy L σ μ Δ G ε hT).originalKernel O.kernel ∘ₘ Measure.dirac 0) =
      refinedOuterWork L σ μ Δ G ε := by
  rw [OracleProgram.originalKernel_eq_law, Measure.dirac_bind (Kernel.measurable _)]
  exact F.refinedOuterProgram_cost O Δ G ε hT 0

theorem refinedOuterProgram_gradient_accuracy (O : FreshOracle F σ) {Δ G ε : ℝ}
    (hΔ : F.PrimalGapAtMost Δ) (hG : F.DualLocalized G) (hε : 0 < ε) (hreg : ε ^ 2 ≤ L * Δ)
    (hT : 0 < outerStepCount L Δ ε) :
    Integrable (fun p : (Euclid dx × Joint dx dy) × ℕ => ‖gradient F.value p.1.2.1‖ ^ 2)
      ((refinedOuterProgram dx dy L σ μ Δ G ε hT).originalKernel O.kernel ∘ₘ Measure.dirac 0) ∧
    (∫ p, ‖gradient F.value p.1.2.1‖ ^ 2
      ∂(refinedOuterProgram dx dy L σ μ Δ G ε hT).originalKernel O.kernel ∘ₘ Measure.dirac 0) ≤ ε ^ 2 / 12 := by
  have h := F.refinedOuterLaw_gradient_accuracy O hΔ hG hε hreg
  rw [← refinedOuterProgram_original_law L σ μ Δ G ε hT O.kernel] at h
  have hm : Measurable (fun p : Euclid dx × Joint dx dy => ‖gradient F.value p.2.1‖ ^ 2) :=
    F.primal_gradient_square_continuous.measurable.comp measurable_snd.fst
  refine ⟨(integrable_map_measure hm.aestronglyMeasurable measurable_fst.aemeasurable).mp h.1, ?_⟩
  have he := h.2
  rwa [integral_map measurable_fst.aemeasurable hm.aestronglyMeasurable] at he

end NCObjective
end FreshGradientMinimax
