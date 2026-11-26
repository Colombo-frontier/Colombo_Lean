import FreshGradientMinimax.OuterTrace
import FreshGradientMinimax.ProgramSample
import FreshGradientMinimax.OuterSelection

/-! The complete coarse trajectory and an independent uniform index form
one original-query program. Its output is the analysed selectedOuterLaw. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

def selectedOuterProgram (dx dy : ℕ) (L σ μ Δ G η : ℝ) {T : ℕ} (hT : 0 < T) :
    OracleProgram dx dy (OuterTrace dx dy) (Euclid dx × Joint dx dy) :=
  (outerTraceProgram dx dy L σ μ η (outerColdEnvelope L μ Δ G η) (outerWarmEnvelope Δ η T) T).chain
    (OracleProgram.uniformRead hT (fun j t => t (j + 1)) (fun j => measurable_pi_apply (j + 1)))

theorem selectedOuterProgram_result_law {dx dy : ℕ} (L σ μ Δ G η : ℝ) {T : ℕ} (hT : 0 < T)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] :
    (selectedOuterProgram dx dy L σ μ Δ G η hT).resultKernel K ∘ₘ Measure.dirac 0 =
      selectedOuterLaw L σ μ Δ G η T K := by
  rw [selectedOuterProgram, OracleProgram.chain_result, ← Measure.comp_assoc,
    OracleProgram.uniformRead_result_law]
  apply uniformMeasure_congr
  intro j hj
  exact outerTraceLaw_coordinate L σ μ η _ _ K T (j + 1) (by omega)

theorem selectedOuterProgram_original_law {dx dy : ℕ} (L σ μ Δ G η : ℝ) {T : ℕ} (hT : 0 < T)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] :
    ((selectedOuterProgram dx dy L σ μ Δ G η hT).originalKernel K ∘ₘ Measure.dirac 0).map Prod.fst =
      selectedOuterLaw L σ μ Δ G η T K := by
  rw [OracleProgram.original_result_law, selectedOuterProgram_result_law]

namespace NCObjective
variable {dx dy : ℕ} {L μ σ : ℝ} (F : NCObjective dx dy L μ)

theorem selectedOuterProgram_cost (O : FreshOracle F σ) (Δ G η : ℝ) {T : ℕ} (hT : 0 < T)
    (t : OuterTrace dx dy) :
    Integrable costValue ((selectedOuterProgram dx dy L σ μ Δ G η hT).lawKernel O.kernel t) ∧
    (∫ p, costValue p ∂(selectedOuterProgram dx dy L σ μ Δ G η hT).lawKernel O.kernel t) =
      outerRunWork L σ μ η (outerColdEnvelope L μ Δ G η) (outerWarmEnvelope Δ η T) T := by
  have hc := F.outerTraceProgram_cost O η (outerColdEnvelope L μ Δ G η) (outerWarmEnvelope Δ η T) T t
  have hr (r : OuterTrace dx dy) := OracleProgram.uniformRead_cost hT
    (fun j (s : OuterTrace dx dy) => s (j + 1)) (fun j => measurable_pi_apply (j + 1)) O.kernel r
  rw [selectedOuterProgram, OracleProgram.chain_law]
  have h := costedCompose_cost _ _ t hc.1 (fun r => (hr r).1) 0 (fun r => (hr r).2)
  simpa only [hc.2, add_zero] using h

end NCObjective
end FreshGradientMinimax
