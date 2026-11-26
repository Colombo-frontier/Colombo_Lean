import FreshGradientMinimax.AdjacentMoments

/-! Marginals after each solve, before the next quadratic update. All
are marginals of the same finite sequence of original-query programs. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

def recursiveOutputKernel (dx dy : ℕ) (ℓ α σ μ δ : ℝ) (N : ℕ) (E : ℝ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) (j : ℕ) :
    Kernel (Euclid dy × Joint dx dy) (Euclid dy × Joint dx dy) :=
  (recursiveStageProgram dx dy ℓ α σ μ δ N E j).resultKernel K ∘ₖ
    (recursiveRunProgram dx dy ℓ α σ μ δ N E j).resultKernel K

instance recursiveOutputKernel_markov (dx dy : ℕ) (ℓ α σ μ δ : ℝ) (N : ℕ) (E : ℝ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (j : ℕ) :
    IsMarkovKernel (recursiveOutputKernel dx dy ℓ α σ μ δ N E K j) := by
  unfold recursiveOutputKernel
  infer_instance

theorem recursiveOutputKernel_zero (dx dy : ℕ) (ℓ α σ μ δ : ℝ) (N : ℕ) (E : ℝ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) :
    recursiveOutputKernel dx dy ℓ α σ μ δ N E K 0 =
      (recursiveStageProgram dx dy ℓ α σ μ δ N E 0).resultKernel K := by
  rw [recursiveOutputKernel, recursiveRunProgram, OracleProgram.pure_result]
  exact Kernel.comp_id _

theorem recursiveOutputKernel_succ (dx dy : ℕ) (ℓ α σ μ δ : ℝ) (N : ℕ) (E : ℝ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (j : ℕ) :
    recursiveOutputKernel dx dy ℓ α σ μ δ N E K (j + 1) =
      (((recursiveStageProgram dx dy ℓ α σ μ δ N E (j + 1)).resultKernel K).comap
        (quadraticAdvance (recursiveMass μ j)) (quadraticAdvance_continuous _).measurable) ∘ₖ
      recursiveOutputKernel dx dy ℓ α σ μ δ N E K j := by
  rw [recursiveOutputKernel, recursiveRunProgram, OracleProgram.chain_result,
    ← Kernel.comp_assoc, recursiveRestartProgram, OracleProgram.map_result, Kernel.comp_map]
  exact Kernel.comp_assoc _ _ _

theorem recursiveOutputKernel_final (dx dy : ℕ) (ℓ α σ μ δ : ℝ) (N : ℕ) (E : ℝ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] :
    recursiveOutputKernel dx dy ℓ α σ μ δ N E K N =
      (recursiveSolverProgram dx dy ℓ α σ μ δ N E).resultKernel K := by
  rw [recursiveSolverProgram, OracleProgram.chain_result]
  rfl

namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem recursiveOutputKernel_accuracy (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) (E : ℝ)
    (ν : Measure (Euclid dy × Joint dx dy)) [IsProbabilityMeasure ν]
    (hi : Integrable (S.dualQuadraticEnergy hfast 0 le_rfl) ν)
    (hb : (∫ z, S.dualQuadraticEnergy hfast 0 le_rfl z ∂ν) ≤ E) (j : ℕ) :
    Integrable (S.dualQuadraticGap hfast (recursiveCurvature μ j) (recursiveCurvature_nonneg S.μ_pos j))
      (recursiveOutputKernel dx dy ℓ α σ μ δ N E O.kernel j ∘ₘ ν) ∧
    Integrable (fun z : Euclid dy × Joint dx dy => S.fastError (recursiveMass μ j) z.2)
      (recursiveOutputKernel dx dy ℓ α σ μ δ N E O.kernel j ∘ₘ ν) ∧
    (∫ z, S.dualQuadraticGap hfast (recursiveCurvature μ j) (recursiveCurvature_nonneg S.μ_pos j) z
      ∂recursiveOutputKernel dx dy ℓ α σ μ δ N E O.kernel j ∘ₘ ν) ≤ recursiveAccuracy μ δ N j ∧
    (∫ z, S.fastError (recursiveMass μ j) z.2
      ∂recursiveOutputKernel dx dy ℓ α σ μ δ N E O.kernel j ∘ₘ ν) ≤ recursiveAccuracy μ δ N j := by
  obtain ⟨hri, hrb⟩ := S.recursiveRunProgram_energy O hαℓ hfast hδ N E ν hi hb j
  rw [recursiveOutputKernel, ← Measure.comp_assoc]
  exact S.recursiveStageProgram_accuracy O hαℓ hfast hδ N E j _ hri hrb

end SCObjective
end FreshGradientMinimax
