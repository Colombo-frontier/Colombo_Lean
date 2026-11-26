import FreshGradientMinimax.SCSCWorkRate
import FreshGradientMinimax.PrimalNormalization

/-! F.5 for a fixed base objective, with arbitrary random initialization
and the original paper's parameter range, including zero-dimensional
spaces. Both guarantees concern the same actual original-query law. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

def localizedSCSCProgram (dx dy : ℕ) (ℓ α σ μ η E₀ : ℝ) : OracleProgram dx dy (Joint dx dy) (Joint dx dy) :=
  scscSolverProgram dx dy ℓ (min α ℓ) σ μ η E₀

namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem saddleStartEnergy_nonneg (z : Joint dx dy) : 0 ≤ S.saddleStartEnergy z := by
  have hℓ := S.L_pos
  have hμ := S.μ_pos
  unfold saddleStartEnergy
  positivity

theorem localizedSCSCProgram_accuracy_cost (O : FreshOracle S.toNCObjective σ)
    (hfast : ℓ / 4 ≤ α) {η E₀ : ℝ} (hη : 0 < η)
    (ν : Measure (Joint dx dy)) [IsProbabilityMeasure ν]
    (hi : Integrable S.saddleStartEnergy ν) (hb : (∫ z, S.saddleStartEnergy z ∂ν) ≤ E₀) :
    Integrable (fun t : Joint dx dy × ℕ => S.gap t.1.1 t.1.2)
      ((localizedSCSCProgram dx dy ℓ α σ μ η E₀).originalKernel O.kernel ∘ₘ ν) ∧
    (∫ t, S.gap t.1.1 t.1.2 ∂(localizedSCSCProgram dx dy ℓ α σ μ η E₀).originalKernel O.kernel ∘ₘ ν) ≤ η ∧
    Integrable costValue ((localizedSCSCProgram dx dy ℓ α σ μ η E₀).originalKernel O.kernel ∘ₘ ν) ∧
    (∫ t, costValue t ∂(localizedSCSCProgram dx dy ℓ α σ μ η E₀).originalKernel O.kernel ∘ₘ ν) ≤
      10 ^ 110 * valueLogFactor ℓ σ μ η ^ 8 *
        (Real.sqrt (ℓ / μ) * Real.log (2 + (ℓ / μ) * E₀ / η) + σ ^ 2 / (μ * η)) := by
  have hi' : Integrable S.normalizedPrimal.saddleStartEnergy ν := by
    rw [S.normalizedPrimal_startEnergy]
    exact hi
  have hb' : (∫ z, S.normalizedPrimal.saddleStartEnergy z ∂ν) ≤ E₀ := by
    rw [S.normalizedPrimal_startEnergy]
    exact hb
  have hE : 0 ≤ E₀ := (integral_nonneg S.saddleStartEnergy_nonneg).trans hb
  have hgap := S.normalizedPrimal.scscSolverProgram_original_gap O (min_le_right α ℓ)
    (S.normalizedPrimal_fast hfast) hη ν hi' hb'
  have hcost := S.normalizedPrimal.scscSolverProgram_mean_calls O η E₀ ν
  have hrate := S.normalizedPrimal.scscSolverProgram_calls_rate O (S.normalizedPrimal_fast hfast) hη hE ν
  exact ⟨hgap.1, hgap.2, hcost.1, hrate⟩

end SCObjective

theorem localizedSCSC_primitive (dx dy : ℕ) (ℓ α σ μ : ℝ)
    (hfast : ℓ / 4 ≤ α) {η E₀ : ℝ} (hη : 0 < η) :
    ∃ P : OracleProgram dx dy (Joint dx dy) (Joint dx dy),
      ∀ (S : SCObjective dx dy ℓ μ α) (O : FreshOracle S.toNCObjective σ)
      (ν : Measure (Joint dx dy)) (_ : IsProbabilityMeasure ν),
      Integrable S.saddleStartEnergy ν → (∫ z, S.saddleStartEnergy z ∂ν) ≤ E₀ →
        Integrable (fun t : Joint dx dy × ℕ => S.gap t.1.1 t.1.2) (P.originalKernel O.kernel ∘ₘ ν) ∧
        (∫ t, S.gap t.1.1 t.1.2 ∂P.originalKernel O.kernel ∘ₘ ν) ≤ η ∧
        Integrable costValue (P.originalKernel O.kernel ∘ₘ ν) ∧
        (∫ t, costValue t ∂P.originalKernel O.kernel ∘ₘ ν) ≤
          10 ^ 110 * valueLogFactor ℓ σ μ η ^ 8 *
            (Real.sqrt (ℓ / μ) * Real.log (2 + (ℓ / μ) * E₀ / η) + σ ^ 2 / (μ * η)) := by
  refine ⟨localizedSCSCProgram dx dy ℓ α σ μ η E₀, ?_⟩
  intro S O ν hν hi hb
  letI := hν
  exact S.localizedSCSCProgram_accuracy_cost O hfast hη ν hi hb

end FreshGradientMinimax
