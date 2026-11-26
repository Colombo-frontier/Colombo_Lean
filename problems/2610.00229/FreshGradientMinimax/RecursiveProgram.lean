import FreshGradientMinimax.RecursiveInitialization
import FreshGradientMinimax.ProgramResult

/-! The actual finite sequence of value solves and known quadratic
updates used in F.5. Only the first stage uses the cold-start envelope;
all later stages use the proved unconditional 69e warm-start bound. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

def recursiveInputEnvelope (μ δ : ℝ) (N : ℕ) (E : ℝ) : ℕ → ℝ
  | 0 => E
  | j + 1 => 69 * recursiveAccuracy μ δ N j

def recursiveStageProgram (dx dy : ℕ) (ℓ α σ μ δ : ℝ) (N : ℕ) (E : ℝ) (j : ℕ) :
    OracleProgram dx dy (Euclid dy × Joint dx dy) (Euclid dy × Joint dx dy) :=
  quadraticValueProgram dx dy ℓ α σ μ (recursiveCurvature μ j)
    (recursiveAccuracy μ δ N j) (recursiveInputEnvelope μ δ N E j)

def recursiveRestartProgram (dx dy : ℕ) (ℓ α σ μ δ : ℝ) (N : ℕ) (E : ℝ) (j : ℕ) :
    OracleProgram dx dy (Euclid dy × Joint dx dy) (Euclid dy × Joint dx dy) :=
  (recursiveStageProgram dx dy ℓ α σ μ δ N E j).map (quadraticAdvance (recursiveMass μ j))
    (quadraticAdvance_continuous _).measurable

def recursiveRunProgram (dx dy : ℕ) (ℓ α σ μ δ : ℝ) (N : ℕ) (E : ℝ) :
    ℕ → OracleProgram dx dy (Euclid dy × Joint dx dy) (Euclid dy × Joint dx dy)
  | 0 => OracleProgram.pure id measurable_id
  | j + 1 => (recursiveRunProgram dx dy ℓ α σ μ δ N E j).chain (recursiveRestartProgram dx dy ℓ α σ μ δ N E j)

def recursiveSolverProgram (dx dy : ℕ) (ℓ α σ μ δ : ℝ) (N : ℕ) (E : ℝ) :
    OracleProgram dx dy (Euclid dy × Joint dx dy) (Euclid dy × Joint dx dy) :=
  (recursiveRunProgram dx dy ℓ α σ μ δ N E N).chain (recursiveStageProgram dx dy ℓ α σ μ δ N E N)

namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem dualQuadraticEnergy_congr (hfast : ℓ / 4 ≤ α) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a = b) :
    S.dualQuadraticEnergy hfast a ha = S.dualQuadraticEnergy hfast b hb := by
  cases hab
  rfl

theorem recursiveRestartProgram_energy (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) (E : ℝ) (j : ℕ)
    (ν : Measure (Euclid dy × Joint dx dy)) [IsProbabilityMeasure ν]
    (hi : Integrable (S.dualQuadraticEnergy hfast (recursiveCurvature μ j) (recursiveCurvature_nonneg S.μ_pos j)) ν)
    (hb : (∫ z, S.dualQuadraticEnergy hfast (recursiveCurvature μ j) (recursiveCurvature_nonneg S.μ_pos j) z ∂ν)
      ≤ recursiveInputEnvelope μ δ N E j) :
    Integrable (S.dualQuadraticEnergy hfast (recursiveCurvature μ (j + 1)) (recursiveCurvature_nonneg S.μ_pos (j + 1)))
      ((recursiveRestartProgram dx dy ℓ α σ μ δ N E j).resultKernel O.kernel ∘ₘ ν) ∧
    (∫ z, S.dualQuadraticEnergy hfast (recursiveCurvature μ (j + 1)) (recursiveCurvature_nonneg S.μ_pos (j + 1)) z
      ∂(recursiveRestartProgram dx dy ℓ α σ μ δ N E j).resultKernel O.kernel ∘ₘ ν) ≤ recursiveInputEnvelope μ δ N E (j + 1) := by
  have h := S.quadraticValueProgram_restart O hαℓ hfast (recursiveCurvature_nonneg S.μ_pos j)
    (recursiveAccuracy_pos S.μ_pos hδ N j) ν hi hb
  rw [OracleProgram.original_result_law, Measure.map_comp _ _ (quadraticAdvance_continuous _).measurable] at h
  have hf : S.dualQuadraticEnergy hfast (recursiveCurvature μ (j + 1)) (recursiveCurvature_nonneg S.μ_pos (j + 1)) =
      S.dualQuadraticEnergy hfast (recursiveCurvature μ j + (μ + recursiveCurvature μ j))
        (add_nonneg (recursiveCurvature_nonneg S.μ_pos j) (add_nonneg S.μ_pos.le (recursiveCurvature_nonneg S.μ_pos j))) := by
    apply S.dualQuadraticEnergy_congr
    rw [recursiveCurvature_succ, recursiveMass_add_curvature]
  rw [hf, recursiveRestartProgram, OracleProgram.map_result]
  simpa only [recursiveStageProgram, recursiveInputEnvelope,
    recursiveMass_add_curvature] using h

theorem recursiveRunProgram_energy (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) (E : ℝ)
    (ν : Measure (Euclid dy × Joint dx dy)) [IsProbabilityMeasure ν]
    (hi : Integrable (S.dualQuadraticEnergy hfast 0 le_rfl) ν)
    (hb : (∫ z, S.dualQuadraticEnergy hfast 0 le_rfl z ∂ν) ≤ E) (n : ℕ) :
    Integrable (S.dualQuadraticEnergy hfast (recursiveCurvature μ n) (recursiveCurvature_nonneg S.μ_pos n))
      ((recursiveRunProgram dx dy ℓ α σ μ δ N E n).resultKernel O.kernel ∘ₘ ν) ∧
    (∫ z, S.dualQuadraticEnergy hfast (recursiveCurvature μ n) (recursiveCurvature_nonneg S.μ_pos n) z
      ∂(recursiveRunProgram dx dy ℓ α σ μ δ N E n).resultKernel O.kernel ∘ₘ ν) ≤ recursiveInputEnvelope μ δ N E n := by
  induction n with
  | zero =>
    rw [recursiveRunProgram, OracleProgram.pure_result]
    have heq : (Kernel.deterministic id measurable_id : Kernel (Euclid dy × Joint dx dy) _) ∘ₘ ν = ν := Measure.bind_dirac
    rw [heq]
    have hf : S.dualQuadraticEnergy hfast (recursiveCurvature μ 0) (recursiveCurvature_nonneg S.μ_pos 0) =
        S.dualQuadraticEnergy hfast 0 le_rfl := S.dualQuadraticEnergy_congr hfast _ _ (recursiveCurvature_zero μ)
    rw [hf]
    exact ⟨hi, hb⟩
  | succ n ih =>
    rw [recursiveRunProgram, OracleProgram.chain_result, ← Measure.comp_assoc]
    exact S.recursiveRestartProgram_energy O hαℓ hfast hδ N E n _ ih.1 ih.2

end SCObjective
end FreshGradientMinimax
