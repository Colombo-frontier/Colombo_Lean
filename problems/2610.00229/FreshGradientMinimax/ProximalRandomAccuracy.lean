import FreshGradientMinimax.ProximalProgram
import FreshGradientMinimax.ProximalMeasurability
import FreshGradientMinimax.MixtureEnvelope

/-! The implemented proximal solver accepts arbitrary correlated random
centers and initial points. Only an unconditional energy bound is needed. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem scscSolverProgram_pointwise_gap_envelope (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {η E₀ : ℝ} (hη : 0 < η) (hE : 0 < E₀)
    (z : Joint dx dy) :
    Integrable (fun t : Joint dx dy × ℕ => S.gap t.1.1 t.1.2)
      ((scscSolverProgram dx dy ℓ α σ μ η E₀).originalKernel O.kernel z) ∧
    (∫ t, S.gap t.1.1 t.1.2 ∂(scscSolverProgram dx dy ℓ α σ μ η E₀).originalKernel O.kernel z) ≤
      η * (1 + S.saddleStartEnergy z / E₀) := by
  apply kernel_affine_envelope_of_mean_guarantee
    ((scscSolverProgram dx dy ℓ α σ μ η E₀).originalKernel O.kernel)
    S.saddleStartEnergy S.saddleStartEnergy_nonneg
    (S.saddleU, S.saddleV) (by simp [saddleStartEnergy])
    (fun t : Joint dx dy × ℕ => S.gap t.1.1 t.1.2)
    (fun t => S.gap_nonneg t.1.1 t.1.2) hE
  intro ν hν hi hb
  letI := hν
  exact S.scscSolverProgram_original_gap O hαℓ hfast hη ν hi hb

end SCObjective

namespace NCObjective
variable {dx dy : ℕ} {L μ σ : ℝ} (F : NCObjective dx dy L μ)

theorem proximalSolverProgram_pointwise_gap (O : FreshOracle F σ) {η E₀ : ℝ}
    (hη : 0 < η) (hE : 0 < E₀) (p : Euclid dx × Joint dx dy) :
    Integrable (fun t : (Euclid dx × Joint dx dy) × ℕ => F.proximalGap t.1)
      ((proximalSolverProgram dx dy L σ μ η E₀).originalKernel O.kernel p) ∧
    (∫ t, F.proximalGap t.1 ∂(proximalSolverProgram dx dy L σ μ η E₀).originalKernel O.kernel p) ≤
      η * (1 + F.proximalStartEnergy p / E₀) := by
  rcases p with ⟨c, z⟩
  have hL := F.L_pos
  have h := (F.proximalObjective c).scscSolverProgram_pointwise_gap_envelope (O.proximal c)
    (by linarith) (by linarith) hη hE z
  have hm : StronglyMeasurable (fun t : (Euclid dx × Joint dx dy) × ℕ => F.proximalGap t.1) :=
    (F.proximalGap_continuous.comp continuous_fst).stronglyMeasurable
  rw [F.proximalSolverProgram_apply]
  refine ⟨(integrable_map_measure hm.aestronglyMeasurable
    (costedMap_measurable measurable_prodMk_left).aemeasurable).mpr h.1, ?_⟩
  rw [integral_map (costedMap_measurable measurable_prodMk_left).aemeasurable hm.aestronglyMeasurable]
  exact h.2

theorem proximalSolverProgram_random_gap_envelope (O : FreshOracle F σ) {η E₀ : ℝ}
    (hη : 0 < η) (hE : 0 < E₀) (ν : Measure (Euclid dx × Joint dx dy)) [IsProbabilityMeasure ν]
    (hi : Integrable F.proximalStartEnergy ν) :
    Integrable (fun t : (Euclid dx × Joint dx dy) × ℕ => F.proximalGap t.1)
      ((proximalSolverProgram dx dy L σ μ η E₀).originalKernel O.kernel ∘ₘ ν) ∧
    (∫ t, F.proximalGap t.1 ∂(proximalSolverProgram dx dy L σ μ η E₀).originalKernel O.kernel ∘ₘ ν) ≤
      η * (1 + (∫ p, F.proximalStartEnergy p ∂ν) / E₀) := by
  have hpoint (p : Euclid dx × Joint dx dy) := F.proximalSolverProgram_pointwise_gap O hη hE p
  rw [OracleProgram.originalKernel_eq_law]
  simp only [OracleProgram.originalKernel_eq_law] at hpoint
  have hw : Integrable (fun p => η * (1 + F.proximalStartEnergy p / E₀)) ν :=
    ((integrable_const 1).add (hi.div_const E₀)).const_mul η
  have h := kernel_moment_from_envelope _ ν (fun t : (Euclid dx × Joint dx dy) × ℕ => F.proximalGap t.1)
    (F.proximalGap_continuous.comp continuous_fst).stronglyMeasurable
    (fun t => F.proximalGap_nonneg t.1) _ hw (fun p => (hpoint p).1) (fun p => (hpoint p).2)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [integral_const_mul, integral_add (integrable_const 1) (hi.div_const E₀), integral_div]
  simp only [integral_const, measureReal_univ_eq_one, one_smul]

theorem proximalSolverProgram_random_accuracy (O : FreshOracle F σ) {η E₀ : ℝ}
    (hη : 0 < η) (hE : 0 < E₀) (ν : Measure (Euclid dx × Joint dx dy)) [IsProbabilityMeasure ν]
    (hi : Integrable F.proximalStartEnergy ν) (hb : (∫ p, F.proximalStartEnergy p ∂ν) ≤ E₀) :
    Integrable (fun t : (Euclid dx × Joint dx dy) × ℕ => F.proximalGap t.1)
      ((proximalSolverProgram dx dy L σ μ (η / 2) E₀).originalKernel O.kernel ∘ₘ ν) ∧
    (∫ t, F.proximalGap t.1 ∂(proximalSolverProgram dx dy L σ μ (η / 2) E₀).originalKernel O.kernel ∘ₘ ν) ≤ η := by
  have h := F.proximalSolverProgram_random_gap_envelope O (half_pos hη) hE ν hi
  refine ⟨h.1, h.2.trans ?_⟩
  have hb' : (∫ p, F.proximalStartEnergy p ∂ν) / E₀ ≤ 1 :=
    (div_le_one hE).mpr hb
  nlinarith

end NCObjective
end FreshGradientMinimax
