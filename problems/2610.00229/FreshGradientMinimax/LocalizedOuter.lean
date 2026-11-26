import FreshGradientMinimax.OuterTelescope
import FreshGradientMinimax.OuterCost

/-! The coarse algorithm with its known localization parameters. The
initialization hypotheses of all its solves are discharged analytically. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators

def localizedOuterProgram (dx dy : ℕ) (L σ μ Δ G η : ℝ) (T n : ℕ) :
    OracleProgram dx dy (Euclid dx × Joint dx dy) (Euclid dx × Joint dx dy) :=
  outerRunProgram dx dy L σ μ η (outerColdEnvelope L μ Δ G η) (outerWarmEnvelope Δ η T) n

def localizedOuterLaw {dx dy : ℕ} (L σ μ Δ G η : ℝ) (T : ℕ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) (n : ℕ) : Measure (Euclid dx × Joint dx dy) :=
  outerRunLaw L σ μ η (outerColdEnvelope L μ Δ G η) (outerWarmEnvelope Δ η T) K n

instance localizedOuterLaw_probability {dx dy : ℕ} (L σ μ Δ G η : ℝ) (T : ℕ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    IsProbabilityMeasure (localizedOuterLaw L σ μ Δ G η T K n) := by
  unfold localizedOuterLaw
  infer_instance

theorem localizedOuterLaw_original {dx dy : ℕ} (L σ μ Δ G η : ℝ) (T : ℕ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    ((localizedOuterProgram dx dy L σ μ Δ G η T n).originalKernel K ∘ₘ Measure.dirac 0).map Prod.fst =
      localizedOuterLaw L σ μ Δ G η T K n := outerRunLaw_original _ _ _ _ _ _ _ _

namespace NCObjective
variable {dx dy : ℕ} {L μ σ : ℝ} (F : NCObjective dx dy L μ)

theorem localizedOuter_invariant (O : FreshOracle F σ) {Δ G η : ℝ}
    (hΔ : F.PrimalGapAtMost Δ) (hG : F.DualLocalized G) (hη : 0 < η) (T : ℕ) {n : ℕ} (hn : n ≤ T) :
    Integrable (fun p : Euclid dx × Joint dx dy => F.primalHeight Δ p.2.1) (localizedOuterLaw L σ μ Δ G η T O.kernel n) ∧
    Integrable (fun p => F.proximalStartEnergy (recenterProximal p)) (localizedOuterLaw L σ μ Δ G η T O.kernel n) ∧
    (∫ p, F.primalHeight Δ p.2.1 ∂localizedOuterLaw L σ μ Δ G η T O.kernel n) ≤ Δ + n * η ∧
    (∫ p, F.proximalStartEnergy (recenterProximal p) ∂localizedOuterLaw L σ μ Δ G η T O.kernel n) ≤
      outerStageEnvelope (outerColdEnvelope L μ Δ G η) (outerWarmEnvelope Δ η T) n :=
  F.outerRunLaw_invariant O hΔ hη (F.outerColdEnvelope_pos (F.primalGap_parameter_nonneg hΔ) hη)
    (outerWarmEnvelope_pos (F.primalGap_parameter_nonneg hΔ) hη T)
    (F.outer_initial_energy hΔ hG hη.le) T le_rfl n hn

theorem localizedOuter_gap (O : FreshOracle F σ) {Δ G η : ℝ}
    (hΔ : F.PrimalGapAtMost Δ) (hG : F.DualLocalized G) (hη : 0 < η) (T : ℕ) {n : ℕ} (hn : n < T) :
    Integrable F.proximalGap (localizedOuterLaw L σ μ Δ G η T O.kernel (n + 1)) ∧
    (∫ p, F.proximalGap p ∂localizedOuterLaw L σ μ Δ G η T O.kernel (n + 1)) ≤ η :=
  F.outerRunLaw_gap O hΔ hη (F.outerColdEnvelope_pos (F.primalGap_parameter_nonneg hΔ) hη)
    (outerWarmEnvelope_pos (F.primalGap_parameter_nonneg hΔ) hη T)
    (F.outer_initial_energy hΔ hG hη.le) T le_rfl hn

theorem localizedOuter_step_moments (O : FreshOracle F σ) {Δ G η : ℝ}
    (hΔ : F.PrimalGapAtMost Δ) (hG : F.DualLocalized G) (hη : 0 < η) (T : ℕ) {n : ℕ} (hn : n < T) :
    Integrable (proximalMoveEnergy L) (localizedOuterLaw L σ μ Δ G η T O.kernel (n + 1)) ∧
    Integrable (fun p : Euclid dx × Joint dx dy => F.proximalResidualEnergy p.1)
      (localizedOuterLaw L σ μ Δ G η T O.kernel (n + 1)) :=
  F.outerRunLaw_step_moments O hΔ hη (F.outerColdEnvelope_pos (F.primalGap_parameter_nonneg hΔ) hη)
    (outerWarmEnvelope_pos (F.primalGap_parameter_nonneg hΔ) hη T)
    (F.outer_initial_energy hΔ hG hη.le) T le_rfl hn

theorem localizedOuter_telescope (O : FreshOracle F σ) {Δ G η : ℝ}
    (hΔ : F.PrimalGapAtMost Δ) (hG : F.DualLocalized G) (hη : 0 < η) (T : ℕ) :
    (∫ p, F.primalHeight Δ p.2.1 ∂localizedOuterLaw L σ μ Δ G η T O.kernel T) +
      (∑ j ∈ Finset.range T, ∫ p, proximalMoveEnergy L p ∂localizedOuterLaw L σ μ Δ G η T O.kernel (j + 1)) +
      (∑ j ∈ Finset.range T, ∫ p, F.proximalResidualEnergy p.1 ∂localizedOuterLaw L σ μ Δ G η T O.kernel (j + 1)) ≤ Δ + T * η :=
  F.outerRunLaw_telescope O hΔ hη (F.outerColdEnvelope_pos (F.primalGap_parameter_nonneg hΔ) hη)
    (outerWarmEnvelope_pos (F.primalGap_parameter_nonneg hΔ) hη T)
    (F.outer_initial_energy hΔ hG hη.le) T le_rfl

theorem localizedOuter_residual_bound (O : FreshOracle F σ) {Δ G η : ℝ}
    (hΔ : F.PrimalGapAtMost Δ) (hG : F.DualLocalized G) (hη : 0 < η) (T : ℕ) :
    (∑ j ∈ Finset.range T, ∫ p, F.proximalResidualEnergy p.1 ∂localizedOuterLaw L σ μ Δ G η T O.kernel (j + 1)) ≤ Δ + T * η :=
  F.outerRunLaw_residual_bound O hΔ hη (F.outerColdEnvelope_pos (F.primalGap_parameter_nonneg hΔ) hη)
    (outerWarmEnvelope_pos (F.primalGap_parameter_nonneg hΔ) hη T)
    (F.outer_initial_energy hΔ hG hη.le) T le_rfl

theorem localizedOuter_refinement_energy (O : FreshOracle F σ) {Δ G η : ℝ}
    (hΔ : F.PrimalGapAtMost Δ) (hG : F.DualLocalized G) (hη : 0 < η) (T : ℕ) {n : ℕ} (hn : n < T) :
    Integrable F.proximalStartEnergy (localizedOuterLaw L σ μ Δ G η T O.kernel (n + 1)) ∧
    (∫ p, F.proximalStartEnergy p ∂localizedOuterLaw L σ μ Δ G η T O.kernel (n + 1)) ≤ 6 * η := by
  have hg := F.localizedOuter_gap O hΔ hG hη T hn
  have hi := integrable_nonneg_envelope F.proximalStartEnergy_continuous.measurable F.proximalStartEnergy_nonneg
    (hg.1.const_mul 6) F.proximalStartEnergy_le_gap
  refine ⟨hi, ?_⟩
  have h := integral_mono hi (hg.1.const_mul 6) F.proximalStartEnergy_le_gap
  rw [integral_const_mul] at h
  linarith [hg.2]

end NCObjective
end FreshGradientMinimax
