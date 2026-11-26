import FreshGradientMinimax.OuterMoments

/-! One actual coarse outer step, including changing the proximal center
to the previous primal output. All moments below refer to its actual output
kernel and are derived from the two input moments. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

def outerStepProgram (dx dy : ℕ) (L σ μ η E : ℝ) :
    OracleProgram dx dy (Euclid dx × Joint dx dy) (Euclid dx × Joint dx dy) :=
  (proximalSolverProgram dx dy L σ μ (η / 2) E).precompose recenterProximal recenterProximal_continuous.measurable

theorem outerStepProgram_result_law {dx dy : ℕ} (L σ μ η E : ℝ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) (ν : Measure (Euclid dx × Joint dx dy)) :
    (outerStepProgram dx dy L σ μ η E).resultKernel K ∘ₘ ν =
      (proximalSolverProgram dx dy L σ μ (η / 2) E).resultKernel K ∘ₘ ν.map recenterProximal := by
  rw [outerStepProgram, OracleProgram.precompose_result, comap_comp_measure]

namespace NCObjective
variable {dx dy : ℕ} {L μ σ : ℝ} (F : NCObjective dx dy L μ)

theorem outerStepProgram_gap (O : FreshOracle F σ) {η E : ℝ} (hη : 0 < η) (hE : 0 < E)
    (ν : Measure (Euclid dx × Joint dx dy)) [IsProbabilityMeasure ν]
    (hi : Integrable (fun p => F.proximalStartEnergy (recenterProximal p)) ν)
    (hb : (∫ p, F.proximalStartEnergy (recenterProximal p) ∂ν) ≤ E) :
    Integrable F.proximalGap ((outerStepProgram dx dy L σ μ η E).resultKernel O.kernel ∘ₘ ν) ∧
    (∫ p, F.proximalGap p ∂(outerStepProgram dx dy L σ μ η E).resultKernel O.kernel ∘ₘ ν) ≤ η := by
  letI : IsProbabilityMeasure (ν.map recenterProximal) := isProbabilityMeasure_map recenterProximal_continuous.measurable.aemeasurable
  rw [outerStepProgram_result_law]
  apply F.proximalSolverProgram_result_accuracy O hη hE
  · exact (integrable_map_measure F.proximalStartEnergy_continuous.stronglyMeasurable.aestronglyMeasurable
      recenterProximal_continuous.measurable.aemeasurable).mpr hi
  · rwa [integral_map recenterProximal_continuous.measurable.aemeasurable
      F.proximalStartEnergy_continuous.stronglyMeasurable.aestronglyMeasurable]

theorem outerStepProgram_center (O : FreshOracle F σ) (η E Δ : ℝ)
    (ν : Measure (Euclid dx × Joint dx dy))
    (hi : Integrable (fun p : Euclid dx × Joint dx dy => F.primalHeight Δ p.2.1) ν) :
    Integrable (fun p : Euclid dx × Joint dx dy => F.primalHeight Δ p.1)
      ((outerStepProgram dx dy L σ μ η E).resultKernel O.kernel ∘ₘ ν) ∧
    (∫ p, F.primalHeight Δ p.1 ∂(outerStepProgram dx dy L σ μ η E).resultKernel O.kernel ∘ₘ ν) =
      ∫ p, F.primalHeight Δ p.2.1 ∂ν := by
  have hc : Integrable (fun p : Euclid dx × Joint dx dy => F.primalHeight Δ p.1) (ν.map recenterProximal) :=
    (integrable_map_measure ((F.primalHeight_continuous Δ).comp continuous_fst).stronglyMeasurable.aestronglyMeasurable
      recenterProximal_continuous.measurable.aemeasurable).mpr hi
  have h := F.proximalSolverProgram_center_integrable O (η / 2) E (ν.map recenterProximal)
    (F.primalHeight Δ) (F.primalHeight_continuous Δ).measurable hc
  rw [outerStepProgram_result_law]
  refine ⟨h.1, h.2.trans ?_⟩
  rw [integral_map (f := fun p : Euclid dx × Joint dx dy => F.primalHeight Δ p.1)
    recenterProximal_continuous.measurable.aemeasurable
    ((F.primalHeight_continuous Δ).comp continuous_fst).stronglyMeasurable.aestronglyMeasurable]
  rfl

theorem outerStepProgram_integrability (O : FreshOracle F σ) {Δ η E : ℝ}
    (hΔ : F.PrimalGapAtMost Δ) (hη : 0 < η) (hE : 0 < E)
    (ν : Measure (Euclid dx × Joint dx dy)) [IsProbabilityMeasure ν]
    (hi : Integrable (fun p => F.proximalStartEnergy (recenterProximal p)) ν)
    (hb : (∫ p, F.proximalStartEnergy (recenterProximal p) ∂ν) ≤ E)
    (hh : Integrable (fun p : Euclid dx × Joint dx dy => F.primalHeight Δ p.2.1) ν) :
    Integrable (fun p : Euclid dx × Joint dx dy => F.primalHeight Δ p.2.1)
      ((outerStepProgram dx dy L σ μ η E).resultKernel O.kernel ∘ₘ ν) ∧
    Integrable (proximalMoveEnergy L) ((outerStepProgram dx dy L σ μ η E).resultKernel O.kernel ∘ₘ ν) ∧
    Integrable (fun p : Euclid dx × Joint dx dy => F.proximalResidualEnergy p.1)
      ((outerStepProgram dx dy L σ μ η E).resultKernel O.kernel ∘ₘ ν) ∧
    Integrable (fun p : Euclid dx × Joint dx dy => F.proximalStartEnergy (recenterProximal p))
      ((outerStepProgram dx dy L σ μ η E).resultKernel O.kernel ∘ₘ ν) :=
  F.proximal_output_integrability hΔ _ (F.outerStepProgram_center O η E Δ ν hh).1
    (F.outerStepProgram_gap O hη hE ν hi hb).1

theorem outerStepProgram_descent (O : FreshOracle F σ) {Δ η E : ℝ}
    (hΔ : F.PrimalGapAtMost Δ) (hη : 0 < η) (hE : 0 < E)
    (ν : Measure (Euclid dx × Joint dx dy)) [IsProbabilityMeasure ν]
    (hi : Integrable (fun p => F.proximalStartEnergy (recenterProximal p)) ν)
    (hb : (∫ p, F.proximalStartEnergy (recenterProximal p) ∂ν) ≤ E)
    (hh : Integrable (fun p : Euclid dx × Joint dx dy => F.primalHeight Δ p.2.1) ν) :
    (∫ p, F.primalHeight Δ p.2.1 ∂(outerStepProgram dx dy L σ μ η E).resultKernel O.kernel ∘ₘ ν) +
      (∫ p, proximalMoveEnergy L p ∂(outerStepProgram dx dy L σ μ η E).resultKernel O.kernel ∘ₘ ν) +
      (∫ p, F.proximalResidualEnergy p.1 ∂(outerStepProgram dx dy L σ μ η E).resultKernel O.kernel ∘ₘ ν) ≤
      (∫ p, F.primalHeight Δ p.2.1 ∂ν) + η := by
  have hc := F.outerStepProgram_center O η E Δ ν hh
  have hg := F.outerStepProgram_gap O hη hE ν hi hb
  have h := F.proximal_output_descent hΔ _ hc.1 hg.1
  rw [hc.2] at h
  linarith [hg.2]

theorem outerStepProgram_energy_bound (O : FreshOracle F σ) {Δ η E : ℝ}
    (hΔ : F.PrimalGapAtMost Δ) (hη : 0 < η) (hE : 0 < E)
    (ν : Measure (Euclid dx × Joint dx dy)) [IsProbabilityMeasure ν]
    (hi : Integrable (fun p => F.proximalStartEnergy (recenterProximal p)) ν)
    (hb : (∫ p, F.proximalStartEnergy (recenterProximal p) ∂ν) ≤ E)
    (hh : Integrable (fun p : Euclid dx × Joint dx dy => F.primalHeight Δ p.2.1) ν) :
    (∫ p, F.proximalStartEnergy (recenterProximal p) ∂(outerStepProgram dx dy L σ μ η E).resultKernel O.kernel ∘ₘ ν) ≤
      12 * η + 24 * (∫ p, proximalMoveEnergy L p ∂(outerStepProgram dx dy L σ μ η E).resultKernel O.kernel ∘ₘ ν) := by
  have hg := F.outerStepProgram_gap O hη hE ν hi hb
  have h := F.proximal_output_warm_energy hΔ _ (F.outerStepProgram_center O η E Δ ν hh).1 hg.1
  linarith [hg.2]

end NCObjective
end FreshGradientMinimax
