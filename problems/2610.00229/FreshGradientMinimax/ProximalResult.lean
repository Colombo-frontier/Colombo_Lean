import FreshGradientMinimax.ProximalPrimitive

/-! The random proximal solve's output marginal, retained center, and
energy for a refinement of the same subproblem. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace NCObjective
variable {dx dy : ℕ} {L μ σ : ℝ} (F : NCObjective dx dy L μ)

theorem proximalSolverProgram_center_marginal (O : FreshOracle F σ) (η E₀ : ℝ)
    (ν : Measure (Euclid dx × Joint dx dy)) :
    ((proximalSolverProgram dx dy L σ μ η E₀).resultKernel O.kernel ∘ₘ ν).map Prod.fst = ν.map Prod.fst := by
  have hk : ((proximalSolverProgram dx dy L σ μ η E₀).originalKernel O.kernel).map
      (fun t : (Euclid dx × Joint dx dy) × ℕ => t.1.1) = Kernel.deterministic Prod.fst measurable_fst := by
    apply Kernel.ext
    intro p
    rw [Kernel.map_apply _ measurable_fst.fst, F.proximalSolverProgram_apply,
      Measure.map_map measurable_fst.fst (costedMap_measurable measurable_prodMk_left)]
    change (((scscSolverProgram dx dy (3 * L) L σ μ η E₀).originalKernel (O.proximal p.1).kernel) p.2).map
      (fun _ => p.1) = Measure.dirac p.1
    rw [OracleProgram.originalKernel_eq_law, Measure.map_const]
    simp only [measure_univ, one_smul]
  rw [← OracleProgram.original_result_law, Measure.map_map measurable_fst measurable_fst]
  simp only [Function.comp_def]
  rw [Measure.map_comp _ _ (measurable_fst.fst : Measurable (fun t : (Euclid dx × Joint dx dy) × ℕ => t.1.1))]
  rw [hk, Measure.deterministic_comp_eq_map measurable_fst]

theorem proximalSolverProgram_center_integrable (O : FreshOracle F σ) (η E₀ : ℝ)
    (ν : Measure (Euclid dx × Joint dx dy)) (h : Euclid dx → ℝ) (hh : Measurable h)
    (hi : Integrable (fun p : Euclid dx × Joint dx dy => h p.1) ν) :
    Integrable (fun p : Euclid dx × Joint dx dy => h p.1)
      ((proximalSolverProgram dx dy L σ μ η E₀).resultKernel O.kernel ∘ₘ ν) ∧
    (∫ p, h p.1 ∂(proximalSolverProgram dx dy L σ μ η E₀).resultKernel O.kernel ∘ₘ ν) = ∫ p, h p.1 ∂ν := by
  have hm := F.proximalSolverProgram_center_marginal O η E₀ ν
  constructor
  · apply (integrable_map_measure hh.stronglyMeasurable.aestronglyMeasurable measurable_fst.aemeasurable).mp
    rw [hm]
    exact (integrable_map_measure hh.stronglyMeasurable.aestronglyMeasurable measurable_fst.aemeasurable).mpr hi
  · have he := congrArg (fun ρ : Measure (Euclid dx) => ∫ c, h c ∂ρ) hm
    simpa only [integral_map measurable_fst.aemeasurable hh.stronglyMeasurable.aestronglyMeasurable] using he

theorem proximalSolverProgram_result_accuracy (O : FreshOracle F σ) {η E₀ : ℝ}
    (hη : 0 < η) (hE : 0 < E₀) (ν : Measure (Euclid dx × Joint dx dy)) [IsProbabilityMeasure ν]
    (hi : Integrable F.proximalStartEnergy ν) (hb : (∫ p, F.proximalStartEnergy p ∂ν) ≤ E₀) :
    Integrable F.proximalGap ((proximalSolverProgram dx dy L σ μ (η / 2) E₀).resultKernel O.kernel ∘ₘ ν) ∧
    (∫ p, F.proximalGap p ∂(proximalSolverProgram dx dy L σ μ (η / 2) E₀).resultKernel O.kernel ∘ₘ ν) ≤ η := by
  have h := F.proximalSolverProgram_random_accuracy O hη hE ν hi hb
  rw [← OracleProgram.original_result_law]
  refine ⟨(integrable_map_measure F.proximalGap_continuous.stronglyMeasurable.aestronglyMeasurable
    measurable_fst.aemeasurable).mpr h.1, ?_⟩
  rw [integral_map measurable_fst.aemeasurable F.proximalGap_continuous.stronglyMeasurable.aestronglyMeasurable]
  exact h.2

theorem proximalStartEnergy_nonneg (p : Euclid dx × Joint dx dy) : 0 ≤ F.proximalStartEnergy p :=
  (F.proximalObjective p.1).saddleStartEnergy_nonneg p.2

theorem proximalStartEnergy_le_gap (p : Euclid dx × Joint dx dy) :
    F.proximalStartEnergy p ≤ 6 * F.proximalGap p := by
  have h := F.proximal_gap_controls_distance p.1 p.2.1 p.2.2
  have hy := mul_nonneg F.μ_pos.le (sq_nonneg ‖p.2.2 - F.dualMax (F.proxPoint p.1)‖)
  simp only [proximalStartEnergy, SCObjective.saddleStartEnergy,
    F.proximalObjective_saddleU, F.proximalObjective_saddleV]
  change _ ≤ 6 * (F.proximalObjective p.1).gap p.2.1 p.2.2
  linarith

theorem proximalSolverProgram_refinement_energy (O : FreshOracle F σ) {η E₀ : ℝ}
    (hη : 0 < η) (hE : 0 < E₀) (ν : Measure (Euclid dx × Joint dx dy)) [IsProbabilityMeasure ν]
    (hi : Integrable F.proximalStartEnergy ν) (hb : (∫ p, F.proximalStartEnergy p ∂ν) ≤ E₀) :
    Integrable F.proximalStartEnergy ((proximalSolverProgram dx dy L σ μ (η / 2) E₀).resultKernel O.kernel ∘ₘ ν) ∧
    (∫ p, F.proximalStartEnergy p ∂(proximalSolverProgram dx dy L σ μ (η / 2) E₀).resultKernel O.kernel ∘ₘ ν) ≤ 6 * η := by
  have ha := F.proximalSolverProgram_result_accuracy O hη hE ν hi hb
  have he : Integrable F.proximalStartEnergy
      ((proximalSolverProgram dx dy L σ μ (η / 2) E₀).resultKernel O.kernel ∘ₘ ν) := by
    apply (ha.1.const_mul 6).mono' F.proximalStartEnergy_continuous.stronglyMeasurable.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun p => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (F.proximalStartEnergy_nonneg p)] using F.proximalStartEnergy_le_gap p)
  refine ⟨he, ?_⟩
  have h := integral_mono he (ha.1.const_mul 6) F.proximalStartEnergy_le_gap
  rw [integral_const_mul] at h
  linarith [ha.2]

end NCObjective
end FreshGradientMinimax
