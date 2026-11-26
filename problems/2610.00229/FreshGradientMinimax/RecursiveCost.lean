import FreshGradientMinimax.RecursiveProgram

/-! Exact expected original-call count of the full recursive program.
Each later initialization envelope is 69 times the preceding requested
accuracy; no new cold-start logarithm is introduced at later stages. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators

def recursiveStageWork (ℓ α σ μ δ : ℝ) (N : ℕ) (E : ℝ) (j : ℕ) : ℝ :=
  valueSolverWork ℓ α σ (μ + recursiveCurvature μ j) (5 * ℓ + recursiveCurvature μ j)
    (recursiveAccuracy μ δ N j) (recursiveInputEnvelope μ δ N E j)

namespace OracleProgram
variable {dx dy : ℕ} {X Y Z : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

theorem map_cost (P : OracleProgram dx dy X Y) (f : Y → Z) (hf : Measurable f)
    (K : Kernel (Joint dx dy) (Joint dx dy)) (x : X) (hi : Integrable costValue (P.lawKernel K x)) :
    Integrable costValue ((P.map f hf).lawKernel K x) ∧
    (∫ t, costValue t ∂(P.map f hf).lawKernel K x) = ∫ t, costValue t ∂P.lawKernel K x := by
  rw [P.map_law, Kernel.map_apply (f := fun z : Y × ℕ => (f z.1, z.2)) _
    ((hf.comp measurable_fst).prodMk measurable_snd)]
  constructor
  · exact (integrable_map_measure (g := costValue) costValue_measurable.aestronglyMeasurable
      ((hf.comp measurable_fst).prodMk measurable_snd).aemeasurable).mpr hi
  · rw [integral_map (φ := fun z : Y × ℕ => (f z.1, z.2))
      ((hf.comp measurable_fst).prodMk measurable_snd).aemeasurable costValue_measurable.aestronglyMeasurable]
    rfl

end OracleProgram
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem recursiveStageProgram_cost (O : FreshOracle S.toNCObjective σ) (δ : ℝ) (N : ℕ) (E : ℝ) (j : ℕ)
    (z : Euclid dy × Joint dx dy) :
    Integrable costValue ((recursiveStageProgram dx dy ℓ α σ μ δ N E j).lawKernel O.kernel z) ∧
    (∫ t, costValue t ∂(recursiveStageProgram dx dy ℓ α σ μ δ N E j).lawKernel O.kernel z) =
      recursiveStageWork ℓ α σ μ δ N E j := by
  have h := S.parameterValueSolverProgram_cost O (μ + recursiveCurvature μ j) (5 * ℓ + recursiveCurvature μ j)
    (recursiveAccuracy μ δ N j) (recursiveInputEnvelope μ δ N E j)
    (dualQuadraticCorrection (recursiveCurvature μ j)) (dualQuadraticCorrection_continuous _).measurable z
  rw [OracleProgram.originalKernel_eq_law] at h
  exact h

theorem recursiveRestartProgram_cost (O : FreshOracle S.toNCObjective σ) (δ : ℝ) (N : ℕ) (E : ℝ) (j : ℕ)
    (z : Euclid dy × Joint dx dy) :
    Integrable costValue ((recursiveRestartProgram dx dy ℓ α σ μ δ N E j).lawKernel O.kernel z) ∧
    (∫ t, costValue t ∂(recursiveRestartProgram dx dy ℓ α σ μ δ N E j).lawKernel O.kernel z) =
      recursiveStageWork ℓ α σ μ δ N E j := by
  obtain ⟨hi, he⟩ := S.recursiveStageProgram_cost O δ N E j z
  have h := (recursiveStageProgram dx dy ℓ α σ μ δ N E j).map_cost (quadraticAdvance (recursiveMass μ j))
    (quadraticAdvance_continuous (recursiveMass μ j)).measurable O.kernel z hi
  exact ⟨h.1, h.2.trans he⟩

theorem recursiveRunProgram_cost (O : FreshOracle S.toNCObjective σ) (δ : ℝ) (N : ℕ) (E : ℝ) (n : ℕ)
    (z : Euclid dy × Joint dx dy) :
    Integrable costValue ((recursiveRunProgram dx dy ℓ α σ μ δ N E n).lawKernel O.kernel z) ∧
    (∫ t, costValue t ∂(recursiveRunProgram dx dy ℓ α σ μ δ N E n).lawKernel O.kernel z) =
      ∑ j ∈ Finset.range n, recursiveStageWork ℓ α σ μ δ N E j := by
  induction n with
  | zero =>
    rw [recursiveRunProgram, OracleProgram.pure_law]
    exact ⟨taggedKernel_cost_integrable _ _ _, by
      simpa only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero] using
        taggedKernel_mean_cost (Kernel.deterministic id measurable_id) 0 z⟩
  | succ n ih =>
    rw [recursiveRunProgram, OracleProgram.chain_law]
    have h := costedCompose_cost _ _ z ih.1
      (fun y => (S.recursiveRestartProgram_cost O δ N E n y).1) _
      (fun y => (S.recursiveRestartProgram_cost O δ N E n y).2)
    simpa only [ih.2, Finset.sum_range_succ] using h

theorem recursiveSolverProgram_cost (O : FreshOracle S.toNCObjective σ) (δ : ℝ) (N : ℕ) (E : ℝ)
    (z : Euclid dy × Joint dx dy) :
    Integrable costValue ((recursiveSolverProgram dx dy ℓ α σ μ δ N E).lawKernel O.kernel z) ∧
    (∫ t, costValue t ∂(recursiveSolverProgram dx dy ℓ α σ μ δ N E).lawKernel O.kernel z) =
      ∑ j ∈ Finset.range (N + 1), recursiveStageWork ℓ α σ μ δ N E j := by
  rw [recursiveSolverProgram, OracleProgram.chain_law]
  have hr := S.recursiveRunProgram_cost O δ N E N z
  have h := costedCompose_cost _ _ z hr.1 (fun y => (S.recursiveStageProgram_cost O δ N E N y).1) _
    (fun y => (S.recursiveStageProgram_cost O δ N E N y).2)
  simpa only [hr.2, Finset.sum_range_succ] using h

theorem recursiveSolverProgram_mean_calls (O : FreshOracle S.toNCObjective σ) (δ : ℝ) (N : ℕ) (E : ℝ)
    (ν : Measure (Euclid dy × Joint dx dy)) [IsProbabilityMeasure ν] :
    Integrable costValue ((recursiveSolverProgram dx dy ℓ α σ μ δ N E).originalKernel O.kernel ∘ₘ ν) ∧
    (∫ t, costValue t ∂(recursiveSolverProgram dx dy ℓ α σ μ δ N E).originalKernel O.kernel ∘ₘ ν) =
      ∑ j ∈ Finset.range (N + 1), recursiveStageWork ℓ α σ μ δ N E j := by
  rw [OracleProgram.originalKernel_eq_law]
  have h (z : Euclid dy × Joint dx dy) := S.recursiveSolverProgram_cost O δ N E z
  have hi := (kernel_moment_from_envelope _ ν costValue costValue_measurable.stronglyMeasurable
    (fun t => Nat.cast_nonneg t.2) _ (integrable_const _) (fun z => (h z).1) (fun z => (h z).2.le)).1
  refine ⟨hi, ?_⟩
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi, Kernel.const_apply]
  simp_rw [(h _).2]
  simp only [integral_const, measureReal_univ_eq_one, one_smul]

theorem recursive_warm_envelope_ratio {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (N j : ℕ) (E : ℝ) :
    recursiveInputEnvelope μ δ N E (j + 1) / recursiveAccuracy μ δ N (j + 1) = 138 := by
  rw [recursiveInputEnvelope, recursiveAccuracy_halving]
  have hp := (recursiveAccuracy_pos hμ hδ N j).ne'
  field_simp
  ring

end SCObjective
end FreshGradientMinimax
