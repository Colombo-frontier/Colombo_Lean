import FreshGradientMinimax.RecursiveProgram
import FreshGradientMinimax.RecursiveConversion

/-! Each stage of the actual recursive program satisfies its requested
unconditional value and fast-variable accuracy. This is not yet a proof
of the final saddle gap: applying F.4 to a common trajectory law and the
final residual certificate remain separate steps. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem dualQuadraticGap_measurable (hfast : ℓ / 4 ≤ α) (a : ℝ) (ha : 0 ≤ a) :
    Measurable (S.dualQuadraticGap hfast a ha) := by
  have hQ := ((S.effective_model hfast).quadraticFamily_joint_continuous a).measurable
  exact (hQ.comp (measurable_fst.prodMk measurable_snd.snd)).sub
    (hQ.comp (measurable_fst.prodMk ((S.dualQuadraticMin_continuous hfast a ha).measurable.comp measurable_fst)))

theorem recursiveStageProgram_accuracy (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) (E : ℝ) (j : ℕ)
    (ν : Measure (Euclid dy × Joint dx dy)) [IsProbabilityMeasure ν]
    (hi : Integrable (S.dualQuadraticEnergy hfast (recursiveCurvature μ j) (recursiveCurvature_nonneg S.μ_pos j)) ν)
    (hb : (∫ z, S.dualQuadraticEnergy hfast (recursiveCurvature μ j) (recursiveCurvature_nonneg S.μ_pos j) z ∂ν)
      ≤ recursiveInputEnvelope μ δ N E j) :
    Integrable (S.dualQuadraticGap hfast (recursiveCurvature μ j) (recursiveCurvature_nonneg S.μ_pos j))
      ((recursiveStageProgram dx dy ℓ α σ μ δ N E j).resultKernel O.kernel ∘ₘ ν) ∧
    Integrable (fun z : Euclid dy × Joint dx dy => S.fastError (recursiveMass μ j) z.2)
      ((recursiveStageProgram dx dy ℓ α σ μ δ N E j).resultKernel O.kernel ∘ₘ ν) ∧
    (∫ z, S.dualQuadraticGap hfast (recursiveCurvature μ j) (recursiveCurvature_nonneg S.μ_pos j) z
      ∂(recursiveStageProgram dx dy ℓ α σ μ δ N E j).resultKernel O.kernel ∘ₘ ν) ≤ recursiveAccuracy μ δ N j ∧
    (∫ z, S.fastError (recursiveMass μ j) z.2
      ∂(recursiveStageProgram dx dy ℓ α σ μ δ N E j).resultKernel O.kernel ∘ₘ ν) ≤ recursiveAccuracy μ δ N j := by
  obtain ⟨hg, hf, hgb, hfb⟩ := S.quadraticValueProgram_accuracy O hαℓ hfast (recursiveCurvature_nonneg S.μ_pos j)
    (recursiveAccuracy_pos S.μ_pos hδ N j) ν hi hb
  simp only [recursiveMass_add_curvature] at hf hfb
  have hgm := (S.dualQuadraticGap_measurable hfast (recursiveCurvature μ j) (recursiveCurvature_nonneg S.μ_pos j)).stronglyMeasurable
  have hfm : StronglyMeasurable (fun z : Euclid dy × Joint dx dy => S.fastError (recursiveMass μ j) z.2) :=
    ((S.fastError_continuous _).measurable.comp measurable_snd).stronglyMeasurable
  rw [← OracleProgram.original_result_law]
  refine ⟨(integrable_map_measure hgm.aestronglyMeasurable measurable_fst.aemeasurable).mpr hg,
    (integrable_map_measure hfm.aestronglyMeasurable measurable_fst.aemeasurable).mpr hf, ?_, ?_⟩
  · rw [integral_map measurable_fst.aemeasurable hgm.aestronglyMeasurable]
    exact hgb
  · rw [integral_map measurable_fst.aemeasurable hfm.aestronglyMeasurable]
    exact hfb

theorem recursiveSolverProgram_accuracy (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) (E : ℝ)
    (ν : Measure (Euclid dy × Joint dx dy)) [IsProbabilityMeasure ν]
    (hi : Integrable (S.dualQuadraticEnergy hfast 0 le_rfl) ν)
    (hb : (∫ z, S.dualQuadraticEnergy hfast 0 le_rfl z ∂ν) ≤ E) :
    Integrable (S.dualQuadraticGap hfast (recursiveCurvature μ N) (recursiveCurvature_nonneg S.μ_pos N))
      ((recursiveSolverProgram dx dy ℓ α σ μ δ N E).resultKernel O.kernel ∘ₘ ν) ∧
    Integrable (fun z : Euclid dy × Joint dx dy => S.fastError (recursiveMass μ N) z.2)
      ((recursiveSolverProgram dx dy ℓ α σ μ δ N E).resultKernel O.kernel ∘ₘ ν) ∧
    (∫ z, S.dualQuadraticGap hfast (recursiveCurvature μ N) (recursiveCurvature_nonneg S.μ_pos N) z
      ∂(recursiveSolverProgram dx dy ℓ α σ μ δ N E).resultKernel O.kernel ∘ₘ ν) ≤ recursiveAccuracy μ δ N N ∧
    (∫ z, S.fastError (recursiveMass μ N) z.2
      ∂(recursiveSolverProgram dx dy ℓ α σ μ δ N E).resultKernel O.kernel ∘ₘ ν) ≤ recursiveAccuracy μ δ N N := by
  obtain ⟨hri, hrb⟩ := S.recursiveRunProgram_energy O hαℓ hfast hδ N E ν hi hb N
  rw [recursiveSolverProgram, OracleProgram.chain_result, ← Measure.comp_assoc]
  exact S.recursiveStageProgram_accuracy O hαℓ hfast hδ N E N _ hri hrb

end SCObjective
end FreshGradientMinimax
