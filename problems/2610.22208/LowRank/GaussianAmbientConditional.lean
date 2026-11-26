import LowRank.GaussianAmbientTranscript
import Mathlib.Probability.ConditionalExpectation

/-! Conditional Gaussian residual law for the actual original record of an
arbitrary measurable fixed-horizon policy, including redundant queries. -/

namespace LowRank
open MeasureTheory ProbabilityTheory
noncomputable section

theorem ambientOracle_conditional_test (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : AmbientOraclePolicy (r + n) n S)
    {v : NNReal} (hv : v ≠ 0) (φ : Matrix (Fin r) (Fin s) ℝ → ℝ) (hφ : Measurable φ)
    (hφint : Integrable φ (iidMatrixLaw r s v)) :
    let μ := ν.prod (iidMatrixLaw (r + n) (s + n) v)
    let T := runAmbientGram r s n policy
    let R := ambientOracleResidual r s n policy
    Integrable (φ ∘ R) μ ∧
      μ[φ ∘ R | MeasurableSpace.comap T inferInstance] =ᵐ[μ]
        (fun _ => ∫ D, φ D ∂iidMatrixLaw r s v) := by
  let μ := ν.prod (iidMatrixLaw (r + n) (s + n) v)
  let T := runAmbientGram r s n policy
  let R := ambientOracleResidual r s n policy
  change Integrable (φ ∘ R) μ ∧ _
  have hT : Measurable T := measurable_runAmbientGram r s n policy
  have hR : Measurable R :=
    (runGaussianPolicy_preserving r s n ν
      (compileGramOracle r s n (normalizedAmbientPolicy r s n policy)) v).measurable.snd
  have hRlaw : MeasurePreserving R μ (iidMatrixLaw r s v) :=
    ⟨hR, ambientOracle_residual_law r s n ν policy v⟩
  refine ⟨(hRlaw.integrable_comp hφ.stronglyMeasurable.aestronglyMeasurable).mpr hφint, ?_⟩
  have hind : IndepFun R T μ := (ambientOracle_transcript_residual_independent r s n ν policy hv).symm
  have hsm : StronglyMeasurable[(inferInstance : MeasurableSpace (Matrix (Fin r) (Fin s) ℝ)).comap R]
      (φ ∘ R) := (hφ.comp (comap_measurable R)).stronglyMeasurable
  have hcond := condExp_indep_eq hR.comap_le hT.comap_le hsm ((IndepFun_iff_Indep R T μ).mp hind)
  have hint : (∫ p, φ (R p) ∂μ) = ∫ D, φ D ∂iidMatrixLaw r s v := by
    rw [← hRlaw.map_eq, integral_map_of_stronglyMeasurable hR hφ.stronglyMeasurable]
  simpa only [Function.comp_def, hint] using hcond

theorem ambientOracle_conditional_bounded (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : AmbientOraclePolicy (r + n) n S)
    {v : NNReal} (hv : v ≠ 0) (φ : Matrix (Fin r) (Fin s) ℝ → ℝ) (hφ : Measurable φ)
    (C : ℝ) (hbound : ∀ D, ‖φ D‖ ≤ C) :
    let μ := ν.prod (iidMatrixLaw (r + n) (s + n) v)
    let T := runAmbientGram r s n policy
    μ[φ ∘ ambientOracleResidual r s n policy | MeasurableSpace.comap T inferInstance] =ᵐ[μ]
      (fun _ => ∫ D, φ D ∂iidMatrixLaw r s v) := by
  have hφint : Integrable φ (iidMatrixLaw r s v) :=
    (integrable_const C).mono' hφ.stronglyMeasurable.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  exact (ambientOracle_conditional_test r s n ν policy hv φ hφ hφint).2

end
end LowRank
