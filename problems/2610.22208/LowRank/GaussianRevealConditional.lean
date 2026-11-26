import LowRank.GaussianRevealProcess
import Mathlib.Probability.ConditionalExpectation

/-! Conditional expectation for the full enlarged history of the explicit
adaptive Gaussian revelation process. Integrability is proved alongside the
conditional identity for each integrable measurable test function. -/

namespace LowRank
open MeasureTheory ProbabilityTheory
noncomputable section

theorem runGaussianPolicy_conditional_test (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : GaussianPolicy r s n S) (v : NNReal)
    (φ : Matrix (Fin r) (Fin s) ℝ → ℝ) (hφ : Measurable φ)
    (hφint : Integrable φ (iidMatrixLaw r s v)) :
    let μ := ν.prod (iidMatrixLaw (r + n) (s + n) v)
    let T := fun p => (runGaussianPolicy r s n policy p).1
    let R := fun p => (runGaussianPolicy r s n policy p).2
    Integrable (φ ∘ R) μ ∧
      μ[φ ∘ R | MeasurableSpace.comap T inferInstance] =ᵐ[μ]
        (fun _ => ∫ D, φ D ∂iidMatrixLaw r s v) := by
  let μ := ν.prod (iidMatrixLaw (r + n) (s + n) v)
  let T := fun p => (runGaussianPolicy r s n policy p).1
  let R := fun p => (runGaussianPolicy r s n policy p).2
  change Integrable (φ ∘ R) μ ∧ _
  have h := runGaussianPolicy_preserving r s n ν policy v
  have hT : Measurable T := h.measurable.fst
  have hR : Measurable R := h.measurable.snd
  have hRlaw : MeasurePreserving R μ (iidMatrixLaw r s v) :=
    ⟨hR, runGaussianPolicy_residual_law r s n ν policy v⟩
  refine ⟨(hRlaw.integrable_comp hφ.stronglyMeasurable.aestronglyMeasurable).mpr hφint, ?_⟩
  have hind := (runGaussianPolicy_independent r s n ν policy v).symm
  have hsm : StronglyMeasurable[(inferInstance : MeasurableSpace (Matrix (Fin r) (Fin s) ℝ)).comap R]
      (φ ∘ R) := (hφ.comp (comap_measurable R)).stronglyMeasurable
  have hcond := condExp_indep_eq hR.comap_le hT.comap_le hsm
    ((IndepFun_iff_Indep R T μ).mp hind)
  have hint : (∫ p, φ (R p) ∂μ) = ∫ D, φ D ∂iidMatrixLaw r s v := by
    rw [← hRlaw.map_eq, integral_map_of_stronglyMeasurable hR hφ.stronglyMeasurable]
  simpa only [Function.comp_def, hint] using hcond

end
end LowRank
