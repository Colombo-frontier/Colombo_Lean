import GradientHessian.AmbientDeferredFactors
import GradientHessian.DeferredGaussianSource

/-! Full source deferred-factorization statement for actual adaptive
orthonormal ambient policies and their original seed/reply transcripts. -/

noncomputable section
namespace GradientHessian.AmbientOrthonormal
open Classical Matrix MeasureTheory ProbabilityTheory LowRank DeferredGaussian

variable (r s n : ℕ) {Seed : Type*} [MeasurableSpace Seed]
variable (policy : AmbientOraclePolicy (r+n) n Seed)
variable (ν : Measure Seed) [IsProbabilityMeasure ν] {v : NNReal} (hv : v≠0)
variable (hqueries : ∀ᵐ w ∂ν.prod (iidMatrixLaw (r+n) (s+n) v),
  OrthonormalAfter [] (queryLog (r+n) n policy (w.2*w.2ᵀ) w.1))

include hv hqueries in
theorem source_conditional_test (φ : Matrix (Fin r) (Fin s) ℝ → ℝ) (hφ : Measurable φ)
    (hint : Integrable φ (iidMatrixLaw r s v)) :
    let μ := ν.prod (iidMatrixLaw (r+n) (s+n) v)
    let G := gramOracleResidual r s n (compile (r+n) r n 0 policy)
    Integrable (φ ∘ G) μ ∧ μ[φ ∘ G | sourceField r s n policy] =ᵐ[μ]
      (fun _ => ∫ D,φ D ∂iidMatrixLaw r s v) := by
  let μ := ν.prod (iidMatrixLaw (r+n) (s+n) v)
  let G := gramOracleResidual r s n (compile (r+n) r n 0 policy)
  have hG : Measurable G := (runGaussianPolicy_preserving r s n ν
    (compileGramOracle r s n (compile (r+n) r n 0 policy)) v).measurable.snd
  have hlaw : MeasurePreserving G μ (iidMatrixLaw r s v) :=
    ⟨hG,gramOracle_residual_law r s n ν (compile (r+n) r n 0 policy) v⟩
  refine ⟨(hlaw.integrable_comp hφ.stronglyMeasurable.aestronglyMeasurable).mpr hint,?_⟩
  have hind := (source_residual_independent r s n policy ν hv hqueries).symm
  have hsm : StronglyMeasurable[(inferInstance : MeasurableSpace (Matrix (Fin r) (Fin s) ℝ)).comap G]
      (φ ∘ G) := (hφ.comp (comap_measurable G)).stronglyMeasurable
  have hc := condExp_indep_eq hG.comap_le (sourceField_le r s n policy ν v) hsm
    ((IndepFun_iff_Indep G (sourceEnlargement r s n policy) μ).mp hind)
  have hi : (∫ w,φ (G w) ∂μ)=∫ D,φ D ∂iidMatrixLaw r s v := by
    rw [← hlaw.map_eq,integral_map_of_stronglyMeasurable hG hφ.stronglyMeasurable]
  simpa only [Function.comp_def,hi] using hc

include hv hqueries in
theorem source_conditional_bounded (φ : Matrix (Fin r) (Fin s) ℝ → ℝ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ D,‖φ D‖≤C) :
    let μ := ν.prod (iidMatrixLaw (r+n) (s+n) v)
    let G := gramOracleResidual r s n (compile (r+n) r n 0 policy)
    μ[φ ∘ G | sourceField r s n policy] =ᵐ[μ] (fun _ => ∫ D,φ D ∂iidMatrixLaw r s v) := by
  apply (source_conditional_test r s n policy ν hv hqueries φ hφ _).2
  exact (integrable_const C).mono' hφ.stronglyMeasurable.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

include hv hqueries in
theorem ambient_deferred_factorization :
    let μ := ν.prod (iidMatrixLaw (r+n) (s+n) v)
    let st := sourceFactors r s n policy
    let G := gramOracleResidual r s n (compile (r+n) r n 0 policy)
    originalField r s n policy≤sourceField r s n policy ∧
    Measurable[originalField r s n policy] (fun w => (st w).1) ∧
    Measurable[originalField r s n policy] (fun w => (st w).2.1) ∧
    Measurable[sourceField r s n policy] (fun w => (st w).2.2) ∧
    (∀ᵐ w ∂μ,(st w).Orthogonal ∧ IsUnit (st w).1.1 ∧
      (st w).2.1ᵀ*w.2*(st w).2.2=fromBlocks (st w).1.1 0 (st w).1.2 (G w)) ∧
    (∀ᵐ w ∂μ,queryColumns (visibleFactorData (st w))=queryLog (r+n) n policy (w.2*w.2ᵀ) w.1) ∧
    μ.map G=iidMatrixLaw r s v ∧ IndepFun (sourceEnlargement r s n policy) G μ ∧
    (∀ (φ : Matrix (Fin r) (Fin s) ℝ → ℝ),Measurable φ → ∀ C : ℝ,(∀ D,‖φ D‖≤C) →
      μ[φ ∘ G | sourceField r s n policy] =ᵐ[μ] (fun _ => ∫ D,φ D ∂iidMatrixLaw r s v)) := by
  exact ⟨originalField_le_sourceField r s n policy,(source_visible_measurable r s n policy).fst,
    (source_visible_measurable r s n policy).snd,source_column_measurable r s n policy,
    source_factorization_ae r s n policy ν hv hqueries,source_query_columns_ae r s n policy ν hv hqueries,
    gramOracle_residual_law r s n ν (compile (r+n) r n 0 policy) v,
    source_residual_independent r s n policy ν hv hqueries,
    fun φ hφ C hC => source_conditional_bounded r s n policy ν hv hqueries φ hφ C hC⟩

end GradientHessian.AmbientOrthonormal
