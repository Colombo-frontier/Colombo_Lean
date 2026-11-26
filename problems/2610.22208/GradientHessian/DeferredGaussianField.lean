import LowRank.GaussianOracleConditional
import LowRank.GaussianRevealConditional

/-! An explicit enlarged sigma-field contains the actual seed/reply
transcript. The latent Gaussian residual is independent of that field. -/

noncomputable section
namespace GradientHessian.DeferredGaussian
open Classical Matrix MeasureTheory ProbabilityTheory LowRank

variable (r s n : ℕ) {Seed : Type*} [MeasurableSpace Seed]
variable (policy : VisibleOraclePolicy (r+n) r n 0 Seed)

abbrev Input := Seed × Matrix (Fin (r+n)) (Fin (s+n)) ℝ

def transcript (w : Input r s n (Seed := Seed)) : OracleHistory (r+n) n Seed :=
  (runGramOracle r s n policy w).1

def revealed (w : Input r s n (Seed := Seed)) : GaussianHistory r s n Seed :=
  (runGaussianPolicy r s n (compileGramOracle r s n policy) w).1

def enlargement (w : Input r s n (Seed := Seed)) :=
  (transcript r s n policy w,revealed r s n policy w)

def transcriptField : MeasurableSpace (Input r s n (Seed := Seed)) :=
  MeasurableSpace.comap (transcript r s n policy) inferInstance

def enlargedField : MeasurableSpace (Input r s n (Seed := Seed)) :=
  MeasurableSpace.comap (enlargement r s n policy) inferInstance

theorem transcript_measurable_enlarged :
    Measurable[enlargedField r s n policy] (transcript r s n policy) := by
  change Measurable[enlargedField r s n policy] (Prod.fst ∘ enlargement r s n policy)
  exact measurable_fst.comp (comap_measurable (enlargement r s n policy))

theorem transcriptField_le_enlarged : transcriptField r s n policy≤enlargedField r s n policy :=
  (transcript_measurable_enlarged r s n policy).comap_le

theorem revealed_measurable_enlarged :
    Measurable[enlargedField r s n policy] (revealed r s n policy) :=
  measurable_snd.comp (comap_measurable (enlargement r s n policy))

theorem visible_measurable_transcript :
    Measurable[transcriptField r s n policy] (fun w => (runGramOracle r s n policy w).2) :=
  gramOracle_visible_measurable_transcript r s n policy

variable (ν : Measure Seed) [IsProbabilityMeasure ν]

include ν in
theorem enlargement_measurable (v : NNReal) : Measurable (enlargement r s n policy) :=
  (measurable_runGramOracle r s n policy).fst.prodMk
    (runGaussianPolicy_preserving r s n ν (compileGramOracle r s n policy) v).measurable.fst

include ν in
theorem enlargedField_le (v : NNReal) : enlargedField r s n policy ≤
    (inferInstance : MeasurableSpace (Input r s n (Seed := Seed))) :=
  (enlargement_measurable r s n policy ν v).comap_le

theorem residual_independent_enlargement
    (hunit : VisibleOraclePolicy.IsUnit (r+n) r n 0 policy) {v : NNReal} (hv : v≠0) :
    IndepFun (enlargement r s n policy) (gramOracleResidual r s n policy)
      (ν.prod (iidMatrixLaw (r+n) (s+n) v)) := by
  let read := readOracleHistory (r+n) (s+n) r s n 0 policy
    (initialFactorState _ _) (identityMemory Seed)
  have hread : Measurable read := measurable_readOracleHistory _ _ _ _ _ _ policy _ _
  have hind := (runGaussianPolicy_independent r s n ν (compileGramOracle r s n policy) v).comp
    (hread.prodMk measurable_id) measurable_id
  apply hind.congr
  · filter_upwards [gramOracle_simulation_ae r s n ν policy hunit hv] with w hw
    exact Prod.ext (congrArg Prod.fst hw).symm rfl
  · exact Filter.Eventually.of_forall (fun _ => rfl)

theorem residual_conditional_test
    (hunit : VisibleOraclePolicy.IsUnit (r+n) r n 0 policy) {v : NNReal} (hv : v≠0)
    (φ : Matrix (Fin r) (Fin s) ℝ → ℝ) (hφ : Measurable φ)
    (hint : Integrable φ (iidMatrixLaw r s v)) :
    let μ := ν.prod (iidMatrixLaw (r+n) (s+n) v)
    Integrable (φ ∘ gramOracleResidual r s n policy) μ ∧
      μ[φ ∘ gramOracleResidual r s n policy | enlargedField r s n policy] =ᵐ[μ]
        (fun _ => ∫ D, φ D ∂iidMatrixLaw r s v) := by
  let μ := ν.prod (iidMatrixLaw (r+n) (s+n) v)
  let R := gramOracleResidual r s n policy
  have hR : Measurable R :=
    (runGaussianPolicy_preserving r s n ν (compileGramOracle r s n policy) v).measurable.snd
  have hlaw : MeasurePreserving R μ (iidMatrixLaw r s v) :=
    ⟨hR,gramOracle_residual_law r s n ν policy v⟩
  refine ⟨(hlaw.integrable_comp hφ.stronglyMeasurable.aestronglyMeasurable).mpr hint,?_⟩
  have hind := (residual_independent_enlargement r s n policy ν hunit hv).symm
  have hsm : StronglyMeasurable[(inferInstance : MeasurableSpace (Matrix (Fin r) (Fin s) ℝ)).comap R]
      (φ ∘ R) := (hφ.comp (comap_measurable R)).stronglyMeasurable
  have hc := condExp_indep_eq hR.comap_le (enlargedField_le r s n policy ν v) hsm
    ((IndepFun_iff_Indep R (enlargement r s n policy) μ).mp hind)
  have hi : (∫ w, φ (R w) ∂μ)=∫ D, φ D ∂iidMatrixLaw r s v := by
    rw [← hlaw.map_eq,integral_map_of_stronglyMeasurable hR hφ.stronglyMeasurable]
  simpa only [Function.comp_def,hi] using hc

theorem residual_conditional_bounded
    (hunit : VisibleOraclePolicy.IsUnit (r+n) r n 0 policy) {v : NNReal} (hv : v≠0)
    (φ : Matrix (Fin r) (Fin s) ℝ → ℝ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ D,‖φ D‖≤C) :
    let μ := ν.prod (iidMatrixLaw (r+n) (s+n) v)
    μ[φ ∘ gramOracleResidual r s n policy | enlargedField r s n policy] =ᵐ[μ]
      (fun _ => ∫ D, φ D ∂iidMatrixLaw r s v) := by
  apply (residual_conditional_test r s n policy ν hunit hv φ hφ _).2
  exact (integrable_const C).mono' hφ.stronglyMeasurable.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

end GradientHessian.DeferredGaussian
