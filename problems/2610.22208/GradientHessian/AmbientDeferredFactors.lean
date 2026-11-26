import GradientHessian.AmbientOrthonormalExecution

/-! Deferred factors reconstructed from the original ambient transcript.
Visible blocks are exact transcript functions; only the column gauge uses
the unobserved Gaussian revelation record. Query columns are chronological. -/

noncomputable section
namespace GradientHessian.AmbientOrthonormal
open Classical Matrix MeasureTheory ProbabilityTheory LowRank DeferredGaussian

variable (r s n : ℕ) {Seed : Type*} [MeasurableSpace Seed]
variable (policy : AmbientOraclePolicy (r+n) n Seed)

def originalField : MeasurableSpace (Input r s n (Seed := Seed)) :=
  MeasurableSpace.comap (runAmbientGram r s n policy) inferInstance

def originalVisible (w : Input r s n (Seed := Seed)) : VisibleFactorData (r+n) (factorCount n 0) r :=
  replayVisibleFactors (r+n) r n 0 (compile (r+n) r n 0 policy)
    (fun _ => visibleFactorData (initialFactorData (r+n) (s+n))) (runAmbientGram r s n policy w)

def sourceFactors (w : Input r s n (Seed := Seed)) : FactorData (r+n) (s+n) (factorCount n 0) r s :=
  chronological ((originalVisible r s n policy w).1,((originalVisible r s n policy w).2,
    (gramOracleFactors r s n (compile (r+n) r n 0 policy) w).2.2))

def sourceEnlargement (w : Input r s n (Seed := Seed)) :=
  (runAmbientGram r s n policy w,revealed r s n (compile (r+n) r n 0 policy) w)

def sourceField : MeasurableSpace (Input r s n (Seed := Seed)) :=
  MeasurableSpace.comap (sourceEnlargement r s n policy) inferInstance

theorem originalVisible_measurable :
    Measurable[originalField r s n policy] (originalVisible r s n policy) :=
  (measurable_replayVisibleFactors (r+n) r n 0 (compile (r+n) r n 0 policy) _ measurable_const).comp
    (comap_measurable (runAmbientGram r s n policy))

theorem originalField_le_sourceField : originalField r s n policy≤sourceField r s n policy :=
  (measurable_fst.comp (comap_measurable (sourceEnlargement r s n policy))).comap_le

theorem source_visible_measurable :
    Measurable[originalField r s n policy] (fun w => visibleFactorData (sourceFactors r s n policy w)) := by
  letI : MeasurableSpace (Input r s n (Seed := Seed)) := originalField r s n policy
  have h := originalVisible_measurable r s n policy
  exact ((measurable_submatrix _ h.fst.fst _ _).prodMk
    (measurable_submatrix _ h.fst.snd _ _)).prodMk (measurable_submatrix _ h.snd _ _)

theorem source_column_measurable :
    Measurable[sourceField r s n policy] (fun w => (sourceFactors r s n policy w).2.2) := by
  letI : MeasurableSpace (Input r s n (Seed := Seed)) := sourceField r s n policy
  have hr : Measurable (revealed r s n (compile (r+n) r n 0 policy)) :=
    measurable_snd.comp (comap_measurable (sourceEnlargement r s n policy))
  have hc := (measurable_finalFactorData (r+n) (s+n) r s n 0
    (compileGramOracle r s n (compile (r+n) r n 0 policy))
      (fun _ => initialFactorData (r+n) (s+n)) measurable_const).snd.snd.comp hr
  exact measurable_submatrix _ hc _ _

variable (ν : Measure Seed) [IsProbabilityMeasure ν]

include ν in
theorem sourceEnlargement_measurable (v : NNReal) : Measurable (sourceEnlargement r s n policy) :=
  (measurable_runAmbientGram r s n policy).prodMk
    (runGaussianPolicy_preserving r s n ν (compileGramOracle r s n (compile (r+n) r n 0 policy)) v).measurable.fst

include ν in
theorem sourceField_le (v : NNReal) : sourceField r s n policy≤
    (inferInstance : MeasurableSpace (Input r s n (Seed := Seed))) :=
  (sourceEnlargement_measurable r s n policy ν v).comap_le

variable {v : NNReal} (hv : v≠0)
variable (hqueries : ∀ᵐ w ∂ν.prod (iidMatrixLaw (r+n) (s+n) v),
  OrthonormalAfter [] (queryLog (r+n) n policy (w.2*w.2ᵀ) w.1))

include hv hqueries in
theorem originalVisible_eq_ae :
    originalVisible r s n policy =ᵐ[ν.prod (iidMatrixLaw (r+n) (s+n) v)]
      fun w => (runGramOracle r s n (compile (r+n) r n 0 policy) w).2 := by
  filter_upwards [compile_simulates_ae r s n policy ν hv hqueries] with w hw
  unfold originalVisible
  rw [← hw.1]
  exact (runVisibleOracle_replay (r+n) r n 0 (compile (r+n) r n 0 policy)
    (fun _ => visibleFactorData (initialFactorData (r+n) (s+n))) (w.2*w.2ᵀ) w.1).symm

include hv hqueries in
theorem sourceFactors_eq_ae :
    sourceFactors r s n policy =ᵐ[ν.prod (iidMatrixLaw (r+n) (s+n) v)]
      fun w => chronological (factors r s n (compile (r+n) r n 0 policy) w) := by
  filter_upwards [originalVisible_eq_ae r s n policy ν hv hqueries] with w hw
  unfold sourceFactors
  rw [hw]
  rfl

include hv hqueries in
theorem source_factorization_ae :
    ∀ᵐ w ∂ν.prod (iidMatrixLaw (r+n) (s+n) v),
      let st := sourceFactors r s n policy w
      st.Orthogonal ∧ IsUnit st.1.1 ∧ st.2.1ᵀ*w.2*st.2.2=
        fromBlocks st.1.1 0 st.1.2 (gramOracleResidual r s n (compile (r+n) r n 0 policy) w) := by
  filter_upwards [sourceFactors_eq_ae r s n policy ν hv hqueries,
    chronological_factorization_ae r s n (compile (r+n) r n 0 policy) ν
      (compile_unit (r+n) r n 0 policy) hv] with w heq hf
  rw [heq]
  exact hf

include hv hqueries in
theorem source_query_columns_ae :
    ∀ᵐ w ∂ν.prod (iidMatrixLaw (r+n) (s+n) v),
      queryColumns (visibleFactorData (sourceFactors r s n policy w))=
        queryLog (r+n) n policy (w.2*w.2ᵀ) w.1 := by
  filter_upwards [sourceFactors_eq_ae r s n policy ν hv hqueries,
    compile_simulates_ae r s n policy ν hv hqueries] with w heq hs
  rw [heq,chronological_leading_queries r s n _ (compile_unit (r+n) r n 0 policy)]
  exact hs.2

include hv hqueries in
theorem source_residual_independent :
    IndepFun (sourceEnlargement r s n policy) (gramOracleResidual r s n (compile (r+n) r n 0 policy))
      (ν.prod (iidMatrixLaw (r+n) (s+n) v)) := by
  apply (residual_independent_enlargement r s n (compile (r+n) r n 0 policy) ν
    (compile_unit (r+n) r n 0 policy) hv).congr
  · filter_upwards [compile_simulates_ae r s n policy ν hv hqueries] with w hw
    exact Prod.ext hw.1 rfl
  · exact Filter.Eventually.of_forall (fun _ => rfl)

end GradientHessian.AmbientOrthonormal
