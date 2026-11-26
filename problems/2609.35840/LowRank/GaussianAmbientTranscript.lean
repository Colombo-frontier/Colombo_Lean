import LowRank.AmbientProcessSimulation
import LowRank.GaussianOracleTranscript

/-! Arbitrary measurable fixed-horizon Gram policies are simulated by unit
direction policies. Their original records are measurable decodings of the
enhanced records, and hence are independent of the residual Gaussian block. -/

namespace LowRank
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix
noncomputable section

def initialVisibleState {S : Type*} [MeasurableSpace S] (d t : ℕ) :
    MeasurableStateMap S (VisibleFactorData d 0 d) :=
  ⟨fun _ => visibleFactorData (initialFactorData d t), measurable_const⟩

def normalizedAmbientPolicy (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : AmbientOraclePolicy (r + n) n S) : VisibleOraclePolicy (r + n) r n 0 S :=
  reduceAmbientOracle (r + n) r n 0 policy (identityMemory S)
    (initialVisibleState (r + n) (s + n))

def decodeAmbientHistory (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : AmbientOraclePolicy (r + n) n S) :
    OracleHistory (r + n) n S → OracleHistory (r + n) n S :=
  readReducedHistory (r + n) r n 0 policy (identityMemory S)
    (initialVisibleState (r + n) (s + n))

def runAmbientGram (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : AmbientOraclePolicy (r + n) n S)
    (p : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ) : OracleHistory (r + n) n S :=
  runAmbientOracle (r + n) n policy (p.2 * p.2ᵀ) p.1

def ambientOracleResidual (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : AmbientOraclePolicy (r + n) n S) :=
  gramOracleResidual r s n (normalizedAmbientPolicy r s n policy)

def ambientOracleFactors (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : AmbientOraclePolicy (r + n) n S) :=
  gramOracleFactors r s n (normalizedAmbientPolicy r s n policy)

theorem normalizedAmbientPolicy_unit (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : AmbientOraclePolicy (r + n) n S) :
    VisibleOraclePolicy.IsUnit (r + n) r n 0 (normalizedAmbientPolicy r s n policy) :=
  reduceAmbientOracle_unit _ _ _ _ policy _ _

theorem measurable_decodeAmbientHistory (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : AmbientOraclePolicy (r + n) n S) : Measurable (decodeAmbientHistory r s n policy) :=
  measurable_readReducedHistory _ _ _ _ policy _ _

theorem measurable_runAmbientGram (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : AmbientOraclePolicy (r + n) n S) : Measurable (runAmbientGram r s n policy) := by
  have hw : Measurable (fun p : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ => p.2 * p.2ᵀ) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop
  exact (measurable_runAmbientOracle (r + n) n policy).comp (hw.prodMk measurable_fst)

theorem ambientOracle_history_recovery_ae (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν] (policy : AmbientOraclePolicy (r + n) n S)
    {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      runAmbientGram r s n policy p = decodeAmbientHistory r s n policy
        (runGramOracle r s n (normalizedAmbientPolicy r s n policy) p).1 := by
  let vp := normalizedAmbientPolicy r s n policy
  filter_upwards [gaussianPolicy_regular_ae r s n ν (compileGramOracle r s n vp) hv,
    gramOracle_simulation_ae r s n ν vp (normalizedAmbientPolicy_unit r s n policy) hv]
    with p hreg hs
  have h := reduceAmbientOracle_gaussian_simulates (r + n) (s + n) r s n 0 policy
    (identityMemory S) (initialVisibleState (r + n) (s + n))
    (initialFactorState (r + n) (s + n)) (identityMemory S) p rfl
    (initialFactorData_orthogonal _ _) hreg
  have hread : runAmbientGram r s n policy p = decodeAmbientHistory r s n policy
      (readOracleHistory (r + n) (s + n) r s n 0 vp (initialFactorState _ _) (identityMemory S)
        (runGaussianPolicy r s n (compileGramOracle r s n vp) p).1) := by
    simpa only [initialFactorState, identityMemory, initialFactorData_represents, id_eq] using h
  exact hread.trans (congrArg (decodeAmbientHistory r s n policy) (congrArg Prod.fst hs).symm)

theorem ambientOracle_residual_law (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : AmbientOraclePolicy (r + n) n S)
    (v : NNReal) :
    (ν.prod (iidMatrixLaw (r + n) (s + n) v)).map (ambientOracleResidual r s n policy) =
      iidMatrixLaw r s v :=
  gramOracle_residual_law r s n ν (normalizedAmbientPolicy r s n policy) v

theorem ambientOracle_transcript_residual_independent (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : AmbientOraclePolicy (r + n) n S)
    {v : NNReal} (hv : v ≠ 0) :
    IndepFun (runAmbientGram r s n policy) (ambientOracleResidual r s n policy)
      (ν.prod (iidMatrixLaw (r + n) (s + n) v)) := by
  have hind := (gramOracle_transcript_residual_independent r s n ν
    (normalizedAmbientPolicy r s n policy) (normalizedAmbientPolicy_unit r s n policy) hv).comp
    ((measurable_decodeAmbientHistory r s n policy).comp measurable_fst) measurable_id
  apply hind.congr
  · filter_upwards [ambientOracle_history_recovery_ae r s n ν policy hv] with p hp
    exact hp.symm
  · exact Filter.Eventually.of_forall (fun _ => rfl)

/-- These visible factors belong to the enhanced normalized record. The
theorem does not assert that they are measurable in the original record. -/
theorem ambientOracle_factorization_ae (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν] (policy : AmbientOraclePolicy (r + n) n S)
    {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      representedMatrix (ambientOracleFactors r s n policy p) (ambientOracleResidual r s n policy p) = p.2 ∧
      (ambientOracleFactors r s n policy p).Orthogonal ∧ IsUnit (ambientOracleFactors r s n policy p).1.1 ∧
      visibleFactorData (ambientOracleFactors r s n policy p) =
        (runGramOracle r s n (normalizedAmbientPolicy r s n policy) p).2 :=
  gramOracle_factorization_ae r s n ν (normalizedAmbientPolicy r s n policy)
    (normalizedAmbientPolicy_unit r s n policy) hv

theorem ambientOracle_output_recovery_ae (r s n : ℕ) {S O : Type*}
    [MeasurableSpace S] [MeasurableSpace O] (ν : Measure S) [SFinite ν]
    (policy : AmbientOraclePolicy (r + n) n S) {v : NNReal} (hv : v ≠ 0)
    (output : OracleHistory (r + n) n S → O) (hout : Measurable output) :
    Measurable (output ∘ decodeAmbientHistory r s n policy) ∧
      ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
        output (runAmbientGram r s n policy p) =
          (output ∘ decodeAmbientHistory r s n policy)
            (runGramOracle r s n (normalizedAmbientPolicy r s n policy) p).1 := by
  refine ⟨hout.comp (measurable_decodeAmbientHistory r s n policy), ?_⟩
  filter_upwards [ambientOracle_history_recovery_ae r s n ν policy hv] with p hp
  exact congrArg output hp

end
end LowRank
