import LowRank.OracleProcessSimulation
import LowRank.OracleTranscriptReplay
import LowRank.FactorInitial

/-! Actual Gram-oracle transcripts for visible unit-direction policies on a
genuine Gaussian input. Their residual block has a fixed Gaussian law and is
independent of the actual transcript and recovered visible factors. -/

namespace LowRank
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix
noncomputable section

def initialFactorState {S : Type*} [MeasurableSpace S] (d t : ℕ) :
    MeasurableStateMap S (FactorData d t 0 d t) :=
  ⟨fun _ => initialFactorData d t, measurable_const⟩

def identityMemory (S : Type*) [MeasurableSpace S] : MeasurableStateMap S S :=
  ⟨id, measurable_id⟩

def compileGramOracle (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : VisibleOraclePolicy (r + n) r n 0 S) : GaussianPolicy r s n S :=
  compileVisibleOracle (r + n) (s + n) r s n 0 policy
    (initialFactorState _ _) (identityMemory S)

def runGramOracle (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (p : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ) :
    OracleHistory (r + n) n S × VisibleFactorData (r + n) (factorCount n 0) r :=
  runVisibleOracle (r + n) r n 0 policy (p.2 * p.2ᵀ)
    (p.1, visibleFactorData (initialFactorData (r + n) (s + n)))

def gramOracleResidual (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (p : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ) : Matrix (Fin r) (Fin s) ℝ :=
  (runGaussianPolicy r s n (compileGramOracle r s n policy) p).2

def gramOracleFactors (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (p : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ) :
    FactorData (r + n) (s + n) (factorCount n 0) r s :=
  finalFactorData (r + n) (s + n) r s n 0 (compileGramOracle r s n policy)
    (fun _ => initialFactorData (r + n) (s + n))
    (runGaussianPolicy r s n (compileGramOracle r s n policy) p).1

theorem measurable_runGramOracle (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : VisibleOraclePolicy (r + n) r n 0 S) : Measurable (runGramOracle r s n policy) := by
  have hw : Measurable (fun p : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ => p.2 * p.2ᵀ) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop
  exact (measurable_runVisibleOracle (r + n) r n 0 policy).comp
    (hw.prodMk (measurable_fst.prodMk measurable_const))

theorem gramOracle_simulation_ae (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy) {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      runGramOracle r s n policy p =
        (readOracleHistory (r + n) (s + n) r s n 0 policy
          (initialFactorState _ _) (identityMemory S)
          (runGaussianPolicy r s n (compileGramOracle r s n policy) p).1,
          visibleFactorData (gramOracleFactors r s n policy p)) := by
  have h := compileVisibleOracle_simulates_ae (r + n) (s + n) r s n 0 ν policy
    (initialFactorState _ _) (identityMemory S) hunit
    (Filter.Eventually.of_forall (fun _ => initialFactorData_orthogonal _ _)) hv
  simpa only [initialFactorState, identityMemory, initialFactorData_represents,
    compileGramOracle, runGramOracle, gramOracleFactors, id_eq] using h

theorem gramOracle_residual_law (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (v : NNReal) :
    (ν.prod (iidMatrixLaw (r + n) (s + n) v)).map (gramOracleResidual r s n policy) =
      iidMatrixLaw r s v :=
  runGaussianPolicy_residual_law r s n ν (compileGramOracle r s n policy) v

theorem gramOracle_transcript_residual_independent (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy) {v : NNReal} (hv : v ≠ 0) :
    IndepFun (runGramOracle r s n policy) (gramOracleResidual r s n policy)
      (ν.prod (iidMatrixLaw (r + n) (s + n) v)) := by
  let gp := compileGramOracle r s n policy
  have hm : Measurable (fun h : GaussianHistory r s n S =>
      (readOracleHistory (r + n) (s + n) r s n 0 policy (initialFactorState _ _) (identityMemory S) h,
        visibleFactorData (finalFactorData (r + n) (s + n) r s n 0 gp
          (fun _ => initialFactorData (r + n) (s + n)) h))) :=
    (measurable_readOracleHistory _ _ _ _ _ _ policy _ _).prodMk
      ((measurable_visibleFactorData _ _ _ _ _).comp
        (measurable_finalFactorData _ _ _ _ _ _ gp _ measurable_const))
  have hind := (runGaussianPolicy_independent r s n ν gp v).comp hm measurable_id
  apply hind.congr
  · filter_upwards [gramOracle_simulation_ae r s n ν policy hunit hv] with p hp
    exact hp.symm
  · exact Filter.Eventually.of_forall (fun _ => rfl)

theorem gramOracle_factorization_ae (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy) {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      representedMatrix (gramOracleFactors r s n policy p) (gramOracleResidual r s n policy p) = p.2 ∧
      (gramOracleFactors r s n policy p).Orthogonal ∧ IsUnit (gramOracleFactors r s n policy p).1.1 ∧
      visibleFactorData (gramOracleFactors r s n policy p) = (runGramOracle r s n policy p).2 := by
  filter_upwards [gaussianPolicy_factorization_ae r s n ν (compileGramOracle r s n policy) hv,
    gramOracle_simulation_ae r s n ν policy hunit hv] with p hf hs
  exact ⟨hf.1, hf.2.1, hf.2.2, (congrArg Prod.snd hs).symm⟩

end
end LowRank
