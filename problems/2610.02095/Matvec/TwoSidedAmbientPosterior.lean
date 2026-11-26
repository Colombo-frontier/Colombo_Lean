import Matvec.TwoSidedOracleCompile

/-!
# Constructed posterior for arbitrary ambient two-sided oracle policies

Every original query is replayed exactly, including zero and redundant queries.
The enhanced record exposes one row and column at each step; this may reveal
more than the original oracle transcript. Its residual is independent Gaussian,
the actual ambient matrix has a visible affine factorization with orthonormal
residual frames, and the residual is also independent of the original record.
No adaptive-posterior or transcript-replay premise is assumed.
-/

namespace Matvec
open Matrix MeasureTheory ProbabilityTheory
noncomputable section
universe u

def initialOracleState (m n : ℕ) (S : Type u) [MeasurableSpace S] :
    OracleMap S (TwoSidedState m n m n) := ⟨fun _ => initialTwoSidedState m n, measurable_const⟩

def initialOracleMemory (S : Type u) [MeasurableSpace S] : OracleMap S S := ⟨id, measurable_id⟩

def compiledAmbientPolicy (r s t : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy (r + t) (s + t) t S) : TwoSidedPolicy r s t S :=
  compileTwoSidedOracle (r + t) (s + t) r s t policy
    (initialOracleState (r + t) (s + t) S) (initialOracleMemory S)

def ambientTwoSidedRecord (r s t : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy (r + t) (s + t) t S)
    (p : S × Matrix (Fin (r + t)) (Fin (s + t)) ℝ) :
    TwoSidedOracleHistory (r + t) (s + t) t S :=
  runTwoSidedOracle (r + t) (s + t) t policy p.2 p.1

def ambientTwoSidedResidual (r s t : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy (r + t) (s + t) t S)
    (p : S × Matrix (Fin (r + t)) (Fin (s + t)) ℝ) : Matrix (Fin r) (Fin s) ℝ :=
  (runTwoSidedPolicy r s t (compiledAmbientPolicy r s t policy) p).2

def ambientTwoSidedFactors (r s t : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy (r + t) (s + t) t S)
    (p : S × Matrix (Fin (r + t)) (Fin (s + t)) ℝ) : TwoSidedState (r + t) (s + t) r s :=
  readTwoSidedState (r + t) (s + t) r s t policy
    (initialOracleState (r + t) (s + t) S) (initialOracleMemory S)
    (runTwoSidedPolicy r s t (compiledAmbientPolicy r s t policy) p).1

def decodeAmbientTwoSided (r s t : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy (r + t) (s + t) t S) :=
  decodeTwoSidedHistory (r + t) (s + t) r s t policy
    (initialOracleState (r + t) (s + t) S) (initialOracleMemory S)

theorem ambientTwoSided_replay (r s t : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy (r + t) (s + t) t S)
    (p : S × Matrix (Fin (r + t)) (Fin (s + t)) ℝ) :
    decodeAmbientTwoSided r s t policy
      (runTwoSidedPolicy r s t (compiledAmbientPolicy r s t policy) p).1 =
      ambientTwoSidedRecord r s t policy p := by
  have h := compileTwoSidedOracle_replay (r + t) (s + t) r s t policy
    (initialOracleState (r + t) (s + t) S) (initialOracleMemory S) p
  simpa only [initialOracleState, initialOracleMemory, initialTwoSidedState_represents, id_eq] using h

/-- Pointwise affine posterior representation with actual cumulative frames. -/
theorem ambientTwoSided_factorization (r s t : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy (r + t) (s + t) t S)
    (p : S × Matrix (Fin (r + t)) (Fin (s + t)) ℝ) :
    representedTwoSided (ambientTwoSidedFactors r s t policy p)
      (ambientTwoSidedResidual r s t policy p) = p.2 := by
  have h := compileTwoSidedOracle_factorization (r + t) (s + t) r s t policy
    (initialOracleState (r + t) (s + t) S) (initialOracleMemory S) p
  simpa only [initialOracleState, initialTwoSidedState_represents] using h

theorem ambientTwoSided_factors_orthogonal (r s t : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy (r + t) (s + t) t S)
    (p : S × Matrix (Fin (r + t)) (Fin (s + t)) ℝ) :
    (ambientTwoSidedFactors r s t policy p).Orthogonal :=
  readTwoSidedState_orthogonal (r + t) (s + t) r s t policy
    (initialOracleState (r + t) (s + t) S) (initialOracleMemory S)
    (fun _ => initialTwoSidedState_orthogonal _ _) _

theorem measurable_ambientTwoSidedRecord (r s t : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy (r + t) (s + t) t S) :
    Measurable (ambientTwoSidedRecord r s t policy) := by
  have hp := runTwoSidedPolicy_preserving r s t (0 : Measure S) (compiledAmbientPolicy r s t policy) 1
  have hd := measurable_decodeTwoSidedHistory (r + t) (s + t) r s t policy
    (initialOracleState (r + t) (s + t) S) (initialOracleMemory S)
  have h := hd.comp hp.measurable.fst
  change Measurable (fun p => decodeAmbientTwoSided r s t policy
    (runTwoSidedPolicy r s t (compiledAmbientPolicy r s t policy) p).1) at h
  simpa only [ambientTwoSided_replay] using h

theorem measurable_ambientTwoSidedResidual (r s t : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy (r + t) (s + t) t S) :
    Measurable (ambientTwoSidedResidual r s t policy) :=
  (runTwoSidedPolicy_preserving r s t (0 : Measure S) (compiledAmbientPolicy r s t policy) 1).measurable.snd

theorem measurable_ambientTwoSidedFactors (r s t : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy (r + t) (s + t) t S) :
    Measurable (ambientTwoSidedFactors r s t policy) :=
  (measurable_readTwoSidedState (r + t) (s + t) r s t policy
    (initialOracleState (r + t) (s + t) S) (initialOracleMemory S)).comp
    (runTwoSidedPolicy_preserving r s t (0 : Measure S) (compiledAmbientPolicy r s t policy) 1).measurable.fst

theorem ambientTwoSided_residual_law (r s t : ℕ) {S : Type u} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν]
    (policy : TwoSidedOraclePolicy (r + t) (s + t) t S) (v : NNReal) :
    (ν.prod (LowRank.iidMatrixLaw (r + t) (s + t) v)).map
      (ambientTwoSidedResidual r s t policy) = LowRank.iidMatrixLaw r s v :=
  runTwoSidedPolicy_residual_law r s t ν (compiledAmbientPolicy r s t policy) v

theorem ambientTwoSided_transcript_residual_independent (r s t : ℕ) {S : Type u}
    [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (policy : TwoSidedOraclePolicy (r + t) (s + t) t S) (v : NNReal) :
    IndepFun (ambientTwoSidedRecord r s t policy) (ambientTwoSidedResidual r s t policy)
      (ν.prod (LowRank.iidMatrixLaw (r + t) (s + t) v)) := by
  have h := runTwoSidedPolicy_decoded_independent r s t ν (compiledAmbientPolicy r s t policy) v
    (decodeAmbientTwoSided r s t policy)
    (measurable_decodeTwoSidedHistory (r + t) (s + t) r s t policy
      (initialOracleState (r + t) (s + t) S) (initialOracleMemory S))
  simpa only [ambientTwoSided_replay] using h

theorem ambientTwoSided_conditional_bounded (r s t : ℕ) {S : Type u} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν]
    (policy : TwoSidedOraclePolicy (r + t) (s + t) t S) (v : NNReal)
    (φ : Matrix (Fin r) (Fin s) ℝ → ℝ) (hφ : Measurable φ)
    (C : ℝ) (hbound : ∀ D, ‖φ D‖ ≤ C) :
    let μ := ν.prod (LowRank.iidMatrixLaw (r + t) (s + t) v)
    let T := ambientTwoSidedRecord r s t policy
    let Z := ambientTwoSidedResidual r s t policy
    Integrable (φ ∘ Z) μ ∧
      μ[φ ∘ Z | MeasurableSpace.comap T inferInstance] =ᵐ[μ]
        (fun _ => ∫ D, φ D ∂LowRank.iidMatrixLaw r s v) := by
  let μ := ν.prod (LowRank.iidMatrixLaw (r + t) (s + t) v)
  let T := ambientTwoSidedRecord r s t policy
  let Z := ambientTwoSidedResidual r s t policy
  have hT : Measurable T := measurable_ambientTwoSidedRecord r s t policy
  have hZ : Measurable Z := measurable_ambientTwoSidedResidual r s t policy
  have hZlaw : MeasurePreserving Z μ (LowRank.iidMatrixLaw r s v) :=
    ⟨hZ, ambientTwoSided_residual_law r s t ν policy v⟩
  have hiφ : Integrable φ (LowRank.iidMatrixLaw r s v) :=
    (integrable_const C).mono' hφ.stronglyMeasurable.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  refine ⟨(hZlaw.integrable_comp hφ.stronglyMeasurable.aestronglyMeasurable).mpr hiφ, ?_⟩
  have hind : IndepFun Z T μ := (ambientTwoSided_transcript_residual_independent r s t ν policy v).symm
  have hsm : StronglyMeasurable[(inferInstance : MeasurableSpace (Matrix (Fin r) (Fin s) ℝ)).comap Z]
      (φ ∘ Z) := (hφ.comp (comap_measurable Z)).stronglyMeasurable
  have hc := condExp_indep_eq hZ.comap_le hT.comap_le hsm ((IndepFun_iff_Indep Z T μ).mp hind)
  have hi : (∫ p, φ (Z p) ∂μ) = ∫ D, φ D ∂LowRank.iidMatrixLaw r s v := by
    rw [← hZlaw.map_eq, integral_map_of_stronglyMeasurable hZ hφ.stronglyMeasurable]
  simpa only [Function.comp_def, hi] using hc

end
end Matvec
