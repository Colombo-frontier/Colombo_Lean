import LowRank.GaussianHistoryNoAtoms
import LowRank.GaussianAmbientTranscript

/-! A measurable output selected from the actual adaptive Gram transcript
cannot exactly contain the input range in a proper subspace if fewer
queries than input columns have been made. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

theorem gramOracle_annihilator_zero_ae (r s n : ℕ) (hs : 0 < s)
    {S : Type*} [MeasurableSpace S] (ν : Measure S) [SFinite ν]
    (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy) {v : NNReal} (hv : v ≠ 0)
    (Q : OracleHistory (r + n) n S → Matrix (Fin (r + n)) (Fin (r + n)) ℝ)
    (hQ : Measurable Q) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      Q (runGramOracle r s n policy p).1 * p.2 = 0 →
        Q (runGramOracle r s n policy p).1 = 0 := by
  let read := readOracleHistory (r + n) (s + n) r s n 0 policy
    (initialFactorState _ _) (identityMemory S)
  have hread : Measurable read := measurable_readOracleHistory _ _ _ _ _ _ policy _ _
  filter_upwards [gaussianPolicy_annihilator_zero_ae r s n hs ν
    (compileGramOracle r s n policy) hv (Q ∘ read) (hQ.comp hread),
    gramOracle_simulation_ae r s n ν policy hunit hv] with p hp hsim
  have heq := congrArg Prod.fst hsim
  dsimp only at heq
  rw [heq]
  exact hp

theorem ambientOracle_annihilator_zero_ae (r s n : ℕ) (hs : 0 < s)
    {S : Type*} [MeasurableSpace S] (ν : Measure S) [SFinite ν]
    (policy : AmbientOraclePolicy (r + n) n S) {v : NNReal} (hv : v ≠ 0)
    (Q : OracleHistory (r + n) n S → Matrix (Fin (r + n)) (Fin (r + n)) ℝ)
    (hQ : Measurable Q) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      Q (runAmbientGram r s n policy p) * p.2 = 0 →
        Q (runAmbientGram r s n policy p) = 0 := by
  filter_upwards [gramOracle_annihilator_zero_ae r s n hs ν
    (normalizedAmbientPolicy r s n policy) (normalizedAmbientPolicy_unit r s n policy) hv
    (Q ∘ decodeAmbientHistory r s n policy)
    (hQ.comp (measurable_decodeAmbientHistory r s n policy)),
    ambientOracle_history_recovery_ae r s n ν policy hv] with p hp hsim
  rw [hsim]
  exact hp

theorem ambientOracle_exact_containment_ae (r s n : ℕ) (hs : 0 < s)
    {S : Type*} [MeasurableSpace S] (ν : Measure S) [SFinite ν]
    (policy : AmbientOraclePolicy (r + n) n S) {v : NNReal} (hv : v ≠ 0)
    (P : OracleHistory (r + n) n S → Matrix (Fin (r + n)) (Fin (r + n)) ℝ)
    (hP : Measurable P) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      (1 - P (runAmbientGram r s n policy p)) * p.2 = 0 →
        P (runAmbientGram r s n policy p) = 1 := by
  have hm : Measurable (fun h => 1 - P h) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    simp only [Matrix.sub_apply]
    fun_prop
  filter_upwards [ambientOracle_annihilator_zero_ae r s n hs ν policy hv
    (fun h => 1 - P h) hm] with p hp
  exact fun he => (sub_eq_zero.mp (hp he)).symm

theorem ambientOracle_no_exact_range_ae (r s n : ℕ) (hs : 0 < s)
    {S : Type*} [MeasurableSpace S] (ν : Measure S) [SFinite ν]
    (policy : AmbientOraclePolicy (r + n) n S) {v : NNReal} (hv : v ≠ 0)
    (P : OracleHistory (r + n) n S → Matrix (Fin (r + n)) (Fin (r + n)) ℝ)
    (hP : Measurable P) (hproper : ∀ h, P h ≠ 1) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      (1 - P (runAmbientGram r s n policy p)) * p.2 ≠ 0 := by
  filter_upwards [ambientOracle_exact_containment_ae r s n hs ν policy hv P hP] with p hp
  exact fun he => hproper _ (hp he)

end
end LowRank
