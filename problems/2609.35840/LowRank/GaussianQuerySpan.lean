import LowRank.QuerySpan
import LowRank.GaussianAmbientTranscript

/-! Identify the Gaussian factorization's leading space with actual queried
directions. Under positive variance this space has exactly the query budget
as its dimension, including the supplementary queries of the reduction. -/

namespace LowRank
open MeasureTheory Matrix
open scoped Matrix
noncomputable section

theorem gramOracle_exposedSpan (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy)
    (p : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ) :
    exposedSpan (runGramOracle r s n policy p).2 =
      visibleQueriedSpan (r + n) r n 0 policy (p.2 * p.2ᵀ)
        (p.1, visibleFactorData (initialFactorData (r + n) (s + n))) := by
  simpa only [runGramOracle, exposedSpan_initial, bot_sup_eq] using
    (runVisibleOracle_exposedSpan (r + n) r n 0 policy hunit (p.2 * p.2ᵀ)
      (p.1, visibleFactorData (initialFactorData (r + n) (s + n))))

theorem gramOracle_querySpan_ae (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy) {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      let K := visibleQueriedSpan (r + n) r n 0 policy (p.2 * p.2ᵀ)
        (p.1, visibleFactorData (initialFactorData (r + n) (s + n)))
      exposedSpan (visibleFactorData (gramOracleFactors r s n policy p)) = K ∧
        Module.finrank ℝ K = n := by
  filter_upwards [gramOracle_factorization_ae r s n ν policy hunit hv] with p hp
  dsimp only
  have he : exposedSpan (visibleFactorData (gramOracleFactors r s n policy p)) =
      visibleQueriedSpan (r + n) r n 0 policy (p.2 * p.2ᵀ)
        (p.1, visibleFactorData (initialFactorData (r + n) (s + n))) := by
    rw [hp.2.2.2, gramOracle_exposedSpan r s n policy hunit]
  refine ⟨he, ?_⟩
  have hd := exposedSpan_finrank_eq (visibleFactorData (gramOracleFactors r s n policy p)) hp.2.1.1
  rw [he] at hd
  simpa only [factorCount_eq, Nat.zero_add] using hd

theorem ambientOracle_querySpan_ae (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν] (policy : AmbientOraclePolicy (r + n) n S)
    {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      let K := visibleQueriedSpan (r + n) r n 0 (normalizedAmbientPolicy r s n policy) (p.2 * p.2ᵀ)
        (p.1, visibleFactorData (initialFactorData (r + n) (s + n)))
      exposedSpan (visibleFactorData (ambientOracleFactors r s n policy p)) = K ∧
        Module.finrank ℝ K = n :=
  gramOracle_querySpan_ae r s n ν (normalizedAmbientPolicy r s n policy)
    (normalizedAmbientPolicy_unit r s n policy) hv

end
end LowRank
