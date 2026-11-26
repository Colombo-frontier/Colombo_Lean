import LowRank.GaussianKernelPosterior
import LowRank.BlockPosterior
import LowRank.MatrixConditionalTrace

/-! Conditional overlap for an output projector expressed in the actual
query basis. The query-span mass still has to be bounded by summing the
successive adaptive queries; it is not assumed small in these statements. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

def gramOracleQueryMass (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (p : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ) : ℝ :=
  ((gramOracleKernelCoordinates r s n policy p).submatrix Sum.inl Sum.inl).trace

theorem gramOracleQueryMass_integrable (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (v : NNReal) : Integrable (gramOracleQueryMass r s n policy)
      (ν.prod (iidMatrixLaw (r + n) (s + n) v)) := by
  unfold gramOracleQueryMass Matrix.trace Matrix.diag
  exact integrable_finset_sum Finset.univ (fun i _ =>
    gramOracleKernelCoordinates_entryIntegrable r s n policy
      (ν.prod (iidMatrixLaw (r + n) (s + n) v)) (Sum.inl i) (Sum.inl i))

theorem gramOracleQueryMass_condExp (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (v : NNReal) :
    let μ := ν.prod (iidMatrixLaw (r + n) (s + n) v)
    let T := fun p => (runGramOracle r s n policy p).1
    μ[gramOracleQueryMass r s n policy | MeasurableSpace.comap T inferInstance] =ᵐ[μ]
      (fun p => ((gramOracleKernelPosterior r s n ν policy v p).submatrix Sum.inl Sum.inl).trace) := by
  exact matrixCondMean_trace _ _ _ (fun i j =>
    gramOracleKernelCoordinates_entryIntegrable r s n policy _ (Sum.inl i) (Sum.inl j))

theorem gramOracleKernelPosterior_trace_bound (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy) (hs : s ≤ r)
    {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      ∀ P : Matrix (Fin (factorCount n 0) ⊕ Fin r) (Fin (factorCount n 0) ⊕ Fin r) ℝ,
        IsOrthogonalProjector P →
        (P * gramOracleKernelPosterior r s n ν policy v p).trace ≤
          2 * ((gramOracleKernelPosterior r s n ν policy v p).submatrix Sum.inl Sum.inl).trace +
            2 * (((r : ℝ) - s) / r) * P.trace := by
  filter_upwards [gramOracleKernelPosterior_posSemidef r s n ν policy v,
    gramOracleKernelPosterior_bottom_le r s n ν policy hunit hs hv] with p hpos hbottom
  intro P hP
  exact posterior_trace_bound_of_bottom _ _ hpos hP
    (div_nonneg (sub_nonneg.mpr (by exact_mod_cast hs)) (Nat.cast_nonneg r)) hbottom

theorem gramOracle_conditional_overlap_coordinates (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy) (hs : s ≤ r)
    {v : NNReal} (hv : v ≠ 0)
    (P : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ →
      Matrix (Fin (factorCount n 0) ⊕ Fin r) (Fin (factorCount n 0) ⊕ Fin r) ℝ)
    (hPmeas : ∀ i j, AEStronglyMeasurable[
      MeasurableSpace.comap (fun p => (runGramOracle r s n policy p).1) inferInstance]
        (fun p => P p i j) (ν.prod (iidMatrixLaw (r + n) (s + n) v)))
    (hP : ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v), IsOrthogonalProjector (P p)) :
    let μ := ν.prod (iidMatrixLaw (r + n) (s + n) v)
    let T := fun p => (runGramOracle r s n policy p).1
    ∀ᵐ p ∂μ,
      μ[fun z => (P z * gramOracleKernelCoordinates r s n policy z).trace |
        MeasurableSpace.comap T inferInstance] p ≤
          2 * μ[gramOracleQueryMass r s n policy | MeasurableSpace.comap T inferInstance] p +
            2 * (((r : ℝ) - s) / r) * (P p).trace := by
  have he := condExp_projector_trace_mul _ _ (measurable_runGramOracle r s n policy).fst.comap_le
    P (gramOracleKernelCoordinates r s n policy) hPmeas hP
    (gramOracleKernelCoordinates_entryIntegrable r s n policy _)
  filter_upwards [he, gramOracleQueryMass_condExp r s n ν policy v,
    gramOracleKernelPosterior_trace_bound r s n ν policy hunit hs hv, hP] with p he hm hb hP
  rw [he, hm]
  exact hb (P p) hP

end
end LowRank
