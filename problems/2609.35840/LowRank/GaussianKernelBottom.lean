import LowRank.FactorKernelProjector
import LowRank.GaussianKernelConditional

/-! The bottom block of the actual input kernel projector in the algorithm's
query basis is dominated almost surely by the residual-kernel projector.
This also gives an unconditional mean bound. The full posterior overlap
bound still requires conditional order and query-mass arguments. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

theorem measurable_gramOracleResidual (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : VisibleOraclePolicy (r + n) r n 0 S) : Measurable (gramOracleResidual r s n policy) :=
  (runGaussianPolicy_preserving r s n (0 : Measure S) (compileGramOracle r s n policy) 0).measurable.snd

theorem measurable_gramOracleFactors (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : VisibleOraclePolicy (r + n) r n 0 S) : Measurable (gramOracleFactors r s n policy) := by
  have hr := (runGaussianPolicy_preserving r s n (0 : Measure S) (compileGramOracle r s n policy) 0).measurable
  exact (measurable_finalFactorData (r + n) (s + n) r s n 0 (compileGramOracle r s n policy)
    (fun _ : S => initialFactorData (r + n) (s + n)) measurable_const).comp hr.fst

theorem gramOracleFactors_orthogonal (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (p : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ) : (gramOracleFactors r s n policy p).Orthogonal :=
  finalFactorData_orthogonal (r + n) (s + n) r s n 0 (compileGramOracle r s n policy)
    (fun _ : S => initialFactorData (r + n) (s + n)) (fun _ => initialFactorData_orthogonal _ _) _

def gramOracleKernelCoordinates (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (p : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ) :
    Matrix (Fin (factorCount n 0) ⊕ Fin r) (Fin (factorCount n 0) ⊕ Fin r) ℝ :=
  (gramOracleFactors r s n policy p).2.1ᵀ * leftKernelProjector p.2 *
    (gramOracleFactors r s n policy p).2.1

theorem gramOracleKernelCoordinates_isProjector (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (p : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ) :
    IsOrthogonalProjector (gramOracleKernelCoordinates r s n policy p) :=
  (leftKernelProjector_isProjector p.2).coordinates _ (gramOracleFactors_orthogonal r s n policy p).2.1

theorem measurable_gramOracleKernelCoordinates (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : VisibleOraclePolicy (r + n) r n 0 S) :
    Measurable (gramOracleKernelCoordinates r s n policy) := by
  have hf := measurable_gramOracleFactors r s n policy
  have hk : Measurable (fun p : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ => leftKernelProjector p.2) :=
    measurable_leftKernelProjector.comp measurable_snd
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp only [gramOracleKernelCoordinates, Matrix.mul_apply, Matrix.transpose_apply]
  fun_prop

theorem gramOracleKernelCoordinates_entryIntegrable (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (μ : Measure (S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ)) [IsProbabilityMeasure μ] :
    EntryIntegrable (gramOracleKernelCoordinates r s n policy) μ := by
  intro i j
  have hm := (measurable_pi_apply j).comp
    ((measurable_pi_apply i).comp (measurable_gramOracleKernelCoordinates r s n policy))
  exact (integrable_const (1 : ℝ)).mono' hm.stronglyMeasurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p =>
      (gramOracleKernelCoordinates_isProjector r s n policy p).entry_norm_le_one i j))

theorem gramOracle_kernel_bottom_le_ae (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy) (hs : s ≤ r)
    {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      LoewnerLE ((gramOracleKernelCoordinates r s n policy p).submatrix Sum.inr Sum.inr)
        (leftKernelProjector (gramOracleResidual r s n policy p)) := by
  have hr : MeasurePreserving (gramOracleResidual r s n policy)
      (ν.prod (iidMatrixLaw (r + n) (s + n) v)) (iidMatrixLaw r s v) :=
    ⟨measurable_gramOracleResidual r s n policy, gramOracle_residual_law r s n ν policy v⟩
  have hX : ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v), Function.Injective p.2.mulVec :=
    Measure.quasiMeasurePreserving_snd.ae (iidMatrixLaw_mulVec_injective_ae (r + n) (s + n) (by omega) hv)
  filter_upwards [gramOracle_factorization_ae r s n ν policy hunit hv, hX,
    hr.quasiMeasurePreserving.ae (iidMatrixLaw_mulVec_injective_ae r s hs hv)] with p hf hX hD
  have hh : Function.Injective (representedMatrix (gramOracleFactors r s n policy p)
      (gramOracleResidual r s n policy p)).mulVec := by rw [hf.1]; exact hX
  have h := factorKernelProjector_bottom_le (gramOracleFactors r s n policy p)
    (gramOracleResidual r s n policy p) hf.2.1 hh hD
  simpa only [factorKernelProjector, hf.1] using h

theorem gramOracle_kernel_bottom_mean_le (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy) (hs : s ≤ r)
    {v : NNReal} (hv : v ≠ 0) :
    LoewnerLE (matrixMean (ν.prod (iidMatrixLaw (r + n) (s + n) v))
      (fun p => (gramOracleKernelCoordinates r s n policy p).submatrix Sum.inr Sum.inr))
      ((((r : ℝ) - s) / r) • (1 : Matrix (Fin r) (Fin r) ℝ)) := by
  let μ := ν.prod (iidMatrixLaw (r + n) (s + n) v)
  let R := gramOracleResidual r s n policy
  have hR : MeasurePreserving R μ (iidMatrixLaw r s v) :=
    ⟨measurable_gramOracleResidual r s n policy, gramOracle_residual_law r s n ν policy v⟩
  have hQ : EntryIntegrable (fun p => leftKernelProjector (R p)) μ := by
    intro i j
    have hm : Measurable (fun D : Matrix (Fin r) (Fin s) ℝ => leftKernelProjector D i j) :=
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_leftKernelProjector)
    exact (hR.integrable_comp hm.stronglyMeasurable.aestronglyMeasurable).mpr
      (leftKernelProjector_entryIntegrable (iidMatrixLaw r s v) i j)
  have hmean : matrixMean μ (fun p => leftKernelProjector (R p)) =
      (((r : ℝ) - s) / r) • (1 : Matrix (Fin r) (Fin r) ℝ) := by
    rw [← gaussianKernelMean_isotropic r s hs hv]
    ext i j
    have hm : Measurable (fun D : Matrix (Fin r) (Fin s) ℝ => leftKernelProjector D i j) :=
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_leftKernelProjector)
    have h := integral_map_of_stronglyMeasurable (μ := μ) hR.measurable hm.stronglyMeasurable
    rw [hR.map_eq] at h
    exact h.symm
  exact mean_bottom_covariance
    (fun i j => gramOracleKernelCoordinates_entryIntegrable r s n policy μ (Sum.inr i) (Sum.inr j))
    hQ (gramOracle_kernel_bottom_le_ae r s n ν policy hunit hs hv) hmean

end
end LowRank
