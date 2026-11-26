import LowRank.GaussianQueryMassBound
import LowRank.GaussianOverlapMean
import LowRank.KernelProjectorGram

/-!
# Adaptive Wishart posterior overlap, arbitrary output rank

This uses the existing, separately checked LowRank factor-state and conditional
Gaussian-law proofs through a local Lake dependency. It does not assume a
posterior-overlap inequality or a cumulative query-mass inequality.

Parameter correspondence with manuscript `lem:overlap`:
`D = r + q`, `k = r - s`, and the residual denominator `D - q = r`.
The rectangular factor has `r + q` rows and `s + q = D - k` columns.
The real trace cap `outputRank` is arbitrary; it need not equal the kernel rank.

`LowRank.AmbientOraclePolicy` uses arbitrary measurable adaptive vectors and
an independent seed. It executes exactly `q` products and returns a measurable
history-dependent projector. The finite-horizon Wishart statement is complete.
The modules `MachineCompiler`, `MachineMatrixBridge`, `MachineUnboundedPosterior`
and `MachineOutputSanitization` supply the cutoff, padding, limit and arbitrary
actual-output decoder bridges. Literal sigma-field/gauge wording of
`lem:deferred` is replaced here by the concrete factor-state probability law.
-/

namespace GradientHessian.GaussianPosterior

open Matrix MeasureTheory LowRank
noncomputable section

/-- The matrix in the overlap integrand really is the orthogonal projector
onto `ker (X Xᵀ)`, almost surely, with the source's rectangular nullity. -/
theorem wishart_kernel_projector_spec (r s q : ℕ) (hs : s ≤ r)
    {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ X ∂iidMatrixLaw (r + q) (s + q) v,
      IsOrthogonalProjector (leftKernelProjector X) ∧
      LinearMap.range (leftKernelProjector X).mulVecLin = LinearMap.ker (X * Xᵀ).mulVecLin ∧
      (leftKernelProjector X).trace = (r : ℝ) - s := by
  filter_upwards [iidMatrixLaw_kernel_projector_spec_ae (r + q) (s + q)
    (Nat.add_le_add_right hs q) hv] with X hX
  refine ⟨leftKernelProjector_isProjector X, hX.1, ?_⟩
  simpa only [Nat.add_sub_add_right, Nat.cast_sub hs] using hX.2.2.1

/-- Actual adaptive Gram-product posterior bound with an arbitrary output
trace cap. All random quantities are evaluated on the presampled iid Gaussian
factor and the independent seed, using the actual adaptive oracle run. -/
theorem arbitrary_rank_posterior_overlap (r s q : ℕ) {Seed : Type*}
    [MeasurableSpace Seed] (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (policy : AmbientOraclePolicy (r + q) q Seed)
    (hs : s ≤ r) (hr : 0 < r) {v : NNReal} (hv : v ≠ 0)
    (output : OracleHistory (r + q) q Seed → Matrix (Fin (r + q)) (Fin (r + q)) ℝ)
    (hout : Measurable output) (hproj : ∀ h, IsOrthogonalProjector (output h))
    {outputRank : ℝ} (htrace : ∀ h, (output h).trace ≤ outputRank) :
    (∫ p, (output (runAmbientGram r s q policy p) * leftKernelProjector p.2).trace
      ∂seedLaw.prod (iidMatrixLaw (r + q) (s + q) v)) ≤
        2 * ((r : ℝ) - s) * ((q : ℝ) + outputRank) / r := by
  have hp := ambientOracle_output_overlap_mean_le r s q seedLaw policy hs hv
    output hout hproj htrace
  have hm := ambientOracleQueryMass_mean_le r s q seedLaw policy hs hr hv
  calc
    _ ≤ 2 * (∫ p, gramOracleQueryMass r s q (normalizedAmbientPolicy r s q policy) p
          ∂seedLaw.prod (iidMatrixLaw (r + q) (s + q) v)) +
        2 * (((r : ℝ) - s) / r) * outputRank := hp
    _ ≤ 2 * (((r : ℝ) - s) * q / r) +
        2 * (((r : ℝ) - s) / r) * outputRank := by linarith
    _ = _ := by ring

/-- The displayed manuscript denominator and numerator, with dimension and
kernel-nullity equalities made explicit. This is the same actual probability
experiment as the preceding theorem, not an assumed trace estimate. -/
theorem manuscript_posterior_overlap (r s q D k : ℕ) {Seed : Type*}
    [MeasurableSpace Seed] (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (policy : AmbientOraclePolicy (r + q) q Seed)
    (hs : s ≤ r) (hr : 0 < r) (hD : D = r + q) (hk : k + s = r)
    {v : NNReal} (hv : v ≠ 0)
    (output : OracleHistory (r + q) q Seed → Matrix (Fin (r + q)) (Fin (r + q)) ℝ)
    (hout : Measurable output) (hproj : ∀ h, IsOrthogonalProjector (output h))
    {outputRank : ℝ} (htrace : ∀ h, (output h).trace ≤ outputRank) :
    (∫ p, (output (runAmbientGram r s q policy p) * leftKernelProjector p.2).trace
      ∂seedLaw.prod (iidMatrixLaw (r + q) (s + q) v)) ≤
        2 * (k : ℝ) * ((q : ℝ) + outputRank) / ((D : ℝ) - q) := by
  have hkr : (k : ℝ) + s = r := by exact_mod_cast hk
  have hDr : (D : ℝ) = r + q := by exact_mod_cast hD
  have hk' : (r : ℝ) - s = k := by linarith
  have hD' : (D : ℝ) - q = r := by linarith
  rw [hD']
  simpa only [hk'] using arbitrary_rank_posterior_overlap r s q seedLaw policy hs hr hv
    output hout hproj htrace

end
end GradientHessian.GaussianPosterior
