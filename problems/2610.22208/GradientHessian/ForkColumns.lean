import GradientHessian.ForkGeometry
import GradientHessian.SphereColumnNorm
import GradientHessian.ReadoutMarks

/-!
# The actual family of fork kernel vectors

The column matrix is the literal product `D Q [w_i] diag (1 / nu_i)`.
On the source event its operator norm is at most twelve whenever the mark
column matrix has norm at most four.  Hits refer to the actual polynomial
readout and actual branch tests; the trace inequality is a consequence.
-/

namespace GradientHessian.ForkColumns

open Matrix LowRank
open GradientHessian.MatrixGoodSpectrum GradientHessian.MatrixProjectorCompression
open GradientHessian.MatrixAnalyticNorms GradientHessian.ReadoutSpectral
open GradientHessian.ForkGeometry GradientHessian.ForkTrace
open GradientHessian.SphereColumnNorm
open scoped Matrix InnerProductSpace
noncomputable section

def kernelColumns {d n r : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (J : ℕ)
    (X : Matrix (Fin d) (Fin n) ℝ) (w : Fin r → EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin r) ℝ :=
  (dilation P (Real.sqrt (1/(J:ℝ)))*sourceKernel P J X)*columnMatrix w *
    diagonal (fun i => ‖idealResidual P (sourceKernel P J X) (w i)‖⁻¹)

theorem kernelColumns_column {d n r : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (J : ℕ)
    (X : Matrix (Fin d) (Fin n) ℝ) (w : Fin r → EuclideanSpace ℝ (Fin d)) (i : Fin r) :
    columnVector (kernelColumns P J X w) i = kernelVector P J X (w i) := by
  ext j
  change (((dilation P (Real.sqrt (1/(J:ℝ)))*sourceKernel P J X)*columnMatrix w *
      diagonal (fun i => ‖idealResidual P (sourceKernel P J X) (w i)‖⁻¹)) j i) =
    ‖idealResidual P (sourceKernel P J X) (w i)‖⁻¹ *
      (((dilation P (Real.sqrt (1/(J:ℝ)))*sourceKernel P J X)*ᵥ ⇑(w i)) j)
  rw [Matrix.mul_diagonal]
  change (((dilation P (Real.sqrt (1/(J:ℝ)))*sourceKernel P J X)*ᵥ ⇑(w i)) j) *
      ‖idealResidual P (sourceKernel P J X) (w i)‖⁻¹ = _
  exact mul_comm _ _

theorem kernelColumns_fixed {d n r : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) {J : ℕ} (hJ : 0 < J)
    {X : Matrix (Fin d) (Fin n) ℝ} (hX : Function.Injective X.mulVec)
    (w : Fin r → EuclideanSpace ℝ (Fin d)) :
    leftKernelProjector X * kernelColumns P J X w = kernelColumns P J X w := by
  ext j i
  have h := congrArg (fun z : EuclideanSpace ℝ (Fin d) => z j)
    (show matrixEuclideanMap (leftKernelProjector X)
        (columnVector (kernelColumns P J X w) i) =
        columnVector (kernelColumns P J X w) i from by
      rw [kernelColumns_column]
      exact congrArg (WithLp.equiv 2 (Fin d → ℝ)).symm (kernelVector_fixed hP hJ hX (w i)))
  exact h

theorem dilation_opNorm_le_one {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) {J : ℕ} (hJ : 0 < J) :
    ‖matrixEuclideanMap (dilation P (Real.sqrt (1/(J:ℝ))))‖ ≤ 1 := by
  have hJR : (0:ℝ)<J := by exact_mod_cast hJ
  have hJ1 : (1:ℝ)≤J := by exact_mod_cast hJ
  apply matrix_norm_le_of_gram_le _ zero_le_one
  simpa only [dilation_symmetric hP, one_pow, one_smul] using
    dilation_square_upper hP (by positivity : 0 ≤ 1/(J:ℝ))
      ((div_le_iff₀ hJR).mpr (by linarith) : 1/(J:ℝ) ≤ 1)

theorem source_normalizer_inverse_le {d n : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) {J : ℕ} (hJ : 4 ≤ J)
    {X : Matrix (Fin d) (Fin n) ℝ}
    (hX : X ∈ MatrixKernelConcentration.sourceGoodEvent P J)
    (w : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖ = 1) (hPw : P *ᵥ ⇑w = ⇑w) :
    |‖idealResidual P (sourceKernel P J X) w‖⁻¹| ≤ 3 := by
  have h := (source_ideal_bounds hP hJ hX w hw hPw).1
  have hs : 1 ≤ Real.sqrt (2:ℝ) := by
    have he := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    have hn := Real.sqrt_nonneg (2:ℝ)
    nlinarith
  have hl : (1/3:ℝ) ≤ ‖idealResidual P (sourceKernel P J X) w‖ := by linarith
  have hp : 0 < ‖idealResidual P (sourceKernel P J X) w‖ := by linarith
  rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_eq_one_div, div_le_iff₀ hp]
  linarith

theorem source_kernelColumns_norm {d n r : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) {J : ℕ} (hJ : 4 ≤ J)
    {X : Matrix (Fin d) (Fin n) ℝ}
    (hX : X ∈ MatrixKernelConcentration.sourceGoodEvent P J)
    (w : Fin r → EuclideanSpace ℝ (Fin d))
    (hw : ∀ i, ‖w i‖ = 1) (hPw : ∀ i, P *ᵥ ⇑(w i) = ⇑(w i))
    (hW : ‖matrixEuclideanMap (columnMatrix w)‖ ≤ 4) :
    ‖matrixEuclideanMap (kernelColumns P J X w)‖ ≤ 12 := by
  have hD := dilation_opNorm_le_one hP (by omega : 0 < J)
  have hQ := projector_norm_le (sourceKernel_isProjector P J X)
  have hdiag := diagonal_opNorm_le
    (fun i => ‖idealResidual P (sourceKernel P J X) (w i)‖⁻¹)
    (by norm_num : (0:ℝ)≤3)
    (fun i => source_normalizer_inverse_le hP hJ hX (w i) (hw i) (hPw i))
  unfold kernelColumns
  simp only [matrixEuclideanMap_mul]
  calc
    _ ≤ ‖(matrixEuclideanMap (dilation P (Real.sqrt (1/(J:ℝ))))).comp
        (matrixEuclideanMap (sourceKernel P J X))‖ *
        ‖matrixEuclideanMap (columnMatrix w)‖ *
        ‖matrixEuclideanMap (diagonal (fun i =>
          ‖idealResidual P (sourceKernel P J X) (w i)‖⁻¹))‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (1*1)*4*3 := by
      apply mul_le_mul
      · apply mul_le_mul
        · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul hD hQ (norm_nonneg _) zero_le_one)
        · exact hW
        · exact norm_nonneg _
        · norm_num
      · exact hdiag
      · exact norm_nonneg _
      · norm_num
    _ = 12 := by norm_num

def flattenedTests {d r s : ℕ} (tests : Fin r → Fin s → EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin (r*s)) ℝ :=
  columnMatrix (fun i => tests (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)

theorem flattenedTests_column {d r s : ℕ}
    (tests : Fin r → Fin s → EuclideanSpace ℝ (Fin d)) (i : Fin r) (j : Fin s) :
    columnVector (flattenedTests tests) (finProdFinEquiv (i,j)) = tests i j := by
  ext k
  simp [columnVector, flattenedTests, columnMatrix]

def branchProjector {d r s : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (tests : Fin r → Fin s → EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  testProjector P (flattenedTests tests)

theorem branchProjector_rank_le {d r s : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (tests : Fin r → Fin s → EuclideanSpace ℝ (Fin d)) :
    (branchProjector P tests).rank ≤ r*s := testProjector_rank_le _ _

def sourceHits {d n r s : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (J : ℕ)
    (X : Matrix (Fin d) (Fin n) ℝ) (fallback : Fin d → ℝ)
    (w : Fin r → EuclideanSpace ℝ (Fin d))
    (tests : Fin r → Fin s → EuclideanSpace ℝ (Fin d)) (γ : ℝ) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter (fun i => ∃ j,
    γ < |⟪(WithLp.equiv 2 (Fin d → ℝ)).symm
      (ReadoutOracle.readout (ReadoutFilter.matrixUpper J) P (sourceMatrix P J X) fallback ⇑(w i)),
        tests i j⟫_ℝ|)

/-- The literal source hit count forces the claimed kernel overlap.  The
tests may depend arbitrarily on the matrix; their chronological admissibility
is a separate requirement for the later posterior upper bound. -/
theorem source_fork_trace {d n r s : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) {J : ℕ} (hJ : 4 ≤ J)
    {X : Matrix (Fin d) (Fin n) ℝ}
    (hX : X ∈ MatrixKernelConcentration.sourceGoodEvent P J)
    (fallback : Fin d → ℝ) (w : Fin r → EuclideanSpace ℝ (Fin d))
    (hw : ∀ i, ‖w i‖ = 1) (hPw : ∀ i, P *ᵥ ⇑(w i) = ⇑(w i))
    (hW : ‖matrixEuclideanMap (columnMatrix w)‖ ≤ 4)
    (tests : Fin r → Fin s → EuclideanSpace ℝ (Fin d))
    (htests : ∀ i j, ‖tests i j‖ ≤ 1) {γ : ℝ} (hγ : 0 ≤ γ)
    (hδ : 5*ReadoutFilter.delta ≤ γ/4) :
    γ^2*((sourceHits P J X fallback w tests γ).card : ℝ)/256 ≤
      (branchProjector P tests * leftKernelProjector X).trace := by
  have hJ0 : 0 < J := by omega
  apply fork_trace_lower_bound (testProjector_isProjector P (flattenedTests tests))
    (leftKernelProjector_isProjector X) (kernelColumns P J X w)
    (kernelColumns_fixed hP hJ0 (sourceGoodEvent_injective P hJ0 hX) w)
    (source_kernelColumns_norm hP hJ hX w hw hPw hW) _ hγ
  intro i hi
  obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hi).2
  rw [kernelColumns_column]
  apply hit_implies_projected_norm hP (testProjector_isProjector P (flattenedTests tests))
    _ (idealReadout P (sourceKernel P J X) (w i)) _ (tests i j) (htests i j)
    _ (kernelVector_inner hP J X (w i) (tests i j))
    (source_readout_perturbation hP hJ hX fallback (w i) (hw i) (hPw i)) hδ hj
  simpa only [flattenedTests_column] using
    testProjector_fixes_test P (flattenedTests tests) (finProdFinEquiv (i,j))

end
end GradientHessian.ForkColumns
