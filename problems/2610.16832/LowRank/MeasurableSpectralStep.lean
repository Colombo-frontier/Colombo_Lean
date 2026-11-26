import LowRank.MeasurableEigenvector
import LowRank.LeadingBlockMatrix
import LowRank.GaussianGaugeMatrix

/-! Split off a measurably chosen smallest-eigenvalue direction. A concrete
Householder basis identifies its orthogonal complement with one fewer coordinate. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix InnerProductSpace
noncomputable section

def eigenvectorGauge {d : ℕ} (u : Fin (d + 1) → ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  gaugeMatrix (EuclideanSpace.basisFun (Fin (d + 1)) ℝ)
    (rowGauge (EuclideanSpace.basisFun (Fin (d + 1)) ℝ) u)

theorem eigenvectorGauge_orthogonal {d : ℕ} (u : Fin (d + 1) → ℝ) :
    (eigenvectorGauge u)ᵀ * eigenvectorGauge u = 1 := gaugeMatrix_transpose_mul_self _ _

theorem eigenvectorGauge_first_column {d : ℕ} (u : Fin (d + 1) → ℝ) (hu : u ⬝ᵥ u = 1) :
    (fun i => eigenvectorGauge u i 0) = u := by
  let b := EuclideanSpace.basisFun (Fin (d + 1)) ℝ
  have hd := basisCoordinates_dot b ((basisCoordinates b).symm u) ((basisCoordinates b).symm u)
  simp only [ContinuousLinearEquiv.apply_symm_apply, real_inner_self_eq_norm_sq] at hd
  have hn : ‖(basisCoordinates b).symm u‖ = 1 := by
    change u ⬝ᵥ u = ‖(basisCoordinates b).symm u‖ ^ 2 at hd
    nlinarith [norm_nonneg ((basisCoordinates b).symm u)]
  have halign : coordinateRotation b (rowGauge b u) u = Pi.single 0 1 := by
    ext j
    rw [rowGauge_aligns, hn]
    simp [Pi.single_apply]
  have hinv := query_rotation_involutive b u u
  rw [halign] at hinv
  funext i
  exact (gaugeMatrix_apply b (rowGauge b u) i 0).trans (congrFun hinv i)

theorem measurable_eigenvectorGauge (d : ℕ) : Measurable (eigenvectorGauge (d := d)) :=
  measurable_rowGauge_matrix (EuclideanSpace.basisFun (Fin (d + 1)) ℝ)

def spectralGauge {d : ℕ} (A : RealSymmetricMatrix (d + 1)) :=
  eigenvectorGauge (orderedEigenvector A 0)

theorem spectralGauge_orthogonal {d : ℕ} (A : RealSymmetricMatrix (d + 1)) :
    (spectralGauge A)ᵀ * spectralGauge A = 1 := eigenvectorGauge_orthogonal _

theorem spectralGauge_first_column {d : ℕ} (A : RealSymmetricMatrix (d + 1)) :
    (fun i => spectralGauge A i 0) = orderedEigenvector A 0 :=
  eigenvectorGauge_first_column _ (orderedEigenvector_dot_self A 0)

theorem measurable_spectralGauge (d : ℕ) : Measurable (spectralGauge (d := d)) :=
  (measurable_eigenvectorGauge d).comp (measurable_orderedEigenvector (d + 1) 0)

def spectralTailBasis {d : ℕ} (A : RealSymmetricMatrix (d + 1)) : Matrix (Fin (d + 1)) (Fin d) ℝ :=
  (spectralGauge A).submatrix id Fin.succ

theorem spectralTailBasis_orthogonal {d : ℕ} (A : RealSymmetricMatrix (d + 1)) :
    (spectralTailBasis A)ᵀ * spectralTailBasis A = 1 := by
  have h := compressed_submatrix (spectralGauge A) (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) Fin.succ
  simpa only [spectralTailBasis, Matrix.mul_one, spectralGauge_orthogonal,
    Matrix.submatrix_one _ (Fin.succ_injective d)] using h

def spectralTail {d : ℕ} (A : RealSymmetricMatrix (d + 1)) : RealSymmetricMatrix d :=
  ⟨(spectralTailBasis A)ᵀ * A.1 * spectralTailBasis A,
    compression_isHermitian A.2 (spectralTailBasis A)⟩

theorem measurable_spectralTailBasis (d : ℕ) : Measurable (spectralTailBasis (d := d)) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact (measurable_pi_apply j.succ).comp ((measurable_pi_apply i).comp (measurable_spectralGauge d))

theorem measurable_spectralTail (d : ℕ) : Measurable (spectralTail (d := d)) := by
  apply Measurable.subtype_mk
  have hB := measurable_spectralTailBasis d
  have hA : Measurable (fun A : RealSymmetricMatrix (d + 1) => A.1) := measurable_subtype_coe
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp only [spectralTail, Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.measurable_sum
  intro l _
  apply Measurable.mul ?_ ((measurable_pi_apply j).comp ((measurable_pi_apply l).comp hB))
  apply Finset.measurable_sum
  intro q _
  exact ((measurable_pi_apply i).comp ((measurable_pi_apply q).comp hB)).mul
    ((measurable_pi_apply l).comp ((measurable_pi_apply q).comp hA))

theorem spectralGauge_diagonal_block {d : ℕ} (A : RealSymmetricMatrix (d + 1)) :
    (spectralGauge A)ᵀ * A.1 * spectralGauge A =
      leadingBlock ((orderedMatrixSpectrum A.2).value 0) (spectralTail A).1 := by
  let U := spectralGauge A
  let e : Fin (d + 1) → ℝ := Pi.single 0 1
  let lam := (orderedMatrixSpectrum A.2).value 0
  have hU : Uᵀ * U = 1 := spectralGauge_orthogonal A
  have he : U *ᵥ e = orderedEigenvector A 0 := by
    calc
      _ = fun i => U i 0 := by ext i; simp [e, Matrix.mulVec, dotProduct, Pi.single_apply]
      _ = _ := spectralGauge_first_column A
  have hback : Uᵀ *ᵥ orderedEigenvector A 0 = e := by
    rw [← he, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  have hcolvec : (Uᵀ * A.1 * U) *ᵥ e = lam • e := by
    rw [← Matrix.mulVec_mulVec, he, ← Matrix.mulVec_mulVec,
      orderedEigenvector_eigen, Matrix.mulVec_smul, hback]
  have hcol (i : Fin (d + 1)) : (Uᵀ * A.1 * U) i 0 = if i = 0 then lam else 0 := by
    simpa [e, Matrix.mulVec, dotProduct, Pi.single_apply] using congrFun hcolvec i
  have hsym : (Uᵀ * A.1 * U)ᵀ = Uᵀ * A.1 * U := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      compression_isHermitian A.2 U
  have htail := compressed_submatrix U A.1 Fin.succ
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simpa [leadingBlock, lam, U] using hcol 0
  · change (Uᵀ * A.1 * U) 0 j.succ = 0
    exact (congrFun (congrFun hsym j.succ) 0).trans (by simpa using hcol j.succ)
  · simpa [leadingBlock, U] using hcol i.succ
  · exact (congrFun (congrFun htail i) j).symm

theorem spectralTail_eigenvalue_ge_min {d : ℕ} (A : RealSymmetricMatrix (d + 1))
    (sp : OrderedMatrixSpectrum (spectralTail A).1) (j : Fin d) :
    (orderedMatrixSpectrum A.2).value 0 ≤ sp.value j := by
  exact ((orderedMatrixSpectrum A.2).increasing (Fin.zero_le _)).trans
    (ordered_compression_eigenvalue_le (by omega) (orderedMatrixSpectrum A.2) sp
      (spectralTailBasis A) (spectralTailBasis_orthogonal A) rfl j)

end
end LowRank
