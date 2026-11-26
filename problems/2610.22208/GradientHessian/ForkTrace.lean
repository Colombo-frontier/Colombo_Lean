import GradientHessian.MatrixGoodUpper
import GradientHessian.MatrixAnalyticNorms
import LowRank.MeasurableKernelProjector
import LowRank.FrobeniusCompression

/-!
# Measurable test projectors and the deterministic fork trace inequality

All projectors are concrete matrices.  In particular, repeated and zero test
columns use the total measurable Gram--Schmidt projector from `LowRank`.
-/

namespace GradientHessian.ForkTrace

open Matrix MeasureTheory LowRank
open GradientHessian.MatrixAnalyticNorms GradientHessian.MatrixGoodUpper
open scoped Matrix InnerProductSpace
noncomputable section

def columnVector {d r : ℕ} (C : Matrix (Fin d) (Fin r) ℝ) (i : Fin r) :
    EuclideanSpace ℝ (Fin d) := (WithLp.equiv 2 (Fin d → ℝ)).symm (fun j => C j i)

def testProjector {d s : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (tests : Matrix (Fin d) (Fin s) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  columnRangeProjector ((1-P)*tests)

theorem testProjector_isProjector {d s : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (tests : Matrix (Fin d) (Fin s) ℝ) : IsOrthogonalProjector (testProjector P tests) :=
  columnRangeProjector_isProjector _

theorem testProjector_rank_le {d s : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (tests : Matrix (Fin d) (Fin s) ℝ) : (testProjector P tests).rank ≤ s :=
  columnRangeProjector_rank_le _

theorem testProjector_trace_le {d s : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (tests : Matrix (Fin d) (Fin s) ℝ) : (testProjector P tests).trace ≤ (s : ℝ) :=
  columnRangeProjector_trace_le _

theorem measurable_testProjector {d s : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) :
    Measurable (testProjector (s := s) P) := by
  exact (measurable_columnRangeProjector d s).comp
    (show Continuous (fun tests : Matrix (Fin d) (Fin s) ℝ => (1-P)*tests) by fun_prop).measurable

theorem testProjector_fixes {d s : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (tests : Matrix (Fin d) (Fin s) ℝ) :
    testProjector P tests*((1-P)*tests) = (1-P)*tests := columnRangeProjector_fixes _

theorem testProjector_fixes_test {d s : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (tests : Matrix (Fin d) (Fin s) ℝ) (i : Fin s) :
    matrixEuclideanMap (testProjector P tests)
      (matrixEuclideanMap (1-P) (columnVector tests i)) =
        matrixEuclideanMap (1-P) (columnVector tests i) := by
  ext j
  exact congrFun (congrFun (testProjector_fixes P tests) j) i

theorem columnVector_mul {d s r : ℕ} (A : Matrix (Fin d) (Fin s) ℝ)
    (C : Matrix (Fin s) (Fin r) ℝ) (i : Fin r) :
    columnVector (A*C) i = matrixEuclideanMap A (columnVector C i) := by
  ext j
  rfl

theorem sum_column_norm_sq {d r : ℕ} (C : Matrix (Fin d) (Fin r) ℝ) :
    (∑ i, ‖columnVector C i‖^2) = frobeniusSq C := by
  simp_rw [← euclidean_dot_self]
  change (∑ i, ∑ j, C j i*C j i) = ∑ j, ∑ i, (C j i)^2
  rw [Finset.sum_comm]
  simp only [pow_two]

theorem column_energy_eq_trace {d r : ℕ} {R : Matrix (Fin d) (Fin d) ℝ}
    (hR : IsOrthogonalProjector R) (C : Matrix (Fin d) (Fin r) ℝ) :
    (∑ i, ‖matrixEuclideanMap R (columnVector C i)‖^2) = (R*(C*Cᵀ)).trace := by
  simp_rw [← columnVector_mul]
  rw [sum_column_norm_sq, frobeniusSq_eq_trace, Matrix.transpose_mul, hR.symmetric]
  calc
    _ = (R*(C*Cᵀ)*R).trace := by simp only [Matrix.mul_assoc]
    _ = (R*R*(C*Cᵀ)).trace := by rw [Matrix.trace_mul_cycle]
    _ = _ := by rw [hR.idempotent]

/-- A bounded family of vectors in the kernel obeys the corresponding
Loewner bound, with the kernel projector rather than the identity. -/
theorem column_gram_le_projector {d r : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : IsOrthogonalProjector K) (C : Matrix (Fin d) (Fin r) ℝ)
    (hKC : K*C = C) {B : ℝ} (hB : 0 ≤ B) (hC : ‖matrixEuclideanMap C‖ ≤ B) :
    LoewnerLE (C*Cᵀ) ((B^2) • K) := by
  have hu : LoewnerLE (C*Cᵀ) ((B^2) • 1) := by
    apply wishart_le_of_transpose_opNorm C hB
    rwa [matrixEuclideanMap_transpose_norm]
  have hCK : Cᵀ*K = Cᵀ := by
    have h := congrArg Matrix.transpose hKC
    simpa only [Matrix.transpose_mul, hK.symmetric] using h
  have hc := loewner_congruence hu K
  have hl : Kᵀ*(C*Cᵀ)*K = C*Cᵀ := by
    rw [hK.symmetric]
    calc
      _ = (K*C)*(Cᵀ*K) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hKC,hCK]
  rw [hl] at hc
  simpa only [hK.symmetric, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, hK.idempotent] using hc

theorem column_projection_energy_le {d r : ℕ} {R K : Matrix (Fin d) (Fin d) ℝ}
    (hR : IsOrthogonalProjector R) (hK : IsOrthogonalProjector K)
    (C : Matrix (Fin d) (Fin r) ℝ) (hKC : K*C = C)
    (hC : ‖matrixEuclideanMap C‖ ≤ 12) :
    (∑ i, ‖matrixEuclideanMap R (columnVector C i)‖^2) ≤ 144*(R*K).trace := by
  rw [column_energy_eq_trace hR C]
  have h := trace_mul_mono hR.posSemidef (column_gram_le_projector hK C hKC (by norm_num) hC)
  norm_num only [show (12:ℝ)^2 = 144 by norm_num, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul] at h
  exact h

/-- The exact deterministic trace lower bound used in source `lem:fork`.
`hits` is an actual finite set of columns whose projected norm clears the
threshold; no hit-count inequality is an input hypothesis. -/
theorem fork_trace_lower_bound {d r : ℕ} {R K : Matrix (Fin d) (Fin d) ℝ}
    (hR : IsOrthogonalProjector R) (hK : IsOrthogonalProjector K)
    (C : Matrix (Fin d) (Fin r) ℝ) (hKC : K*C = C)
    (hC : ‖matrixEuclideanMap C‖ ≤ 12) (hits : Finset (Fin r))
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hhit : ∀ i ∈ hits, 3*γ/4 < ‖matrixEuclideanMap R (columnVector C i)‖) :
    γ^2*(hits.card : ℝ)/256 ≤ (R*K).trace := by
  have hl : (9*γ^2/16)*(hits.card : ℝ) ≤ ∑ i, ‖matrixEuclideanMap R (columnVector C i)‖^2 := by
    calc
      _ = ∑ _i ∈ hits, (3*γ/4)^2 := by simp; ring
      _ ≤ ∑ i ∈ hits, ‖matrixEuclideanMap R (columnVector C i)‖^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have h := hhit i hi
        nlinarith [norm_nonneg (matrixEuclideanMap R (columnVector C i))]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ hits)
        (fun i _ _ => sq_nonneg _)
  have hu := column_projection_energy_le hR hK C hKC hC
  nlinarith

end
end GradientHessian.ForkTrace
