import LowRank.KrylovBlockPolicy
import LowRank.ColumnRangeImage

/-! Concatenate the Krylov blocks and reconstruct the restricted operator
using only the stored query transcript. The resulting projector fixes every
block polynomial of the available degree. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

def flattenBlockMatrices {d s n : ℕ} (B : Fin n → Matrix (Fin d) (Fin s) ℝ) :
    Matrix (Fin d) (Fin (n * s)) ℝ :=
  fun i j => B (finProdFinEquiv.symm j).1 i (finProdFinEquiv.symm j).2

theorem measurable_flattenBlockMatrices (d s n : ℕ) :
    Measurable (flattenBlockMatrices (d := d) (s := s) (n := n)) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact (measurable_pi_apply (finProdFinEquiv.symm j).2).comp
    ((measurable_pi_apply i).comp (measurable_pi_apply (finProdFinEquiv.symm j).1))

def krylovRightBlocks {a b s n : ℕ} (data : Fin n → KrylovBlockPair a b s) :
    Matrix (Fin b) (Fin (n * s)) ℝ := flattenBlockMatrices (fun i => (data i).1)

def krylovImageBlocks {a b s n : ℕ} (data : Fin n → KrylovBlockPair a b s) :
    Matrix (Fin a) (Fin (n * s)) ℝ := flattenBlockMatrices (fun i => (data i).2)

theorem measurable_krylovRightBlocks (a b s n : ℕ) :
    Measurable (krylovRightBlocks (a := a) (b := b) (s := s) (n := n)) :=
  (measurable_flattenBlockMatrices b s n).comp
    (measurable_pi_lambda _ (fun i => (measurable_pi_apply i).fst))

theorem measurable_krylovImageBlocks (a b s n : ℕ) :
    Measurable (krylovImageBlocks (a := a) (b := b) (s := s) (n := n)) :=
  (measurable_flattenBlockMatrices a s n).comp
    (measurable_pi_lambda _ (fun i => (measurable_pi_apply i).snd))

theorem krylovRightBlocks_column {a b s n : ℕ}
    (data : Fin n → KrylovBlockPair a b s) (i : Fin n) (j : Fin s) (r : Fin b) :
    krylovRightBlocks data r (finProdFinEquiv (i, j)) = (data i).1 r j := by
  simp only [krylovRightBlocks, flattenBlockMatrices, Equiv.symm_apply_apply]

theorem krylovImageBlocks_mul {a b s n : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (U : Matrix (Fin a) (Fin s) ℝ) :
    krylovImageBlocks (krylovBlockData A n U) = A * krylovRightBlocks (krylovBlockData A n U) := by
  ext i j
  simp only [krylovImageBlocks, krylovRightBlocks, flattenBlockMatrices,
    krylovBlockData_power, Matrix.mul_apply]

def krylovCompressedMatrix {a b s n : ℕ} (data : Fin n → KrylovBlockPair a b s) :
    Matrix (Fin a) (Fin b) ℝ :=
  columnRangeImage (krylovRightBlocks data) (krylovImageBlocks data)

theorem measurable_krylovCompressedMatrix (a b s n : ℕ) :
    Measurable (krylovCompressedMatrix (a := a) (b := b) (s := s) (n := n)) :=
  (measurable_columnRangeImage a b (n * s)).comp
    ((measurable_krylovRightBlocks a b s n).prodMk (measurable_krylovImageBlocks a b s n))

theorem krylovCompressedMatrix_eq {a b s n : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (U : Matrix (Fin a) (Fin s) ℝ) :
    krylovCompressedMatrix (krylovBlockData A n U) =
      A * columnRangeProjector (krylovRightBlocks (krylovBlockData A n U)) := by
  rw [krylovCompressedMatrix, krylovImageBlocks_mul, columnRangeImage_mul]

theorem krylovProjector_fixes_power {a b s n : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (U : Matrix (Fin a) (Fin s) ℝ) (i : Fin n) :
    columnRangeProjector (krylovRightBlocks (krylovBlockData A n U)) *
        ((Aᵀ * A) ^ i.val * (Aᵀ * U)) = (Aᵀ * A) ^ i.val * (Aᵀ * U) := by
  have h := columnRangeProjector_fixes (krylovRightBlocks (krylovBlockData A n U))
  ext r j
  have hentry := congrFun (congrFun h r) (finProdFinEquiv (i, j))
  simpa only [Matrix.mul_apply, krylovRightBlocks_column, krylovBlockData_power] using hentry

theorem krylovProjector_fixes_polynomial {a b s n : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (U : Matrix (Fin a) (Fin s) ℝ) (coeff : Fin n → ℝ) :
    columnRangeProjector (krylovRightBlocks (krylovBlockData A n U)) *
        (∑ i : Fin n, coeff i • ((Aᵀ * A) ^ i.val * (Aᵀ * U))) =
      ∑ i : Fin n, coeff i • ((Aᵀ * A) ^ i.val * (Aᵀ * U)) := by
  rw [Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_smul, krylovProjector_fixes_power]

end
end LowRank
