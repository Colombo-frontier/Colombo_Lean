import Matvec.KernelFrame
import Matvec.GaussianCompression
import Matvec.LeastStretchContinuity
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! Fresh Gaussian core for a fixed low-rank shift. The output-space rotation
is constructed from the left factor of the shift, and the right kernel frame
is selected measurably from the exposed shifted rows. -/

namespace Matvec
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators
noncomputable section

def splitGaussianRows (q ℓ d : ℕ) (X : Matrix (Fin (q + ℓ)) (Fin d) ℝ) :
    Matrix (Fin q) (Fin d) ℝ × Matrix (Fin ℓ) (Fin d) ℝ :=
  (fun i => X (finSumFinEquiv (Sum.inl i)), fun i => X (finSumFinEquiv (Sum.inr i)))

theorem splitGaussianRows_preserving (q ℓ d : ℕ) (v : NNReal) :
    MeasurePreserving (splitGaussianRows q ℓ d) (LowRank.iidMatrixLaw (q + ℓ) d v)
      ((LowRank.iidMatrixLaw q d v).prod (LowRank.iidMatrixLaw ℓ d v)) := by
  let e : Fin q ⊕ Fin ℓ ≃ Fin (q + ℓ) := finSumFinEquiv
  have hr := (measurePreserving_piCongrLeft
    (fun _ : Fin (q + ℓ) => LowRank.iidVectorLaw d v) e).symm
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (q + ℓ) => Fin d → ℝ) e)
  have hs := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin q ⊕ Fin ℓ => LowRank.iidVectorLaw d v)
  exact hs.comp hr

/-- Orthonormal basis of the kernel of the shift's left factor transpose. -/
def shiftBottomFrame {q ℓ : ℕ} (C : Matrix (Fin (q + ℓ)) (Fin q) ℝ) := kernelFrame Cᵀ ℓ

/-- Complete the bottom frame to a square orthonormal basis. -/
def shiftTopFrame {q ℓ : ℕ} (C : Matrix (Fin (q + ℓ)) (Fin q) ℝ) :=
  kernelFrame (shiftBottomFrame C)ᵀ q

def shiftFullFrame {q ℓ : ℕ} (C : Matrix (Fin (q + ℓ)) (Fin q) ℝ) :
    Matrix (Fin (q + ℓ)) (Fin q ⊕ Fin ℓ) ℝ :=
  Matrix.fromCols (shiftTopFrame C) (shiftBottomFrame C)

theorem shiftFullFrame_orthogonal {q ℓ : ℕ} (C : Matrix (Fin (q + ℓ)) (Fin q) ℝ) :
    (shiftFullFrame C)ᵀ * shiftFullFrame C = 1 := by
  have hb : (shiftBottomFrame C)ᵀ * shiftBottomFrame C = 1 := kernelFrame_orthonormal Cᵀ le_rfl
  have ht : (shiftTopFrame C)ᵀ * shiftTopFrame C = 1 :=
    kernelFrame_orthonormal _ (by omega)
  have hbt : (shiftBottomFrame C)ᵀ * shiftTopFrame C = 0 := mul_kernelFrame _ q
  have htb : (shiftTopFrame C)ᵀ * shiftBottomFrame C = 0 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero]
      using congrArg Matrix.transpose hbt
  rw [shiftFullFrame, Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, ht, hb, hbt, htb]
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.one_apply]

theorem shiftFullFrame_complete {q ℓ : ℕ} (C : Matrix (Fin (q + ℓ)) (Fin q) ℝ) :
    shiftFullFrame C * (shiftFullFrame C)ᵀ = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv (finSumFinEquiv : Fin q ⊕ Fin ℓ ≃ Fin (q + ℓ))).mp
    (shiftFullFrame_orthogonal C)

/-- Square coordinate rotation with the shift confined to its first `q` rows. -/
def shiftRowRotation {q ℓ : ℕ} (C : Matrix (Fin (q + ℓ)) (Fin q) ℝ) :
    Matrix (Fin (q + ℓ)) (Fin (q + ℓ)) ℝ :=
  (shiftFullFrame C)ᵀ.submatrix finSumFinEquiv.symm id

theorem shiftRowRotation_orthogonal {q ℓ : ℕ} (C : Matrix (Fin (q + ℓ)) (Fin q) ℝ) :
    shiftRowRotation C * (shiftRowRotation C)ᵀ = 1 := by
  have h := congrArg (fun X => X.submatrix finSumFinEquiv.symm finSumFinEquiv.symm)
    (shiftFullFrame_orthogonal C)
  simpa only [shiftRowRotation, Matrix.transpose_submatrix, Matrix.submatrix_mul,
    Matrix.submatrix_one_equiv, Matrix.submatrix_id_id] using h

theorem shiftBottomFrame_annihilates {q ℓ : ℕ} (C : Matrix (Fin (q + ℓ)) (Fin q) ℝ) :
    (shiftBottomFrame C)ᵀ * C = 0 := by
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero]
    using congrArg Matrix.transpose (mul_kernelFrame Cᵀ ℓ)

theorem shiftRowRotation_bottom_shift {q ℓ : ℕ}
    (C : Matrix (Fin (q + ℓ)) (Fin q) ℝ) (B : Matrix (Fin q) (Fin (q + ℓ)) ℝ) :
    (splitGaussianRows q ℓ (q + ℓ) (shiftRowRotation C * (C * B))).2 = 0 := by
  ext i j
  have hz : (shiftBottomFrame C)ᵀ * (C * B) = 0 := by
    rw [← Matrix.mul_assoc, shiftBottomFrame_annihilates, Matrix.zero_mul]
  have h := congrFun (congrFun hz i) j
  simpa [splitGaussianRows, shiftRowRotation, shiftFullFrame, Matrix.mul_apply,
    Matrix.fromCols, Matrix.submatrix, Matrix.transpose_apply] using h

def lowRankShiftKernel {q ℓ : ℕ} (C : Matrix (Fin (q + ℓ)) (Fin q) ℝ)
    (B : Matrix (Fin q) (Fin (q + ℓ)) ℝ)
    (Y : Matrix (Fin q) (Fin (q + ℓ)) ℝ) : Matrix (Fin (q + ℓ)) (Fin ℓ) ℝ :=
  kernelFrame (Y - (splitGaussianRows q ℓ (q + ℓ) (shiftRowRotation C * (C * B))).1) ℓ

theorem measurable_lowRankShiftKernel {q ℓ : ℕ}
    (C : Matrix (Fin (q + ℓ)) (Fin q) ℝ) (B : Matrix (Fin q) (Fin (q + ℓ)) ℝ) :
    Measurable (lowRankShiftKernel C B) := by
  apply (measurable_kernelFrame q (q + ℓ) ℓ).comp
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  change Measurable (fun Y : Matrix (Fin q) (Fin (q + ℓ)) ℝ => Y i j -
    (splitGaussianRows q ℓ (q + ℓ) (shiftRowRotation C * (C * B))).1 i j)
  exact ((measurable_pi_apply j).comp (measurable_pi_apply i)).sub measurable_const

theorem lowRankShiftKernel_orthogonal {q ℓ : ℕ}
    (C : Matrix (Fin (q + ℓ)) (Fin q) ℝ) (B : Matrix (Fin q) (Fin (q + ℓ)) ℝ)
    (Y : Matrix (Fin q) (Fin (q + ℓ)) ℝ) :
    (lowRankShiftKernel C B Y)ᵀ * lowRankShiftKernel C B Y = 1 :=
  kernelFrame_orthonormal _ le_rfl

def lowRankShiftCore {q ℓ : ℕ} (C : Matrix (Fin (q + ℓ)) (Fin q) ℝ)
    (B : Matrix (Fin q) (Fin (q + ℓ)) ℝ)
    (X : Matrix (Fin (q + ℓ)) (Fin (q + ℓ)) ℝ) : Matrix (Fin ℓ) (Fin ℓ) ℝ :=
  let p := splitGaussianRows q ℓ (q + ℓ) (shiftRowRotation C * X)
  p.2 * lowRankShiftKernel C B p.1

theorem lowRankShiftCore_preserving {q ℓ : ℕ}
    (C : Matrix (Fin (q + ℓ)) (Fin q) ℝ) (B : Matrix (Fin q) (Fin (q + ℓ)) ℝ)
    (v : NNReal) :
    MeasurePreserving (lowRankShiftCore C B) (LowRank.iidMatrixLaw (q + ℓ) (q + ℓ) v)
      (LowRank.iidMatrixLaw ℓ ℓ v) := by
  have hr := LowRank.iidMatrixLaw_left_compression_preserving (r := q + ℓ)
    (shiftRowRotation C)ᵀ (by simpa using shiftRowRotation_orthogonal C) v
  have hs := (splitGaussianRows_preserving q ℓ (q + ℓ) v).comp hr
  have hc := state_dependent_gaussian_compression (r := ℓ)
    (LowRank.iidMatrixLaw q (q + ℓ) v) (lowRankShiftKernel C B)
    (measurable_lowRankShiftKernel C B) (lowRankShiftKernel_orthogonal C B) v
  have hp := hc.comp hs
  have hsnd : MeasurePreserving Prod.snd
      ((LowRank.iidMatrixLaw q (q + ℓ) v).prod (LowRank.iidMatrixLaw ℓ ℓ v))
      (LowRank.iidMatrixLaw ℓ ℓ v) := ⟨measurable_snd, by simp⟩
  exact hsnd.comp hp

theorem lowRankShiftCore_annihilation {q ℓ : ℕ}
    (C : Matrix (Fin (q + ℓ)) (Fin q) ℝ) (B : Matrix (Fin q) (Fin (q + ℓ)) ℝ)
    (X : Matrix (Fin (q + ℓ)) (Fin (q + ℓ)) ℝ) :
    let p := splitGaussianRows q ℓ (q + ℓ) (shiftRowRotation C * X)
    (splitGaussianRows q ℓ (q + ℓ) (shiftRowRotation C * (X - C * B))).1 *
      lowRankShiftKernel C B p.1 = 0 := by
  have h := mul_kernelFrame
    ((splitGaussianRows q ℓ (q + ℓ) (shiftRowRotation C * X)).1 -
      (splitGaussianRows q ℓ (q + ℓ) (shiftRowRotation C * (C * B))).1) ℓ
  simpa [lowRankShiftKernel, splitGaussianRows, Matrix.mul_sub] using h

theorem lowRankShiftCore_bottom {q ℓ : ℕ}
    (C : Matrix (Fin (q + ℓ)) (Fin q) ℝ) (B : Matrix (Fin q) (Fin (q + ℓ)) ℝ)
    (X : Matrix (Fin (q + ℓ)) (Fin (q + ℓ)) ℝ) :
    let p := splitGaussianRows q ℓ (q + ℓ) (shiftRowRotation C * X)
    (splitGaussianRows q ℓ (q + ℓ) (shiftRowRotation C * (X - C * B))).2 *
      lowRankShiftKernel C B p.1 = lowRankShiftCore C B X := by
  have h := shiftRowRotation_bottom_shift C B
  have hs : (splitGaussianRows q ℓ (q + ℓ) (shiftRowRotation C * (X - C * B))).2 =
      (splitGaussianRows q ℓ (q + ℓ) (shiftRowRotation C * X)).2 -
      (splitGaussianRows q ℓ (q + ℓ) (shiftRowRotation C * (C * B))).2 := by
    ext i j
    simp [splitGaussianRows, Matrix.mul_sub]
  dsimp only
  rw [hs, h, sub_zero]
  rfl

end
end Matvec
