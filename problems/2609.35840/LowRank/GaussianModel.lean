import LowRank.MatrixOrder
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.MeasureTheory.Constructions.Pi

/-! The actual rectangular Gaussian distribution and its matrix transformations.
This file does not establish the adaptive deferred-decision theorem. -/

namespace LowRank
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix

instance matrixMeasurableSpace (a b : Type*) : MeasurableSpace (Matrix a b ℝ) :=
  inferInstanceAs (MeasurableSpace (a → b → ℝ))

instance matrixBorelSpace (a b : Type*) [Fintype a] [Fintype b] :
    BorelSpace (Matrix a b ℝ) := inferInstanceAs (BorelSpace (a → b → ℝ))

noncomputable def gaussianMatrixLaw (d s : ℕ) : Measure (Matrix (Fin d) (Fin s) ℝ) :=
  Measure.pi (fun _ : Fin d => Measure.pi
    (fun _ : Fin s => gaussianReal 0 (d : NNReal)⁻¹))

instance gaussianMatrixLaw_probability (d s : ℕ) :
    IsProbabilityMeasure (gaussianMatrixLaw d s) := by
  unfold gaussianMatrixLaw
  exact Measure.pi.instIsProbabilityMeasure _

def wishart {d s : ℕ} (X : Matrix (Fin d) (Fin s) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  X * Xᵀ

noncomputable def hardMatrix {d : ℕ} (L : ℝ) (W : Matrix (Fin d) (Fin d) ℝ) :=
  1 - L⁻¹ • W

theorem wishart_posSemidef {d s : ℕ} (X : Matrix (Fin d) (Fin s) ℝ) :
    (wishart X).PosSemidef := by
  simpa only [wishart, conjTranspose_eq_transpose_of_trivial]
    using Matrix.posSemidef_self_mul_conjTranspose X

theorem wishart_symmetric {d s : ℕ} (X : Matrix (Fin d) (Fin s) ℝ) :
    (wishart X)ᵀ = wishart X := by simp [wishart, transpose_mul]

theorem hardMatrix_symmetric {d : ℕ} (L : ℝ) {W : Matrix (Fin d) (Fin d) ℝ}
    (hW : Wᵀ = W) : (hardMatrix L W)ᵀ = hardMatrix L W := by
  simp [hardMatrix, transpose_sub, transpose_smul, hW]

theorem hardMatrix_matvec {d : ℕ} (L : ℝ) (W : Matrix (Fin d) (Fin d) ℝ)
    (v : Fin d → ℝ) : hardMatrix L W *ᵥ v = v - L⁻¹ • (W *ᵥ v) := by
  simp [hardMatrix, sub_mulVec, smul_mulVec_assoc]

theorem recover_wishart_matvec {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    (W : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    L • (v - hardMatrix L W *ᵥ v) = W *ᵥ v := by
  rw [hardMatrix_matvec, sub_sub_cancel, smul_smul, mul_inv_cancel₀ hL, one_smul]

theorem measurable_wishart (d s : ℕ) :
    Measurable (wishart : Matrix (Fin d) (Fin s) ℝ → Matrix (Fin d) (Fin d) ℝ) := by
  unfold wishart
  change Measurable (fun X : Fin d → Fin s → ℝ =>
    fun i j => ∑ t, X i t * X j t)
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  apply Finset.measurable_sum
  intro t _
  exact ((measurable_pi_apply t).comp (measurable_pi_apply i)).mul
    ((measurable_pi_apply t).comp (measurable_pi_apply j))

theorem measurable_hardMatrix (d : ℕ) (L : ℝ) :
    Measurable (hardMatrix L : Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ) := by
  unfold hardMatrix
  fun_prop

end LowRank
