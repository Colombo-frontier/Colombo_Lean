import LowRank.ProjectorRank
import LowRank.GaussianKernelMean

/-! The explicit projector used in the probability estimates is the
orthogonal projector onto the actual Wishart kernel, almost surely.
Its rank and trace equal the rectangular nullity. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

theorem leftKernelProjector_gram_range {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (X : Matrix a b ℝ) (hX : Function.Injective X.mulVec) :
    LinearMap.range (leftKernelProjector X).mulVecLin = LinearMap.ker (X * Xᵀ).mulVecLin := by
  rw [leftKernelProjector_range X hX]
  ext z
  exact (gram_kernel_iff X z).symm

theorem leftKernelProjector_mul_gram {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (X : Matrix a b ℝ) (hX : Function.Injective X.mulVec) :
    leftKernelProjector X * (X * Xᵀ) = 0 := by
  have h := congrArg Matrix.transpose (transpose_mul_leftKernelProjector X hX)
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero,
    (leftKernelProjector_isProjector X).symmetric] at h
  rw [← Matrix.mul_assoc, h, Matrix.zero_mul]

theorem iidMatrixLaw_kernel_projector_spec_ae (d s : ℕ) (hs : s ≤ d) {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ X ∂iidMatrixLaw d s v,
      LinearMap.range (leftKernelProjector X).mulVecLin = LinearMap.ker (wishart X).mulVecLin ∧
        leftKernelProjector X * wishart X = 0 ∧
        (leftKernelProjector X).trace = (d - s : ℕ) ∧ (leftKernelProjector X).rank = d - s := by
  filter_upwards [iidMatrixLaw_mulVec_injective_ae d s hs hv] with X hX
  have ht : (leftKernelProjector X).trace = (d - s : ℕ) := by
    simpa only [Fintype.card_fin, Nat.cast_sub hs] using leftKernelProjector_trace X hX
  refine ⟨leftKernelProjector_gram_range X hX, leftKernelProjector_mul_gram X hX, ht, ?_⟩
  exact_mod_cast (leftKernelProjector_isProjector X).trace_eq_rank.symm.trans ht

theorem gaussianMatrixLaw_kernel_projector_spec_ae (d s : ℕ) (hd : 0 < d) (hs : s ≤ d) :
    ∀ᵐ X ∂gaussianMatrixLaw d s,
      LinearMap.range (leftKernelProjector X).mulVecLin = LinearMap.ker (wishart X).mulVecLin ∧
        leftKernelProjector X * wishart X = 0 ∧
        (leftKernelProjector X).trace = (d - s : ℕ) ∧ (leftKernelProjector X).rank = d - s := by
  rw [gaussianMatrixLaw_eq_iidMatrixLaw]
  apply iidMatrixLaw_kernel_projector_spec_ae d s hs
  apply inv_ne_zero
  exact_mod_cast Nat.ne_of_gt hd

end
end LowRank
