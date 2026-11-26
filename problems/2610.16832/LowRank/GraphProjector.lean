import LowRank.MatrixOrder
import Mathlib.Data.Matrix.Block

/-! Bottom-block domination for a projected graph, without matrix inverses. -/

namespace LowRank
open Matrix
open scoped Matrix

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

/-- A positive contraction supported on a subspace is bounded by that subspace's
orthogonal projector. -/
theorem contraction_le_support_projector {M Q : Matrix b b ℝ}
    (hM : M.PosSemidef) (hM1 : LoewnerLE M 1)
    (hQ : IsOrthogonalProjector Q) (hsupport : Q * M = M) : LoewnerLE M Q := by
  have hsym : Mᵀ = M := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hM.isHermitian.eq
  have hsupport' : M * Q = M := by
    have h := congrArg Matrix.transpose hsupport
    simpa only [transpose_mul, hQ.symmetric, hsym] using h
  have h := loewner_congruence hM1 Q
  simpa only [hQ.symmetric, hsupport, hsupport', mul_one, hQ.idempotent] using h

/-- Deterministic domination of the bottom block of an orthogonal projector.
The support hypothesis follows when the full space is a graph over `range Q`. -/
theorem bottom_block_le_of_support {K : Matrix (a ⊕ b) (a ⊕ b) ℝ}
    {Q : Matrix b b ℝ} (hK : IsOrthogonalProjector K)
    (hQ : IsOrthogonalProjector Q)
    (hsupport : Q * K.submatrix Sum.inr Sum.inr = K.submatrix Sum.inr Sum.inr) :
    LoewnerLE (K.submatrix Sum.inr Sum.inr) Q := by
  have hM := hK.posSemidef.submatrix (Sum.inr : b → a ⊕ b)
  have hM1 : LoewnerLE (K.submatrix Sum.inr Sum.inr) 1 := by
    have h := hK.complement.posSemidef.submatrix (Sum.inr : b → a ⊕ b)
    have hI : (1 : Matrix (a ⊕ b) (a ⊕ b) ℝ).submatrix Sum.inr Sum.inr = 1 := by
      ext i j
      simp [Matrix.one_apply]
    simpa only [LoewnerLE, submatrix_sub, Pi.sub_apply, hI] using h
  exact contraction_le_support_projector hM hM1 hQ hsupport

/-- Converts a vectorwise bottom-range inclusion into the support identity. -/
theorem bottom_support_of_range {K : Matrix (a ⊕ b) (a ⊕ b) ℝ}
    {Q : Matrix b b ℝ}
    (h : ∀ v : a ⊕ b → ℝ,
      Q *ᵥ ((K *ᵥ v) ∘ Sum.inr) = (K *ᵥ v) ∘ Sum.inr) :
    Q * K.submatrix Sum.inr Sum.inr = K.submatrix Sum.inr Sum.inr := by
  ext i j
  have hv := congrFun (h (Pi.single (Sum.inr j) 1)) i
  simpa [mulVec_single_one, Matrix.mul_apply, mulVec, dotProduct] using hv

end LowRank
