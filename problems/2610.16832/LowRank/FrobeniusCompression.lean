import LowRank.HardTransform

/-! A full matrix compression identity for the special case p=2.
This does not stand in for the general finite-p Schatten theorem. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def frobeniusSq (A : Matrix m n ℝ) : ℝ := ∑ i, ∑ j, (A i j) ^ 2

theorem frobeniusSq_nonneg (A : Matrix m n ℝ) : 0 ≤ frobeniusSq A := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))

theorem frobeniusSq_eq_trace (A : Matrix m n ℝ) :
    frobeniusSq A = (A * Aᵀ).trace := by
  simp only [frobeniusSq, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    transpose_apply, pow_two]

theorem frobeniusSq_residual (H P : Matrix n n ℝ)
    (hH : Hᵀ = H) (hP : IsOrthogonalProjector P) :
    frobeniusSq (H * (1 - P)) = (H * H).trace - (P * (H * H)).trace := by
  rw [frobeniusSq_eq_trace, transpose_mul, hH, hP.complement.symmetric]
  have heq : (H * (1 - P)) * ((1 - P) * H) = H * (1 - P) * H := by
    calc
      _ = H * ((1 - P) * (1 - P)) * H := by noncomm_ring
      _ = _ := by rw [hP.complement.idempotent]
  rw [heq, Matrix.trace_mul_cycle, Matrix.trace_mul_comm (H * H) (1 - P)]
  simp only [sub_mul, one_mul, Matrix.trace_sub]

/-- If K consists of unit eigenvectors of H, comparing the actual p=2 residual
with K bounds the compression deficit by `3 ε d` for ε≤1 and H²≤I. -/
theorem frobenius_relative_compression {H P K : Matrix n n ℝ} {k ε : ℝ}
    (hH : Hᵀ = H) (hP : IsOrthogonalProjector P) (hK : IsOrthogonalProjector K)
    (hKrank : K.trace = k) (hKunit : K * (H * H) = K)
    (hHbound : LoewnerLE (H * H) 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hsuccess : frobeniusSq (H * (1 - P)) ≤
      (1 + ε) ^ 2 * frobeniusSq (H * (1 - K))) :
    k - (P * (H * H)).trace ≤ 3 * ε * Fintype.card n := by
  have hres := frobeniusSq_nonneg (H * (1 - K))
  have htrace : (H * H).trace ≤ Fintype.card n := by
    have h := psd_trace_nonneg hHbound
    rw [Matrix.trace_sub, Matrix.trace_one] at h
    linarith
  have hk0 : 0 ≤ k := hKrank ▸ psd_trace_nonneg hK.posSemidef
  have hresle : frobeniusSq (H * (1 - K)) ≤ Fintype.card n := by
    rw [frobeniusSq_residual H K hH hK, hKunit, hKrank]
    linarith
  have hs : (1 + ε) ^ 2 - 1 ≤ 3 * ε := by nlinarith
  have he := mul_le_mul_of_nonneg_right hs hres
  have he' := mul_le_mul_of_nonneg_left hresle (show 0 ≤ 3 * ε by positivity)
  rw [frobeniusSq_residual H P hH hP] at hsuccess
  rw [frobeniusSq_residual H K hH hK, hKunit, hKrank] at hsuccess he he'
  nlinarith

end LowRank
