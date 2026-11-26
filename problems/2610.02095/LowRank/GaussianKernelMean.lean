import LowRank.KernelProjectorMeasurable
import LowRank.KernelProjectorSymmetry
import LowRank.GaussianMatrixSymmetry
import LowRank.GaussianFullRank

/-! Compute the mean of the actual Gaussian left-kernel projector. Finite
sign and permutation symmetries force a scalar matrix; its trace identifies
the scalar. No isotropy premise is assumed. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

theorem gaussianKernelMean_offdiag (r s : ℕ) (v : NNReal) (i j : Fin r) (hij : i ≠ j) :
    matrixMean (iidMatrixLaw r s v) leftKernelProjector i j = 0 := by
  let a : Fin r → ℝ := fun k => if k = i then -1 else 1
  have ha : ∀ k, a k * a k = 1 := by intro k; dsimp [a]; split_ifs <;> norm_num
  have hp := iidMatrixLaw_signed_rows_preserving r s a ha v
  have hm : Measurable (fun D : Matrix (Fin r) (Fin s) ℝ => leftKernelProjector D i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_leftKernelProjector)
  have h := integral_map_of_stronglyMeasurable (μ := iidMatrixLaw r s v) hp.measurable hm.stronglyMeasurable
  rw [hp.map_eq] at h
  have he : ∀ D : Matrix (Fin r) (Fin s) ℝ,
      leftKernelProjector (fun k l => a k * D k l) i j = -leftKernelProjector D i j := by
    intro D
    rw [leftKernelProjector_signed_rows D a ha]
    simp [a, hij, Ne.symm hij]
  simp_rw [he] at h
  rw [integral_neg] at h
  change matrixMean (iidMatrixLaw r s v) leftKernelProjector i j =
    -matrixMean (iidMatrixLaw r s v) leftKernelProjector i j at h
  linarith

theorem gaussianKernelMean_diag_eq (r s : ℕ) (v : NNReal) (i j : Fin r) :
    matrixMean (iidMatrixLaw r s v) leftKernelProjector i i =
      matrixMean (iidMatrixLaw r s v) leftKernelProjector j j := by
  have hp := iidMatrixLaw_reindex_rows_preserving r s (Equiv.swap i j) v
  have hm : Measurable (fun D : Matrix (Fin r) (Fin s) ℝ => leftKernelProjector D i i) :=
    (measurable_pi_apply i).comp ((measurable_pi_apply i).comp measurable_leftKernelProjector)
  have h := integral_map_of_stronglyMeasurable (μ := iidMatrixLaw r s v) hp.measurable hm.stronglyMeasurable
  rw [hp.map_eq] at h
  simpa only [leftKernelProjector_reindex_rows, Matrix.submatrix_apply,
    Equiv.swap_apply_left] using h

theorem gaussianKernelMean_trace (r s : ℕ) (hs : s ≤ r) {v : NNReal} (hv : v ≠ 0) :
    (matrixMean (iidMatrixLaw r s v) leftKernelProjector).trace = (r : ℝ) - s := by
  rw [matrixMean_trace (leftKernelProjector_entryIntegrable _)]
  calc
    _ = ∫ _ : Matrix (Fin r) (Fin s) ℝ, ((r : ℝ) - s) ∂iidMatrixLaw r s v := by
      apply integral_congr_ae
      filter_upwards [iidMatrixLaw_mulVec_injective_ae r s hs hv] with D hD
      simpa only [Fintype.card_fin] using leftKernelProjector_trace D hD
    _ = _ := by simp

theorem gaussianKernelMean_isotropic (r s : ℕ) (hs : s ≤ r) {v : NNReal} (hv : v ≠ 0) :
    matrixMean (iidMatrixLaw r s v) leftKernelProjector =
      (((r : ℝ) - s) / r) • (1 : Matrix (Fin r) (Fin r) ℝ) := by
  have hd : ∀ i : Fin r, matrixMean (iidMatrixLaw r s v) leftKernelProjector i i =
      ((r : ℝ) - s) / r := by
    intro i
    have ht : (matrixMean (iidMatrixLaw r s v) leftKernelProjector).trace =
        (r : ℝ) * matrixMean (iidMatrixLaw r s v) leftKernelProjector i i := by
      unfold Matrix.trace Matrix.diag
      simp_rw [gaussianKernelMean_diag_eq r s v _ i]
      simp [Matrix.diag, nsmul_eq_mul]
    have hr : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt))
    apply (eq_div_iff hr).mpr
    rw [mul_comm, ← ht, gaussianKernelMean_trace r s hs hv]
  ext i j
  by_cases hij : i = j
  · subst j
    simpa only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] using hd i
  · simp only [gaussianKernelMean_offdiag r s v i j hij, Matrix.smul_apply,
      Matrix.one_apply_ne hij, smul_eq_mul, mul_zero]

theorem gaussianKernelMean_nullity_ratio (k s : ℕ) {v : NNReal} (hv : v ≠ 0) :
    matrixMean (iidMatrixLaw (k + s) s v) leftKernelProjector =
      ((k : ℝ) / (k + s)) • (1 : Matrix (Fin (k + s)) (Fin (k + s)) ℝ) := by
  simpa only [Nat.cast_add, add_sub_cancel_right] using
    gaussianKernelMean_isotropic (k + s) s (by omega) hv

end
end LowRank
