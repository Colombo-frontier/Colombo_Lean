import GradientHessian.ReadoutCertificate
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The actual linear readout on orthonormal coordinates of the marked range,
and the deterministic reduction of a readout hit to a spherical linear test. -/

namespace GradientHessian.ReadoutMarks
open Matrix Polynomial LowRank ReadoutOracle ReadoutNormalization ReadoutCertificate
  MatrixAnalyticNorms
open scoped InnerProductSpace
noncomputable section

theorem mark_norm {d r : ℕ} (B : Matrix (Fin d) (Fin r) ℝ) (hB : Bᵀ * B = 1)
    (z : EuclideanSpace ℝ (Fin r)) : ‖matrixEuclideanMap B z‖ = ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← euclidean_dot_self, ← euclidean_dot_self]
  change (B *ᵥ ⇑z) ⬝ᵥ (B *ᵥ ⇑z) = (⇑z) ⬝ᵥ ⇑z
  have h := quadratic_coordinates B 1 (⇑z)
  simpa only [Matrix.mul_one, hB, Matrix.one_mulVec] using h

theorem mark_in_range {d r : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (B : Matrix (Fin d) (Fin r) ℝ) (hPB : P * B = B)
    (z : EuclideanSpace ℝ (Fin r)) :
    P *ᵥ ⇑(matrixEuclideanMap B z) = ⇑(matrixEuclideanMap B z) := by
  change P *ᵥ (B *ᵥ ⇑z) = B *ᵥ ⇑z
  rw [Matrix.mulVec_mulVec, hPB]

def markReadoutMap {d r n : ℕ} (J : ℕ) (P : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin n) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) :
    EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  matrixEuclideanMap ((1 - P) *
    aeval (MatrixGoodSpectrum.sourceMatrix P J X)
      (ReadoutFilter.filterPolynomial (ReadoutFilter.matrixUpper J) ReadoutFilter.delta) * B)

theorem markReadoutMap_apply {d r n : ℕ} (J : ℕ) (P : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin n) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (z : EuclideanSpace ℝ (Fin r)) :
    markReadoutMap J P X B z = matrixEuclideanMap (1 - P)
      (matrixEuclideanMap (aeval (MatrixGoodSpectrum.sourceMatrix P J X)
        (ReadoutFilter.filterPolynomial (ReadoutFilter.matrixUpper J) ReadoutFilter.delta))
          (matrixEuclideanMap B z)) := by
  simp only [markReadoutMap, matrixEuclideanMap_mul, ContinuousLinearMap.comp_apply]

theorem markReadoutMap_bounds {d r n : ℕ} {J : ℕ} (hJ : 4 ≤ J)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    {X : Matrix (Fin d) (Fin n) ℝ} (hX : X ∈ MatrixKernelConcentration.sourceGoodEvent P J)
    (B : Matrix (Fin d) (Fin r) ℝ) (hB : Bᵀ * B = 1) (hPB : P * B = B)
    (z : EuclideanSpace ℝ (Fin r)) (hz : ‖z‖ = 1) :
    2 / 5 ≤ ‖markReadoutMap J P X B z‖ ∧ ‖markReadoutMap J P X B z‖ ≤ 3 / 5 := by
  have h := (source_readout_certificate hP hJ hX 0 (matrixEuclideanMap B z)
    ((mark_norm B hB z).trans hz) (mark_in_range P B hPB z)).1
  simpa only [← ContinuousLinearMap.comp_apply,
    ← matrixEuclideanMap_mul, Matrix.mul_assoc, hPB, markReadoutMap] using h

theorem markReadoutMap_opNorm {d r n : ℕ} {J : ℕ} (hJ : 4 ≤ J)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    {X : Matrix (Fin d) (Fin n) ℝ} (hX : X ∈ MatrixKernelConcentration.sourceGoodEvent P J)
    (B : Matrix (Fin d) (Fin r) ℝ) (hB : Bᵀ * B = 1) (hPB : P * B = B) :
    ‖markReadoutMap J P X B‖ ≤ 3 / 5 :=
  ContinuousLinearMap.opNorm_le_of_unit_norm (by norm_num)
    (fun z hz => (markReadoutMap_bounds hJ hP hX B hB hPB z hz).2)

theorem source_readout_eq_direction {d r n : ℕ} {J : ℕ} (hJ : 4 ≤ J)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    {X : Matrix (Fin d) (Fin n) ℝ} (hX : X ∈ MatrixKernelConcentration.sourceGoodEvent P J)
    (B : Matrix (Fin d) (Fin r) ℝ) (hB : Bᵀ * B = 1) (hPB : P * B = B)
    (fallback : Fin d → ℝ) (z : EuclideanSpace ℝ (Fin r)) (hz : ‖z‖ = 1) :
    (WithLp.equiv 2 (Fin d → ℝ)).symm
      (readout (ReadoutFilter.matrixUpper J) P (MatrixGoodSpectrum.sourceMatrix P J X)
        fallback ⇑(matrixEuclideanMap B z)) = direction (markReadoutMap J P X B z) := by
  have hp : 0 < ‖markReadoutMap J P X B z‖ :=
    lt_of_lt_of_le (by norm_num) (markReadoutMap_bounds hJ hP hX B hB hPB z hz).1
  rw [markReadoutMap_apply] at hp ⊢
  exact readout_lift_eq_direction _ P _ fallback (matrixEuclideanMap B z) hp

theorem direction_hit_linear {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) (z : E) (y : F) {γ : ℝ} (hγ : 0 ≤ γ)
    (hl : 2 / 5 ≤ ‖L z‖) (hh : γ < |⟪direction (L z), y⟫_ℝ|) :
    (2 / 5) * γ < |⟪ContinuousLinearMap.adjoint L y, z⟫_ℝ| := by
  have hp : 0 < ‖L z‖ := by linarith
  rw [direction, real_inner_smul_left, abs_mul, abs_inv, abs_norm] at hh
  have hmul : γ * ‖L z‖ < |⟪L z, y⟫_ℝ| :=
    (lt_div_iff₀ hp).mp (by simpa only [div_eq_mul_inv, mul_comm] using hh)
  rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  exact (by nlinarith [mul_le_mul_of_nonneg_right hl hγ] : (2 / 5) * γ ≤ γ * ‖L z‖).trans_lt hmul

theorem adjoint_test_norm {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 3 / 5) (y : F) (hy : ‖y‖ ≤ 1) :
    ‖ContinuousLinearMap.adjoint L y‖ ≤ 3 / 5 := by
  have h := (ContinuousLinearMap.adjoint L).le_opNorm y
  rw [ContinuousLinearMap.adjoint.norm_map] at h
  exact h.trans ((mul_le_mul hL hy (norm_nonneg _) (by norm_num)).trans_eq (by ring))

end
end GradientHessian.ReadoutMarks
