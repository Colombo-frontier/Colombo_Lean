import GradientHessian.ReadoutFilter
import LowRank.KrylovMatrixPolynomial
import LowRank.MatrixNetBound

/-! Euclidean operator control of the actual polynomial matrix, and the
spectral consequences of the source's analytic matrix inequalities. -/

namespace GradientHessian.ReadoutSpectral

open Matrix Polynomial LowRank
open scoped BigOperators InnerProductSpace
noncomputable section

theorem matrixMap_mul {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) :
    matrixEuclideanMap (A * B) = (matrixEuclideanMap A).comp (matrixEuclideanMap B) := by
  ext v i
  change ((A * B) *ᵥ ⇑v) i = (A *ᵥ (B *ᵥ ⇑v)) i
  rw [Matrix.mulVec_mulVec]

theorem orthogonal_map_norm {d : ℕ} (U : Matrix (Fin d) (Fin d) ℝ)
    (hU : Uᵀ * U = 1) (v : EuclideanSpace ℝ (Fin d)) :
    ‖matrixEuclideanMap U v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← euclidean_dot_self, ← euclidean_dot_self, matrixEuclideanMap_apply]
  exact orthogonal_columns_dot U hU _

theorem orthogonal_map_opNorm_le {d : ℕ} (U : Matrix (Fin d) (Fin d) ℝ)
    (hU : Uᵀ * U = 1) : ‖matrixEuclideanMap U‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [orthogonal_map_norm U hU, one_mul]

theorem diagonal_opNorm_le {d : ℕ} (a : Fin d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (ha : ∀ i, |a i| ≤ B) : ‖matrixEuclideanMap (diagonal a)‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro v
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg v))).mp
  rw [mul_pow, ← euclidean_dot_self, ← euclidean_dot_self, matrixEuclideanMap_apply]
  simp only [dotProduct, mulVec_diagonal, Pi.mul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hs : (a i) ^ 2 ≤ B ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (a i)) hB).mpr (ha i)
    simpa only [sq_abs] using h
  nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg (v i))]

theorem conjugated_diagonal_opNorm_le {d : ℕ} (U : Matrix (Fin d) (Fin d) ℝ)
    (hU : Uᵀ * U = 1) (a : Fin d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (ha : ∀ i, |a i| ≤ B) :
    ‖matrixEuclideanMap (U * diagonal a * Uᵀ)‖ ≤ B := by
  have hUt : Uᵀᵀ * Uᵀ = 1 := by
    rw [transpose_transpose]
    exact Matrix.mul_eq_one_comm.mp hU
  rw [matrixMap_mul, matrixMap_mul]
  calc
    _ ≤ (‖matrixEuclideanMap U‖ * ‖matrixEuclideanMap (diagonal a)‖) *
        ‖matrixEuclideanMap Uᵀ‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (1 * B) * 1 := by
      apply mul_le_mul
      · exact mul_le_mul (orthogonal_map_opNorm_le U hU) (diagonal_opNorm_le a hB ha)
          (norm_nonneg _) zero_le_one
      · exact orthogonal_map_opNorm_le Uᵀ hUt
      · exact norm_nonneg _
      · positivity
    _ = B := by ring

def eigenspaceOne {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum A) : Matrix (Fin d) (Fin d) ℝ :=
  sp.basis * diagonal (fun i => if sp.value i = 1 then 1 else 0) * sp.basisᵀ

theorem filter_error_from_spectrum {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum A) {M tolerance : ℝ} (hM : 16 ≤ M)
    (ht : 0 < tolerance) (hvals : ∀ i, sp.value i = 1 ∨ (5 ≤ sp.value i ∧ sp.value i ≤ M)) :
    ‖matrixEuclideanMap (aeval A (ReadoutFilter.filterPolynomial M tolerance) - eigenspaceOne sp)‖ ≤
      tolerance := by
  have he : aeval A (ReadoutFilter.filterPolynomial M tolerance) - eigenspaceOne sp =
      sp.basis * diagonal (fun i =>
        (ReadoutFilter.filterPolynomial M tolerance).eval (sp.value i) -
          if sp.value i = 1 then 1 else 0) * sp.basisᵀ := by
    rw [sp.aeval_reconstruct, eigenspaceOne, ← Matrix.sub_mul, ← Matrix.mul_sub,
      ← Matrix.diagonal_sub]
  rw [he]
  apply conjugated_diagonal_opNorm_le sp.basis sp.orthogonal _ ht.le
  intro i
  rcases hvals i with hi | hi
  · simp [hi, ReadoutFilter.filterPolynomial_one (by linarith : 5 < M), ht.le]
  · have hn : sp.value i ≠ 1 := by linarith [hi.1]
    simpa only [if_neg hn, sub_zero] using ReadoutFilter.filterPolynomial_tail hM ht hi.1 hi.2

theorem conjugate_projector {d : ℕ} (U Q : Matrix (Fin d) (Fin d) ℝ)
    (hU : Uᵀ * U = 1) (hQ : IsOrthogonalProjector Q) :
    IsOrthogonalProjector (Uᵀ * Q * U) := by
  have hUr := Matrix.mul_eq_one_comm.mp hU
  constructor
  · simp [transpose_mul, hQ.symmetric, Matrix.mul_assoc]
  · calc
      _ = Uᵀ * Q * (U * Uᵀ) * Q * U := by noncomm_ring
      _ = _ := by rw [hUr, mul_one]; simp only [Matrix.mul_assoc, hQ.idempotent]

theorem spectral_projector_and_gap {d : ℕ} {A Q : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum A) (hQ : IsOrthogonalProjector Q) (hAQ : A * Q = Q)
    (hgap : LoewnerLE (Q + (5 : ℝ) • (1 - Q)) A) {M : ℝ} (hupp : LoewnerLE A (M • 1)) :
    eigenspaceOne sp = Q ∧
      ∀ i, sp.value i = 1 ∨ (5 ≤ sp.value i ∧ sp.value i ≤ M) := by
  let B := sp.basisᵀ * Q * sp.basis
  have hB : IsOrthogonalProjector B := conjugate_projector sp.basis Q sp.orthogonal hQ
  have hDB : diagonal sp.value * B = B := by
    calc
      _ = sp.basisᵀ * A * (sp.basis * sp.basisᵀ) * Q * sp.basis := by
        rw [← sp.diagonalizes]
        dsimp only [B]
        noncomm_ring
      _ = B := by
        rw [sp.orthogonal_right, mul_one]
        dsimp only [B]
        calc
          _ = sp.basisᵀ * (A * Q) * sp.basis := by noncomm_ring
          _ = _ := by rw [hAQ]
  have hl : LoewnerLE (B + (5 : ℝ) • (1 - B)) (diagonal sp.value) := by
    have h := loewner_congruence hgap sp.basis
    simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, sp.orthogonal, sp.diagonalizes, B] using h
  have hu : LoewnerLE (diagonal sp.value) (M • 1) := by
    have h := loewner_congruence hupp sp.basis
    simpa only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      sp.orthogonal, sp.diagonalizes] using h
  have hrow : ∀ i, sp.value i ≠ 1 → ∀ j, B i j = 0 := by
    intro i hi j
    have h := congrFun (congrFun hDB i) j
    simp only [Matrix.diagonal_mul] at h
    have hm : (sp.value i - 1) * B i j = 0 := by nlinarith
    exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hi)
  have hdiag : ∀ i, sp.value i = 1 → B i i = 1 := by
    intro i hi
    have hl' := psd_diagonal_nonneg hl i
    have hb' := psd_diagonal_nonneg hB.complement.posSemidef i
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply_eq, Matrix.diagonal_apply_eq, hi] at hl' hb'
    linarith
  have hBeq : B = diagonal (fun i => if sp.value i = 1 then 1 else 0) := by
    ext j i
    by_cases hi : sp.value i = 1
    · have hz : (1 - B) *ᵥ Pi.single i 1 = 0 := by
        apply (hB.complement.posSemidef.dotProduct_mulVec_zero_iff _).mp
        simp [hdiag i hi]
      have hj := congrFun hz j
      simp only [Matrix.mulVec_single_one, Matrix.transpose_apply, Matrix.sub_apply,
        Pi.zero_apply] at hj
      have he : B j i = (1 : Matrix (Fin d) (Fin d) ℝ) j i := by linarith
      rw [he]
      by_cases hji : j = i
      · subst j; simp [hi]
      · simp [Matrix.one_apply, Matrix.diagonal_apply, hji]
    · have hij := hrow i hi j
      have hs := congrFun (congrFun hB.symmetric i) j
      change B j i = B i j at hs
      rw [hs, hij]
      by_cases hji : j = i
      · subst j; simp [hi]
      · simp [Matrix.diagonal_apply, hji]
  constructor
  · rw [eigenspaceOne, ← hBeq]
    dsimp only [B]
    calc
      _ = (sp.basis * sp.basisᵀ) * Q * (sp.basis * sp.basisᵀ) := by noncomm_ring
      _ = Q := by rw [sp.orthogonal_right]; simp
  · intro i
    by_cases hi : sp.value i = 1
    · exact Or.inl hi
    · right
      have hl' := psd_diagonal_nonneg hl i
      have hu' := psd_diagonal_nonneg hu i
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply_eq, Matrix.diagonal_apply_eq, hrow i hi i] at hl' hu'
      constructor <;> linarith

/-- The exact filter-error statement from the article, deduced from its
analytic matrix inequalities and the actual eigenspace projector. -/
theorem filter_error {d : ℕ} {A Q : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (hQ : IsOrthogonalProjector Q) (hAQ : A * Q = Q)
    (hgap : LoewnerLE (Q + (5 : ℝ) • (1 - Q)) A) {M : ℝ} (hM : 16 ≤ M)
    (hupp : LoewnerLE A (M • 1)) :
    ‖matrixEuclideanMap (aeval A (ReadoutFilter.filterPolynomial M ReadoutFilter.delta) - Q)‖ ≤
      ReadoutFilter.delta := by
  let sp := orderedMatrixSpectrum hA
  obtain ⟨he, hv⟩ := spectral_projector_and_gap sp hQ hAQ hgap hupp
  rw [← he]
  exact filter_error_from_spectrum sp hM ReadoutFilter.delta_pos hv

end
end GradientHessian.ReadoutSpectral
