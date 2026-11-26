import GradientHessian.ReadoutSpectral

/-! Exact cross-projection geometry underlying the readout denominator bound. -/

namespace GradientHessian.ReadoutSpectral

open Matrix LowRank
open scoped InnerProductSpace
noncomputable section

theorem loewner_opNorm_le {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    {B : ℝ} (hB : 0 ≤ B) (hl : LoewnerLE ((-B) • 1) A) (hu : LoewnerLE A (B • 1)) :
    ‖matrixEuclideanMap A‖ ≤ B := by
  let sp := orderedMatrixSpectrum hA
  rw [sp.reconstruct]
  apply conjugated_diagonal_opNorm_le sp.basis sp.orthogonal _ hB
  intro i
  exact abs_le.mpr (sp.value_mem_Icc hl hu i)

theorem cross_projection_gram {d : ℕ} {P Q : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q) :
    (((1 - P) * Q * P)ᵀ * ((1 - P) * Q * P)) =
      (1 / 4 : ℝ) • P - (P * Q * P - (1 / 2 : ℝ) • P)^2 := by
  simp only [transpose_mul, transpose_sub, transpose_one, hP.symmetric, hQ.symmetric]
  have hp (X : Matrix (Fin d) (Fin d) ℝ) : P * (P * X) = P * X := by
    rw [← Matrix.mul_assoc, hP.idempotent]
  have hq (X : Matrix (Fin d) (Fin d) ℝ) : Q * (Q * X) = Q * X := by
    rw [← Matrix.mul_assoc, hQ.idempotent]
  noncomm_ring
  simp only [hp, hq, hP.idempotent]
  module

theorem centered_compression_opNorm {d : ℕ} {P Q : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    (hl : LoewnerLE ((1 / 3 : ℝ) • P) (P * Q * P))
    (hu : LoewnerLE (P * Q * P) ((2 / 3 : ℝ) • P)) :
    ‖matrixEuclideanMap (P * Q * P - (1 / 2 : ℝ) • P)‖ ≤ 1 / 6 := by
  have hs : (P * Q * P - (1 / 2 : ℝ) • P).IsHermitian := by
    change (P * Q * P - (1 / 2 : ℝ) • P)ᴴ = _
    simp [conjTranspose_eq_transpose_of_trivial, transpose_mul, hP.symmetric,
      hQ.symmetric, Matrix.mul_assoc]
  apply loewner_opNorm_le hs (by norm_num)
  · change ((P * Q * P - (1 / 2 : ℝ) • P) - (-(1 / 6 : ℝ)) • 1).PosSemidef
    have hh := hl.add (psd_smul hP.complement.posSemidef (by norm_num : (0 : ℝ) ≤ 1 / 6))
    convert hh using 1
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · change ((1 / 6 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) -
        (P * Q * P - (1 / 2 : ℝ) • P)).PosSemidef
    have hh := hu.add (psd_smul hP.complement.posSemidef (by norm_num : (0 : ℝ) ≤ 1 / 6))
    convert hh using 1
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring

theorem map_norm_sq_gram {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (w : EuclideanSpace ℝ (Fin d)) :
    ‖matrixEuclideanMap A w‖ ^ 2 = ⇑w ⬝ᵥ ((Aᵀ * A) *ᵥ ⇑w) := by
  rw [← euclidean_dot_self, matrixEuclideanMap_apply]
  simpa only [one_mulVec, Matrix.mul_one] using
    quadratic_coordinates A (1 : Matrix (Fin d) (Fin d) ℝ) ⇑w

theorem cross_projection_norm_sq {d : ℕ} {P Q : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    (w : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖ = 1) (hPw : P *ᵥ ⇑w = ⇑w) :
    ‖matrixEuclideanMap ((1 - P) * Q * P) w‖ ^ 2 =
      1 / 4 - ‖matrixEuclideanMap (P * Q * P - (1 / 2 : ℝ) • P) w‖ ^ 2 := by
  have hs : (P * Q * P - (1 / 2 : ℝ) • P)ᵀ = P * Q * P - (1 / 2 : ℝ) • P := by
    simp [transpose_mul, hP.symmetric, hQ.symmetric, Matrix.mul_assoc]
  rw [map_norm_sq_gram, cross_projection_gram hP hQ, Matrix.sub_mulVec, dotProduct_sub,
    Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul, hPw, euclidean_dot_self, hw, one_pow, mul_one,
    map_norm_sq_gram, hs, pow_two]

/-- Exact source interval [sqrt(2)/3,1/2] for the ideal readout. -/
theorem cross_projection_norm_bounds {d : ℕ} {P Q : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    (hl : LoewnerLE ((1 / 3 : ℝ) • P) (P * Q * P))
    (hu : LoewnerLE (P * Q * P) ((2 / 3 : ℝ) • P))
    (w : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖ = 1) (hPw : P *ᵥ ⇑w = ⇑w) :
    Real.sqrt 2 / 3 ≤ ‖matrixEuclideanMap ((1 - P) * Q * P) w‖ ∧
      ‖matrixEuclideanMap ((1 - P) * Q * P) w‖ ≤ 1 / 2 := by
  have hc := (matrixEuclideanMap (P * Q * P - (1 / 2 : ℝ) • P)).le_of_opNorm_le
    (centered_compression_opNorm hP hQ hl hu) w
  rw [hw, mul_one] at hc
  have hn := cross_projection_norm_sq hP hQ w hw hPw
  have hcn := norm_nonneg (matrixEuclideanMap (P * Q * P - (1 / 2 : ℝ) • P) w)
  have hln := norm_nonneg (matrixEuclideanMap ((1 - P) * Q * P) w)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsr := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith

end
end GradientHessian.ReadoutSpectral
