import LowRank.MatrixNetBound
import LowRank.GramSpectrum

/-! Elementary Euclidean operator-norm and Loewner estimates used by the
deterministic source-event analysis. -/

namespace GradientHessian.MatrixAnalyticNorms
open Matrix LowRank
open scoped Matrix InnerProductSpace
noncomputable section

theorem matrixEuclideanMap_mul {d n k : ℕ} (A : Matrix (Fin d) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin k) ℝ) :
    matrixEuclideanMap (A*B) = (matrixEuclideanMap A).comp (matrixEuclideanMap B) := by
  ext x i
  change ((A*B)*ᵥ ⇑x) i = (A*ᵥ (B*ᵥ ⇑x)) i
  rw [Matrix.mulVec_mulVec]

theorem matrixEuclideanMap_smul {d n : ℕ} (a : ℝ) (A : Matrix (Fin d) (Fin n) ℝ) :
    matrixEuclideanMap (a • A) = a • matrixEuclideanMap A := by
  ext x i
  exact congrFun (Matrix.smul_mulVec_assoc a A x) i

theorem matrix_norm_le_of_gram_le {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hA : LoewnerLE (Aᵀ*A) (B^2 • 1)) :
    ‖matrixEuclideanMap A‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro u
  have hq := hA.2 (⇑u)
  have hg : (⇑u) ⬝ᵥ ((Aᵀ*A)*ᵥ ⇑u) = ‖matrixEuclideanMap A u‖^2 := by
    rw [← euclidean_dot_self]
    change (⇑u) ⬝ᵥ ((Aᵀ*A)*ᵥ ⇑u) = (A*ᵥ ⇑u) ⬝ᵥ (A*ᵥ ⇑u)
    simpa only [Matrix.mul_one, Matrix.one_mulVec] using (quadratic_coordinates A 1 (⇑u)).symm
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, hg, euclidean_dot_self, smul_eq_mul] at hq
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg u))).mp
  simpa only [mul_pow] using (sub_nonneg.mp hq)

theorem projector_norm_le {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) : ‖matrixEuclideanMap P‖ ≤ 1 := by
  apply matrix_norm_le_of_gram_le P (by norm_num)
  simpa only [hP.symmetric, hP.idempotent, one_pow, one_smul] using hP.le_one

theorem quadratic_abs_le_of_norm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    {ε : ℝ} (hA : ‖matrixEuclideanMap A‖ ≤ ε) (z : Fin d → ℝ) :
    |z ⬝ᵥ (A*ᵥ z)| ≤ ε*(z ⬝ᵥ z) := by
  let u : EuclideanSpace ℝ (Fin d) := (WithLp.equiv 2 (Fin d → ℝ)).symm z
  have hn := (matrixEuclideanMap A).le_of_opNorm_le hA u
  have hi := abs_real_inner_le_norm u (matrixEuclideanMap A u)
  rw [matrixEuclideanMap_inner] at hi
  change |z ⬝ᵥ (A*ᵥ z)| ≤ ‖u‖*‖matrixEuclideanMap A u‖ at hi
  have hz : z ⬝ᵥ z = ‖u‖^2 := euclidean_dot_self u
  rw [hz]
  exact hi.trans ((mul_le_mul_of_nonneg_left hn (norm_nonneg u)).trans_eq (by ring))

theorem loewner_interval_of_norm {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hAs : Aᵀ = A) {ε : ℝ} (hA : ‖matrixEuclideanMap A‖ ≤ ε) :
    LoewnerLE ((-ε) • 1) A ∧ LoewnerLE A (ε • 1) := by
  have hH : A.IsHermitian := by simpa only [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] using hAs
  constructor
  · refine ⟨hH.sub (by simp [Matrix.IsHermitian]), ?_⟩
    intro z
    have h := (abs_le.mp (quadratic_abs_le_of_norm A hA z)).1
    simpa only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul, neg_mul, sub_neg_eq_add] using
      (sub_nonneg.mpr h)
  · refine ⟨(by simp [Matrix.IsHermitian] : (ε • (1 : Matrix (Fin d) (Fin d) ℝ)).IsHermitian).sub hH, ?_⟩
    intro z
    have h := (abs_le.mp (quadratic_abs_le_of_norm A hA z)).2
    simpa only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] using (sub_nonneg.mpr h)

theorem compressed_projector_complement_norm {d : ℕ} {P Q : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    {a : ℝ} (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    ‖matrixEuclideanMap (1-a • (P*Q*P))‖ ≤ 1 := by
  let F := P*Q*P
  have hFs : Fᵀ = F := by simp only [F, Matrix.transpose_mul, hP.symmetric, hQ.symmetric, Matrix.mul_assoc]
  have hF : F.PosSemidef := by
    simpa only [F, conjTranspose_eq_transpose_of_trivial, hP.symmetric] using
      hQ.posSemidef.conjTranspose_mul_mul_same P
  have hPP (M : Matrix (Fin d) (Fin d) ℝ) : P*(P*M) = P*M := by
    rw [← Matrix.mul_assoc, hP.idempotent]
  have hQQ (M : Matrix (Fin d) (Fin d) ℝ) : Q*(Q*M) = Q*M := by
    rw [← Matrix.mul_assoc, hQ.idempotent]
  have hF₂ : (F-F*F).PosSemidef := by
    have h := hP.complement.posSemidef.conjTranspose_mul_mul_same (Q*P)
    convert h using 1
    simp only [F, conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
      hP.symmetric, hQ.symmetric, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.mul_assoc, hPP, hQQ]
  apply matrix_norm_le_of_gram_le _ (by norm_num)
  have ha₂ : 0 ≤ 2*a-a^2 := by nlinarith
  have h := (psd_smul hF₂ (sq_nonneg a)).add (psd_smul hF ha₂)
  simp only [one_pow, one_smul]
  change ((1 : Matrix (Fin d) (Fin d) ℝ) - (1-a • F)ᵀ*(1-a • F)).PosSemidef
  convert h using 1
  change (1 : Matrix (Fin d) (Fin d) ℝ) - (1-a • F)ᵀ*(1-a • F) = _
  simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hFs,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end
end GradientHessian.MatrixAnalyticNorms
