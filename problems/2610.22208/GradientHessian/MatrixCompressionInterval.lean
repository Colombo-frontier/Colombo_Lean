import GradientHessian.MatrixProjectorCompression
import GradientHessian.MatrixAnalyticNorms

/-! Dimension-independent transfer of the compressed kernel event to the
source interval `[1/3,2/3]` for the transformed kernel projector. -/

namespace GradientHessian.MatrixCompressionInterval
open Matrix LowRank MatrixProjectorCompression MatrixAnalyticNorms
open scoped Matrix
noncomputable section
variable {d n : ℕ}

theorem centered_compression_identity {P K Q : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) {η : ℝ} (hη₂ : η ≠ 2)
    (he : (P*Q*P)*(η • 1+(1-η) • (P*K*P)) = P*K*P) :
    (η*(2-η)) • (P*Q*P-(1/(2-η)) • P) =
      (1-(1-η) • (P*Q*P))*(P*K*P-η • P) := by
  have hden : 2-η ≠ 0 := sub_ne_zero.mpr (Ne.symm hη₂)
  have hPP (M : Matrix (Fin d) (Fin d) ℝ) : P*(P*M) = P*M := by
    rw [← Matrix.mul_assoc, hP.idempotent]
  have hFP : (P*Q*P)*P = P*Q*P := by rw [Matrix.mul_assoc, hP.idempotent]
  calc
    _ = (η*(2-η)) • (P*Q*P)-η • P := by
      rw [smul_sub, smul_smul]
      congr 2
      field_simp
    _ = _ := by
      simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_assoc, hPP] at he
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_smul,
        Matrix.smul_mul, smul_smul, hFP]
      ext i j
      have h := congrFun (congrFun he i) j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.mul_assoc, hPP] at h ⊢
      linear_combination h

theorem compression_approximation {P K Q : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    {η : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1)
    (he : (P*Q*P)*(η • 1+(1-η) • (P*K*P)) = P*K*P)
    (hC : ‖matrixEuclideanMap (P*K*P-η • P)‖ ≤ η/24) :
    ‖matrixEuclideanMap (P*Q*P-(1/(2-η)) • P)‖ ≤ 1/24 := by
  have hfac : 0 < η*(2-η) := mul_pos hη (by linarith)
  have hG := compressed_projector_complement_norm hP hQ
    (show 0 ≤ 1-η by linarith) (show 1-η ≤ 1 by linarith)
  have hprod := (matrixEuclideanMap (1-(1-η) • (P*Q*P))).opNorm_comp_le
    (matrixEuclideanMap (P*K*P-η • P))
  rw [← matrixEuclideanMap_mul, ← centered_compression_identity hP (by linarith : η ≠ 2) he,
    matrixEuclideanMap_smul,
    norm_smul (η*(2-η)) (matrixEuclideanMap (P*Q*P-(1/(2-η)) • P)),
    Real.norm_eq_abs, abs_of_pos hfac] at hprod
  have hbound : (η*(2-η))*‖matrixEuclideanMap (P*Q*P-(1/(2-η)) • P)‖ ≤ η/24 := by
    apply hprod.trans
    simpa only [one_mul] using (mul_le_mul hG hC (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1))
  have hfac₁ : η ≤ η*(2-η) := by nlinarith
  have hm := (mul_le_mul_of_nonneg_right hfac₁
    (norm_nonneg (matrixEuclideanMap (P*Q*P-(1/(2-η)) • P)))).trans hbound
  apply (mul_le_mul_left hη).mp
  convert hm using 1
  ring

theorem projector_smul_loewner {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) {a b : ℝ} (hab : a ≤ b) : LoewnerLE (a • P) (b • P) := by
  change (b • P-a • P).PosSemidef
  rw [← sub_smul]
  exact psd_smul hP.posSemidef (sub_nonneg.mpr hab)

theorem compression_loewner_interval {P K Q : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    {η : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1/4)
    (he : (P*Q*P)*(η • 1+(1-η) • (P*K*P)) = P*K*P)
    (hC : ‖matrixEuclideanMap (P*K*P-η • P)‖ ≤ η/24) :
    LoewnerLE ((1/3:ℝ) • P) (P*Q*P) ∧ LoewnerLE (P*Q*P) ((2/3:ℝ) • P) := by
  let a : ℝ := 1/(2-η)
  have hs : (P*Q*P-a • P)ᵀ = P*Q*P-a • P := by
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_smul,
      hP.symmetric, hQ.symmetric, Matrix.mul_assoc]
  obtain ⟨hl, hu⟩ := loewner_interval_of_norm hs
    (compression_approximation hP hQ hη (by linarith) he hC)
  have hlp := loewner_congruence hl P
  have hup := loewner_congruence hu P
  have hPP (M : Matrix (Fin d) (Fin d) ℝ) : P*(P*M) = P*M := by
    rw [← Matrix.mul_assoc, hP.idempotent]
  simp only [hP.symmetric, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hP.idempotent, hPP] at hlp hup
  have hl' : LoewnerLE ((a-1/24) • P) (P*Q*P) := by
    unfold LoewnerLE at hlp ⊢
    convert hlp using 1
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_assoc]
    ring
  have hu' : LoewnerLE (P*Q*P) ((a+1/24) • P) := by
    unfold LoewnerLE at hup ⊢
    convert hup using 1
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_assoc]
    ring
  have hden : 0 < 2-η := by linarith
  have ha₀ : (1/3:ℝ) ≤ a-1/24 := by
    dsimp [a]
    rw [le_sub_iff_add_le, le_div_iff₀ hden]
    nlinarith
  have ha₁ : a+1/24 ≤ (2/3:ℝ) := by
    dsimp [a]
    rw [← le_sub_iff_add_le, div_le_iff₀ hden]
    nlinarith
  exact ⟨loewner_trans (projector_smul_loewner hP ha₀) hl',
    loewner_trans hu' (projector_smul_loewner hP ha₁)⟩

/-- The interval for the actual transformed Wishart kernel, rather than an
abstract projector satisfying an assumed compression identity. -/
theorem transformed_kernel_interval (X : Matrix (Fin d) (Fin n) ℝ)
    (hX : Function.Injective X.mulVec) {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) {η : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1/4)
    (hC : ‖matrixEuclideanMap (P*leftKernelProjector X*P-η • P)‖ ≤ η/24) :
    LoewnerLE ((1/3:ℝ) • P) (P*leftKernelProjector (dilation P (Real.sqrt η)*X)*P) ∧
    LoewnerLE (P*leftKernelProjector (dilation P (Real.sqrt η)*X)*P) ((2/3:ℝ) • P) := by
  have hs : Real.sqrt η ≠ 0 := (Real.sqrt_pos.mpr hη).ne'
  obtain ⟨ha, hb⟩ := transformed_kernel_relations X hX hP hs
  have he := compression_equation hP (leftKernelProjector_isProjector X)
    (leftKernelProjector_isProjector (dilation P (Real.sqrt η)*X)) hs ha hb
  rw [Real.sq_sqrt hη.le] at he
  exact compression_loewner_interval hP
    (leftKernelProjector_isProjector (dilation P (Real.sqrt η)*X)) hη hη₁ he hC

/-- The Loewner interval is the asserted spectral interval in every
orthonormal coordinate system for the marked range. -/
theorem compressed_range_spectrum {r : ℕ} {P Q : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P)
    (hQ : LoewnerLE ((1/3:ℝ) • P) (P*Q*P) ∧ LoewnerLE (P*Q*P) ((2/3:ℝ) • P))
    (B : Matrix (Fin d) (Fin r) ℝ) (hB : Bᵀ*B = 1) (hPB : P*B = B)
    (sp : OrderedMatrixSpectrum (Bᵀ*Q*B)) (i : Fin r) : sp.value i ∈ Set.Icc (1/3) (2/3) := by
  have hBtP : Bᵀ*P = Bᵀ := by
    have h := congrArg Matrix.transpose hPB
    simpa only [Matrix.transpose_mul, hP.symmetric] using h
  have he : Bᵀ*(P*Q*P)*B = Bᵀ*Q*B := by
    calc
      _ = (Bᵀ*P)*Q*(P*B) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hBtP, hPB]
  have hc (a : ℝ) : Bᵀ*(a • P)*B = a • 1 := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hBtP, hB]
  apply sp.value_mem_Icc
  · simpa only [he, hc] using loewner_congruence hQ.1 B
  · simpa only [he, hc] using loewner_congruence hQ.2 B

end
end GradientHessian.MatrixCompressionInterval
