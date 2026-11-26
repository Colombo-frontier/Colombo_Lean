import GradientHessian.MatrixKernelConcentration
import GradientHessian.MatrixProjectorCompression
import GradientHessian.MatrixAnalyticNorms

/-!
# Deterministic spectral consequences of the source event

The matrix and its kernel projector are concrete functions of the Gaussian
factor.  Positive Gram lower bounds imply full column rank, so the projector
formula is exact everywhere on the source event, not merely almost surely.
-/

namespace GradientHessian.MatrixGoodSpectrum

open Matrix LowRank
open GradientHessian.MatrixProjectorCompression
open scoped Matrix InnerProductSpace
noncomputable section

theorem injective_of_projected_gram_lower {d n : ℕ}
    (X : Matrix (Fin d) (Fin n) ℝ) (R : Matrix (Fin d) (Fin d) ℝ)
    {c : ℝ} (hc : 0 < c) (hG : LoewnerLE (c • 1) (Xᵀ * R * X)) :
    Function.Injective X.mulVec := by
  have hker : LinearMap.ker X.mulVecLin = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    change z = 0
    have hz0 : X *ᵥ z = 0 := hz
    have hq := loewner_quadratic_le hG z
    rw [← Matrix.mulVec_mulVec, hz0, Matrix.mulVec_zero] at hq
    simp only [Matrix.smul_mulVec_assoc, Matrix.one_mulVec, dotProduct_smul,
      smul_eq_mul, dotProduct_zero] at hq
    have hn : 0 ≤ z ⬝ᵥ z := Finset.sum_nonneg fun i _ => mul_self_nonneg (z i)
    exact dotProduct_self_eq_zero.mp (by nlinarith)
  exact LinearMap.ker_eq_bot.mp hker

theorem sourceGoodEvent_injective {d n : ℕ}
    (P : Matrix (Fin d) (Fin d) ℝ) {J : ℕ} (hJ : 0 < J)
    {X : Matrix (Fin d) (Fin n) ℝ}
    (hX : X ∈ GradientHessian.MatrixKernelConcentration.sourceGoodEvent P J) :
    Function.Injective X.mulVec := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  exact injective_of_projected_gram_lower X (1-P) (by positivity) hX.2.1

/-- Scalar inversion of a positive Gram lower bound, via its actual positive
square root. -/
theorem inverseGram_upper_of_gram_lower {d n : ℕ} (X : Matrix (Fin d) (Fin n) ℝ)
    {c : ℝ} (hc : 0 < c) (hG : LoewnerLE (c • 1) (Xᵀ * X)) :
    LoewnerLE (inverseGram X) (c⁻¹ • 1) := by
  have hX : Function.Injective X.mulVec :=
    injective_of_projected_gram_lower X 1 hc (by simpa using hG)
  let G := Xᵀ * X
  have hGp : G.PosSemidef := rightGram_posSemidef X
  let S := hGp.sqrt
  have hSS : S * S = G := hGp.sqrt_mul_self
  have hSt : Sᵀ = S := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hGp.posSemidef_sqrt.isHermitian.eq
  have hSdet : IsUnit S.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hs
    have hd := congrArg Matrix.det hSS
    rw [Matrix.det_mul, hs, zero_mul] at hd
    exact (gram_det_isUnit_of_injective X hX).ne_zero hd.symm
  have hSl : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSdet
  have hSr : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSdet
  have hSi : (S⁻¹)ᵀ = S⁻¹ := by rw [Matrix.transpose_nonsing_inv, hSt]
  have hInv : G⁻¹ = S⁻¹ * S⁻¹ := by rw [← hSS, Matrix.mul_inv_rev]
  have hconj : (S⁻¹)ᵀ * G * S⁻¹ = 1 := by
    rw [hSi, ← hSS]
    calc
      S⁻¹ * (S * S) * S⁻¹ = (S⁻¹ * S) * (S * S⁻¹) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hSl, hSr]; simp
  have hb := loewner_congruence hG S⁻¹
  change LoewnerLE ((S⁻¹)ᵀ * (c • 1) * S⁻¹) ((S⁻¹)ᵀ * G * S⁻¹) at hb
  rw [hconj, hSi] at hb
  simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← hInv] at hb
  have hp := psd_smul hb (inv_nonneg.mpr hc.le)
  change (c⁻¹ • (1 - c • G⁻¹)).PosSemidef at hp
  rw [smul_sub, smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at hp
  exact hp

theorem wishart_lower_of_gram_lower {d n : ℕ} (X : Matrix (Fin d) (Fin n) ℝ)
    {c : ℝ} (hc : 0 < c) (hG : LoewnerLE (c • 1) (Xᵀ * X)) :
    LoewnerLE (c • (1 - leftKernelProjector X)) (wishart X) := by
  have hp := wishart_lower_of_inverseGram_le X (inv_pos.mpr hc)
    (inverseGram_upper_of_gram_lower X hc hG)
  simpa only [inv_inv] using hp

theorem dilation_square_lower {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) {η : ℝ} (hη : 0 ≤ η) :
    LoewnerLE (1-P) (dilation P (Real.sqrt η) * dilation P (Real.sqrt η)) := by
  rw [dilation_mul hP, ← pow_two, Real.sq_sqrt hη]
  have hp := psd_smul hP.posSemidef hη
  change (dilation P η - (1-P)).PosSemidef
  convert hp using 1
  change dilation P η - (1-P) = η • P
  ext i j
  simp only [dilation, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem dilation_square_upper {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    LoewnerLE (dilation P (Real.sqrt η) * dilation P (Real.sqrt η)) 1 := by
  rw [dilation_mul hP, ← pow_two, Real.sq_sqrt hη]
  have hp := psd_smul hP.posSemidef (sub_nonneg.mpr hη1)
  change (1 - dilation P η).PosSemidef
  convert hp using 1
  change 1 - dilation P η = (1-η) • P
  ext i j
  simp only [dilation, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem transformed_gram_lower {d n : ℕ} (X : Matrix (Fin d) (Fin n) ℝ)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P) {η c : ℝ}
    (hη : 0 ≤ η) (hG : LoewnerLE (c • 1) (Xᵀ * (1-P) * X)) :
    LoewnerLE (c • 1)
      ((dilation P (Real.sqrt η) * X)ᵀ * (dilation P (Real.sqrt η) * X)) := by
  have hp := loewner_congruence (dilation_square_lower hP hη) X
  apply loewner_trans hG
  simpa only [Matrix.transpose_mul, dilation_symmetric hP, Matrix.mul_assoc] using hp

def sourceMatrix {d n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (J : ℕ)
    (X : Matrix (Fin d) (Fin n) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  1 + (256 * (J : ℝ) ^ 2) •
    (dilation P (Real.sqrt (1 / (J : ℝ))) * wishart X * dilation P (Real.sqrt (1 / (J : ℝ))))

def sourceKernel {d n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (J : ℕ)
    (X : Matrix (Fin d) (Fin n) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  leftKernelProjector (dilation P (Real.sqrt (1 / (J : ℝ))) * X)

theorem transformed_wishart {d n : ℕ} (X : Matrix (Fin d) (Fin n) ℝ)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P) (s : ℝ) :
    wishart (dilation P s * X) = dilation P s * wishart X * dilation P s := by
  simp only [wishart, Matrix.transpose_mul, dilation_symmetric hP, Matrix.mul_assoc]

theorem sourceKernel_isProjector {d n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (J : ℕ)
    (X : Matrix (Fin d) (Fin n) ℝ) : IsOrthogonalProjector (sourceKernel P J X) :=
  leftKernelProjector_isProjector _

theorem sourceMatrix_lower {d n : ℕ} (X : Matrix (Fin d) (Fin n) ℝ)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P) (J : ℕ) :
    LoewnerLE 1 (sourceMatrix P J X) := by
  have hp := psd_smul (wishart_posSemidef (dilation P (Real.sqrt (1 / (J : ℝ))) * X))
    (by positivity : 0 ≤ 256 * (J : ℝ) ^ 2)
  change (sourceMatrix P J X - 1).PosSemidef
  simpa only [sourceMatrix, transformed_wishart X hP, add_sub_cancel_left] using hp

theorem sourceMatrix_gap {d n : ℕ} (X : Matrix (Fin d) (Fin n) ℝ)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P) {J : ℕ} (hJ : 0 < J)
    (hG : LoewnerLE ((1 / (64 * (J : ℝ) ^ 2)) • 1) (Xᵀ * (1-P) * X)) :
    LoewnerLE (sourceKernel P J X + (5 : ℝ) • (1 - sourceKernel P J X)) (sourceMatrix P J X) := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  let Y := dilation P (Real.sqrt (1 / (J : ℝ))) * X
  have hGY := transformed_gram_lower X hP (by positivity : 0 ≤ 1 / (J : ℝ)) hG
  have hp := psd_smul (wishart_lower_of_gram_lower Y (by positivity) hGY)
    (by positivity : 0 ≤ 256 * (J : ℝ) ^ 2)
  have hc : (256 * (J : ℝ) ^ 2) * (1 / (64 * (J : ℝ) ^ 2)) = 4 := by field_simp; ring
  change ((256 * (J : ℝ) ^ 2) •
    (wishart Y - (1 / (64 * (J : ℝ) ^ 2)) • (1-sourceKernel P J X))).PosSemidef at hp
  rw [smul_sub, smul_smul, hc] at hp
  change (sourceMatrix P J X - (sourceKernel P J X + (5 : ℝ) • (1-sourceKernel P J X))).PosSemidef
  convert hp using 1
  change sourceMatrix P J X - (sourceKernel P J X + (5 : ℝ) • (1-sourceKernel P J X)) =
    (256 * (J : ℝ) ^ 2) • wishart Y - (4 : ℝ) • (1-sourceKernel P J X)
  dsimp only [Y]
  rw [transformed_wishart X hP]
  ext i j
  simp only [sourceMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem sourceMatrix_upper {d n : ℕ} (X : Matrix (Fin d) (Fin n) ℝ)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P) {J : ℕ} (hJ : 0 < J)
    (hW : ‖matrixEuclideanMap (wishart X)‖ ≤ 16) :
    LoewnerLE (sourceMatrix P J X) ((1 + 4096 * (J : ℝ) ^ 2) • 1) := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hη : 0 ≤ 1 / (J : ℝ) := by positivity
  have hη1 : 1 / (J : ℝ) ≤ 1 := (div_le_iff₀ hJR).mpr (by linarith)
  let D := dilation P (Real.sqrt (1 / (J : ℝ)))
  have hW' := (GradientHessian.MatrixAnalyticNorms.loewner_interval_of_norm
    (wishart_symmetric X) hW).2
  have hu := loewner_congruence hW' D
  have hDs : Dᵀ = D := dilation_symmetric hP _
  simp only [hDs, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at hu
  have hDupper := psd_smul (dilation_square_upper hP hη hη1) (by norm_num : (0 : ℝ) ≤ 16)
  change ((16 : ℝ) • (1 - D * D)).PosSemidef at hDupper
  rw [smul_sub] at hDupper
  have hS := loewner_trans hu hDupper
  have hp := psd_smul hS (by positivity : 0 ≤ 256 * (J : ℝ) ^ 2)
  change ((256 * (J : ℝ) ^ 2) • ((16 : ℝ) • 1 - D * wishart X * D)).PosSemidef at hp
  change ((1 + 4096 * (J : ℝ) ^ 2) • 1 - sourceMatrix P J X).PosSemidef
  convert hp using 1
  change ((1 + 4096 * (J : ℝ) ^ 2) • 1 - sourceMatrix P J X) =
    (256 * (J : ℝ) ^ 2) • ((16 : ℝ) • 1 - D * wishart X * D)
  ext i j
  simp only [sourceMatrix, D, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem sourceMatrix_kernel {d n : ℕ} (X : Matrix (Fin d) (Fin n) ℝ)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P) {J : ℕ} (hJ : 0 < J)
    (hG : LoewnerLE ((1 / (64 * (J : ℝ) ^ 2)) • 1) (Xᵀ * (1-P) * X)) :
    sourceMatrix P J X * sourceKernel P J X = sourceKernel P J X := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  let Y := dilation P (Real.sqrt (1 / (J : ℝ))) * X
  have hGY := transformed_gram_lower X hP (by positivity : 0 ≤ 1 / (J : ℝ)) hG
  have hY : Function.Injective Y.mulVec :=
    injective_of_projected_gram_lower Y 1 (c := 1 / (64 * (J : ℝ) ^ 2))
      (by positivity) (by simpa only [Matrix.mul_one] using hGY)
  have hQW := leftKernelProjector_mul_gram Y hY
  have hWQ := congrArg Matrix.transpose hQW
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero,
    (leftKernelProjector_isProjector Y).symmetric, Matrix.mul_assoc] at hWQ
  have ha : sourceMatrix P J X = 1 + (256 * (J : ℝ) ^ 2) • wishart Y := by
    rw [sourceMatrix, transformed_wishart X hP]
  rw [ha]
  change (1 + (256 * (J : ℝ) ^ 2) • (Y * Yᵀ)) * leftKernelProjector Y = leftKernelProjector Y
  simp only [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc,
    hWQ, smul_zero, add_zero]

theorem sourceGoodEvent_spectral {d n : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) {J : ℕ} (hJ : 0 < J)
    {X : Matrix (Fin d) (Fin n) ℝ}
    (hX : X ∈ GradientHessian.MatrixKernelConcentration.sourceGoodEvent P J) :
    LoewnerLE 1 (sourceMatrix P J X) ∧
      LoewnerLE (sourceMatrix P J X) ((1 + 4096 * (J : ℝ) ^ 2) • 1) ∧
      LoewnerLE (sourceKernel P J X + (5 : ℝ) • (1-sourceKernel P J X)) (sourceMatrix P J X) ∧
      sourceMatrix P J X * sourceKernel P J X = sourceKernel P J X :=
  ⟨sourceMatrix_lower X hP J, sourceMatrix_upper X hP hJ hX.1,
    sourceMatrix_gap X hP hJ hX.2.1, sourceMatrix_kernel X hP hJ hX.2.1⟩

theorem sourceMatrix_symmetric {d n : ℕ} (X : Matrix (Fin d) (Fin n) ℝ)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P) (J : ℕ) :
    (sourceMatrix P J X)ᵀ = sourceMatrix P J X := by
  simp only [sourceMatrix, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_smul, Matrix.transpose_mul, dilation_symmetric hP,
    wishart_symmetric X, Matrix.mul_assoc]

theorem sourceMatrix_posDef {d n : ℕ} (X : Matrix (Fin d) (Fin n) ℝ)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P) (J : ℕ) :
    (sourceMatrix P J X).PosDef := by
  have hI : (1 : Matrix (Fin d) (Fin d) ℝ).PosDef := by
    simpa using scalar_identity_posDef (d := d) 1 (by norm_num)
  have hp := hI.add_posSemidef (sourceMatrix_lower X hP J)
  simpa only [add_sub_cancel] using hp

/-- Exact identification of the transformed kernel with the inverse image
of the original Wishart kernel under the dilation, i.e. `D⁻¹ ker W`. -/
theorem sourceKernel_range {d n : ℕ} (X : Matrix (Fin d) (Fin n) ℝ)
    (hX : Function.Injective X.mulVec) {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) {J : ℕ} (hJ : 0 < J) :
    LinearMap.range (sourceKernel P J X).mulVecLin =
      (LinearMap.ker (wishart X).mulVecLin).comap
        (dilation P (Real.sqrt (1 / (J : ℝ)))).mulVecLin := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  let D := dilation P (Real.sqrt (1 / (J : ℝ)))
  have hD : Function.Injective D.mulVec :=
    dilation_injective hP (Real.sqrt_pos.mpr (by positivity : 0 < 1 / (J : ℝ))).ne'
  have hDX : Function.Injective (D*X).mulVec := by
    intro x y hxy
    apply hX
    apply hD
    simpa only [Matrix.mulVec_mulVec] using hxy
  change LinearMap.range (leftKernelProjector (D*X)).mulVecLin = _
  rw [leftKernelProjector_range (D*X) hDX]
  ext z
  change (D*X)ᵀ *ᵥ z = 0 ↔ wishart X *ᵥ (D*ᵥz) = 0
  rw [Matrix.transpose_mul, dilation_symmetric hP, ← Matrix.mulVec_mulVec]
  exact (gram_kernel_iff X (D*ᵥz)).symm

end
end GradientHessian.MatrixGoodSpectrum
