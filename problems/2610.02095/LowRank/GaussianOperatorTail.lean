import LowRank.MatrixNetBound
import LowRank.GaussianLinearTail
import LowRank.GaussianMatrixTranspose

/-! An unconditional dimension-uniform upper spectral tail for the actual
Gaussian matrix distribution. Constants are deliberately generous. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix InnerProductSpace
noncomputable section

theorem iidMatrixLaw_operator_tail (r s : ℕ) (v : NNReal) {t : ℝ} (ht : 0 ≤ t) :
    (iidMatrixLaw r s v).real {X | 4 * t < ‖matrixEuclideanMap X‖} ≤
      2 * (5 : ℝ) ^ (r + s) * Real.exp (-t ^ 2 / (2 * (v : ℝ))) := by
  classical
  obtain ⟨U, hUcard, hUunit, hUnet⟩ := exists_half_sphere_net (EuclideanSpace ℝ (Fin r))
  obtain ⟨V, hVcard, hVunit, hVnet⟩ := exists_half_sphere_net (EuclideanSpace ℝ (Fin s))
  have hUc : U.card ≤ 5 ^ r := by simpa using hUcard
  have hVc : V.card ≤ 5 ^ s := by simpa using hVcard
  let bad := fun z : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin s) =>
    {X : Matrix (Fin r) (Fin s) ℝ | t ≤ |⇑z.1 ⬝ᵥ (X *ᵥ ⇑z.2)|}
  have hsub : {X : Matrix (Fin r) (Fin s) ℝ | 4 * t < ‖matrixEuclideanMap X‖} ⊆
      ⋃ z ∈ U.product V, bad z := by
    intro X hX
    by_contra hmem
    have hsmall : ∀ u ∈ U, ∀ w ∈ V, |⟪u, matrixEuclideanMap X w⟫_ℝ| ≤ t := by
      intro u hu w hw
      rw [matrixEuclideanMap_inner]
      apply le_of_not_ge
      intro hlarge
      apply hmem
      exact Set.mem_iUnion.mpr ⟨(u, w), Set.mem_iUnion.mpr ⟨Finset.mem_product.mpr ⟨hu, hw⟩, hlarge⟩⟩
    exact (not_le_of_gt hX) (opNorm_le_four_of_bilinear_net (matrixEuclideanMap X) U V hUnet hVnet ht hsmall)
  have htail : ∀ z ∈ U.product V, (iidMatrixLaw r s v).real (bad z) ≤
      2 * Real.exp (-t ^ 2 / (2 * (v : ℝ))) := by
    intro z hz
    obtain ⟨hu, hw⟩ := Finset.mem_product.mp hz
    apply iidMatrixLaw_bilinear_abs_tail v _ _ ?_ ?_ ht
    · rw [euclidean_dot_self, hUunit z.1 hu, one_pow]
    · rw [euclidean_dot_self, hVunit z.2 hw, one_pow]
  have hcard : ((U.product V).card : ℝ) ≤ (5 : ℝ) ^ (r + s) := by
    exact_mod_cast (show (U.product V).card ≤ 5 ^ (r + s) by
      calc
        (U.product V).card = U.card * V.card := Finset.card_product U V
        _ ≤ 5 ^ r * 5 ^ s := Nat.mul_le_mul hUc hVc
        _ = 5 ^ (r + s) := (pow_add 5 r s).symm)
  calc
    _ ≤ (iidMatrixLaw r s v).real (⋃ z ∈ U.product V, bad z) := measureReal_mono hsub
    _ ≤ ∑ z ∈ U.product V, (iidMatrixLaw r s v).real (bad z) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _z ∈ U.product V, 2 * Real.exp (-t ^ 2 / (2 * (v : ℝ))) := Finset.sum_le_sum htail
    _ = ((U.product V).card : ℝ) * (2 * Real.exp (-t ^ 2 / (2 * (v : ℝ)))) := by simp
    _ ≤ _ := by nlinarith [Real.exp_pos (-t ^ 2 / (2 * (v : ℝ)))]

theorem gaussian_operator_constant_arithmetic {d s : ℕ} (hd : 0 < d) (hs : s ≤ d) :
    2 * (5 : ℝ) ^ (d + s) * Real.exp (-(16 : ℝ) ^ 2 / (2 * ((d : NNReal)⁻¹ : ℝ))) ≤ 1 / 40 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hexp : Real.exp (128 : ℝ) ≥ 2000 := by
    have h64 := Real.add_one_le_exp (64 : ℝ)
    have heq : Real.exp (128 : ℝ) = Real.exp 64 ^ 2 := by
      rw [show (128 : ℝ) = 64 + 64 by norm_num, Real.exp_add, pow_two]
    rw [heq]
    nlinarith
  have hbase : (25 : ℝ) * Real.exp (-128) ≤ 1 / 80 := by
    rw [Real.exp_neg]
    have hpos := Real.exp_pos (128 : ℝ)
    apply (mul_le_mul_right hpos).mp
    field_simp
    linarith
  have hnonneg : 0 ≤ (25 : ℝ) * Real.exp (-128) := by positivity
  have hpow : ((25 : ℝ) * Real.exp (-128)) ^ d ≤ 1 / 80 :=
    (pow_le_pow_left₀ hnonneg hbase d).trans (pow_le_of_le_one (by norm_num) (by norm_num) hd.ne')
  have hdim : (5 : ℝ) ^ (d + s) ≤ (25 : ℝ) ^ d := by
    calc
      (5 : ℝ) ^ (d + s) ≤ 5 ^ (d + d) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 25 ^ d := by rw [pow_add, ← mul_pow]; norm_num
  have harg : -(16 : ℝ) ^ 2 / (2 * ((d : NNReal)⁻¹ : ℝ)) = (d : ℝ) * (-128) := by
    simp only [NNReal.coe_inv, NNReal.coe_natCast]
    field_simp
    ring
  rw [harg, Real.exp_nat_mul]
  have hstep := mul_le_mul_of_nonneg_right hdim (pow_nonneg (Real.exp_nonneg (-128)) d)
  rw [← mul_pow] at hstep
  linarith

theorem gaussianMatrixLaw_transpose_operator_tail {d s : ℕ} (hd : 0 < d) (hs : s ≤ d) :
    (gaussianMatrixLaw d s).real {X | 64 < ‖matrixEuclideanMap Xᵀ‖} ≤ 1 / 40 := by
  have hmeas : MeasurableSet {Y : Matrix (Fin s) (Fin d) ℝ | 64 < ‖matrixEuclideanMap Y‖} :=
    (isOpen_lt continuous_const (continuous_matrixEuclideanMap s d).norm).measurableSet
  have hpres := iidMatrixLaw_transpose_preserving d s (d : NNReal)⁻¹
  have heq : (gaussianMatrixLaw d s).real {X | 64 < ‖matrixEuclideanMap Xᵀ‖} =
      (iidMatrixLaw s d (d : NNReal)⁻¹).real {Y | 64 < ‖matrixEuclideanMap Y‖} := by
    exact congrArg ENNReal.toReal (hpres.measure_preimage hmeas.nullMeasurableSet)
  rw [heq]
  have htail := iidMatrixLaw_operator_tail s d (d : NNReal)⁻¹ (t := 16) (by norm_num)
  norm_num only [show (4 : ℝ) * 16 = 64 by norm_num] at htail
  exact htail.trans (by simpa only [Nat.add_comm s d, show (16 : ℝ) ^ 2 = 256 by norm_num] using
    gaussian_operator_constant_arithmetic hd hs)

theorem gaussianMatrixLaw_wishart_upper_tail {d s : ℕ} (hd : 0 < d) (hs : s ≤ d) :
    (gaussianMatrixLaw d s).real {X | ¬LoewnerLE (wishart X) ((4096 : ℝ) • 1)} ≤ 1 / 40 := by
  apply le_trans (measureReal_mono ?_) (gaussianMatrixLaw_transpose_operator_tail hd hs)
  intro X hX
  change 64 < ‖matrixEuclideanMap Xᵀ‖
  by_contra h
  apply hX
  simpa only [show (64 : ℝ) ^ 2 = 4096 by norm_num] using
    wishart_le_of_transpose_opNorm X (by norm_num : (0 : ℝ) ≤ 64) (le_of_not_gt h)

end
end LowRank
