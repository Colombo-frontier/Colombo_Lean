import LowRank.GaussianSquaredMoments
import LowRank.SpectralPowers

/-! A Gaussian quadratic-form moment dominates every nonnegative eigenvalue
moment, with the exact one-dimensional Gaussian factor. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem iidVectorLaw_coordinate_square_moment {m : ℕ} (i : Fin m) {a : ℝ}
    (ha : 0 ≤ a) :
    (∫⁻ x, ENNReal.ofReal ((x i ^ 2) ^ a) ∂iidVectorLaw m 1) =
      ENNReal.ofReal (gaussianMomentFormula 1 a) := by
  classical
  let B : Matrix (Fin m) (Fin 1) ℝ := fun j _ => if j = i then 1 else 0
  have hB : Bᵀ * B = 1 := by
    ext j k
    fin_cases j
    fin_cases k
    simp [B, Matrix.mul_apply]
  have hmul (x : Fin m → ℝ) : Bᵀ *ᵥ x = fun _ => x i := by
    ext j
    simp [B, Matrix.mulVec, dotProduct]
  have hmeas : Measurable (fun x : Fin m → ℝ => Bᵀ *ᵥ x) := by
    apply measurable_pi_lambda
    intro j
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hf : Measurable (fun z : Fin 1 → ℝ => ENNReal.ofReal ((z ⬝ᵥ z) ^ a)) := by
    fun_prop
  have hmap := lintegral_map (μ := iidVectorLaw m 1) hf hmeas
  rw [iidVectorLaw_orthogonal_compression B hB] at hmap
  have hh := gaussian_radial_lintegral (m := 1) (by omega) (a := a) (by norm_num; linarith)
  rw [hh] at hmap
  symm
  convert hmap using 1
  simp only [hmul, dotProduct, Fin.sum_univ_one, pow_two]

theorem iidVectorLaw_quadratic_spectral_moment {m : ℕ}
    {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.PosSemidef)
    (sp : OrderedMatrixSpectrum A) (i : Fin m) {a : ℝ} (ha : 0 ≤ a) :
    ENNReal.ofReal ((sp.value i) ^ a) * ENNReal.ofReal (gaussianMomentFormula 1 a) ≤
      ∫⁻ x, ENNReal.ofReal ((x ⬝ᵥ (A *ᵥ x)) ^ a) ∂iidVectorLaw m 1 := by
  have hm : Measurable (fun x : Fin m → ℝ => sp.basis *ᵥ x) := by
    apply measurable_pi_lambda
    intro j
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hf : Measurable (fun x : Fin m → ℝ => ENNReal.ofReal ((x ⬝ᵥ (A *ᵥ x)) ^ a)) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  have hrot : (iidVectorLaw m 1).map (fun x => sp.basis *ᵥ x) = iidVectorLaw m 1 := by
    simpa only [Matrix.transpose_transpose] using
      iidVectorLaw_orthogonal_compression sp.basisᵀ
        (by simpa only [Matrix.transpose_transpose] using sp.orthogonal_right) 1
  have hint := lintegral_map (μ := iidVectorLaw m 1) hf hm
  rw [hrot] at hint
  rw [hint]
  simp_rw [sp.quadratic]
  have hscalar : (∫⁻ x, ENNReal.ofReal ((sp.value i * x i ^ 2) ^ a) ∂iidVectorLaw m 1) =
      ENNReal.ofReal ((sp.value i) ^ a) * ENNReal.ofReal (gaussianMomentFormula 1 a) := by
    simp_rw [Real.mul_rpow (sp.value_nonneg hA i) (sq_nonneg _),
      ENNReal.ofReal_mul (Real.rpow_nonneg (sp.value_nonneg hA i) a)]
    rw [lintegral_const_mul _ (by fun_prop), iidVectorLaw_coordinate_square_moment i ha]
  rw [← hscalar]
  apply lintegral_mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow (mul_nonneg (sp.value_nonneg hA i) (sq_nonneg _))
    (Finset.single_le_sum (fun j _ => mul_nonneg (sp.value_nonneg hA j) (sq_nonneg _))
      (Finset.mem_univ i)) ha

end
end LowRank
