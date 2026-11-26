import LowRank.GaussianMomentScaling

/-! Explicit real-order moments for inverse Gram quadratic forms and
independent Gaussian probes, including half-order moments. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem iidMatrixLaw_inverseGram_quadratic_real_moment {d s : ℕ} (hs : s + 1 ≤ d)
    {v : NNReal} (hv : v ≠ 0) (w : Fin (s + 1) → ℝ) {a : ℝ}
    (ha : 0 < ((d - s : ℕ) : ℝ) / 2 - a) :
    (∫⁻ X, ENNReal.ofReal ((w ⬝ᵥ (inverseGram X *ᵥ w)) ^ a)
      ∂iidMatrixLaw d (s + 1) v) =
      ENNReal.ofReal ((w ⬝ᵥ w) ^ a) *
        ENNReal.ofReal ((v : ℝ) ^ (-a) * gaussianMomentFormula (d - s) (-a)) := by
  have hf : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ a)) := by fun_prop
  have hm : Measurable (fun t : ℝ => (w ⬝ᵥ w) * t⁻¹) := by fun_prop
  rw [← lintegral_map hf (measurable_inverseGram_quadratic d (s + 1) w),
    iidMatrixLaw_inverseGram_quadratic hs hv w, lintegral_map hf hm, squaredGaussianLaw]
  have hmap := lintegral_map (μ := iidVectorLaw (d - s) v) (hf.comp hm)
    (measurable_dot_self (d - s))
  simp only [Function.comp_def] at hmap
  rw [hmap]
  have hw : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i))
  have he (z : Fin (d - s) → ℝ) :
      ENNReal.ofReal (((w ⬝ᵥ w) * (z ⬝ᵥ z)⁻¹) ^ a) =
        ENNReal.ofReal ((w ⬝ᵥ w) ^ a) * ENNReal.ofReal ((z ⬝ᵥ z) ^ (-a)) := by
    have hz : 0 ≤ z ⬝ᵥ z := Finset.sum_nonneg (fun i _ => mul_self_nonneg (z i))
    rw [Real.mul_rpow hw (inv_nonneg.mpr hz), Real.inv_rpow hz,
      ← Real.rpow_neg hz, ENNReal.ofReal_mul (Real.rpow_nonneg hw a)]
  simp_rw [he]
  rw [lintegral_const_mul _ (by fun_prop),
    gaussian_radial_lintegral_variance (by omega : 0 < d - s) (by linarith) v]

theorem iidMatrixLaw_inverseGram_gaussian_real_moment {d s : ℕ} (hs : s + 1 ≤ d)
    {v : NNReal} (hv : v ≠ 0) (wvar : NNReal) {a : ℝ}
    (ha : 0 < ((d - s : ℕ) : ℝ) / 2 - a)
    (hw : 0 < ((s + 1 : ℕ) : ℝ) / 2 + a) :
    (∫⁻ p : Matrix (Fin d) (Fin (s + 1)) ℝ × (Fin (s + 1) → ℝ),
      ENNReal.ofReal ((p.2 ⬝ᵥ (inverseGram p.1 *ᵥ p.2)) ^ a)
      ∂(iidMatrixLaw d (s + 1) v).prod (iidVectorLaw (s + 1) wvar)) =
      ENNReal.ofReal ((wvar : ℝ) ^ a * gaussianMomentFormula (s + 1) a) *
        ENNReal.ofReal ((v : ℝ) ^ (-a) * gaussianMomentFormula (d - s) (-a)) := by
  have hm : Measurable (fun p : Matrix (Fin d) (Fin (s + 1)) ℝ × (Fin (s + 1) → ℝ) =>
      ENNReal.ofReal ((p.2 ⬝ᵥ (inverseGram p.1 *ᵥ p.2)) ^ a)) := by
    exact ((measurable_inverseGram_quadratic_pair d (s + 1)).pow_const a).ennreal_ofReal
  rw [lintegral_prod_symm _ hm.aemeasurable]
  simp_rw [iidMatrixLaw_inverseGram_quadratic_real_moment hs hv _ ha]
  rw [lintegral_mul_const _ (by fun_prop), gaussian_radial_lintegral_variance (by omega) hw wvar]

theorem iidMatrixLaw_inverseGram_gaussian_real_moment_finite {d s : ℕ} (hs : s + 1 ≤ d)
    {v : NNReal} (hv : v ≠ 0) (wvar : NNReal) {a : ℝ}
    (ha : 0 < ((d - s : ℕ) : ℝ) / 2 - a)
    (hw : 0 < ((s + 1 : ℕ) : ℝ) / 2 + a) :
    (∫⁻ p : Matrix (Fin d) (Fin (s + 1)) ℝ × (Fin (s + 1) → ℝ),
      ENNReal.ofReal ((p.2 ⬝ᵥ (inverseGram p.1 *ᵥ p.2)) ^ a)
      ∂(iidMatrixLaw d (s + 1) v).prod (iidVectorLaw (s + 1) wvar)) < ∞ := by
  rw [iidMatrixLaw_inverseGram_gaussian_real_moment hs hv wvar ha hw]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

theorem iidMatrixLaw_inverseGram_gaussian_moment_formula {d s : ℕ} (hs : s + 1 ≤ d)
    {v : NNReal} (hv : v ≠ 0) (wvar : NNReal) {q : ℕ} (hq : 2 * q < d - s) :
    (∫⁻ p : Matrix (Fin d) (Fin (s + 1)) ℝ × (Fin (s + 1) → ℝ),
      ENNReal.ofReal ((p.2 ⬝ᵥ (inverseGram p.1 *ᵥ p.2)) ^ q)
      ∂(iidMatrixLaw d (s + 1) v).prod (iidVectorLaw (s + 1) wvar)) =
      ENNReal.ofReal ((wvar : ℝ) ^ q *
        ∏ j ∈ Finset.range q, (((s + 1 : ℕ) : ℝ) + 2 * j)) *
      ENNReal.ofReal ((v : ℝ)⁻¹ ^ q *
        (∏ j ∈ Finset.range q, (((d - s : ℕ) : ℝ) - 2 * (j + 1)))⁻¹) := by
  rw [iidMatrixLaw_inverseGram_gaussian_moment hs hv wvar,
    gaussianRadialMoment_formula (by omega), reciprocalSquaredGaussianMoment_formula hq]

end
end LowRank
