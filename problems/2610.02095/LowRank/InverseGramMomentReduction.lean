import LowRank.GaussianInverseGramQuadratic

/-! Exact nonnegative moment reduction for inverse Gram quadratic forms.
The identities allow infinite moments and do not assume integrability. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

def gaussianRadialMoment (s q : ℕ) (v : NNReal) : ℝ≥0∞ :=
  ∫⁻ w : Fin s → ℝ, ENNReal.ofReal ((w ⬝ᵥ w) ^ q) ∂iidVectorLaw s v

def reciprocalSquaredGaussianMoment (m q : ℕ) (v : NNReal) : ℝ≥0∞ :=
  ∫⁻ t : ℝ, ENNReal.ofReal (t⁻¹ ^ q) ∂squaredGaussianLaw m v

theorem iidMatrixLaw_inverseGram_quadratic_moment {d s : ℕ} (hs : s + 1 ≤ d)
    {v : NNReal} (hv : v ≠ 0) (w : Fin (s + 1) → ℝ) (q : ℕ) :
    (∫⁻ X, ENNReal.ofReal ((w ⬝ᵥ (inverseGram X *ᵥ w)) ^ q) ∂iidMatrixLaw d (s + 1) v) =
      ENNReal.ofReal ((w ⬝ᵥ w) ^ q) * reciprocalSquaredGaussianMoment (d - s) q v := by
  have hf : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ q)) := by fun_prop
  have hm : Measurable (fun t : ℝ => (w ⬝ᵥ w) * t⁻¹) := by fun_prop
  rw [← lintegral_map hf (measurable_inverseGram_quadratic d (s + 1) w),
    iidMatrixLaw_inverseGram_quadratic hs hv w, lintegral_map hf hm]
  have hn : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i))
  simp_rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hn q)]
  exact lintegral_const_mul _ (by fun_prop)

theorem measurable_inverseGram_quadratic_pair (d s : ℕ) :
    Measurable (fun p : Matrix (Fin d) (Fin s) ℝ × (Fin s → ℝ) =>
      p.2 ⬝ᵥ (inverseGram p.1 *ᵥ p.2)) := by
  have hG : Measurable (fun p : Matrix (Fin d) (Fin s) ℝ × (Fin s → ℝ) => inverseGram p.1) :=
    (measurable_inverseGram d s).comp measurable_fst
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

theorem iidMatrixLaw_inverseGram_gaussian_moment {d s : ℕ} (hs : s + 1 ≤ d)
    {v : NNReal} (hv : v ≠ 0) (wvar : NNReal) (q : ℕ) :
    (∫⁻ p : Matrix (Fin d) (Fin (s + 1)) ℝ × (Fin (s + 1) → ℝ),
      ENNReal.ofReal ((p.2 ⬝ᵥ (inverseGram p.1 *ᵥ p.2)) ^ q)
      ∂(iidMatrixLaw d (s + 1) v).prod (iidVectorLaw (s + 1) wvar)) =
      gaussianRadialMoment (s + 1) q wvar * reciprocalSquaredGaussianMoment (d - s) q v := by
  have hm : Measurable (fun p : Matrix (Fin d) (Fin (s + 1)) ℝ × (Fin (s + 1) → ℝ) =>
      ENNReal.ofReal ((p.2 ⬝ᵥ (inverseGram p.1 *ᵥ p.2)) ^ q)) :=
    ((measurable_inverseGram_quadratic_pair d (s + 1)).pow_const q).ennreal_ofReal
  rw [lintegral_prod_symm _ hm.aemeasurable]
  simp_rw [iidMatrixLaw_inverseGram_quadratic_moment hs hv]
  exact lintegral_mul_const _ (by fun_prop)

end
end LowRank
