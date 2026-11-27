import Nonsmooth.GaussianCharacteristic

open MeasureTheory ProbabilityTheory Filter Function
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

theorem standardGaussianCoordinates_exp_linear (d : ℕ) (t : Fin d → ℝ) :
    (∫ v : Fin d → ℝ, Real.exp (∑ i, t i * v i) ∂standardGaussianCoordinates d) =
      Real.exp ((∑ i, (t i) ^ 2) / 2) := by
  simp_rw [Real.exp_sum]
  have hp : (∫ v : Fin d → ℝ, ∏ i, Real.exp (t i * v i) ∂standardGaussianCoordinates d) =
      ∏ i, ∫ z : ℝ, Real.exp (t i * z) ∂gaussianReal 0 1 := by
    letI : MeasureSpace ℝ := ⟨gaussianReal 0 1⟩
    letI : SigmaFinite (volume : Measure ℝ) := by
      change SigmaFinite (gaussianReal 0 1)
      infer_instance
    exact integral_fintype_prod_eq_prod (fun (i : Fin d) (z : ℝ) => Real.exp (t i * z))
  rw [hp]
  have hg (i : Fin d) : (∫ z : ℝ, Real.exp (t i * z) ∂gaussianReal 0 1) =
      Real.exp ((t i) ^ 2 / 2) := standardGaussian_mgf (t i)
  simp_rw [hg]
  rw [← Real.exp_sum, Finset.sum_div]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem euclideanGaussian_exp_inner (u : E) :
    (∫ z : E, Real.exp ⟪u, z⟫_ℝ ∂euclideanGaussianLaw E) = Real.exp (‖u‖ ^ 2 / 2) := by
  rw [euclideanGaussianLaw]
  have hf : StronglyMeasurable (fun z : E => Real.exp ⟪u, z⟫_ℝ) :=
    ((continuous_const.inner continuous_id).rexp).stronglyMeasurable
  rw [integral_map_of_stronglyMeasurable gaussianSynthesis_continuous.measurable hf]
  have he (v : Fin (Module.finrank ℝ E) → ℝ) :
      ⟪u, gaussianSynthesis E v⟫_ℝ = ∑ i, ⟪stdOrthonormalBasis ℝ E i, u⟫_ℝ * v i := by
    simp only [gaussianSynthesis, inner_sum, inner_smul_right, real_inner_comm u, mul_comm]
  simp_rw [he]
  rw [standardGaussianCoordinates_exp_linear]
  congr 2
  simpa only [Real.norm_eq_abs, sq_abs] using (stdOrthonormalBasis ℝ E).sum_sq_norm_inner_right u

theorem euclideanGaussian_exp_inner_integrable (u : E) :
    Integrable (fun z : E => Real.exp ⟪u, z⟫_ℝ) (euclideanGaussianLaw E) := by
  by_contra hn
  have hz := integral_undef hn
  rw [euclideanGaussian_exp_inner] at hz
  exact (Real.exp_ne_zero _) hz

end
end Nonsmooth
