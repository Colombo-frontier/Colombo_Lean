import LowRank.GaussianProjectionSquaredLaw
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! A radial density formula for the actual product standard Gaussian law. -/

namespace LowRank
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal
noncomputable section

theorem standardGaussian_product_density (m : ℕ) :
    iidVectorLaw m 1 = volume.withDensity (fun x : Fin m → ℝ =>
      ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  unfold iidVectorLaw
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hi : Integrable (fun x : Fin m → ℝ => ∏ i, gaussianPDFReal 0 1 (x i)) :=
    Integrable.fintype_prod (fun _ => integrable_gaussianPDFReal 0 1)
  rw [← ofReal_integral_eq_lintegral_ofReal hi.integrableOn
    (ae_of_all _ (fun x => Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg 0 1 (x i))))]
  rw [volume_pi, Measure.restrict_pi_pi]
  have hp : (∫ x : Fin m → ℝ, ∏ i, gaussianPDFReal 0 1 (x i)
      ∂Measure.pi (fun i => volume.restrict (s i))) =
      ∏ i, ∫ x in s i, gaussianPDFReal 0 1 x := by
    exact @integral_fintype_prod_eq_prod ℝ _ (Fin m) _ (fun _ => ℝ)
      (fun _ x => gaussianPDFReal 0 1 x) (fun i => ⟨volume.restrict (s i)⟩)
      (fun i => show SigmaFinite ((volume : Measure ℝ).restrict (s i)) from inferInstance)
  rw [hp, ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg
    (fun x => gaussianPDFReal_nonneg 0 1 x))]
  apply Finset.prod_congr rfl
  intro i _
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal 0 1).integrableOn
    (ae_of_all _ (gaussianPDFReal_nonneg 0 1))

theorem standardGaussian_product_density_eq (m : ℕ) (x : Fin m → ℝ) :
    (∏ i, gaussianPDFReal 0 1 (x i)) =
      (1 / Real.sqrt (2 * Real.pi)) ^ m * Real.exp (-(x ⬝ᵥ x) / 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum, ← Finset.sum_div, ← Finset.sum_neg_distrib, dotProduct, pow_two, one_div]

theorem iidVectorLaw_standard_integral_density (m : ℕ) (f : (Fin m → ℝ) → ℝ) :
    (∫ x, f x ∂iidVectorLaw m 1) =
      (1 / Real.sqrt (2 * Real.pi)) ^ m *
        ∫ x, Real.exp (-(x ⬝ᵥ x) / 2) * f x := by
  rw [standardGaussian_product_density]
  have hm : Measurable (fun x : Fin m → ℝ => ∏ i, gaussianPDFReal 0 1 (x i)) :=
    Finset.measurable_prod _ (fun i _ => (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i))
  rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have hn (x : Fin m → ℝ) : 0 ≤ ∏ i, gaussianPDFReal 0 1 (x i) :=
    Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg 0 1 (x i))
  simp_rw [ENNReal.toReal_ofReal (hn _), smul_eq_mul,
    standardGaussian_product_density_eq, mul_assoc]
  exact integral_const_mul _ _

theorem iidVectorLaw_standard_integral_radial (m : ℕ) (f : ℝ → ℝ) :
    (∫ x, f (x ⬝ᵥ x) ∂iidVectorLaw m 1) =
      (1 / Real.sqrt (2 * Real.pi)) ^ m *
        ∫ x : EuclideanSpace ℝ (Fin m), Real.exp (-‖x‖ ^ 2 / 2) * f (‖x‖ ^ 2) := by
  rw [iidVectorLaw_standard_integral_density]
  congr 1
  rw [← (EuclideanSpace.volume_preserving_measurableEquiv (Fin m)).integral_comp
    (EuclideanSpace.measurableEquiv (Fin m)).measurableEmbedding]
  congr 1
  funext x
  have hn : (fun i => x i) ⬝ᵥ (fun i => x i) = ‖x‖ ^ 2 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
      using real_inner_self_eq_norm_sq x
  change Real.exp (-((fun i => x i) ⬝ᵥ (fun i => x i)) / 2) *
    f ((fun i => x i) ⬝ᵥ (fun i => x i)) = _
  rw [hn]

end
end LowRank
