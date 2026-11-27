import Nonsmooth.AffineProjectionShift
import Nonsmooth.AffineObservationCDF

open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] [Nontrivial F]

theorem affine_isometry_projection_rank (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable (fun z : E => z) μ) (L : E →ₗᵢ[ℝ] F) (s : ℝ) (o : F)
    (u : E) (q : F) {c : ℝ} (hc : 0 < c) (a : ℝ)
    (hobs : ∀ z : E, ⟪o + s • L z, q⟫_ℝ = a + c * ⟪z, u⟫_ℝ) (K : ℝ)
    (hrank : ∀ᵐ y ∂μ.map (fun z : E => ⟪z, u⟫_ℝ),
      ‖projectionPosteriorShift μ u y‖ ^ 2 ≤
        K * (1 + rankQuantileLog (cdf (μ.map (fun z : E => ⟪z, u⟫_ℝ)) y))) :
    let ν := μ.map (fun z => o + s • L z)
    letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (by fun_prop)
    ∀ᵐ y ∂ν.map (fun z : F => ⟪z, q⟫_ℝ),
      ‖projectionPosteriorShift ν q y‖ ^ 2 ≤
        (s ^ 2 * K) * (1 + rankQuantileLog (cdf (ν.map (fun z : F => ⟪z, q⟫_ℝ)) y)) := by
  let f : E → F := fun z => o + s • L z
  have hf : Measurable f := by fun_prop
  have hu : Measurable (fun z : E => ⟪z, u⟫_ℝ) := by fun_prop
  have hq : Measurable (fun z : F => ⟪z, q⟫_ℝ) := by fun_prop
  letI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hg : Measurable (fun y : ℝ => (y - a) / c) := by fun_prop
  have hrank' : ∀ᵐ y ∂((μ.map f).map (fun z : F => ⟪z, q⟫_ℝ)).map
      (fun y => (y - a) / c),
      ‖projectionPosteriorShift μ u y‖ ^ 2 ≤
        K * (1 + rankQuantileLog (cdf (μ.map (fun z : E => ⟪z, u⟫_ℝ)) y)) := by
    rw [affine_observation_law_inverse μ f hf _ hu _ hq hc.ne' a hobs]
    exact hrank
  have hr := ae_of_ae_map hg.aemeasurable hrank'
  have hs := affine_isometry_projection_shift μ hi L s o u q hc.ne' a hobs
  filter_upwards [hr, hs] with y hy he
  rw [he]
  rw [affine_observation_cdf μ f hf _ hu _ hq hc a hobs y]
  rw [norm_smul, L.norm_map, Real.norm_eq_abs, mul_pow, sq_abs]
  exact (mul_le_mul_of_nonneg_left hy (sq_nonneg s)).trans_eq (mul_assoc _ _ _).symm

end
end Nonsmooth
