import Nonsmooth.SoftPosteriorLimits
import Nonsmooth.SupportWinnerRank

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem integrable_unit_weightedLaw {α F : Type} [MeasurableSpace α]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → F) (hf : Integrable f μ)
    (w : α → ℝ) (hw : Measurable w) (hb : ∀ x, 0 ≤ w x ∧ w x ≤ 1) :
    Integrable f (weightedDensityLaw μ w) := by
  have hp : Integrable (fun x => w x • f x) μ := hf.norm.mono'
    (hw.aestronglyMeasurable.smul hf.aestronglyMeasurable) (Eventually.of_forall (fun x => by
      rw [norm_smul, Real.norm_of_nonneg (hb x).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hb x).2))
  have hi : Integrable f (μ.withDensity (fun x => ENNReal.ofReal (w x))) := by
    rw [integrable_withDensity_iff_integrable_smul' hw.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simpa only [ENNReal.toReal_ofReal (hb _).1] using hp
  by_cases hz : (μ.withDensity (fun x => ENNReal.ofReal (w x))) univ = 0
  · rw [weightedDensityLaw, cond_eq_zero_of_meas_eq_zero hz]
    exact integrable_zero_measure
  · simpa only [weightedDensityLaw, ProbabilityTheory.cond, Measure.restrict_univ] using
      hi.smul_measure (ENNReal.inv_ne_top.mpr hz)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem projectionPosteriorShift_eq_sub (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable (fun z : E => z) μ) (u : E) :
    ∀ᵐ y ∂μ.map (fun z : E => ⟪z, u⟫_ℝ),
      projectionPosteriorShift μ u y =
        (∫ z : E, z ∂condDistrib id (fun z : E => ⟪z, u⟫_ℝ) μ y) - ∫ z : E, z ∂μ := by
  have hpair : Integrable (fun p : ℝ × E => p.2)
      (μ.map (fun z : E => (⟪z, u⟫_ℝ, z))) := hi.comp_snd_map_prodMk _
  filter_upwards [hpair.condDistrib_ae_map (Y := id) aemeasurable_id] with y hy
  rw [projectionPosteriorShift, integral_sub hy (integrable_const _),
    integral_const, measureReal_univ_eq_one, one_smul]

/-- Actual centered projection posterior means converge for soft event
approximations. All probability instances are derived from positivity. -/
theorem soft_projection_shift_tendsto (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable (fun z : E => z) μ) (u : E)
    (w : ℕ → E → ℝ) (hw : ∀ n, Measurable (w n))
    (hb : ∀ n z, 0 ≤ w n z ∧ w n z ≤ 1) (hp : ∀ n, ∀ᵐ z ∂μ, 0 < w n z)
    (A : Set E) (hA : MeasurableSet A) (hpos : μ A ≠ 0)
    (hlim : ∀ᵐ z ∂μ, Tendsto (fun n => w n z) atTop (𝓝 (A.indicator (fun _ => (1 : ℝ)) z))) :
    letI : IsProbabilityMeasure μ[|A] := cond_isProbabilityMeasure hpos
    letI (n : ℕ) : IsProbabilityMeasure (weightedDensityLaw μ (w n)) :=
      weightedDensityLaw_probability_of_positive μ (w n) (hw n) (hb n) (hp n)
    ∀ᵐ y ∂μ[|A].map (fun z : E => ⟪z, u⟫_ℝ),
      Tendsto (fun n => projectionPosteriorShift (weightedDensityLaw μ (w n)) u y) atTop
        (𝓝 (projectionPosteriorShift μ[|A] u y)) := by
  try dsimp only
  letI : IsProbabilityMeasure μ[|A] := cond_isProbabilityMeasure hpos
  letI (n : ℕ) : IsProbabilityMeasure (weightedDensityLaw μ (w n)) :=
    weightedDensityLaw_probability_of_positive μ (w n) (hw n) (hb n) (hp n)
  let X : E → ℝ := fun z => ⟪z, u⟫_ℝ
  have hX : Measurable X := (continuous_id.inner continuous_const).measurable
  have hiA : Integrable (fun z : E => z) μ[|A] :=
    (hi.mono_measure Measure.restrict_le_self).smul_measure (ENNReal.inv_ne_top.mpr hpos)
  have hmean := soft_weighted_law_integral_tendsto μ (fun z : E => z) hi w hw hb A hA hpos hlim
  have hposterior := soft_weighted_posterior_integral_tendsto μ X hX (fun z : E => z) hi w hw hb hp A hA hlim
  have hshift (n : ℕ) : ∀ᵐ y ∂μ[|A].map X,
      projectionPosteriorShift (weightedDensityLaw μ (w n)) u y =
        (∫ z : E, z ∂condDistrib id X (weightedDensityLaw μ (w n)) y) -
          ∫ z : E, z ∂weightedDensityLaw μ (w n) := by
    have hAC : μ[|A] ≪ weightedDensityLaw μ (w n) := cond_absolutelyContinuous.trans
      (absolutelyContinuous_weightedDensityLaw μ (w n) (hw n)
        (unit_weight_integrable μ (w n) (hw n) (hb n)) (fun z => (hb n z).1) (hp n))
    exact (absolutelyContinuous_map_measurable _ _ hAC X hX).ae_le
      (projectionPosteriorShift_eq_sub (weightedDensityLaw μ (w n))
        (integrable_unit_weightedLaw μ _ hi (w n) (hw n) (hb n)) u)
  filter_upwards [hposterior, ae_all_iff.mpr hshift, projectionPosteriorShift_eq_sub μ[|A] hiA u]
    with y hy hn htarget
  have he : (fun n => projectionPosteriorShift (weightedDensityLaw μ (w n)) u y) =
      (fun n => (∫ z : E, z ∂condDistrib id X (weightedDensityLaw μ (w n)) y) -
        ∫ z : E, z ∂weightedDensityLaw μ (w n)) := funext hn
  rw [he, htarget]
  exact hy.sub hmean

end
end Nonsmooth
