import Nonsmooth.RotationalUniqueness

open MeasureTheory Metric Filter Function
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- The radius and direction are independent under every nonzero rotationally invariant
probability. Equality is between actual measures, with the existing spherical law. -/
theorem rotational_radius_direction_product (μ : Measure E) [IsProbabilityMeasure μ]
    (hn : ∀ᵐ z ∂μ, z ≠ 0)
    (hi : ∀ e : E ≃ₗᵢ[ℝ] E, Measure.map e μ = μ) :
    Measure.map (fun z : E => (‖z‖, normalizedDirection z)) μ =
      (Measure.map (fun z : E => ‖z‖) μ).prod (sphericalLaw E) := by
  have hm : Measurable (fun z : E => (‖z‖, normalizedDirection z)) :=
    continuous_norm.measurable.prodMk normalizedDirection_measurable
  letI : IsProbabilityMeasure (Measure.map (fun z : E => (‖z‖, normalizedDirection z)) μ) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  letI : IsProbabilityMeasure (Measure.map (fun z : E => ‖z‖) μ) :=
    Measure.isProbabilityMeasure_map continuous_norm.measurable.aemeasurable
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map_of_stronglyMeasurable hm f.continuous.stronglyMeasurable]
  have hjoint : Measurable (fun p : OrthogonalTransform E × E =>
      f (‖p.2‖, p.1.val (normalizedDirection p.2))) :=
    f.continuous.measurable.comp ((continuous_norm.measurable.comp measurable_snd).prodMk
      (orthogonalAction_continuous.measurable.comp
        (measurable_fst.prodMk (normalizedDirection_measurable.comp measurable_snd))))
  have hint : Integrable (fun p : OrthogonalTransform E × E =>
      f (‖p.2‖, p.1.val (normalizedDirection p.2))) ((orthogonalHaar E).prod μ) :=
    (integrable_const ‖f‖).mono' hjoint.aestronglyMeasurable
      (Eventually.of_forall (fun p => f.norm_coe_le_norm _))
  have hfirst (Q : OrthogonalTransform E) :
      (∫ z : E, f (‖z‖, Q.val (normalizedDirection z)) ∂μ) =
        ∫ z : E, f (‖z‖, normalizedDirection z) ∂μ := by
    let e : E ≃ₗᵢ[ℝ] E := Unitary.linearIsometryEquiv Q
    have heq (x : E) : e x = Q.val x := rfl
    have hp : MeasurePreserving e μ μ := ⟨e.continuous.measurable, hi e⟩
    have h := hp.integral_comp e.toMeasurableEquiv.measurableEmbedding
      (fun z : E => f (‖z‖, normalizedDirection z))
    simp only [e.norm_map, ← normalizedDirection_isometry] at h
    simpa only [heq] using h
  have hsecond : (∫ z : E, (∫ Q : OrthogonalTransform E,
      f (‖z‖, Q.val (normalizedDirection z)) ∂orthogonalHaar E) ∂μ) =
        ∫ z : E, (∫ u : E, f (‖z‖, u) ∂sphericalLaw E) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hn] with z hz
    exact orthogonalHaar_sphere_integral (normalizedDirection_norm hz)
      (f.continuous.comp (continuous_const.prodMk continuous_id))
  have hswap := integral_integral_swap (μ := orthogonalHaar E) (ν := μ)
    (f := fun (Q : OrthogonalTransform E) (z : E) => f (‖z‖, Q.val (normalizedDirection z))) hint
  simp_rw [hfirst] at hswap
  have hav : (∫ z : E, f (‖z‖, normalizedDirection z) ∂μ) =
      ∫ z : E, (∫ u : E, f (‖z‖, u) ∂sphericalLaw E) ∂μ := by
    simpa only [integral_const, probReal_univ, one_smul] using hswap.trans hsecond
  rw [hav, integral_prod _ (f.integrable _)]
  have hinner : StronglyMeasurable (fun r : ℝ => ∫ u : E, f (r, u) ∂sphericalLaw E) :=
    (show StronglyMeasurable (Function.uncurry (fun (r : ℝ) (u : E) => f (r, u))) from
      f.continuous.stronglyMeasurable).integral_prod_right
  exact (integral_map_of_stronglyMeasurable continuous_norm.measurable hinner).symm

end
end Nonsmooth
