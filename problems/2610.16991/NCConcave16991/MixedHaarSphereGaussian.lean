import NCConcave16991.MixedHaarSphereInvariant
import NCConcave16991.MixedHaarNormalizedGaussian

/-! # Normalized standard Gaussian direction is the actual Haar sphere law -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace NCConcave16991.MixedHaar

variable {k : ℕ}

/-- Equality of actual probability measures, derived from standard Gaussian
rotational invariance and the proved uniqueness of invariant sphere laws. -/
theorem normalizedGaussianLaw_eq_sphereOrbitLaw (e : SphereSpace k) (he : ‖e‖ = 1) :
    normalizedGaussianLaw (SphereSpace k) = sphereOrbitLaw e := by
  apply sphere_invariant_probability_unique _ e he (normalizedGaussianLaw_unit e he)
  intro Q
  exact normalizedGaussianLaw_rotation (Haar.orthogonalLinearIsometryEquiv Q)

theorem normalized_stdGaussian_eq_haarAction (e : SphereSpace k) (he : ‖e‖ = 1) :
    (stdGaussian (SphereSpace k)).map normalize =
      (Haar.haarLaw k).map (fun Q ↦ Haar.orthogonalLinearIsometryEquiv Q e) :=
  normalizedGaussianLaw_eq_sphereOrbitLaw e he

theorem normalize_stdGaussian_preserving (e : SphereSpace k) (he : ‖e‖ = 1) :
    MeasurePreserving (normalize (E := SphereSpace k)) (stdGaussian (SphereSpace k)) (sphereOrbitLaw e) :=
  ⟨normalize_measurable,normalized_stdGaussian_eq_haarAction e he⟩

theorem scaled_normalized_stdGaussian_eq_haarAction (e : SphereSpace k) (he : ‖e‖ = 1) (r : ℝ) :
    (stdGaussian (SphereSpace k)).map (fun g ↦ r • normalize g) =
      (Haar.haarLaw k).map (fun Q ↦ Haar.orthogonalLinearIsometryEquiv Q (r • e)) := by
  have hs : Measurable (fun x : SphereSpace k ↦ r • x) :=
    (continuous_const.fun_smul continuous_id).measurable
  have hn := normalize_measurable (E := SphereSpace k)
  have hQ := (Haar.continuous_orthogonalLinearIsometryEquiv_apply e).measurable
  have hleft : (stdGaussian (SphereSpace k)).map (fun g ↦ r • normalize g) =
      ((stdGaussian (SphereSpace k)).map normalize).map (fun x ↦ r • x) := by
    simpa only [Function.comp_def] using (Measure.map_map hs hn).symm
  rw [hleft,normalized_stdGaussian_eq_haarAction e he,Measure.map_map hs hQ]
  congr 1
  funext Q
  exact (Haar.orthogonalLinearIsometryEquiv Q).map_smul r e |>.symm

theorem normalized_stdGaussian_transport_eq_haarAction
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (U : E ≃ₗᵢ[ℝ] SphereSpace k)
    (e : SphereSpace k) (he : ‖e‖ = 1) :
    (stdGaussian E).map (fun g ↦ U (normalize g)) =
      (Haar.haarLaw k).map (fun Q ↦ Haar.orthogonalLinearIsometryEquiv Q e) := by
  have hnE := normalize_measurable (E := E)
  have hnF := normalize_measurable (E := SphereSpace k)
  have hU := U.continuous.measurable
  have hcomm : (fun g : E ↦ U (normalize g)) = (fun g ↦ normalize (U g)) := by
    funext g
    simp only [normalize,U.norm_map,map_smul]
  rw [hcomm]
  calc
    _ = ((stdGaussian E).map U).map normalize := by
      simpa only [Function.comp_def] using (Measure.map_map hnF hU).symm
    _ = (stdGaussian (SphereSpace k)).map normalize := by rw [stdGaussian_map U]
    _ = _ := normalized_stdGaussian_eq_haarAction e he

end NCConcave16991.MixedHaar
