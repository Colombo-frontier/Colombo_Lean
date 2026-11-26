import NCConcave16991.MixedHaarGaussianProjection

/-! # Actual Gaussian residual directions have the corresponding Haar orbit law -/

noncomputable section

open Set MeasureTheory ProbabilityTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {k : ℕ}

/-- The normalized projected direction in complement coordinates is an
actual independent Haar orbit draw. -/
theorem normalized_projection_eq_haarAction (D : Submodule ℝ E)
    (U : D ≃ₗᵢ[ℝ] SphereSpace k) (e : SphereSpace k) (he : ‖e‖ = 1) :
    (stdGaussian E).map (fun g ↦ U (normalize (D.orthogonalProjectionOnto g))) =
      (Haar.haarLaw k).map (fun Q ↦ Haar.orthogonalLinearIsometryEquiv Q e) := by
  have hm : Measurable (fun x : D ↦ U (normalize x)) :=
    U.continuous.measurable.comp normalize_measurable
  have hP := D.orthogonalProjectionOnto.continuous.measurable
  have hmap : (stdGaussian E).map (fun g ↦ U (normalize (D.orthogonalProjectionOnto g))) =
      ((stdGaussian E).map D.orthogonalProjectionOnto).map (fun x ↦ U (normalize x)) := by
    simpa only [Function.comp_def] using (Measure.map_map hm hP).symm
  rw [hmap,stdGaussian_map_orthogonalProjectionOnto]
  exact normalized_stdGaussian_transport_eq_haarAction U e he

/-- The same identity in ambient coordinates, suitable for an actual inverse
completion step whose residual lies in D. -/
theorem normalized_starProjection_eq_haarAction (D : Submodule ℝ E)
    (U : D ≃ₗᵢ[ℝ] SphereSpace k) (e : SphereSpace k) (he : ‖e‖ = 1) :
    (stdGaussian E).map (fun g ↦ normalize (D.starProjection g)) =
      (Haar.haarLaw k).map (fun Q ↦ (U.symm (Haar.orthogonalLinearIsometryEquiv Q e) : E)) := by
  let back : SphereSpace k → E := fun x ↦ (U.symm x : E)
  have hb : Measurable back := measurable_subtype_coe.comp U.symm.continuous.measurable
  have hc : Measurable (fun g : E ↦ U (normalize (D.orthogonalProjectionOnto g))) :=
    U.continuous.measurable.comp (normalize_measurable.comp D.orthogonalProjectionOnto.continuous.measurable)
  have hQ := (Haar.continuous_orthogonalLinearIsometryEquiv_apply e).measurable
  have hlaw := congrArg (fun μ : Measure (SphereSpace k) ↦ μ.map back)
    (normalized_projection_eq_haarAction D U e he)
  rw [Measure.map_map hb hc,Measure.map_map hb hQ] at hlaw
  have hfn : back ∘ (fun g : E ↦ U (normalize (D.orthogonalProjectionOnto g))) =
      (fun g ↦ normalize (D.starProjection g)) := by
    funext g
    simp only [Function.comp_apply,back,U.symm_apply_apply,normalize,Submodule.coe_smul,
      Submodule.norm_coe,Submodule.coe_orthogonalProjectionOnto_apply]
    rw [← Submodule.norm_coe (D.orthogonalProjectionOnto g),Submodule.coe_orthogonalProjectionOnto_apply]
  rw [hfn] at hlaw
  simpa only [Function.comp_def,back] using hlaw

theorem normalized_starProjection_unit_ae (D : Submodule ℝ E)
    (hdim : 0 < Module.finrank ℝ D) :
    ∀ᵐ g ∂stdGaussian E, ‖normalize (D.starProjection g)‖ = 1 := by
  filter_upwards [stdGaussian_projection_ne_zero_ae D hdim] with g hg
  apply normalize_norm
  intro hz
  apply hg
  apply Subtype.ext
  simpa only [Submodule.coe_orthogonalProjectionOnto_apply,Submodule.coe_zero] using hz

theorem normalized_orthogonal_residual_eq_haarAction (D : Submodule ℝ E)
    (U : Dᗮ ≃ₗᵢ[ℝ] SphereSpace k) (e : SphereSpace k) (he : ‖e‖ = 1) :
    (stdGaussian E).map (fun g ↦ normalize (g - D.starProjection g)) =
      (Haar.haarLaw k).map (fun Q ↦ (U.symm (Haar.orthogonalLinearIsometryEquiv Q e) : E)) := by
  simpa only [Submodule.starProjection_orthogonal_val] using
    normalized_starProjection_eq_haarAction Dᗮ U e he

theorem normalized_starProjection_mem (D : Submodule ℝ E) (g : E) :
    normalize (D.starProjection g) ∈ D :=
  D.smul_mem _ (D.starProjection_apply_mem g)

theorem scaled_normalized_starProjection_eq_haarAction (D : Submodule ℝ E)
    (U : D ≃ₗᵢ[ℝ] SphereSpace k) (e : SphereSpace k) (he : ‖e‖ = 1) (r : ℝ) :
    (stdGaussian E).map (fun g ↦ r • normalize (D.starProjection g)) =
      (Haar.haarLaw k).map (fun Q ↦ r • (U.symm (Haar.orthogonalLinearIsometryEquiv Q e) : E)) := by
  have hs : Measurable (fun x : E ↦ r • x) := (continuous_const.fun_smul continuous_id).measurable
  have hnorm : Measurable (fun g : E ↦ normalize (D.starProjection g)) :=
    normalize_measurable.comp D.starProjection.continuous.measurable
  have hQ : Measurable (fun Q : Haar.OrthogonalGroup k ↦
      (U.symm (Haar.orthogonalLinearIsometryEquiv Q e) : E)) :=
    measurable_subtype_coe.comp (U.symm.continuous.measurable.comp
      (Haar.continuous_orthogonalLinearIsometryEquiv_apply e).measurable)
  have hlaw := congrArg (fun μ : Measure E ↦ μ.map (fun x ↦ r • x))
    (normalized_starProjection_eq_haarAction D U e he)
  rw [Measure.map_map hs hnorm,Measure.map_map hs hQ] at hlaw
  simpa only [Function.comp_def] using hlaw

end NCConcave16991.MixedHaar
