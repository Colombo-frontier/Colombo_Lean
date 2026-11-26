import RandomizedFO2003.RotationGroup

namespace RandomizedFO2003.Rotations

open MeasureTheory Set

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem measurable_orbit (v : E) : Measurable (fun U : Rotation E => isometry E U v) :=
  ((continuous_action E).comp (continuous_id.prodMk continuous_const)).measurable

noncomputable def orbitLaw (v : E) : Measure E := (haarLaw E).map (fun U => isometry E U v)

instance orbitLaw_probability (v : E) : IsProbabilityMeasure (orbitLaw E v) :=
  isProbabilityMeasure_map (measurable_orbit E v).aemeasurable

theorem orbitLaw_eq_of_norm_eq (v w : E) (hvw : ‖v‖ = ‖w‖) : orbitLaw E v = orbitLaw E w := by
  let Q : Rotation E := unitary.linearIsometryEquiv.symm (Submodule.span ℝ {w - v})ᗮ.reflection
  have hQ : isometry E Q w = v := by
    change (unitary.linearIsometryEquiv (unitary.linearIsometryEquiv.symm
      (Submodule.span ℝ {w - v})ᗮ.reflection)) w = v
    rw [MulEquiv.apply_symm_apply]
    exact Submodule.reflection_sub hvw.symm
  have heq : (fun U : Rotation E => isometry E U v) =
      (fun U => isometry E U w) ∘ (fun U => U * Q) := by
    funext U
    simp only [Function.comp_apply, isometry_mul, hQ]
  unfold orbitLaw
  rw [heq, ← Measure.map_map (measurable_orbit E w) (measurable_mul_const Q), (haar_right E Q).map_eq]

/-- Rotating any fixed unit vector by Haar gives the previously constructed
sphere law. This identifies two actual measures, not just their low moments. -/
theorem orbitLaw_eq_sphereLaw [Nontrivial E] (v : E) (hv : ‖v‖ = 1) :
    orbitLaw E v = Spherical.sphereLaw E := by
  apply Measure.ext
  intro s hs
  have hset : MeasurableSet {p : Rotation E × E | isometry E p.1 p.2 ∈ s} :=
    measurable_action E hs
  have hproduct : ((haarLaw E).prod (Spherical.sphereLaw E))
      {p : Rotation E × E | isometry E p.1 p.2 ∈ s} = Spherical.sphereLaw E s := by
    have ht := (haar_sphere_product E).measure_preimage
      ((MeasurableSet.univ.prod hs).nullMeasurableSet)
    simpa only [preimage, mem_prod, mem_univ, true_and, Measure.prod_prod, measure_univ, one_mul] using ht
  rw [Measure.prod_apply_symm hset] at hproduct
  have heq : (∫⁻ x : E, haarLaw E {U | isometry E U x ∈ s} ∂Spherical.sphereLaw E) =
      orbitLaw E v s := by
    calc
      _ = ∫⁻ _x : E, orbitLaw E v s ∂Spherical.sphereLaw E := by
        apply lintegral_congr_ae
        filter_upwards [Spherical.ae_norm_one E] with x hx
        change haarLaw E ((fun U => isometry E U x) ⁻¹' s) = _
        rw [← Measure.map_apply (measurable_orbit E x) hs]
        exact congrArg (fun μ : Measure E => μ s) (orbitLaw_eq_of_norm_eq E x v (hx.trans hv.symm))
      _ = _ := by simp
  exact heq.symm.trans hproduct

theorem haar_unit_orbit_preserving [Nontrivial E] (v : E) (hv : ‖v‖ = 1) :
    MeasurePreserving (fun U : Rotation E => isometry E U v) (haarLaw E) (Spherical.sphereLaw E) :=
  ⟨measurable_orbit E v, orbitLaw_eq_sphereLaw E v hv⟩

theorem haar_inverse_unit_orbit_preserving [Nontrivial E] (v : E) (hv : ‖v‖ = 1) :
    MeasurePreserving (fun U : Rotation E => (isometry E U).symm v)
      (haarLaw E) (Spherical.sphereLaw E) := by
  simpa only [Function.comp_def, isometry_inv] using
    (haar_unit_orbit_preserving E v hv).comp (haar_inverse E)

end RandomizedFO2003.Rotations
