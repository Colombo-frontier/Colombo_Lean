import RandomizedFO2003.HaarSphere

namespace RandomizedFO2003.Spherical

open MeasureTheory Set Rotations

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- A rotation-invariant probability supported on the unit sphere is the
concrete sphere law already used in the spectral concentration estimates. -/
theorem sphereLaw_unique (μ : Measure E) [IsProbabilityMeasure μ]
    (hunit : ∀ᵐ x ∂μ, ‖x‖ = 1)
    (hinv : ∀ U : E ≃ₗᵢ[ℝ] E, MeasurePreserving U μ μ) : μ = sphereLaw E := by
  apply Measure.ext
  intro s hs
  have hset : MeasurableSet {p : Rotation E × E | isometry E p.1 p.2 ∈ s} :=
    measurable_action E hs
  have hprod : ((haarLaw E).prod μ) {p : Rotation E × E | isometry E p.1 p.2 ∈ s} = μ s := by
    rw [Measure.prod_apply hset]
    calc
      _ = ∫⁻ _U : Rotation E, μ s ∂haarLaw E := by
        apply lintegral_congr
        intro U
        exact (hinv (isometry E U)).measure_preimage hs.nullMeasurableSet
      _ = _ := by simp
  rw [Measure.prod_apply_symm hset] at hprod
  have heq : (∫⁻ x : E, haarLaw E {U | isometry E U x ∈ s} ∂μ) = sphereLaw E s := by
    calc
      _ = ∫⁻ _x : E, sphereLaw E s ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hunit] with x hx
        change haarLaw E ((fun U => isometry E U x) ⁻¹' s) = _
        rw [← Measure.map_apply (measurable_orbit E x) hs]
        exact congrArg (fun ν : Measure E => ν s) (orbitLaw_eq_sphereLaw E x hx)
      _ = _ := by simp
  exact hprod.symm.trans heq

end RandomizedFO2003.Spherical
