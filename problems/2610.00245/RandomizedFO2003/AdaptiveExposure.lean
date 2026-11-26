import RandomizedFO2003.HaarExposure

namespace RandomizedFO2003.Rotations

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A history-dependent change of coordinates preserves independent Haar
randomness when the history parameter is independent of the remaining rotation. -/
theorem parameter_inverse_right (μ : Measure Ω) [SFinite μ]
    (A : Ω → Rotation E) (hA : Measurable A) :
    MeasurePreserving (fun p : Ω × Rotation E => (p.1, p.2⁻¹ * A p.1))
      (μ.prod (haarLaw E)) (μ.prod (haarLaw E)) := by
  apply (MeasurePreserving.id μ).skew_product
    (g := fun ω U => U⁻¹ * A ω) (measurable_snd.inv.mul (hA.comp measurable_fst))
  exact Filter.Eventually.of_forall (fun ω => ((haar_right E (A ω)).comp (haar_inverse E)).map_eq)

noncomputable def queryCoordinates (e : E) (q : Ω → E) (p : Ω × Rotation E) :
    Ω × (E × Rotation (Submodule.span ℝ {e})ᗮ) :=
  (p.1, splitExposure e (p.2⁻¹ * householder (e - q p.1)))

/-- The full triple consists of the old history, a fresh uniform direction,
and a fresh residual Haar rotation. It has the product law even when the
queried direction is an arbitrary measurable function of the old history. -/
theorem queryCoordinates_preserving (μ : Measure Ω) [SFinite μ]
    (e : E) (he : ‖e‖ = 1) (q : Ω → E) (hq : Measurable q) :
    MeasurePreserving (queryCoordinates e q) (μ.prod (haarLaw E))
      (μ.prod ((Spherical.sphereLaw E).prod (haarLaw (Submodule.span ℝ {e})ᗮ))) := by
  exact ((MeasurePreserving.id μ).prod (splitExposure_preserving e he)).comp
    (parameter_inverse_right μ (fun ω => householder (e - q ω)) ((measurable_section e).comp hq))

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
theorem queryCoordinates_direction (e : E) (he : ‖e‖ = 1)
    (q : Ω → E) (p : Ω × Rotation E) (hq : ‖q p.1‖ = 1) :
    (queryCoordinates e q p).2.1 = (isometry E p.2).symm (q p.1) := by
  change isometry E (p.2⁻¹ * householder (e - q p.1)) e = _
  rw [isometry_mul, householder_sends e (q p.1) (he.trans hq.symm), isometry_inv]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
theorem queryCoordinates_reconstruct (e : E) (q : Ω → E) (p : Ω × Rotation E) :
    p.2 = householder (e - q p.1) * (exposureSample e (queryCoordinates e q p).2)⁻¹ := by
  change p.2 = householder (e - q p.1) *
    (exposureSample e (splitExposure e (p.2⁻¹ * householder (e - q p.1))))⁻¹
  rw [exposureSample_split]
  group

/-- The zero-query branch uses a fixed auxiliary unit direction. This merely
reveals extra randomness for the information model and avoids partial maps. -/
noncomputable def unitQueryDirection (e x : E) : E := by
  classical
  exact if x = 0 then e else Spherical.radial E x

theorem measurable_unitQueryDirection (e : E) : Measurable (unitQueryDirection e) := by
  classical
  unfold unitQueryDirection
  apply Measurable.ite _ measurable_const (Spherical.measurable_radial E)
  exact measurableSet_singleton (0 : E)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem unitQueryDirection_norm (e : E) (he : ‖e‖ = 1) (x : E) :
    ‖unitQueryDirection e x‖ = 1 := by
  by_cases hx : x = 0
  · simp [unitQueryDirection, hx, he]
  · simp only [unitQueryDirection, if_neg hx]
    exact Spherical.radial_norm E hx

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem norm_smul_unitQueryDirection (e x : E) : ‖x‖ • unitQueryDirection e x = x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [unitQueryDirection, hx, Spherical.radial, smul_smul, norm_ne_zero_iff.mpr hx]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
theorem queryCoordinates_full_query (e : E) (he : ‖e‖ = 1) (x : Ω → E)
    (p : Ω × Rotation E) :
    (isometry E p.2).symm (x p.1) =
      ‖x p.1‖ • (queryCoordinates e (fun ω => unitQueryDirection e (x ω)) p).2.1 := by
  rw [queryCoordinates_direction e he _ p (unitQueryDirection_norm e he (x p.1)),
    ← map_smul, norm_smul_unitQueryDirection]

omit [MeasurableSpace E] [BorelSpace E] in
theorem parameter_right (μ : Measure Ω) [SFinite μ]
    (A : Ω → Rotation E) (hA : Measurable A) :
    MeasurePreserving (fun p : Ω × Rotation E => (p.1, p.2 * A p.1))
      (μ.prod (haarLaw E)) (μ.prod (haarLaw E)) := by
  apply (MeasurePreserving.id μ).skew_product
    (g := fun ω U => U * A ω) (measurable_snd.mul (hA.comp measurable_fst))
  exact Filter.Eventually.of_forall (fun ω => (haar_right E (A ω)).map_eq)

noncomputable def responseCoordinates (e : E) (q : Ω → E) (p : Ω × Rotation E) :
    Ω × (E × Rotation (Submodule.span ℝ {e})ᗮ) :=
  (p.1, splitExposure e (p.2 * householder (e - q p.1)))

/-- Forward exposure handles the physical image of a known latent vector,
such as the vector returned by a matrix-vector oracle. -/
theorem responseCoordinates_preserving (μ : Measure Ω) [SFinite μ]
    (e : E) (he : ‖e‖ = 1) (q : Ω → E) (hq : Measurable q) :
    MeasurePreserving (responseCoordinates e q) (μ.prod (haarLaw E))
      (μ.prod ((Spherical.sphereLaw E).prod (haarLaw (Submodule.span ℝ {e})ᗮ))) := by
  exact ((MeasurePreserving.id μ).prod (splitExposure_preserving e he)).comp
    (parameter_right μ (fun ω => householder (e - q ω)) ((measurable_section e).comp hq))

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
theorem responseCoordinates_direction (e : E) (he : ‖e‖ = 1)
    (q : Ω → E) (p : Ω × Rotation E) (hq : ‖q p.1‖ = 1) :
    (responseCoordinates e q p).2.1 = isometry E p.2 (q p.1) := by
  change isometry E (p.2 * householder (e - q p.1)) e = _
  rw [isometry_mul, householder_sends e (q p.1) (he.trans hq.symm)]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
theorem responseCoordinates_reconstruct (e : E) (q : Ω → E) (p : Ω × Rotation E) :
    p.2 = exposureSample e (responseCoordinates e q p).2 * (householder (e - q p.1))⁻¹ := by
  change p.2 = exposureSample e (splitExposure e (p.2 * householder (e - q p.1))) *
    (householder (e - q p.1))⁻¹
  rw [exposureSample_split]
  group

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
theorem responseCoordinates_full_vector (e : E) (he : ‖e‖ = 1) (x : Ω → E)
    (p : Ω × Rotation E) :
    isometry E p.2 (x p.1) =
      ‖x p.1‖ • (responseCoordinates e (fun ω => unitQueryDirection e (x ω)) p).2.1 := by
  rw [responseCoordinates_direction e he _ p (unitQueryDirection_norm e he (x p.1)),
    ← map_smul, norm_smul_unitQueryDirection]

end RandomizedFO2003.Rotations
