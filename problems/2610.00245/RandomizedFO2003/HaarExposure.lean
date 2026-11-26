import RandomizedFO2003.ReflectionSection

namespace RandomizedFO2003.Rotations

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem mem_fixing_line (e : E) (U : Rotation E) (he : isometry E U e = e) :
    U ∈ fixingSubgroup (Submodule.span ℝ {e}) := by
  intro x
  have hall : ∀ y : E, y ∈ Submodule.span ℝ {e} → isometry E U y = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain rfl := Set.mem_singleton_iff.mp hy; exact he
    | zero => exact map_zero _
    | add y z _ _ hy hz => rw [map_add, hy, hz]
    | smul c y _ hy => rw [map_smul, hy]
  exact hall x x.property

/-- The mismatch between two measurable sections fixes the observed line. -/
theorem section_transition (e : E) (he : ‖e‖ = 1) (Q : Rotation E) (v : E) (hv : ‖v‖ = 1) :
    ∃ R : Rotation (Submodule.span ℝ {e})ᗮ,
      Q * householder (e - v) =
        householder (e - isometry E Q v) * extendComplement (Submodule.span ℝ {e}) R := by
  let C := (householder (e - isometry E Q v))⁻¹ * Q * householder (e - v)
  have hC : C ∈ fixingSubgroup (Submodule.span ℝ {e}) := by
    apply mem_fixing_line
    dsimp only [C]
    rw [isometry_mul, isometry_mul, householder_sends e v (he.trans hv.symm), isometry_inv]
    apply (isometry E (householder (e - isometry E Q v))).symm_apply_eq.mpr
    exact (householder_sends e (isometry E Q v)
      (by rw [(isometry E Q).norm_map, he, hv])).symm
  refine ⟨restrictComplement _ ⟨C, hC⟩, ?_⟩
  have hr := congrArg Subtype.val (extend_restrict (Submodule.span ℝ {e}) ⟨C, hC⟩)
  change extendComplement (Submodule.span ℝ {e}) (restrictComplement _ ⟨C, hC⟩) = C at hr
  rw [hr]
  dsimp [C]
  group

noncomputable def exposureSample (e : E) (p : E × Rotation (Submodule.span ℝ {e})ᗮ) : Rotation E :=
  householder (e - p.1) * extendComplement (Submodule.span ℝ {e}) p.2

theorem exposureSample_observed (e : E) (he : ‖e‖ = 1)
    (v : E) (hv : ‖v‖ = 1) (R : Rotation (Submodule.span ℝ {e})ᗮ) :
    isometry E (exposureSample e (v, R)) e = v := by
  rw [exposureSample, isometry_mul]
  have hf := extendComplement_fixed (Submodule.span ℝ {e}) R
    ⟨e, Submodule.subset_span (Set.mem_singleton e)⟩
  change isometry E (extendComplement (Submodule.span ℝ {e}) R) e = e at hf
  rw [hf, householder_sends e v (he.trans hv.symm)]

variable [MeasurableSpace E] [BorelSpace E]

theorem measurable_exposureSample (e : E) : Measurable (exposureSample e) :=
  ((measurable_section e).comp measurable_fst).mul
    ((continuous_extendComplement (Submodule.span ℝ {e})).measurable.comp measurable_snd)

noncomputable def exposureLaw (e : E) : Measure (Rotation E) :=
  ((Spherical.sphereLaw E).prod (haarLaw (Submodule.span ℝ {e})ᗮ)).map (exposureSample e)

instance exposureLaw_probability (e : E) : IsProbabilityMeasure (exposureLaw e) :=
  isProbabilityMeasure_map (measurable_exposureSample e).aemeasurable

theorem exposure_fiber_left (e : E) (he : ‖e‖ = 1) (Q : Rotation E)
    (v : E) (hv : ‖v‖ = 1) (s : Set (Rotation E)) (hs : MeasurableSet s) :
    haarLaw (Submodule.span ℝ {e})ᗮ {R | Q * exposureSample e (v, R) ∈ s} =
      haarLaw (Submodule.span ℝ {e})ᗮ {R | exposureSample e (isometry E Q v, R) ∈ s} := by
  obtain ⟨R₀, hR₀⟩ := section_transition e he Q v hv
  have heq (R : Rotation (Submodule.span ℝ {e})ᗮ) :
      Q * exposureSample e (v, R) = exposureSample e (isometry E Q v, R₀ * R) := by
    unfold exposureSample
    rw [← mul_assoc, hR₀, extendComplement_mul, mul_assoc]
  have hset : MeasurableSet {R : Rotation (Submodule.span ℝ {e})ᗮ |
      exposureSample e (isometry E Q v, R) ∈ s} :=
    ((measurable_exposureSample e).comp (measurable_const.prodMk measurable_id)) hs
  have hp := (haar_left (Submodule.span ℝ {e})ᗮ R₀).measure_preimage hset.nullMeasurableSet
  simpa only [Set.preimage, Set.mem_setOf_eq, heq] using hp

/-- Sampling an observed direction and an independent Haar stabilizer produces
a Haar rotation. This is the concrete one-vector exposure decomposition. -/
theorem exposureLaw_eq_haar (e : E) (he : ‖e‖ = 1) : exposureLaw e = haarLaw E := by
  haveI : Nontrivial E := ⟨⟨e, 0, by intro hz; simp [hz] at he⟩⟩
  haveI : (exposureLaw e).IsMulLeftInvariant := by
    constructor
    intro Q
    apply Measure.ext
    intro s hs
    rw [Measure.map_apply (measurable_const_mul Q) hs, exposureLaw,
      Measure.map_apply (measurable_exposureSample e) ((measurable_const_mul Q) hs),
      Measure.map_apply (measurable_exposureSample e) hs,
      Measure.prod_apply ((measurable_exposureSample e) ((measurable_const_mul Q) hs)),
      Measure.prod_apply ((measurable_exposureSample e) hs)]
    change (∫⁻ v : E, haarLaw (Submodule.span ℝ {e})ᗮ
        {R | Q * exposureSample e (v, R) ∈ s} ∂Spherical.sphereLaw E) =
      ∫⁻ v : E, haarLaw (Submodule.span ℝ {e})ᗮ {R | exposureSample e (v, R) ∈ s} ∂Spherical.sphereLaw E
    calc
      _ = ∫⁻ v : E, haarLaw (Submodule.span ℝ {e})ᗮ
          {R | exposureSample e (isometry E Q v, R) ∈ s} ∂Spherical.sphereLaw E := by
        apply lintegral_congr_ae
        filter_upwards [Spherical.ae_norm_one E] with v hv
        exact exposure_fiber_left e he Q v hv s hs
      _ = _ := (Spherical.sphereLaw_invariant E (isometry E Q)).lintegral_comp
        (measurable_measure_prodMk_left ((measurable_exposureSample e) hs))
  haveI : (exposureLaw e).IsHaarMeasure :=
    Measure.isHaarMeasure_of_isCompact_nonempty_interior (exposureLaw e) Set.univ
      isCompact_univ (by simp) (by simp) (by simp)
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem exposureSample_preserving (e : E) (he : ‖e‖ = 1) :
    MeasurePreserving (exposureSample e)
      ((Spherical.sphereLaw E).prod (haarLaw (Submodule.span ℝ {e})ᗮ)) (haarLaw E) :=
  ⟨measurable_exposureSample e, exposureLaw_eq_haar e he⟩

noncomputable def exposureRemainderFixing (e : E) (U : Rotation E) :
    fixingSubgroup (Submodule.span ℝ {e}) :=
  ⟨(householder (e - isometry E U e))⁻¹ * U, by
    apply mem_fixing_line
    rw [isometry_mul, isometry_inv]
    apply (isometry E (householder (e - isometry E U e))).symm_apply_eq.mpr
    exact (householder_sends e (isometry E U e) ((isometry E U).norm_map e).symm).symm⟩

noncomputable def exposureRemainder (e : E) (U : Rotation E) :
    Rotation (Submodule.span ℝ {e})ᗮ :=
  restrictComplement (Submodule.span ℝ {e}) (exposureRemainderFixing e U)

theorem measurable_exposureRemainder (e : E) : Measurable (exposureRemainder e) := by
  haveI : BorelSpace (fixingSubgroup (Submodule.span ℝ {e})) := Subtype.borelSpace _
  have hm : Measurable (exposureRemainderFixing e) :=
    (((measurable_section e).comp (measurable_orbit E e)).inv.mul measurable_id).subtype_mk
  exact (continuous_restrictComplement (Submodule.span ℝ {e})).measurable.comp hm

noncomputable def splitExposure (e : E) (U : Rotation E) :
    E × Rotation (Submodule.span ℝ {e})ᗮ := (isometry E U e, exposureRemainder e U)

theorem measurable_splitExposure (e : E) : Measurable (splitExposure e) :=
  (measurable_orbit E e).prodMk (measurable_exposureRemainder e)

omit [MeasurableSpace E] [BorelSpace E] in
theorem splitExposure_sample (e : E) (he : ‖e‖ = 1) (v : E) (hv : ‖v‖ = 1)
    (R : Rotation (Submodule.span ℝ {e})ᗮ) :
    splitExposure e (exposureSample e (v, R)) = (v, R) := by
  apply Prod.ext
  · exact exposureSample_observed e he v hv R
  · change restrictComplement _ (exposureRemainderFixing e (exposureSample e (v, R))) = R
    have hr : exposureRemainderFixing e (exposureSample e (v, R)) =
        extendToFixing (Submodule.span ℝ {e}) R := by
      apply Subtype.ext
      change (householder (e - isometry E (exposureSample e (v, R)) e))⁻¹ *
        exposureSample e (v, R) = extendComplement (Submodule.span ℝ {e}) R
      rw [exposureSample_observed e he v hv R]
      unfold exposureSample
      group
    rw [hr, restrict_extend]

omit [MeasurableSpace E] [BorelSpace E] in
theorem exposureSample_split (e : E) (U : Rotation E) :
    exposureSample e (splitExposure e U) = U := by
  change householder (e - isometry E U e) *
    extendComplement (Submodule.span ℝ {e})
      (restrictComplement _ (exposureRemainderFixing e U)) = U
  have hr := congrArg Subtype.val
    (extend_restrict (Submodule.span ℝ {e}) (exposureRemainderFixing e U))
  change extendComplement (Submodule.span ℝ {e})
    (restrictComplement _ (exposureRemainderFixing e U)) =
      (householder (e - isometry E U e))⁻¹ * U at hr
  rw [hr]
  group

/-- Exposing the image of one fixed unit vector leaves an independent Haar
rotation of its orthogonal complement, in explicit measurable coordinates. -/
theorem splitExposure_preserving (e : E) (he : ‖e‖ = 1) :
    MeasurePreserving (splitExposure e) (haarLaw E)
      ((Spherical.sphereLaw E).prod (haarLaw (Submodule.span ℝ {e})ᗮ)) := by
  haveI : Nontrivial E := ⟨⟨e, 0, by intro hz; simp [hz] at he⟩⟩
  refine ⟨measurable_splitExposure e, ?_⟩
  rw [← (exposureSample_preserving e he).map_eq,
    Measure.map_map (measurable_splitExposure e) (measurable_exposureSample e)]
  have hunit : ∀ᵐ p ∂(Spherical.sphereLaw E).prod (haarLaw (Submodule.span ℝ {e})ᗮ),
      ‖p.1‖ = 1 := by
    apply (Measure.ae_prod_iff_ae_ae
      (isClosed_eq continuous_fst.norm continuous_const).measurableSet).mpr
    filter_upwards [Spherical.ae_norm_one E] with v hv
    exact Filter.Eventually.of_forall (fun _ => hv)
  calc
    _ = ((Spherical.sphereLaw E).prod (haarLaw (Submodule.span ℝ {e})ᗮ)).map id := by
      apply Measure.map_congr
      filter_upwards [hunit] with p hp
      exact splitExposure_sample e he p.1 hp p.2
    _ = _ := Measure.map_id

end RandomizedFO2003.Rotations
