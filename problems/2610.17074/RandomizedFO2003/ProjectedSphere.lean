import RandomizedFO2003.SphereUniqueness
import RandomizedFO2003.EmbeddedRotations
import RandomizedFO2003.FrameMeasurability
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace RandomizedFO2003.Spherical

open MeasureTheory ProbabilityTheory Set Rotations

variable {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace S] [BorelSpace S]

instance sphereLaw_sFinite : SFinite (sphereLaw E) := by
  haveI : IsFiniteMeasure (sphereLaw E) := ⟨by simp⟩
  haveI : SigmaFinite (sphereLaw E) := IsFiniteMeasure.toSigmaFinite _
  infer_instance

/-- A proper linear subspace has zero sphere probability. -/
theorem sphereLaw_submodule_zero (W : Submodule ℝ E) (hW : W ≠ ⊤) : sphereLaw E W = 0 := by
  have hw : MeasurableSet (W : Set E) := W.closed_of_finiteDimensional.measurableSet
  have hpre : radial E ⁻¹' (W : Set E) = W := by
    ext x
    by_cases hx : x = 0
    · simp [hx, radial]
    · exact W.smul_mem_iff (inv_ne_zero (norm_ne_zero_iff.mpr hx))
  rw [sphereLaw, Measure.map_apply (measurable_radial E) hw, hpre]
  exact cond_absolutelyContinuous (Measure.addHaar_submodule volume W hW)

/-- Normalized adjoint projection onto the coordinates of an isometric embedding. -/
noncomputable def projectedDirection (L : S →ₗᵢ[ℝ] E) (g : E) : S :=
  radial S (L.toContinuousLinearMap.adjoint g)

theorem measurable_projectedDirection (L : S →ₗᵢ[ℝ] E) : Measurable (projectedDirection L) :=
  (measurable_radial S).comp L.toContinuousLinearMap.adjoint.continuous.measurable

omit [MeasurableSpace S] [BorelSpace S] in
theorem ae_adjoint_ne_zero [Nontrivial S] (L : S →ₗᵢ[ℝ] E) :
    ∀ᵐ g ∂sphereLaw E, L.toContinuousLinearMap.adjoint g ≠ 0 := by
  let W := LinearMap.ker L.toContinuousLinearMap.adjoint.toLinearMap
  have hW : W ≠ ⊤ := by
    obtain ⟨x, hx⟩ := exists_ne (0 : S)
    intro h
    have hm : L x ∈ W := by rw [h]; trivial
    have hz : L.toContinuousLinearMap.adjoint (L x) = 0 := hm
    rw [embedding_adjoint_self] at hz
    exact hx hz
  apply ae_iff.mpr
  simpa only [not_not, ← LinearMap.mem_ker, Set.setOf_mem_eq] using sphereLaw_submodule_zero W hW

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace S] [BorelSpace S] in
theorem projectedDirection_commutes (L : S →ₗᵢ[ℝ] E) (R : S ≃ₗᵢ[ℝ] S) (g : E) :
    projectedDirection L (extendEmbedding L R g) = R (projectedDirection L g) := by
  unfold projectedDirection
  rw [adjoint_extendEmbedding, radial_commutes]

/-- A fresh ambient sphere vector generates the exact uniform direction in any
nonzero embedded coordinate space. -/
theorem projectedDirection_preserving [Nontrivial S] (L : S →ₗᵢ[ℝ] E) :
    MeasurePreserving (projectedDirection L) (sphereLaw E) (sphereLaw S) := by
  let ν := (sphereLaw E).map (projectedDirection L)
  have hp := measurable_projectedDirection L
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_map hp.aemeasurable
  refine ⟨hp, sphereLaw_unique S ν ?_ ?_⟩
  · apply (ae_map_iff hp.aemeasurable (isClosed_eq continuous_norm continuous_const).measurableSet).mpr
    filter_upwards [ae_adjoint_ne_zero L] with g hg
    exact radial_norm S hg
  · intro R
    refine ⟨R.continuous.measurable, ?_⟩
    change ((sphereLaw E).map (projectedDirection L)).map R = _
    rw [Measure.map_map R.continuous.measurable hp]
    have hcomm : R ∘ projectedDirection L = projectedDirection L ∘ extendEmbedding L R := by
      funext g
      exact (projectedDirection_commutes L R g).symm
    rw [hcomm, ← Measure.map_map hp (extendEmbedding L R).continuous.measurable,
      (sphereLaw_invariant E (extendEmbedding L R)).map_eq]

/-- Joint measurability only requires the concrete embedding operators to be
measurable, and allows their range to depend on the whole history. -/
theorem measurable_projectedDirection_family {Ω : Type*} [MeasurableSpace Ω]
    (L : Ω → S →ₗᵢ[ℝ] E) (hL : Measurable (fun ω => (L ω).toContinuousLinearMap)) :
    Measurable (fun p : Ω × E => projectedDirection (L p.1) p.2) := by
  exact (measurable_radial S).comp (measurable_operator_apply
    ((measurable_operator_adjoint hL).comp measurable_fst) measurable_snd)

/-- The normalized direction is independent of the complete previous history
when its ambient input is freshly sampled independently. -/
theorem projectedDirection_product [Nontrivial S] {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (L : Ω → S →ₗᵢ[ℝ] E)
    (hL : Measurable (fun ω => (L ω).toContinuousLinearMap)) :
    MeasurePreserving (fun p : Ω × E => (p.1, projectedDirection (L p.1) p.2))
      (μ.prod (sphereLaw E)) (μ.prod (sphereLaw S)) := by
  exact (MeasurePreserving.id μ).skew_product (g := fun ω g => projectedDirection (L ω) g)
    (measurable_projectedDirection_family L hL)
    (Filter.Eventually.of_forall (fun ω => (projectedDirection_preserving (L ω)).map_eq))

end RandomizedFO2003.Spherical
