import RandomizedFO2003.RotatedBlock
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Constructions.HaarToSphere

namespace RandomizedFO2003.Spherical

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Uniform volume in the unit ball, normalized to a probability measure. -/
noncomputable def ballLaw : Measure E := ProbabilityTheory.cond volume (ball (0 : E) 1)

instance ballLaw_probability : IsProbabilityMeasure (ballLaw E) := by
  apply cond_isProbabilityMeasure_of_finite
  · exact (measure_ball_pos volume (0 : E) (by norm_num : (0 : ℝ) < 1)).ne'
  · exact measure_ball_lt_top.ne

/-- Radial normalization; its value at zero is irrelevant under volume. -/
noncomputable def radial (x : E) : E := ‖x‖⁻¹ • x

theorem measurable_radial : Measurable (radial E) := by
  exact measurable_id.norm.inv.smul measurable_id

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem radial_norm {x : E} (hx : x ≠ 0) : ‖radial E x‖ = 1 := by
  simp [radial, norm_smul, norm_inv, norm_norm, norm_ne_zero_iff.mpr hx]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem radial_commutes (U : E ≃ₗᵢ[ℝ] E) (x : E) : radial E (U x) = U (radial E x) := by
  simp [radial, U.norm_map, map_smul]

/-- A concrete rotationally invariant sphere law, obtained by radial
normalization of uniform volume in the ball. -/
noncomputable def sphereLaw : Measure E := (ballLaw E).map (radial E)

instance sphereLaw_probability : IsProbabilityMeasure (sphereLaw E) :=
  isProbabilityMeasure_map (measurable_radial E).aemeasurable

theorem ballLaw_invariant (U : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving U (ballLaw E) (ballLaw E) := by
  have hpre : U ⁻¹' ball (0 : E) 1 = ball 0 1 := by
    ext x
    simp [mem_ball_zero_iff, U.norm_map]
  have h := U.measurePreserving.restrict_preimage (s := ball (0 : E) 1) measurableSet_ball
  rw [hpre] at h
  exact h.smul_measure ((volume (ball (0 : E) 1))⁻¹ : ℝ≥0∞)

theorem sphereLaw_invariant (U : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving U (sphereLaw E) (sphereLaw E) := by
  refine ⟨U.continuous.measurable, ?_⟩
  unfold sphereLaw
  rw [Measure.map_map U.continuous.measurable (measurable_radial E)]
  have hc : U ∘ radial E = radial E ∘ U := by
    funext x
    exact (radial_commutes E U x).symm
  rw [hc, ← Measure.map_map (measurable_radial E) U.continuous.measurable,
    (ballLaw_invariant E U).map_eq]

theorem ae_norm_one [Nontrivial E] : ∀ᵐ x ∂sphereLaw E, ‖x‖ = 1 := by
  apply (ae_map_iff (measurable_radial E).aemeasurable
    (isClosed_eq continuous_norm continuous_const).measurableSet).mpr
  have hn : ∀ᵐ x ∂ballLaw E, x ≠ 0 :=
    cond_absolutelyContinuous.ae_le (ae_iff.mpr (by simp))
  filter_upwards [hn] with x hx
  exact radial_norm E hx

theorem integral_rotation (U : E ≃ₗᵢ[ℝ] E) (f : E → ℝ) :
    (∫ x, f (U x) ∂sphereLaw E) = ∫ x, f x ∂sphereLaw E :=
  (sphereLaw_invariant E U).integral_comp U.toHomeomorph.measurableEmbedding f

/-- Applying a measurable random rotation to an independent sphere vector
preserves their product law, so the rotated vector remains independent of the
rotation parameter. This applies to any parameter distribution, including Haar. -/
theorem random_rotation_product {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (U : Ω → E ≃ₗᵢ[ℝ] E)
    (hU : Measurable (fun p : Ω × E => U p.1 p.2)) :
    MeasurePreserving (fun p : Ω × E => (p.1, U p.1 p.2))
      (μ.prod (sphereLaw E)) (μ.prod (sphereLaw E)) := by
  exact (MeasurePreserving.id μ).skew_product (g := fun ω x => U ω x) hU
    (Filter.Eventually.of_forall (fun ω => (sphereLaw_invariant E (U ω)).map_eq))

/-- Rotational invariance gives equality of all scalar projection moments for
vectors of the same norm; the isometry is explicitly a reflection. -/
theorem integral_inner_pow_eq_of_norm_eq (v w : E) (hvw : ‖v‖ = ‖w‖) (k : ℕ) :
    (∫ x, inner (𝕜 := ℝ) v x ^ k ∂sphereLaw E) =
      ∫ x, inner (𝕜 := ℝ) w x ^ k ∂sphereLaw E := by
  let U : E ≃ₗᵢ[ℝ] E := (Submodule.span ℝ {v - w})ᗮ.reflection
  have hUv : U v = w := Submodule.reflection_sub hvw
  have h := integral_rotation E U (fun x => inner (𝕜 := ℝ) w x ^ k)
  have heq : (fun x => inner (𝕜 := ℝ) w (U x) ^ k) =
      (fun x => inner (𝕜 := ℝ) v x ^ k) := by
    funext x
    rw [← hUv, U.inner_map_map]
  rw [heq] at h
  exact h

end RandomizedFO2003.Spherical
