import Bilevel.SphereHaar

/-! Sphere probability and concentration transported to an actual residual subspace. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace Bilevel.TransportedSphere
open EuclideanGaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  (e : E ≃ₗᵢ[ℝ] Space (n + 1))

def law : Measure E := (SphereLaw.sphereLaw (n + 1)).map e.symm

instance probability : IsProbabilityMeasure (law e) :=
  isProbabilityMeasure_map e.symm.continuous.measurable.aemeasurable

theorem unit_norm_ae : ∀ᵐ x ∂law e, ‖x‖ = 1 := by
  rw [law, ae_map_iff e.symm.continuous.measurable.aemeasurable]
  · filter_upwards [SphereLaw.unit_norm_ae n] with x hx
    simpa only [e.symm.norm_map] using hx
  · exact (isClosed_eq continuous_norm continuous_const).measurableSet

theorem coordinates_preserving : MeasurePreserving e (law e) (SphereLaw.sphereLaw (n + 1)) := by
  refine ⟨e.continuous.measurable, ?_⟩
  rw [law, Measure.map_map e.continuous.measurable e.symm.continuous.measurable]
  simpa only [Function.comp_def, e.apply_symm_apply] using
    (Measure.map_id (μ := SphereLaw.sphereLaw (n + 1)))

theorem orthogonal_invariance (U : E ≃ₗᵢ[ℝ] E) : MeasurePreserving U (law e) (law e) := by
  let R : Space (n + 1) ≃ₗᵢ[ℝ] Space (n + 1) := (e.symm.trans U).trans e
  have hR := SphereLaw.orthogonal_invariance (n + 1) R
  have hm := hR.map_eq
  have he : U ∘ e.symm = e.symm ∘ R := by
    funext x
    simp [R]
  refine ⟨U.continuous.measurable, ?_⟩
  rw [law, Measure.map_map U.continuous.measurable e.symm.continuous.measurable, he,
    ← Measure.map_map e.symm.continuous.measurable R.continuous.measurable, hm]

theorem directional_tail (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 2) (w : E) (hw : ‖w‖ = 1) :
    (law e).real {x | t ≤ ⟪w, x⟫ ^ 2} ≤ 2 * Real.exp (-(n : ℝ) * t / 8) := by
  have he : {x : E | t ≤ ⟪w, x⟫ ^ 2} = e ⁻¹' {z | t ≤ ⟪e w, z⟫ ^ 2} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, e.inner_map_map]
  have hs : MeasurableSet {z : Space (n + 1) | t ≤ ⟪e w, z⟫ ^ 2} :=
    measurableSet_le measurable_const ((continuous_const.inner continuous_id).measurable.pow_const 2)
  rw [he, SphericalGaussian.measureReal_preimage (coordinates_preserving e) _ hs]
  exact SphereLaw.directional_tail n t ht ht2 (e w) ((e.norm_map w).trans hw)

end Bilevel.TransportedSphere
