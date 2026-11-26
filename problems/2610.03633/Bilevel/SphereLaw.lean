import Bilevel.SphericalGaussian

/-! A genuine orthogonally invariant probability law supported on the unit sphere. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Bilevel.SphereLaw
open EuclideanGaussian SphericalGaussian

def sphereLaw (d : ℕ) : Measure (Space d) := (law d).map direction

instance probability (d : ℕ) : IsProbabilityMeasure (sphereLaw d) :=
  isProbabilityMeasure_map (direction_measurable d).aemeasurable

theorem gaussian_zero_null (n : ℕ) : law (n + 1) {0} = 0 := by
  exact withDensity_absolutelyContinuous _ _ (measure_singleton 0)

theorem gaussian_nonzero_ae (n : ℕ) : ∀ᵐ x ∂law (n + 1), x ≠ 0 := by
  rw [ae_iff]
  simpa only [not_not, Set.setOf_eq_eq_singleton] using gaussian_zero_null n

theorem unit_norm_ae (n : ℕ) : ∀ᵐ x ∂sphereLaw (n + 1), ‖x‖ = 1 := by
  rw [sphereLaw, ae_map_iff (direction_measurable (n + 1)).aemeasurable]
  · filter_upwards [gaussian_nonzero_ae n] with x hx
    exact direction_norm x hx
  · exact (isClosed_eq continuous_norm continuous_const).measurableSet

theorem orthogonal_invariance (d : ℕ) (U : Space d ≃ₗᵢ[ℝ] Space d) :
    MeasurePreserving U (sphereLaw d) (sphereLaw d) := by
  refine ⟨U.continuous.measurable, ?_⟩
  rw [sphereLaw, Measure.map_map U.continuous.measurable (direction_measurable d)]
  have he : U ∘ direction = direction ∘ U := by
    funext x
    exact (direction_equivariant d U x).symm
  rw [he, ← Measure.map_map (direction_measurable d) U.continuous.measurable,
    (EuclideanGaussian.orthogonal_invariance d U).map_eq]

theorem directional_tail (n : ℕ) (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 2)
    (w : Space (n + 1)) (hw : ‖w‖ = 1) :
    (sphereLaw (n + 1)).real {x | t ≤ ⟪w, x⟫ ^ 2} ≤
      2 * Real.exp (-(n : ℝ) * t / 8) := by
  rw [measureReal_def, sphereLaw, Measure.map_apply (direction_measurable (n + 1))]
  · exact normalized_direction_tail n t ht ht2 w hw
  · exact measurableSet_le measurable_const ((continuous_const.inner continuous_id).measurable.pow_const 2)

end Bilevel.SphereLaw
