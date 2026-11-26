import Nonsmooth.RegularImageMoments

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem regular_vector_direction_memLp (μ : Measure E) {u : E} (hu : ‖u‖ = 1)
    (hd : 2 ≤ Module.finrank ℝ E)
    (H : ∀ w : E, ‖w‖ = 1 → ⟪u, w⟫_ℝ = 0 → RegularProjectionImage μ u w) (v : E) :
    MemLp (fun z : E => ⟪v, z⟫_ℝ) 2 μ := by
  obtain ⟨w₀, hw₀, huw₀⟩ := exists_unit_orthogonal_direction hu hd
  have hx := (regular_projection_image_coordinate_moments μ u w₀ (H w₀ hw₀ huw₀)).1
  rcases unit_axis_plane_decomposition hu v with ⟨a, hv⟩ | ⟨a, c, w, hw, huw, hv, hn⟩
  · simpa only [hv, real_inner_smul_left] using hx.const_mul a
  · have hy := (regular_projection_image_coordinate_moments μ u w (H w hw huw)).2
    simpa only [hv, inner_add_left, real_inner_smul_left, Pi.add_apply] using!
      (hx.const_mul a).add (hy.const_mul c)

/-- Square integrability of the actual vector is derived from its regular
two-coordinate image laws and a finite orthonormal expansion. -/
theorem regular_vector_memLp_two (μ : Measure E) {u : E} (hu : ‖u‖ = 1)
    (hd : 2 ≤ Module.finrank ℝ E)
    (H : ∀ w : E, ‖w‖ = 1 → ⟪u, w⟫_ℝ = 0 → RegularProjectionImage μ u w) :
    MemLp (fun z : E => z) 2 μ := by
  let b := stdOrthonormalBasis ℝ E
  have hi : Integrable (fun z : E => ∑ i, ⟪b i, z⟫_ℝ ^ 2) μ :=
    integrable_finset_sum _ (fun i _ => (regular_vector_direction_memLp μ hu hd H (b i)).integrable_sq)
  apply (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).mpr
  apply hi.congr
  apply Eventually.of_forall
  intro z
  simpa only [real_inner_comm z, ← pow_two, real_inner_self_eq_norm_sq, id_eq] using b.sum_inner_mul_inner z z

end
end Nonsmooth
