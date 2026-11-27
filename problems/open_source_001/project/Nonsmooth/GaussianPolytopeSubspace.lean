import Nonsmooth.GaussianPolytopeSlices
import Nonsmooth.GaussianSubspaceLaw
import Nonsmooth.GaussianQuadraticBoundary

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]

local instance (K : Submodule ℝ E) : BorelSpace K := Subtype.borelSpace _

theorem gaussian_radial_polytope_subspace (K : Submodule ℝ E) [Nontrivial Kᗮ]
    (R : ℝ) (a : ι → E) (b : ι → ℝ) (x : E) :
    ((gaussianOrthogonalResidualLaw K)[|gaussianRadialPolytopeSlice R a b x]).map (fun z => x + z) =
      ((euclideanGaussianLaw Kᗮ)[|Kᗮ.subtype ⁻¹' gaussianRadialPolytopeSlice R a b x]).map
        (fun z : Kᗮ => x + (z : E)) := by
  have hsub : Measurable Kᗮ.subtype := Kᗮ.subtypeL.measurable
  have hadd : Measurable (fun z : E => x + z) := by fun_prop
  rw [gaussianOrthogonalResidualLaw_subspace K,
    conditioning_map_preimage _ Kᗮ.subtype hsub _
      (gaussianRadialPolytopeSlice_measurable R a b x),
    Measure.map_map hadd hsub]
  rfl

theorem gaussian_radial_polytope_positive_radius (K : Submodule ℝ E) [Nontrivial Kᗮ]
    (R : ℝ) (a : ι → E) (b : ι → ℝ) (x : E)
    (hp : gaussianOrthogonalResidualLaw K (gaussianRadialPolytopeSlice R a b x) ≠ 0) :
    0 < R ^ 2 - ‖x‖ ^ 2 := by
  have hsub : Measurable Kᗮ.subtype := Kᗮ.subtypeL.measurable
  rw [gaussianOrthogonalResidualLaw_subspace K,
    Measure.map_apply hsub (gaussianRadialPolytopeSlice_measurable R a b x)] at hp
  by_contra hn
  have hδ : R ^ 2 - ‖x‖ ^ 2 ≤ 0 := le_of_not_gt hn
  apply hp
  apply measure_mono_null ?_ (euclideanGaussian_squared_distance_level_zero (0 : Kᗮ) 0)
  intro z hz
  have hnorm : ‖(z : E)‖ ^ 2 ≤ R ^ 2 - ‖x‖ ^ 2 := hz.1
  change ‖z - (0 : Kᗮ)‖ ^ 2 = 0
  simp only [sub_zero]
  change ‖(z : E)‖ ^ 2 = 0
  nlinarith [sq_nonneg ‖(z : E)‖]

theorem gaussian_radial_polytope_subspace_event (K : Submodule ℝ E)
    (R : ℝ) (a : ι → E) (b : ι → ℝ) (x : E) (hδ : 0 ≤ R ^ 2 - ‖x‖ ^ 2) :
    Kᗮ.subtype ⁻¹' gaussianRadialPolytopeSlice R a b x =
      closedBall (0 : Kᗮ) (Real.sqrt (R ^ 2 - ‖x‖ ^ 2)) ∩
        {z : Kᗮ | ∀ j, ⟪Kᗮ.orthogonalProjection (a j), z⟫_ℝ ≤ b j - ⟪a j, x⟫_ℝ} := by
  ext z
  have hi (j : ι) : ⟪Kᗮ.orthogonalProjection (a j), z⟫_ℝ = ⟪a j, (z : E)⟫_ℝ :=
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right z (a j)
  simp only [mem_preimage, gaussianRadialPolytopeSlice, mem_setOf_eq, mem_inter_iff,
    mem_closedBall, dist_zero_right, hi]
  apply and_congr_left
  intro _
  have hsq := sq_le_sq₀ (norm_nonneg z) (Real.sqrt_nonneg (R ^ 2 - ‖x‖ ^ 2))
  rw [Real.sq_sqrt hδ] at hsq
  exact hsq

end
end Nonsmooth
