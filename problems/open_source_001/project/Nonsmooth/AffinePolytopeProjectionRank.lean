import Nonsmooth.AffineProjectionRank
import Nonsmooth.AllDimensionalPolytopeRank
import Nonsmooth.AffinePolytopeCovariance

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianPolytopeModel_nondegenerate_projection_rank {s : ℝ} (hs : 0 < s)
    (M : GaussianPolytopeModel E) (q : E) (hv : gaussianPolytopeQueryVector M q ≠ 0) :
    let ν := gaussianPolytopeModelLaw s M
    ∀ᵐ y ∂ν.map (fun z : E => ⟪z, q⟫_ℝ),
      ‖projectionPosteriorShift ν q y‖ ^ 2 ≤
        (s ^ 2 * 72) * (1 + rankQuantileLog (cdf (ν.map (fun z : E => ⟪z, q⟫_ℝ)) y)) := by
  let μ := (euclideanGaussianLaw M.Space)[|gaussianBallPolytope M.radius M.normal M.bound]
  letI : IsProbabilityMeasure μ := cond_isProbabilityMeasure M.positive
  let v := gaussianPolytopeQueryVector M q
  have hv' : v ≠ 0 := hv
  let u := normalizedDirection v
  have hu : ‖u‖ = 1 := normalizedDirection_norm hv
  have hnv : ‖v‖ • u = v := by
    simp only [u, normalizedDirection, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv'), one_smul]
  have hL : MemLp (fun z : M.Space => z) 2 μ := by
    apply MemLp.of_bound measurable_id.aestronglyMeasurable M.radius
    filter_upwards [ae_cond_mem (μ := euclideanGaussianLaw M.Space)
      (gaussianBallPolytope_measurable M.radius M.normal M.bound)] with z hz
    simpa only [Metric.mem_closedBall, dist_zero_right, id_eq] using hz.1
  have hobs (z : M.Space) : ⟪M.origin + s • M.embedding z, q⟫_ℝ =
      ⟪M.origin, q⟫_ℝ + (s * ‖v‖) * ⟪z, u⟫_ℝ := by
    rw [show M.origin + s • M.embedding z = gaussianPolytopeModelMap s M z from rfl,
      gaussianPolytopeModelMap_inner]
    change ⟪M.origin, q⟫_ℝ + s * ⟪z, v⟫_ℝ = _
    have he : ⟪z, v⟫_ℝ = ‖v‖ * ⟪z, u⟫_ℝ := by rw [← real_inner_smul_right, hnv]
    rw [he]
    ring
  exact affine_isometry_projection_rank μ (hL.integrable (by norm_num)) M.embedding s M.origin
    u q (mul_pos hs (norm_pos_iff.mpr hv)) ⟪M.origin, q⟫_ℝ hobs 72
    (gaussian_ball_polytope_projection_rank_all_dimensions (0 : M.Space) M.radius_nonneg
      M.normal M.bound M.positive hu)

end
end Nonsmooth
