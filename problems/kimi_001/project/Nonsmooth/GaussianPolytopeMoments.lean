import Nonsmooth.GaussianPolytopeModel

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianPolytopeModelLaw_norm_bound (s : ℝ) (M : GaussianPolytopeModel E) :
    ∀ᵐ z ∂gaussianPolytopeModelLaw s M, ‖z‖ ≤ ‖M.origin‖ + |s| * M.radius := by
  have hm := gaussianPolytopeModelMap_measurable s M
  have hB := measurableSet_le (measurable_norm : Measurable (fun z : E => ‖z‖))
    (measurable_const (a := ‖M.origin‖ + |s| * M.radius))
  apply (ae_map_iff hm.aemeasurable hB).mpr
  filter_upwards [ae_cond_mem (μ := euclideanGaussianLaw M.Space)
    (gaussianBallPolytope_measurable M.radius M.normal M.bound)] with z hz
  have hr : ‖z‖ ≤ M.radius := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1
  calc
    ‖gaussianPolytopeModelMap s M z‖ ≤ ‖M.origin‖ + ‖s • M.embedding z‖ := norm_add_le _ _
    _ = ‖M.origin‖ + |s| * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs, M.embedding.norm_map]
    _ ≤ ‖M.origin‖ + |s| * M.radius := add_le_add le_rfl (mul_le_mul_of_nonneg_left hr (abs_nonneg s))

theorem gaussianPolytopeModelLaw_memLp (s : ℝ) (M : GaussianPolytopeModel E) :
    MemLp (fun z : E => z) 2 (gaussianPolytopeModelLaw s M) :=
  MemLp.of_bound measurable_id.aestronglyMeasurable (‖M.origin‖ + |s| * M.radius)
    (gaussianPolytopeModelLaw_norm_bound s M)

theorem gaussianPolytopeRow_memLp (s : ℝ) (ν : Measure E) [IsProbabilityMeasure ν]
    (hν : GaussianPolytopeRow s ν) : MemLp (fun z : E => z) 2 ν := by
  rcases hν with ⟨x, rfl⟩ | ⟨M, rfl⟩
  · apply MemLp.of_bound measurable_id.aestronglyMeasurable ‖x‖
    filter_upwards [ae_eq_dirac (fun z : E => z)] with z hz
    exact (congrArg (fun z : E => ‖z‖) hz).le
  · exact gaussianPolytopeModelLaw_memLp s M

end
end Nonsmooth
