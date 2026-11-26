import Nonsmooth.GaussianPolytopeMoments
import Nonsmooth.GaussianPolytopeProjectionClosure

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem variance_real_affine {α : Type} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Integrable f μ) (b c : ℝ) :
    variance (fun x => b + c * f x) μ = c ^ 2 * variance f μ := by
  have hm : (∫ x, b + c * f x ∂μ) = b + c * ∫ x, f x ∂μ := by
    rw [integral_add (integrable_const b) (hf.const_mul c), integral_const, integral_const_mul]
    simp only [measureReal_univ_eq_one, one_smul]
  have hg : AEMeasurable (fun x => b + c * f x) μ :=
    aemeasurable_const.add (aemeasurable_const.mul hf.aestronglyMeasurable.aemeasurable)
  rw [variance_eq_integral hg, hm]
  have he : (fun x => (b + c * f x - (b + c * ∫ y, f y ∂μ)) ^ 2) =
      fun x => c ^ 2 * (f x - ∫ y, f y ∂μ) ^ 2 := by
    funext x
    ring
  rw [he, integral_const_mul, variance_eq_integral hf.aestronglyMeasurable.aemeasurable]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianPolytopeQueryVector_norm_le (M : GaussianPolytopeModel E) (q : E) :
    ‖gaussianPolytopeQueryVector M q‖ ≤ ‖q‖ := by
  let v := gaussianPolytopeQueryVector M q
  change ‖v‖ ≤ ‖q‖
  have he : ‖v‖ ^ 2 = ⟪q, M.embedding v⟫_ℝ := by
    have h := M.embedding.toContinuousLinearMap.adjoint_inner_left v q
    change ⟪v, v⟫_ℝ = ⟪q, M.embedding v⟫_ℝ at h
    simpa only [real_inner_self_eq_norm_sq] using h
  have hb : ‖v‖ * ‖v‖ ≤ ‖q‖ * ‖v‖ := by
    calc
      _ = ⟪q, M.embedding v⟫_ℝ := by simpa only [pow_two] using he
      _ ≤ |⟪q, M.embedding v⟫_ℝ| := le_abs_self _
      _ ≤ ‖q‖ * ‖M.embedding v‖ := abs_real_inner_le_norm _ _
      _ = ‖q‖ * ‖v‖ := by rw [M.embedding.norm_map]
  by_cases hv : v = 0
  · simpa only [hv, norm_zero] using norm_nonneg q
  · exact (mul_le_mul_iff_of_pos_right (norm_pos_iff.mpr hv)).mp hb

theorem gaussianPolytopeModel_covariance_of_base (s : ℝ) (M : GaussianPolytopeModel E)
    (hb : ∀ v : M.Space, variance (fun z : M.Space => ⟪v, z⟫_ℝ)
      ((euclideanGaussianLaw M.Space)[|gaussianBallPolytope M.radius M.normal M.bound]) ≤ ‖v‖ ^ 2)
    (q : E) : variance (fun z : E => ⟪q, z⟫_ℝ) (gaussianPolytopeModelLaw s M) ≤ s ^ 2 * ‖q‖ ^ 2 := by
  let μ := (euclideanGaussianLaw M.Space)[|gaussianBallPolytope M.radius M.normal M.bound]
  let v := gaussianPolytopeQueryVector M q
  letI : IsProbabilityMeasure μ := cond_isProbabilityMeasure M.positive
  have hL : MemLp (fun z : M.Space => z) 2 μ := by
    apply MemLp.of_bound measurable_id.aestronglyMeasurable M.radius
    filter_upwards [ae_cond_mem (μ := euclideanGaussianLaw M.Space)
      (gaussianBallPolytope_measurable M.radius M.normal M.bound)] with z hz
    simpa only [Metric.mem_closedBall, dist_zero_right, id_eq] using hz.1
  have hi : Integrable (fun z : M.Space => ⟪z, v⟫_ℝ) μ := by
    simpa only [real_inner_comm v] using (hL.const_inner v).integrable (by norm_num)
  rw [gaussianPolytopeModelLaw, variance_map_measurable μ _ (gaussianPolytopeModelMap_measurable s M)
    (fun z : E => ⟪q, z⟫_ℝ) (by fun_prop)]
  have he : ((fun z : E => ⟪q, z⟫_ℝ) ∘ gaussianPolytopeModelMap s M) =
      fun z : M.Space => ⟪M.origin, q⟫_ℝ + s * ⟪z, v⟫_ℝ := by
    funext z
    simpa only [Function.comp_def, real_inner_comm q] using gaussianPolytopeModelMap_inner s M q z
  rw [he, variance_real_affine μ _ hi]
  have hb' : variance (fun z : M.Space => ⟪z, v⟫_ℝ) μ ≤ ‖v‖ ^ 2 := by
    simpa only [real_inner_comm v] using hb v
  apply (mul_le_mul_of_nonneg_left hb' (sq_nonneg s)).trans
  exact mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg v) (norm_nonneg q)).mpr (gaussianPolytopeQueryVector_norm_le M q))
    (sq_nonneg s)

theorem gaussianPolytopeRow_covariance_of_models (s : ℝ)
    (hb : ∀ (M : GaussianPolytopeModel E) (v : M.Space), variance (fun z : M.Space => ⟪v, z⟫_ℝ)
      ((euclideanGaussianLaw M.Space)[|gaussianBallPolytope M.radius M.normal M.bound]) ≤ ‖v‖ ^ 2)
    (ν : Measure E) [IsProbabilityMeasure ν] (hν : GaussianPolytopeRow s ν) (q : E) :
    variance (fun z : E => ⟪q, z⟫_ℝ) ν ≤ s ^ 2 * ‖q‖ ^ 2 := by
  rcases hν with ⟨x, rfl⟩ | ⟨M, rfl⟩
  · rw [variance_eq_integral (by fun_prop)]
    simp only [integral_dirac, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    positivity
  · exact gaussianPolytopeModel_covariance_of_base s M (hb M) q

end
end Nonsmooth
