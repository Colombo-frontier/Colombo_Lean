import Nonsmooth.GaussianPolytopeConcentration
import Nonsmooth.AffinePolytopeCovariance

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianPolytopeModel_centered_mgf (s : ℝ) (M : GaussianPolytopeModel E) (q : E) (t : ℝ) :
    let ν := gaussianPolytopeModelLaw s M
    Integrable (fun z : E => Real.exp (t * (⟪q, z⟫_ℝ - ∫ y, ⟪q, y⟫_ℝ ∂ν))) ν ∧
      (∫ z : E, Real.exp (t * (⟪q, z⟫_ℝ - ∫ y, ⟪q, y⟫_ℝ ∂ν)) ∂ν) ≤
        Real.exp (t ^ 2 * s ^ 2 * ‖q‖ ^ 2 / 2) := by
  let μ := (euclideanGaussianLaw M.Space)[|gaussianBallPolytope M.radius M.normal M.bound]
  let f := gaussianPolytopeModelMap s M
  let v := gaussianPolytopeQueryVector M q
  letI : IsProbabilityMeasure μ := cond_isProbabilityMeasure M.positive
  have hf : Measurable f := gaussianPolytopeModelMap_measurable s M
  have hg : StronglyMeasurable (fun z : E => ⟪q, z⟫_ℝ) :=
    (continuous_const.inner continuous_id).stronglyMeasurable
  have hL : MemLp (fun z : M.Space => z) 2 μ := by
    apply MemLp.of_bound measurable_id.aestronglyMeasurable M.radius
    filter_upwards [ae_cond_mem (μ := euclideanGaussianLaw M.Space)
      (gaussianBallPolytope_measurable M.radius M.normal M.bound)] with z hz
    simpa only [Metric.mem_closedBall, dist_zero_right, id_eq] using hz.1
  have hi : Integrable (fun z : M.Space => ⟪v, z⟫_ℝ) μ := (hL.const_inner v).integrable (by norm_num)
  have he (z : M.Space) : ⟪q, f z⟫_ℝ = ⟪q, M.origin⟫_ℝ + s * ⟪v, z⟫_ℝ := by
    simpa only [f, v, real_inner_comm q, real_inner_comm (gaussianPolytopeQueryVector M q)] using
      gaussianPolytopeModelMap_inner s M q z
  have hmean : (∫ z : E, ⟪q, z⟫_ℝ ∂gaussianPolytopeModelLaw s M) =
      ⟪q, M.origin⟫_ℝ + s * ∫ z : M.Space, ⟪v, z⟫_ℝ ∂μ := by
    change (∫ z : E, ⟪q, z⟫_ℝ ∂μ.map f) = _
    rw [integral_map_of_stronglyMeasurable hf hg]
    simp_rw [he]
    rw [integral_add (integrable_const _) (hi.const_mul s), integral_const, integral_const_mul]
    simp only [probReal_univ, one_smul]
  let φ : E → ℝ := fun z => Real.exp (t * (⟪q, z⟫_ℝ -
    ∫ y, ⟪q, y⟫_ℝ ∂gaussianPolytopeModelLaw s M))
  have hφ : StronglyMeasurable φ := (by fun_prop : Continuous φ).stronglyMeasurable
  have hφf (z : M.Space) : φ (f z) = Real.exp ((t * s) * (⟪v, z⟫_ℝ - ∫ y, ⟪v, y⟫_ℝ ∂μ)) := by
    dsimp only [φ]
    rw [he, hmean]
    congr 1
    ring
  have hbase := gaussian_ball_polytope_centered_mgf (0 : M.Space) M.radius_nonneg
    M.normal M.bound M.positive v (t * s)
  change Integrable φ (μ.map f) ∧ (∫ z, φ z ∂μ.map f) ≤ _
  constructor
  · apply (integrable_map_measure hφ.aestronglyMeasurable hf.aemeasurable).mpr
    change Integrable (fun z => φ (f z)) μ
    simp_rw [hφf]
    exact hbase.1
  · rw [integral_map_of_stronglyMeasurable hf hφ]
    simp_rw [hφf]
    apply hbase.2.trans
    apply Real.exp_le_exp.mpr
    have hn := (sq_le_sq₀ (norm_nonneg v) (norm_nonneg q)).mpr
      (gaussianPolytopeQueryVector_norm_le M q)
    have hmul := mul_le_mul_of_nonneg_left hn (mul_nonneg (sq_nonneg t) (sq_nonneg s))
    nlinarith

end
end Nonsmooth
