import Nonsmooth.GaussianAxisDecomposition
import Nonsmooth.SoftInequalityWeights

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology InnerProductSpace ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem atomless_quadratic_level_zero (μ : Measure ℝ) (hatom : ∀ x, μ {x} = 0)
    (a b r : ℝ) : μ {t : ℝ | t ^ 2 + a * t + b = r} = 0 := by
  by_cases h : ({t : ℝ | t ^ 2 + a * t + b = r} : Set ℝ).Nonempty
  · obtain ⟨y, hy⟩ := h
    apply measure_mono_null (t := ({y} ∪ {-a - y} : Set ℝ)) ?_
      (measure_union_null (hatom y) (hatom (-a - y)))
    intro t ht
    have hp : (t - y) * (t + y + a) = 0 := by
      have ht' : t ^ 2 + a * t + b = r := ht
      have hy' : y ^ 2 + a * y + b = r := hy
      nlinarith
    rcases mul_eq_zero.mp hp with hty | hty
    · exact Or.inl (by simpa only [mem_singleton_iff] using sub_eq_zero.mp hty)
    · exact Or.inr (by simp only [mem_singleton_iff]; linarith)
  · rw [Set.not_nonempty_iff_eq_empty.mp h, measure_empty]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem euclideanGaussian_squared_distance_level_zero (c : E) (r : ℝ) :
    euclideanGaussianLaw E {x : E | ‖x - c‖ ^ 2 = r} = 0 := by
  let j : Fin (Module.finrank ℝ E) := ⟨0, Module.finrank_pos⟩
  let u : E := stdOrthonormalBasis ℝ E j
  have hu : ‖u‖ = 1 := (stdOrthonormalBasis ℝ E).orthonormal.1 j
  have hA : MeasurableSet {x : E | ‖x - c‖ ^ 2 = r} :=
    measurableSet_eq_fun ((continuous_id.sub continuous_const).norm.pow 2).measurable measurable_const
  have hrec : Measurable (fun p : E × ℝ => p.2 • u + p.1) := by fun_prop
  rw [← euclideanGaussian_axis_reconstruction hu, Measure.map_apply hrec hA]
  apply Measure.measure_prod_null_of_ae_null (hrec hA)
  apply Eventually.of_forall
  intro z
  have hn (t : ℝ) : ‖t • u + z - c‖ ^ 2 = t ^ 2 + (2 * ⟪u, z - c⟫_ℝ) * t + ‖z - c‖ ^ 2 := by
    have he : t • u + z - c = t • u + (z - c) := by abel
    rw [he, norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, hu, mul_one, real_inner_smul_left, sq_abs]
    ring
  have hz := atomless_quadratic_level_zero (gaussianReal 0 1)
    (fun y => gaussianReal_absolutelyContinuous 0 (by norm_num : (1 : NNReal) ≠ 0) (measure_singleton y))
    (2 * ⟪u, z - c⟫_ℝ) (‖z - c‖ ^ 2) r
  change gaussianReal 0 1 {t : ℝ | ‖t • u + z - c‖ ^ 2 = r} = 0
  have he : {t : ℝ | ‖t • u + z - c‖ ^ 2 = r} =
      {t : ℝ | t ^ 2 + (2 * ⟪u, z - c⟫_ℝ) * t + ‖z - c‖ ^ 2 = r} := by
    ext t
    simp only [mem_setOf_eq, hn]
  rw [he]
  exact hz

theorem euclideanGaussian_sphere_zero (c : E) (r : ℝ) :
    euclideanGaussianLaw E (sphere c r) = 0 := by
  apply measure_mono_null ?_ (euclideanGaussian_squared_distance_level_zero c (r ^ 2))
  intro x hx
  have h : ‖x - c‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hx
  exact congrArg (fun t : ℝ => t ^ 2) h

end
end Nonsmooth
