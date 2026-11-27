import Nonsmooth.GaussianPolytopeProjectionClosure

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def gaussianPolytopeLoserModel (M : GaussianPolytopeModel E) (v : M.Space) (t : ℝ)
    (hp : euclideanGaussianLaw M.Space (gaussianBallPolytope M.radius
      (Option.elim' v M.normal) (Option.elim' t M.bound)) ≠ 0) : GaussianPolytopeModel E where
  Space := M.Space
  Index := Option M.Index
  embedding := M.embedding
  origin := M.origin
  radius := M.radius
  radius_nonneg := M.radius_nonneg
  normal := Option.elim' v M.normal
  bound := Option.elim' t M.bound
  positive := hp

theorem gaussianPolytopeModel_halfspace_closed {s : ℝ} (hs : 0 < s)
    (M : GaussianPolytopeModel E) (q : E) (y : ℝ)
    (hpos : gaussianPolytopeModelLaw s M {z : E | ⟪z, q⟫_ℝ ≤ y} ≠ 0) :
    GaussianPolytopeRow s ((gaussianPolytopeModelLaw s M)[|{z : E | ⟪z, q⟫_ℝ ≤ y}]) := by
  let v := gaussianPolytopeQueryVector M q
  let t := (y - ⟪M.origin, q⟫_ℝ) / s
  let f := gaussianPolytopeModelMap s M
  let μ := (euclideanGaussianLaw M.Space)[|gaussianBallPolytope M.radius M.normal M.bound]
  have hf : Measurable f := gaussianPolytopeModelMap_measurable s M
  have hX : Measurable (fun z : E => ⟪z, q⟫_ℝ) := by fun_prop
  have hA := measurableSet_le hX (measurable_const (a := y))
  have hpre : f ⁻¹' {z : E | ⟪z, q⟫_ℝ ≤ y} = {z : M.Space | ⟪z, v⟫_ℝ ≤ t} := by
    ext z
    change ⟪gaussianPolytopeModelMap s M z, q⟫_ℝ ≤ y ↔ ⟪z, v⟫_ℝ ≤ t
    rw [gaussianPolytopeModelMap_inner]
    dsimp only [t, v]
    rw [le_div_iff₀ hs]
    constructor <;> intro hz <;> nlinarith
  change (μ.map f) {z : E | ⟪z, q⟫_ℝ ≤ y} ≠ 0 at hpos
  rw [Measure.map_apply hf hA, hpre] at hpos
  have hp := gaussian_polytope_halfspace_positive M.radius M.normal M.bound v t hpos
  refine Or.inr ⟨gaussianPolytopeLoserModel M v t hp, ?_⟩
  change (μ.map f)[|{z : E | ⟪z, q⟫_ℝ ≤ y}] = _
  rw [conditioning_map_preimage μ f hf _ hA, hpre]
  change (μ[|{z : M.Space | ⟪z, v⟫_ℝ ≤ t}]).map f = _
  rw [gaussian_polytope_condition_halfspace]
  rfl

theorem gaussianPolytopeModel_hyperplane_zero {s : ℝ} (hs : 0 < s)
    (M : GaussianPolytopeModel E) (q : E) (hv : gaussianPolytopeQueryVector M q ≠ 0) (y : ℝ) :
    gaussianPolytopeModelLaw s M {z : E | ⟪z, q⟫_ℝ = y} = 0 := by
  let f := gaussianPolytopeModelMap s M
  have hf : Measurable f := gaussianPolytopeModelMap_measurable s M
  have hX : Measurable (fun z : E => ⟪z, q⟫_ℝ) := by fun_prop
  have hA := measurableSet_eq_fun hX (measurable_const (a := y))
  change (((euclideanGaussianLaw M.Space)[|gaussianBallPolytope M.radius M.normal M.bound]).map f)
    {z : E | ⟪z, q⟫_ℝ = y} = 0
  rw [Measure.map_apply hf hA, cond_apply (gaussianBallPolytope_measurable M.radius M.normal M.bound)]
  have hz : euclideanGaussianLaw M.Space
      (gaussianBallPolytope M.radius M.normal M.bound ∩ f ⁻¹' {z : E | ⟪z, q⟫_ℝ = y}) = 0 := by
    apply measure_mono_null ?_ (euclideanGaussian_hyperplane_zero hv ((y - ⟪M.origin, q⟫_ℝ) / s))
    intro z hz
    have he := gaussianPolytopeModelMap_inner s M q z
    have hy : ⟪gaussianPolytopeModelMap s M z, q⟫_ℝ = y := hz.2
    change ⟪gaussianPolytopeQueryVector M q, z⟫_ℝ = (y - ⟪M.origin, q⟫_ℝ) / s
    rw [real_inner_comm, eq_div_iff hs.ne']
    nlinarith
  rw [hz, mul_zero]

end
end Nonsmooth
