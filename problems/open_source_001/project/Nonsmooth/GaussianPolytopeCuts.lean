import Nonsmooth.GaussianPolytopeSlices

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]

def gaussianBallPolytope (R : ℝ) (a : ι → E) (b : ι → ℝ) : Set E :=
  closedBall (0 : E) R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j}

theorem gaussianBallPolytope_measurable (R : ℝ) (a : ι → E) (b : ι → ℝ) :
    MeasurableSet (gaussianBallPolytope R a b) := by
  have hm (j : ι) : Measurable (fun z : E => ⟪a j, z⟫_ℝ) := by fun_prop
  apply measurableSet_closedBall.inter
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter (fun j => measurableSet_le (hm j) measurable_const)

theorem gaussianBallPolytope_append (R : ℝ) (a : ι → E) (b : ι → ℝ) (u : E) (t : ℝ) :
    gaussianBallPolytope R a b ∩ {z : E | ⟪z, u⟫_ℝ ≤ t} =
      gaussianBallPolytope R (Option.elim' u a) (Option.elim' t b) := by
  ext z
  simp only [gaussianBallPolytope, mem_inter_iff, mem_setOf_eq, Option.forall,
    Option.elim'_none, Option.elim'_some, real_inner_comm z u]
  tauto

theorem gaussian_polytope_condition_halfspace (R : ℝ) (a : ι → E) (b : ι → ℝ) (u : E) (t : ℝ) :
    ((euclideanGaussianLaw E)[|gaussianBallPolytope R a b])[|{z : E | ⟪z, u⟫_ℝ ≤ t}] =
      (euclideanGaussianLaw E)[|gaussianBallPolytope R (Option.elim' u a) (Option.elim' t b)] := by
  have hr : Measurable (fun z : E => ⟪z, u⟫_ℝ) := by fun_prop
  rw [cond_cond_eq_cond_inter (gaussianBallPolytope_measurable R a b)
    (measurableSet_le hr measurable_const), gaussianBallPolytope_append]

theorem gaussian_polytope_halfspace_positive (R : ℝ) (a : ι → E) (b : ι → ℝ) (u : E) (t : ℝ)
    (hp : ((euclideanGaussianLaw E)[|gaussianBallPolytope R a b]) {z : E | ⟪z, u⟫_ℝ ≤ t} ≠ 0) :
    euclideanGaussianLaw E (gaussianBallPolytope R (Option.elim' u a) (Option.elim' t b)) ≠ 0 := by
  intro hz
  apply hp
  rw [cond_apply (gaussianBallPolytope_measurable R a b), gaussianBallPolytope_append,
    hz, mul_zero]

theorem gaussian_polytope_strict_halfspace (R : ℝ) (a : ι → E) (b : ι → ℝ)
    {u : E} (hu : u ≠ 0) (t : ℝ) :
    ((euclideanGaussianLaw E)[|gaussianBallPolytope R a b])[|{z : E | ⟪z, u⟫_ℝ < t}] =
      (euclideanGaussianLaw E)[|gaussianBallPolytope R (Option.elim' u a) (Option.elim' t b)] := by
  have hz : ∀ᵐ z ∂euclideanGaussianLaw E, ⟪z, u⟫_ℝ ≠ t := by
    rw [ae_iff]
    simpa only [not_not, real_inner_comm u] using euclideanGaussian_hyperplane_zero hu t
  have hc := Measure.ae_smul_measure
    (ae_restrict_of_ae (s := gaussianBallPolytope R a b) hz)
    ((euclideanGaussianLaw E (gaussianBallPolytope R a b))⁻¹)
  have he : {z : E | ⟪z, u⟫_ℝ < t} =ᵐ[(euclideanGaussianLaw E)[|gaussianBallPolytope R a b]]
      {z : E | ⟪z, u⟫_ℝ ≤ t} := by
    filter_upwards [hc] with z hz
    exact propext (lt_iff_le_and_ne.trans (and_iff_left hz))
  rw [← gaussian_polytope_condition_halfspace R a b u t]
  exact congrArg₂ (fun (c : ENNReal) (ν : Measure E) => c⁻¹ • ν)
    (measure_congr he) (Measure.restrict_congr_set he)

end
end Nonsmooth
