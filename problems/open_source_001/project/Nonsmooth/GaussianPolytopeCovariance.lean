import Nonsmooth.C2GaussianCovariance
import Nonsmooth.SoftWeightedVarianceLimit
import Nonsmooth.BallPolytopePotentialClass
import Nonsmooth.GaussianPolytopeWeights
import Nonsmooth.SoftGaussianDamping
import Nonsmooth.GaussianLinearTail
import Nonsmooth.GaussianPolytopeCuts

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]

theorem strictSoftInequalityWeight_gaussian_potential (f : ι → E → ℝ) (n : ℕ) :
    gaussianPotentialWeight (fun x : E => (1 + 2 / ((n : ℝ) + 1)) / 2 * ‖x‖ ^ 2 +
      softInequalityPenalty f n x) = strictSoftInequalityWeight f n := by
  funext x
  rw [gaussianPotentialWeight, strictSoftInequalityWeight, softGaussianDamping,
    softInequalityWeight_eq_exp, ← Real.exp_add]
  congr 1
  ring

theorem strict_soft_gaussian_polytope_covariance (c : E) (R : ℝ)
    (a : ι → E) (b : ι → ℝ) (n : ℕ) (v : E) :
    variance (fun z : E => ⟪v, z⟫_ℝ)
      (weightedDensityLaw (euclideanGaussianLaw E)
        (strictSoftInequalityWeight (ballPolytopeConstraint c R a b) n)) ≤ ‖v‖ ^ 2 := by
  have hρ : 1 < 1 + 2 / ((n : ℝ) + 1) := by
    have hp : 0 < 2 / ((n : ℝ) + 1) := by positivity
    linarith
  have h := c2_gaussian_directional_covariance
    (strictGaussianBallPolytopePotential_c2Strong c R a b n) hρ v
  rw [gaussianPotentialLaw, strictSoftInequalityWeight_gaussian_potential] at h
  exact h.trans (div_le_self (sq_nonneg _) hρ.le)

/-- The full static covariance estimate for an actual Gaussian
conditioned to a ball and finitely many halfspaces. -/
theorem gaussian_ball_polytope_covariance (c : E) {R : ℝ} (hR : 0 ≤ R)
    (a : ι → E) (b : ι → ℝ)
    (hp : euclideanGaussianLaw E (closedBall c R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j}) ≠ 0)
    (v : E) :
    variance (fun z : E => ⟪v, z⟫_ℝ)
      ((euclideanGaussianLaw E)[|closedBall c R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j}]) ≤ ‖v‖ ^ 2 := by
  let f := ballPolytopeConstraint c R a b
  let A := closedBall c R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j}
  have hregion : softInequalityRegion f = A := ballPolytopeConstraint_region c hR a b
  have hf (j : Option ι) : ContDiff ℝ ⊤ (f j) := ballPolytopeConstraint_contDiff c R a b j
  have hA : MeasurableSet A := by
    rw [← hregion]
    exact softInequalityRegion_measurable f (fun j => (hf j).continuous.measurable)
  have hlim : ∀ᵐ z ∂euclideanGaussianLaw E,
      Tendsto (fun n => strictSoftInequalityWeight f n z) atTop
        (𝓝 (A.indicator (fun _ => (1 : ℝ)) z)) := by
    rw [← hregion]
    exact strictSoftInequalityWeight_ae_tendsto (euclideanGaussianLaw E) f
      (ballPolytopeConstraint_gaussian_boundary_zero c R a b)
  have hm : Measurable (fun z : E => ⟪v, z⟫_ℝ) := by fun_prop
  have hL : MemLp (fun z : E => ⟪v, z⟫_ℝ) 2 (euclideanGaussianLaw E) :=
    (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
      (euclideanGaussian_inner_square_integrable v)
  exact conditioned_variance_le_of_soft_weights (euclideanGaussianLaw E) _ hm hL
    (strictSoftInequalityWeight f)
    (fun n => (strictSoftInequalityWeight_contDiff f hf n).continuous.measurable)
    (strictSoftInequalityWeight_bounds f) A hA hp hlim
    (fun n => strict_soft_gaussian_polytope_covariance c R a b n v)

theorem gaussianBallPolytope_covariance {R : ℝ} (hR : 0 ≤ R)
    (a : ι → E) (b : ι → ℝ) (hp : euclideanGaussianLaw E (gaussianBallPolytope R a b) ≠ 0)
    (v : E) : variance (fun z : E => ⟪v, z⟫_ℝ)
      ((euclideanGaussianLaw E)[|gaussianBallPolytope R a b]) ≤ ‖v‖ ^ 2 :=
  gaussian_ball_polytope_covariance 0 hR a b hp v

end
end Nonsmooth
