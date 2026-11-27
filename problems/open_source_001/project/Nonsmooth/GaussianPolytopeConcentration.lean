import Nonsmooth.C2GaussianConcentration
import Nonsmooth.GaussianPolytopeCovariance
import Nonsmooth.SoftWeightMGF
import Nonsmooth.GaussianLinearMGF

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]

theorem strict_soft_gaussian_polytope_centered_mgf (c : E) (R : ℝ)
    (a : ι → E) (b : ι → ℝ) (n : ℕ) (v : E) (t : ℝ) :
    let μ := weightedDensityLaw (euclideanGaussianLaw E)
      (strictSoftInequalityWeight (ballPolytopeConstraint c R a b) n)
    (∫ z : E, Real.exp (t * (⟪v, z⟫_ℝ - ∫ y, ⟪v, y⟫_ℝ ∂μ)) ∂μ) ≤
      Real.exp (t ^ 2 * ‖v‖ ^ 2 / 2) := by
  dsimp only
  have hρ : 1 < 1 + 2 / ((n : ℝ) + 1) := by
    have hp : 0 < 2 / ((n : ℝ) + 1) := by positivity
    linarith
  have h := (c2_gaussian_direction_centered_mgf
    (strictGaussianBallPolytopePotential_c2Strong c R a b n) hρ v t).2
  rw [gaussianPotentialLaw, strictSoftInequalityWeight_gaussian_potential] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg t) (sq_nonneg ‖v‖)) (by norm_num)
  linarith

theorem gaussian_ball_polytope_centered_mgf (c : E) {R : ℝ} (hR : 0 ≤ R)
    (a : ι → E) (b : ι → ℝ)
    (hp : euclideanGaussianLaw E (closedBall c R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j}) ≠ 0)
    (v : E) (t : ℝ) :
    let μ := (euclideanGaussianLaw E)[|closedBall c R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j}]
    Integrable (fun z : E => Real.exp (t * (⟪v, z⟫_ℝ - ∫ y, ⟪v, y⟫_ℝ ∂μ))) μ ∧
      (∫ z : E, Real.exp (t * (⟪v, z⟫_ℝ - ∫ y, ⟪v, y⟫_ℝ ∂μ)) ∂μ) ≤
        Real.exp (t ^ 2 * ‖v‖ ^ 2 / 2) := by
  dsimp only
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
  have hExp : Integrable (fun z : E => Real.exp (t * ⟪v, z⟫_ℝ)) (euclideanGaussianLaw E) := by
    simpa only [real_inner_smul_left] using euclideanGaussian_exp_inner_integrable (t • v)
  exact soft_weighted_centered_mgf_bound (euclideanGaussianLaw E) _
    (hL.integrable (by norm_num)) t hExp (strictSoftInequalityWeight f)
    (fun n => (strictSoftInequalityWeight_contDiff f hf n).continuous.measurable)
    (fun n z => ⟨(strictSoftInequalityWeight_bounds f n z).1.le,
      (strictSoftInequalityWeight_bounds f n z).2⟩) A hA hp hlim _
    (fun n => strict_soft_gaussian_polytope_centered_mgf c R a b n v t)

end
end Nonsmooth
