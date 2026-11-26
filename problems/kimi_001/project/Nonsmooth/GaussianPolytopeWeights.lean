import Nonsmooth.GaussianQuadraticBoundary
import Nonsmooth.AffineBallConstraints

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology InnerProductSpace ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem affineSoftConstraint_gaussian_boundary_zero (a : E) (b : ℝ) :
    euclideanGaussianLaw E {x : E | affineSoftConstraint a b x = 0} = 0 := by
  by_cases ha : a = 0
  · by_cases hb : 0 ≤ b <;> simp [affineSoftConstraint, ha, hb]
  · simpa only [affineSoftConstraint, if_neg ha, sub_eq_zero] using
      euclideanGaussian_hyperplane_zero ha b

theorem ballPolytopeConstraint_gaussian_boundary_zero (c : E) (R : ℝ)
    (a : ι → E) (b : ι → ℝ) (j : Option ι) :
    euclideanGaussianLaw E {x : E | ballPolytopeConstraint c R a b j x = 0} = 0 := by
  cases j with
  | none =>
    simpa only [ballPolytopeConstraint, sub_eq_zero] using
      euclideanGaussian_squared_distance_level_zero c (R ^ 2)
  | some j => exact affineSoftConstraint_gaussian_boundary_zero (a j) (b j)

theorem gaussian_ball_polytope_soft_approximation [Fintype ι] (c : E) {R : ℝ} (hR : 0 ≤ R)
    (a : ι → E) (b : ι → ℝ) :
    (∀ n, ContDiff ℝ ⊤ (softInequalityWeight (ballPolytopeConstraint c R a b) n)) ∧
    (∀ n x, 0 < softInequalityWeight (ballPolytopeConstraint c R a b) n x ∧
      softInequalityWeight (ballPolytopeConstraint c R a b) n x ≤ 1) ∧
    (∀ᵐ x ∂euclideanGaussianLaw E,
      Tendsto (fun n => softInequalityWeight (ballPolytopeConstraint c R a b) n x) atTop
        (𝓝 ((closedBall c R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j}).indicator
          (fun _ => (1 : ℝ)) x))) := by
  refine ⟨fun n => softInequalityWeight_contDiff _ (ballPolytopeConstraint_contDiff c R a b) n,
    fun n x => ⟨softInequalityWeight_pos _ n x, softInequalityWeight_le_one _ n x⟩, ?_⟩
  have h := softInequalityWeight_ae_tendsto (euclideanGaussianLaw E) _
    (ballPolytopeConstraint_gaussian_boundary_zero c R a b)
  simpa only [ballPolytopeConstraint_region c hR a b] using h

theorem gaussian_ball_polytope_soft_strongConvex [Fintype ι] (c : E) (R ρ : ℝ)
    (a : ι → E) (b : ι → ℝ) (n : ℕ) :
    StrongConvexOn univ ρ (fun x : E => ρ / 2 * ‖x‖ ^ 2 +
      softInequalityPenalty (ballPolytopeConstraint c R a b) n x) := by
  apply softInequalityPotential_strongConvex _ _ ?_ (ballPolytopeConstraint_convex c R a b) n
  apply strongConvexOn_iff_convex.mpr
  simp only [sub_self]
  exact convexOn_const 0 convex_univ

end
end Nonsmooth
