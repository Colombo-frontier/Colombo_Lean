import Nonsmooth.PolicyGaussianCovariance
import Nonsmooth.AffinePolytopeCovariance

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianPolytopeRow_dimension_covariance
    (hb : ∀ (M : GaussianPolytopeModel E) (v : M.Space), variance (fun z : M.Space => ⟪v, z⟫_ℝ)
      ((euclideanGaussianLaw M.Space)[|gaussianBallPolytope M.radius M.normal M.bound]) ≤ ‖v‖ ^ 2)
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hν : GaussianPolytopeRow ((Real.sqrt (Module.finrank ℝ E : ℝ))⁻¹) ν) (q : E) :
    variance (fun z : E => ⟪q, z⟫_ℝ) ν ≤ ‖q‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  calc
    _ ≤ ((Real.sqrt (Module.finrank ℝ E : ℝ))⁻¹) ^ 2 * ‖q‖ ^ 2 :=
      gaussianPolytopeRow_covariance_of_models _ hb ν hν q
    _ = ‖q‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
      rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      ring

/-- This modular reduction uses a static unscaled Gaussian estimate on
finite ball-polytope regions. All affine, dimensional, and adaptive-history
transfers to the manuscript's actual posterior are proved here. -/
theorem gaussianSupportPosterior_covariance_of_base_models {r : ℕ}
    (hb : ∀ (M : GaussianPolytopeModel E) (v : M.Space), variance (fun z : M.Space => ⟪v, z⟫_ℝ)
      ((euclideanGaussianLaw M.Space)[|gaussianBallPolytope M.radius M.normal M.bound]) ≤ ‖v‖ ^ 2)
    {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    let Q := Measure.pi (fun _ : Fin (r + 1) => gaussianAmbientRowLaw E)
    ∀ᵐ h ∂Q.map (fun a => supportAugmentedTranscript p a ω n), ∀ (v : E) (i : Fin (r + 1)),
      variance (fun a : Fin (r + 1) → E => ⟪v, a i⟫_ℝ) (supportPosteriorKernel Q p ω n h) ≤
        ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ) :=
  gaussianSupportPosterior_covariance_of_polytope_bound
    (fun ν _ hν v => gaussianPolytopeRow_dimension_covariance hb ν hν v) p hp ω n

end
end Nonsmooth
