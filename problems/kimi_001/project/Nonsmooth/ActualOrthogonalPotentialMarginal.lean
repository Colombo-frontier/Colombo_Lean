import Nonsmooth.GaussianCoordinateIntegration
import Nonsmooth.GaussianOrthogonalCoordinateLaw
import Nonsmooth.OrthogonalMarginalClosure

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
local instance (K : Submodule ℝ E) : BorelSpace K := Subtype.borelSpace _

theorem gaussianPotentialLaw_complement_marginal (U : E → ℝ) (hU : Continuous U)
    {u : E} (hu : ‖u‖ = 1) [Nontrivial (ℝ ∙ u)ᗮ]
    {a B : ℝ} (ha : 0 < a) (hb : ∀ z, a * ‖z‖ ^ 2 - B ≤ U z) :
    (gaussianPotentialLaw U).map (ℝ ∙ u)ᗮ.orthogonalProjectionOnto =
      gaussianPotentialLaw (fun t : (ℝ ∙ u)ᗮ =>
        -Real.log (∫ x : ℝ, Real.exp (-U ((t : E) + x • u)))) := by
  let K : Submodule ℝ E := (ℝ ∙ u)ᗮ
  let reconstruct : K × ℝ → E := fun p => (p.1 : E) + p.2 • u
  have hr : Measurable reconstruct := by fun_prop
  have hw : Measurable (gaussianPotentialWeight U) :=
    (((continuous_norm.pow 2).measurable.div_const 2).sub hU.measurable).exp
  have hn (t : K) (x : ℝ) : ‖(t : E) + x • u‖ ^ 2 = ‖t‖ ^ 2 + x ^ 2 :=
    orthogonal_coordinate_norm_sq K.subtypeₗᵢ u hu
      (orthogonal_complement_axis_inner u) t x
  have hrec : ((euclideanGaussianLaw K).prod (gaussianReal 0 1)).map reconstruct =
      euclideanGaussianLaw E := euclideanGaussian_complement_axis_reconstruction hu
  have hleft : K.orthogonalProjectionOnto ∘ reconstruct = Prod.fst := by
    funext p
    exact orthogonal_complement_coordinate_projection u p.1 p.2
  change (weightedDensityLaw (euclideanGaussianLaw E) (gaussianPotentialWeight U)).map _ = _
  rw [← hrec, ← weightedDensityLaw_map _ reconstruct hr _ hw,
    Measure.map_map K.orthogonalProjectionOnto.measurable hr, hleft]
  have hweight : (fun p : K × ℝ => gaussianPotentialWeight U (reconstruct p)) =
      fun p : K × ℝ => Real.exp ((‖p.1‖ ^ 2 + p.2 ^ 2) / 2 - U ((p.1 : E) + p.2 • u)) := by
    funext p
    simp only [gaussianPotentialWeight, reconstruct, hn]
  rw [hweight]
  apply gaussian_coordinate_weight_marginal
    (euclideanGaussianLaw K) (fun t x => U ((t : E) + x • u))
  · exact hU.comp (by fun_prop)
  · exact ha
  · intro t x
    have h := hb ((t : E) + x • u)
    rw [hn] at h
    nlinarith [mul_nonneg ha.le (sq_nonneg ‖t‖)]

/-- The actual projected law and all analytic closure properties are
obtained together from the original potential. -/
theorem c2StrongQuadraticPotential_actual_complement_marginal {U : E → ℝ} {ρ : ℝ}
    (hU : C2StrongQuadraticPotential U ρ) (hρ : 1 < ρ)
    {u : E} (hu : ‖u‖ = 1) [Nontrivial (ℝ ∙ u)ᗮ] :
    let V := fun t : (ℝ ∙ u)ᗮ => -Real.log (∫ x : ℝ, Real.exp (-U ((t : E) + x • u)))
    C2StrongQuadraticPotential V ρ ∧
      (gaussianPotentialLaw U).map (ℝ ∙ u)ᗮ.orthogonalProjectionOnto = gaussianPotentialLaw V := by
  dsimp only
  constructor
  · exact c2StrongQuadraticPotential_orthogonal_marginal hU hρ (ℝ ∙ u)ᗮ.subtypeₗᵢ u hu
      (orthogonal_complement_axis_inner u)
  · obtain ⟨a, B, ha, _, hb⟩ := hU.envelope
    exact gaussianPotentialLaw_complement_marginal U hU.smooth.continuous hu ha (fun z => (hb z).1)

end
end Nonsmooth
