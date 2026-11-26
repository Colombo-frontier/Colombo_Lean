import Nonsmooth.GaussianPotentialDensity
import Nonsmooth.GaussianAxisDecomposition
import Nonsmooth.C2PotentialIsometryPullback

open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem unit_spans_of_finrank_one {u : E} (hu : ‖u‖ = 1)
    (hd : Module.finrank ℝ E = 1) : (ℝ ∙ u : Submodule ℝ E) = ⊤ := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  exact Submodule.eq_top_of_finrank_eq ((finrank_span_singleton hu0).trans hd.symm)

theorem euclideanGaussian_spanning_unit_reconstruction {u : E} (hu : ‖u‖ = 1)
    (hspan : (ℝ ∙ u : Submodule ℝ E) = ⊤) :
    (gaussianReal 0 1).map (fun x : ℝ => x • u) = euclideanGaussianLaw E := by
  rw [← euclideanGaussian_unit_inner_law hu,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun x : ℝ => x • u) ∘ (fun z : E => ⟪u, z⟫_ℝ) = id := by
    funext z
    have hz : z ∈ (ℝ ∙ u : Submodule ℝ E) := by rw [hspan]; trivial
    have hp := unit_orthogonalProjection_formula hu z
    simpa only [Function.comp_apply, id_eq, real_inner_comm u] using
      hp.symm.trans (Submodule.starProjection_eq_self_iff.mpr hz)
  rw [he, Measure.map_id]

theorem gaussianPotentialLaw_spanning_unit_marginal (U : E → ℝ) (hU : Measurable U)
    {u : E} (hu : ‖u‖ = 1) (hspan : (ℝ ∙ u : Submodule ℝ E) = ⊤) :
    (gaussianPotentialLaw U).map (fun z : E => ⟪u, z⟫_ℝ) =
      realDensityLaw (fun x : ℝ => Real.exp (-U (x • u))) := by
  have hr : Measurable (fun x : ℝ => x • u) := by fun_prop
  have hw : Measurable (gaussianPotentialWeight U) :=
    (((continuous_norm.pow 2).measurable.div_const 2).sub hU).exp
  have he : (fun x : ℝ => gaussianPotentialWeight U (x • u)) =
      gaussianPotentialWeight (fun x : ℝ => U (x • u)) := by
    funext x
    simp only [gaussianPotentialWeight, norm_smul, hu, mul_one]
  have hc : (fun z : E => ⟪u, z⟫_ℝ) ∘ (fun x : ℝ => x • u) = id := by
    funext x
    simp only [Function.comp_apply, id_eq, inner_smul_right, real_inner_self_eq_norm_sq,
      hu, one_pow, mul_one]
  rw [gaussianPotentialLaw, ← euclideanGaussian_spanning_unit_reconstruction hu hspan,
    ← weightedDensityLaw_map _ _ hr _ hw,
    Measure.map_map (by fun_prop) hr, hc, Measure.map_id, he]
  exact standardGaussian_potential_law (fun x => U (x • u)) (hU.comp hr)

end
end Nonsmooth
