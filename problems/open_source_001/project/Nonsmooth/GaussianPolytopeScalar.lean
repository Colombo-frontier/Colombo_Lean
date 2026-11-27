import Nonsmooth.GaussianPolytopePosterior
import Nonsmooth.ConditionalReencoding

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
local instance (K : Submodule ℝ E) : BorelSpace K := Subtype.borelSpace _

theorem gaussian_polytope_scalar_subspace_posterior {u : E} (hu : ‖u‖ = 1)
    [Nontrivial (ℝ ∙ u)ᗮ] {R : ℝ} (hR : 0 ≤ R) (a : ι → E) (b : ι → ℝ) :
    let A := closedBall (0 : E) R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j}
    ∀ᵐ y ∂((euclideanGaussianLaw E)[|A]).map (fun z : E => ⟪z, u⟫_ℝ),
      let B := closedBall (0 : (ℝ ∙ u)ᗮ) (Real.sqrt (R ^ 2 - y ^ 2)) ∩
        {z : (ℝ ∙ u)ᗮ | ∀ j, ⟪(ℝ ∙ u)ᗮ.orthogonalProjection (a j), z⟫_ℝ ≤ b j - y * ⟪a j, u⟫_ℝ}
      0 < R ^ 2 - y ^ 2 ∧ euclideanGaussianLaw (ℝ ∙ u)ᗮ B ≠ 0 ∧
      condDistrib id (fun z : E => ⟪z, u⟫_ℝ) ((euclideanGaussianLaw E)[|A]) y =
        ((euclideanGaussianLaw (ℝ ∙ u)ᗮ)[|B]).map (fun z : (ℝ ∙ u)ᗮ => y • u + (z : E)) := by
  let A := closedBall (0 : E) R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j}
  let μ := (euclideanGaussianLaw E)[|A]
  let P : E →L[ℝ] E := (ℝ ∙ u).subtypeL.comp (ℝ ∙ u).orthogonalProjection
  let r : E → ℝ := fun z => ⟪z, u⟫_ℝ
  let g : ℝ → E := fun y => y • u
  have hr : Measurable r := (continuous_id.inner continuous_const).measurable
  have hg : Measurable g := measurable_id.smul measurable_const
  have hZX (z : E) : r z = r (P z) := by
    change ⟪z, u⟫_ℝ = ⟪((ℝ ∙ u).orthogonalProjection z : E), u⟫_ℝ
    rw [unit_orthogonalProjection_formula hu, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hu]
    ring
  have hXZ (z : E) : g (r z) = P z := (unit_orthogonalProjection_formula hu z).symm
  have he := condDistrib_reencoding μ P P.measurable id measurable_id r hr r hr g hg hZX hXZ
  have hm : (μ.map r).map g = μ.map P := by
    rw [Measure.map_map hg hr]
    congr 1
    funext z
    exact hXZ z
  have hp := gaussian_polytope_projection_subspace_posterior (ℝ ∙ u) hR a b
  change ∀ᵐ x ∂μ.map P, _ at hp
  rw [← hm] at hp
  have hpull := ae_of_ae_map hg.aemeasurable hp
  filter_upwards [hpull, he] with y hy heq
  change 0 < R ^ 2 - ‖y • u‖ ^ 2 ∧ _ ∧ _ at hy
  simp only [g, norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs,
    real_inner_smul_right] at hy
  rw [← heq]
  exact hy

end
end Nonsmooth
