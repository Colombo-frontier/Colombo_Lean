import Nonsmooth.GaussianLeftInterval
import Nonsmooth.SymmetricHalfspaceMoment
import Nonsmooth.GaussianProjectionAtoms

open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem euclideanGaussian_axis_product {u : E} (hu : ‖u‖ = 1) :
    (euclideanGaussianLaw E).map
      (fun z : E => (z - ((ℝ ∙ u).orthogonalProjectionOnto z : E), ⟪z, u⟫_ℝ)) =
        (gaussianOrthogonalResidualLaw (ℝ ∙ u)).prod (gaussianReal 0 1) := by
  let K : Submodule ℝ E := ℝ ∙ u
  let P : E →L[ℝ] E := K.subtypeL.comp K.orthogonalProjectionOnto
  let R : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - P
  let r : E → ℝ := fun z => ⟪z, u⟫_ℝ
  have hr : Measurable r := (continuous_id.inner continuous_const).measurable
  have he (z : E) : r (P z) = r z := by
    change ⟪((ℝ ∙ u).orthogonalProjectionOnto z : E), u⟫_ℝ = ⟪z, u⟫_ℝ
    rw [unit_orthogonalProjection_formula hu, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hu]
    ring
  have hind := (euclideanGaussian_orthogonal_independent K).symm.comp measurable_id hr
  change IndepFun (fun z : E => R z) (fun z : E => r (P z)) (euclideanGaussianLaw E) at hind
  simp only [he] at hind
  have hj := (indepFun_iff_map_prod_eq_prod_map_map
    R.measurable.aemeasurable hr.aemeasurable).mp hind
  have hscalar : (euclideanGaussianLaw E).map r = gaussianReal 0 1 := by
    simpa only [r, real_inner_comm u] using euclideanGaussian_unit_inner_law hu
  rw [hscalar] at hj
  exact hj

theorem euclideanGaussian_axis_reconstruction {u : E} (hu : ‖u‖ = 1) :
    ((gaussianOrthogonalResidualLaw (ℝ ∙ u)).prod (gaussianReal 0 1)).map
      (fun p : E × ℝ => p.2 • u + p.1) = euclideanGaussianLaw E := by
  have hpair : Measurable
      (fun z : E => (z - ((ℝ ∙ u).orthogonalProjectionOnto z : E), ⟪z, u⟫_ℝ)) :=
    (measurable_id.sub ((ℝ ∙ u).subtypeL.comp (ℝ ∙ u).orthogonalProjectionOnto).measurable).prodMk
      (continuous_id.inner continuous_const).measurable
  have hrec : Measurable (fun p : E × ℝ => p.2 • u + p.1) := by fun_prop
  rw [← euclideanGaussian_axis_product hu, Measure.map_map hrec hpair]
  have he : (fun p : E × ℝ => p.2 • u + p.1) ∘
      (fun z : E => (z - ((ℝ ∙ u).orthogonalProjectionOnto z : E), ⟪z, u⟫_ℝ)) = id := by
    funext z
    simp only [Function.comp_def, unit_orthogonalProjection_formula hu, id_eq]
    abel
  rw [he, Measure.map_id]

end
end Nonsmooth
