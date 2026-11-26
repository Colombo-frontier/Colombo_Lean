import Nonsmooth.GaussianEventSlices

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

local instance (K : Submodule ℝ E) : BorelSpace K := Subtype.borelSpace _

theorem euclideanGaussian_subspace_projection (K : Submodule ℝ E) [Nontrivial K] :
    (euclideanGaussianLaw E).map K.orthogonalProjectionOnto = euclideanGaussianLaw K := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply]
  have hf : StronglyMeasurable (fun z : K => Complex.exp ((⟪z, t⟫_ℝ : ℂ) * Complex.I)) :=
    (by fun_prop : Continuous _).stronglyMeasurable
  rw [integral_map_of_stronglyMeasurable K.orthogonalProjectionOnto.measurable hf]
  simp_rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  change charFun (euclideanGaussianLaw E) (t : E) = _
  rw [euclideanGaussian_characteristic, euclideanGaussian_characteristic]
  rfl

/-- The residual law is the ordinary isotropic Gaussian on the orthogonal complement,
embedded into the original space. -/
theorem gaussianOrthogonalResidualLaw_subspace (K : Submodule ℝ E) [Nontrivial Kᗮ] :
    gaussianOrthogonalResidualLaw K = (euclideanGaussianLaw Kᗮ).map Kᗮ.subtype := by
  have hm : Measurable Kᗮ.subtype := Kᗮ.subtypeL.measurable
  rw [← euclideanGaussian_subspace_projection Kᗮ,
    Measure.map_map hm Kᗮ.orthogonalProjectionOnto.measurable]
  unfold gaussianOrthogonalResidualLaw
  congr 1
  funext z
  change z - K.starProjection z = Kᗮ.starProjection z
  simp only [Submodule.starProjection_orthogonal, sub_apply, ContinuousLinearMap.id_apply]

end
end Nonsmooth
