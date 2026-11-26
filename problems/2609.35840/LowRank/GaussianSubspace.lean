import LowRank.GaussianOrthogonal

/-! Projection of a standard Gaussian is the standard Gaussian on the target
subspace, including zero-dimensional subspaces. -/

namespace LowRank
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

local instance (K : Submodule ℝ E) : BorelSpace K := Subtype.borelSpace _

theorem gaussian_subspace_projection (K : Submodule ℝ E) :
    (euclideanGaussianLaw E).map K.orthogonalProjection = euclideanGaussianLaw K := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply]
  have hf : StronglyMeasurable (fun z : K => Complex.exp ((⟪z, t⟫_ℝ : ℂ) * Complex.I)) :=
    (by fun_prop : Continuous _).stronglyMeasurable
  rw [integral_map_of_stronglyMeasurable K.orthogonalProjection.measurable hf]
  simp_rw [Submodule.inner_orthogonalProjection_eq_of_mem_right]
  change charFun (euclideanGaussianLaw E) (t : E) = _
  rw [euclideanGaussian_characteristic, euclideanGaussian_characteristic]
  rfl

theorem gaussian_residual_subspace (K : Submodule ℝ E) :
    (euclideanGaussianLaw E).map (fun z => z - (K.orthogonalProjection z : E)) =
      (euclideanGaussianLaw Kᗮ).map Kᗮ.subtype := by
  have hm : Measurable Kᗮ.subtype := Kᗮ.subtypeL.measurable
  rw [← gaussian_subspace_projection Kᗮ,
    Measure.map_map hm Kᗮ.orthogonalProjection.measurable]
  congr 1
  funext z
  exact (K.orthogonalProjection_orthogonal_val z).symm

end
end LowRank
