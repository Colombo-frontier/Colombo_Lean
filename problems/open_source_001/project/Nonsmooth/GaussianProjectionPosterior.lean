import Nonsmooth.GaussianOrthogonalComponents
import Mathlib.Probability.Kernel.CondDistrib

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def gaussianOrthogonalResidualLaw (K : Submodule ℝ E) : Measure E :=
  (euclideanGaussianLaw E).map (fun z : E => z - (K.orthogonalProjection z : E))

instance gaussianOrthogonalResidualLaw_probability (K : Submodule ℝ E) :
    IsProbabilityMeasure (gaussianOrthogonalResidualLaw K) :=
  Measure.isProbabilityMeasure_map (measurable_id.sub
    (K.subtypeL.comp K.orthogonalProjection).measurable).aemeasurable

/-- A measurable affine Gaussian slice kernel, defined at every proposed projection value. -/
def gaussianProjectionKernel (K : Submodule ℝ E) : Kernel E E :=
  (Kernel.id ×ₖ Kernel.const E (gaussianOrthogonalResidualLaw K)).map
    (fun p : E × E => p.1 + p.2)

instance gaussianProjectionKernel_markov (K : Submodule ℝ E) :
    IsMarkovKernel (gaussianProjectionKernel K) :=
  Kernel.IsMarkovKernel.map _ (by fun_prop)

theorem gaussianProjectionKernel_apply (K : Submodule ℝ E) (x : E) :
    gaussianProjectionKernel K x = (gaussianOrthogonalResidualLaw K).map (fun z => x + z) := by
  have hadd : Measurable (fun p : E × E => p.1 + p.2) := by fun_prop
  ext S hS
  rw [gaussianProjectionKernel, Kernel.map_apply' _ hadd _ hS,
    Kernel.id_prod_apply' _ _ (hadd hS), Measure.map_apply (by fun_prop) hS]
  rfl

theorem gaussianProjectionKernel_disintegrates (K : Submodule ℝ E) :
    (euclideanGaussianLaw E).map (fun z : E => ((K.orthogonalProjection z : E), z)) =
      ((euclideanGaussianLaw E).map (fun z : E => (K.orthogonalProjection z : E))) ⊗ₘ
        gaussianProjectionKernel K := by
  let P : E →L[ℝ] E := K.subtypeL.comp K.orthogonalProjection
  let R : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - P
  let T : E × E → E × E := fun p => (p.1, p.1 + p.2)
  have hT : Measurable T := by fun_prop
  have hind := (indepFun_iff_map_prod_eq_prod_map_map
    P.measurable.aemeasurable R.measurable.aemeasurable).mp
      (euclideanGaussian_orthogonal_independent K)
  have he := congrArg (fun ν : Measure (E × E) => ν.map T) hind
  try dsimp only at he
  rw [Measure.map_map hT (P.measurable.prodMk R.measurable)] at he
  have hcomp : T ∘ (fun z : E => (P z, R z)) = fun z : E => (P z, z) := by
    funext z
    change (P z, P z + (z - P z)) = (P z, z)
    congr 1
    abel
  rw [hcomp] at he
  change (euclideanGaussianLaw E).map (fun z : E => (P z, z)) = _
  rw [he]
  ext S hS
  rw [Measure.map_apply hT hS, Measure.prod_apply (hT hS), Measure.compProd_apply hS]
  apply lintegral_congr
  intro x
  rw [gaussianProjectionKernel_apply, Measure.map_apply (by fun_prop)
    (measurable_prodMk_left hS)]
  rfl

/-- The affine kernel is the actual regular conditional distribution, up to the
unavoidable null set of projection values. No conditioning on a null event is used. -/
theorem gaussianProjectionKernel_ae_eq_condDistrib (K : Submodule ℝ E) :
    ∀ᵐ x ∂(euclideanGaussianLaw E).map (fun z : E => (K.orthogonalProjection z : E)),
      gaussianProjectionKernel K x =
        condDistrib id (fun z : E => (K.orthogonalProjection z : E)) (euclideanGaussianLaw E) x := by
  exact (condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (K.subtypeL.comp K.orthogonalProjection).measurable measurable_id
    (gaussianProjectionKernel_disintegrates K)).symm

end
end Nonsmooth
