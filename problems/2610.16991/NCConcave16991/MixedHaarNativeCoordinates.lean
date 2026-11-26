import NCConcave16991.MixedHaarFrameState
import NCConcave16991.MixedHaarSphereOrbit
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! # Public coordinates transport the actual native vertex requests and Gaussians -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency true

variable {I : Type*} [Fintype I] (E : I → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]

abbrev nativeDimension (i : I) := Module.finrank ℝ (E i)
abbrev NativeOrthogonal := ∀ i, Haar.OrthogonalGroup (nativeDimension E i)

def nativeCoordinates (i : I) : E i ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (nativeDimension E i)) :=
  (stdOrthonormalBasis ℝ (E i)).repr

def nativeVertexOperator (Q : NativeOrthogonal E) (i : I) : E i ≃ₗᵢ[ℝ] E i :=
  ((nativeCoordinates E i).trans (Haar.orthogonalLinearIsometryEquiv (Q i))).trans (nativeCoordinates E i).symm

theorem nativeVertexOperator_apply (Q : NativeOrthogonal E) (i : I) (x : E i) :
    nativeVertexOperator E Q i x = (nativeCoordinates E i).symm
      (Haar.orthogonalLinearIsometryEquiv (Q i) (nativeCoordinates E i x)) := rfl

theorem nativeVertexOperator_symm_apply (Q : NativeOrthogonal E) (i : I) (x : E i) :
    (nativeVertexOperator E Q i).symm x = (nativeCoordinates E i).symm
      (Haar.orthogonalLinearIsometryEquiv (Q i)⁻¹ (nativeCoordinates E i x)) := by
  rw [orthogonal_action_inv]
  rfl

attribute [local irreducible] nativeCoordinates nativeVertexOperator Haar.orthogonalLinearIsometryEquiv

theorem nativeVertexOperator_action_measurable (i : I) :
    Measurable (fun p : NativeOrthogonal E × E i ↦ nativeVertexOperator E p.1 i p.2) := by
  simp_rw [nativeVertexOperator_apply]
  have hm : Measurable (fun p : NativeOrthogonal E × E i ↦
      (p.1 i,nativeCoordinates E i p.2)) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((nativeCoordinates E i).continuous.measurable.comp measurable_snd)
  exact (nativeCoordinates E i).symm.continuous.measurable.comp (sphereAction_joint_measurable.comp hm)

theorem nativeVertexOperator_inverse_measurable (i : I) :
    Measurable (fun p : NativeOrthogonal E × E i ↦ (nativeVertexOperator E p.1 i).symm p.2) := by
  simp_rw [nativeVertexOperator_symm_apply]
  have hm : Measurable (fun p : NativeOrthogonal E × E i ↦
      ((p.1 i)⁻¹,nativeCoordinates E i p.2)) :=
    (((measurable_pi_apply i).comp measurable_fst).inv).prodMk
      ((nativeCoordinates E i).continuous.measurable.comp measurable_snd)
  exact (nativeCoordinates E i).symm.continuous.measurable.comp (sphereAction_joint_measurable.comp hm)

theorem nativeGaussian_coordinates_preserving :
    MeasurePreserving (fun g : ∀ i, E i ↦ fun i ↦ nativeCoordinates E i (g i))
      (Measure.pi (fun i ↦ stdGaussian (E i)))
      (Measure.pi (fun i ↦ stdGaussian (EuclideanSpace ℝ (Fin (nativeDimension E i))))) :=
  measurePreserving_pi _ _ (fun i ↦ ⟨(nativeCoordinates E i).continuous.measurable,stdGaussian_map _⟩)

end NCConcave16991.MixedHaar
