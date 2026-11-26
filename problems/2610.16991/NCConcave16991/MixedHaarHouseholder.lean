import NCConcave16991.HaarProbability
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Tactic.Module

/-! # A genuine measurable orthogonal Householder selector -/

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def householder (a : E) : E ≃ₗᵢ[ℝ] E := (ℝ ∙ a)ᗮ.reflection

theorem householder_apply (a x : E) :
    householder a x = x - (2 * ⟪a,x⟫_ℝ / ‖a‖ ^ 2) • a := by
  rw [householder, Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp only [smul_smul, RCLike.ofReal_real_eq_id, id_eq, smul_eq_mul, mul_div_assoc]
  module

theorem householder_swap (v w : E) (h : ‖v‖ = ‖w‖) : householder (v - w) v = w :=
  Submodule.reflection_sub h

theorem householder_fixes (a x : E) (hx : ⟪a,x⟫_ℝ = 0) : householder a x = x := by
  rw [householder_apply, hx]
  simp only [mul_zero, zero_div, zero_smul, sub_zero]

theorem householder_joint_measurable : Measurable (fun p : E × E ↦ householder p.1 p.2) := by
  simp_rw [householder_apply]
  exact measurable_snd.sub
    (((measurable_const.mul (measurable_fst.inner measurable_snd)).div
      (measurable_fst.norm.pow_const 2)).smul measurable_fst)

def orthogonalOfIsometry {k : ℕ} (U : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) :
    Haar.OrthogonalGroup k :=
  ⟨U.toMatrix (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis,
    U.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun (Fin k) ℝ) (EuclideanSpace.basisFun (Fin k) ℝ)⟩

theorem orthogonalOfIsometry_entry {k : ℕ}
    (U : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) (i j : Fin k) :
    (orthogonalOfIsometry U).val i j = (U ((EuclideanSpace.basisFun (Fin k) ℝ) j)) i := by
  change (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin k) ℝ).toBasis U.toLinearEquiv.toLinearMap) i j = _
  rw [LinearMap.toMatrix_apply]
  exact (EuclideanSpace.basisFun (Fin k) ℝ).coe_toBasis_repr_apply _ _

theorem orthogonalOfIsometry_action {k : ℕ}
    (U : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) (x : EuclideanSpace ℝ (Fin k)) :
    Haar.orthogonalLinearIsometryEquiv (orthogonalOfIsometry U) x = U x := by
  have h := U.toLinearEquiv.toLinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Fin k) ℝ).toBasis (EuclideanSpace.basisFun (Fin k) ℝ).toBasis x
  have he (y : EuclideanSpace ℝ (Fin k)) :
      ((EuclideanSpace.basisFun (Fin k) ℝ).toBasis.repr y : Fin k → ℝ) = WithLp.ofLp y := by
    funext i
    exact (EuclideanSpace.basisFun (Fin k) ℝ).coe_toBasis_repr_apply y i
  rw [he, he] at h
  ext i
  change (((orthogonalOfIsometry U).val).mulVec (WithLp.ofLp x)) i = (U x) i
  exact congrFun h i

def householderOrthogonal {k : ℕ} (a : EuclideanSpace ℝ (Fin k)) : Haar.OrthogonalGroup k :=
  orthogonalOfIsometry (householder a)

attribute [local irreducible] householder orthogonalOfIsometry householderOrthogonal

set_option backward.isDefEq.respectTransparency true in
theorem householderOrthogonal_measurable {k : ℕ} :
    Measurable (householderOrthogonal (k := k)) := by
  have hc : IsClosed (Matrix.orthogonalGroup (Fin k) ℝ : Set (Matrix (Fin k) (Fin k) ℝ)) := isClosed_unitary
  have hrange : Set.range (Subtype.val : Haar.OrthogonalGroup k → Matrix (Fin k) (Fin k) ℝ) =
      (Matrix.orthogonalGroup (Fin k) ℝ : Set (Matrix (Fin k) (Fin k) ℝ)) := by
    ext A
    constructor
    · rintro ⟨Q,rfl⟩
      exact Q.property
    · intro hA
      exact ⟨⟨A,hA⟩,rfl⟩
  have he : MeasurableEmbedding (Subtype.val : Haar.OrthogonalGroup k → Matrix (Fin k) (Fin k) ℝ) :=
    (show Topology.IsClosedEmbedding (Subtype.val : Haar.OrthogonalGroup k → Matrix (Fin k) (Fin k) ℝ) from
      ⟨Topology.IsEmbedding.subtypeVal, hrange.symm ▸ hc⟩).measurableEmbedding
  apply he.measurable_comp_iff.mp
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  change Measurable (fun a : EuclideanSpace ℝ (Fin k) ↦ (householderOrthogonal a).val i j)
  simp_rw [householderOrthogonal,orthogonalOfIsometry_entry]
  exact (PiLp.continuous_apply 2 (fun _ : Fin k ↦ ℝ) i).measurable.comp
    (householder_joint_measurable.comp (measurable_id.prodMk measurable_const))

end NCConcave16991.MixedHaar
