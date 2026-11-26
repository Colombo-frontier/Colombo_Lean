import RandomizedFO2003.StabilizerRotations
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

namespace RandomizedFO2003.Rotations

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Householder reflection across the hyperplane normal to `v`; at `v = 0`
this is the identity, so there is no partial definition at the diagonal. -/
noncomputable def householder (v : E) : Rotation E :=
  unitary.linearIsometryEquiv.symm (Submodule.span ℝ {v})ᗮ.reflection

theorem householder_operator (v : E) :
    (householder v : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E -
      (2 / ‖v‖ ^ 2) • (innerSL ℝ v).smulRight v := by
  ext x
  change (Submodule.span ℝ {v})ᗮ.reflection x = _
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply, neg_sub,
    RCLike.ofReal_real_eq_id, id_eq]
  module

@[simp] theorem householder_inverse (v : E) : (householder v)⁻¹ = householder v := by
  apply unitary.linearIsometryEquiv.injective
  rw [map_inv]
  simp only [householder, MulEquiv.apply_symm_apply]
  change ((Submodule.span ℝ {v})ᗮ.reflection).symm = (Submodule.span ℝ {v})ᗮ.reflection
  exact Submodule.reflection_symm

theorem householder_sends (v w : E) (hvw : ‖v‖ = ‖w‖) :
    isometry E (householder (v - w)) v = w := Submodule.reflection_sub hvw

variable [MeasurableSpace E] [BorelSpace E]

theorem measurable_householder : Measurable (householder : E → Rotation E) := by
  apply (rotation_isClosed E).isClosedEmbedding_subtypeVal.measurableEmbedding.measurable_comp_iff.mp
  change Measurable (fun v : E => (householder v : E →L[ℝ] E))
  simp_rw [householder_operator]
  have hc : Continuous (fun v : E => (innerSL ℝ v).smulRight v) := by
    change Continuous (fun v : E => ContinuousLinearMap.smulRightL ℝ E E (innerSL ℝ v) v)
    fun_prop
  exact measurable_const.sub ((measurable_const.div (measurable_id.norm.pow_const 2)).smul hc.measurable)

theorem measurable_section (e : E) : Measurable (fun v : E => householder (e - v)) :=
  measurable_householder.comp (measurable_const.sub measurable_id)

end RandomizedFO2003.Rotations
