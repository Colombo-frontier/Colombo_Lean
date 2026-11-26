import NCConcave16991.MixedHaarSphereOrbit
import Mathlib.MeasureTheory.Measure.Prod

/-! # Uniqueness of the actual invariant unit-sphere probability law -/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 300000

variable {k : ℕ}
/-- Any actual probability law concentrated on the unit sphere and preserved
by every orthogonal rotation is the actual Haar orbit law of a fixed unit
vector. Invariance is used through actual measure-preserving maps. -/
theorem sphere_invariant_probability_unique (ν : Measure (SphereSpace k)) [IsProbabilityMeasure ν]
    (e : SphereSpace k) (he : ‖e‖ = 1)
    (hunit : ∀ᵐ x ∂ν, ‖x‖ = 1)
    (hinv : ∀ Q : Haar.OrthogonalGroup k,
      MeasurePreserving (Haar.orthogonalLinearIsometryEquiv Q) ν ν) :
    ν = sphereOrbitLaw e := by
  let action := fun p : Haar.OrthogonalGroup k × SphereSpace k ↦
    Haar.orthogonalLinearIsometryEquiv p.1 p.2
  have hm : Measurable action := sphereAction_joint_measurable
  have hleft : ((Haar.haarLaw k).prod ν).map action = ν := by
    apply Measure.ext
    intro A hA
    rw [Measure.map_apply hm hA,Measure.prod_apply (hA.preimage hm)]
    change (∫⁻ Q, ν {x | Haar.orthogonalLinearIsometryEquiv Q x ∈ A} ∂Haar.haarLaw k) = ν A
    have hpoint (Q : Haar.OrthogonalGroup k) :
        ν {x | Haar.orthogonalLinearIsometryEquiv Q x ∈ A} = ν A := by
      have he : {x | Haar.orthogonalLinearIsometryEquiv Q x ∈ A} =
          (Haar.orthogonalLinearIsometryEquiv Q) ⁻¹' A := rfl
      rw [he,← Measure.map_apply (Haar.orthogonalLinearIsometryEquiv Q).continuous.measurable hA,
        (hinv Q).map_eq]
    simp_rw [hpoint]
    simp
  have hright : ((Haar.haarLaw k).prod ν).map action = sphereOrbitLaw e := by
    apply Measure.ext
    intro A hA
    rw [Measure.map_apply hm hA,Measure.prod_apply_symm (hA.preimage hm)]
    change (∫⁻ x, (Haar.haarLaw k) {Q | Haar.orthogonalLinearIsometryEquiv Q x ∈ A} ∂ν) =
      sphereOrbitLaw e A
    have hpoint : ∀ᵐ x ∂ν,
        (Haar.haarLaw k) {Q | Haar.orthogonalLinearIsometryEquiv Q x ∈ A} = sphereOrbitLaw e A := by
      filter_upwards [hunit] with x hx
      have hpre : {Q : Haar.OrthogonalGroup k | Haar.orthogonalLinearIsometryEquiv Q x ∈ A} =
          (fun Q ↦ Haar.orthogonalLinearIsometryEquiv Q x) ⁻¹' A := rfl
      rw [hpre,← Measure.map_apply (Haar.continuous_orthogonalLinearIsometryEquiv_apply x).measurable hA]
      change sphereOrbitLaw x A = sphereOrbitLaw e A
      rw [sphereOrbitLaw_eq_of_norm_eq e x (he.trans hx.symm)]
    rw [lintegral_congr_ae hpoint]
    simp
  exact hleft.symm.trans hright

end NCConcave16991.MixedHaar

