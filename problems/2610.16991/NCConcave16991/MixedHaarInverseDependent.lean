import NCConcave16991.MixedHaarInverseCompletion

/-! # Repeated and dependent inverse requests need no new direction -/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (D R : Submodule ℝ E) (U : D ≃ₗᵢ[ℝ] R) (Q : E ≃ₗᵢ[ℝ] E)

theorem residual_eq_zero_iff (x : E) : residual R x = 0 ↔ x ∈ R := by
  rw [residual, sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff]

theorem inverseCandidate_eq_known (x g : E) (hx : x ∈ R) :
    inverseCandidate D R U x g = knownInverse D R U x := by
  rw [inverseCandidate, (residual_eq_zero_iff R x).mpr hx, norm_zero, zero_div, zero_smul, add_zero]

theorem inverseCompletion_known (hQ : PartialIsometry.ExtendsPartial D R U Q)
    (x g : E) (hx : x ∈ R) : inverseCompletion D R U Q x g = Q := by
  have hk : Q (knownInverse D R U x) = x := by
    have hh := hQ (U.symm (R.orthogonalProjectionOnto x))
    simpa only [knownInverse, U.apply_symm_apply, ← Submodule.starProjection_apply,
      Submodule.starProjection_eq_self_iff.mpr hx] using hh
  apply LinearIsometryEquiv.ext
  intro z
  change householder (Q (inverseCandidate D R U x g) - x) (Q z) = Q z
  rw [inverseCandidate_eq_known D R U x g hx, hk, sub_self]
  apply householder_fixes
  simp

theorem inverseCompletion_maps_candidate_or_known
    (hQ : PartialIsometry.ExtendsPartial D R U Q) (x g : E)
    (h : x ∈ R ∨ residual D g ≠ 0) :
    inverseCompletion D R U Q x g (inverseCandidate D R U x g) = x := by
  rcases h with hx | hg
  · rw [inverseCompletion_known D R U Q hQ x g hx, inverseCandidate_eq_known D R U x g hx]
    have hh := hQ (U.symm (R.orthogonalProjectionOnto x))
    simpa only [knownInverse, U.apply_symm_apply, ← Submodule.starProjection_apply,
      Submodule.starProjection_eq_self_iff.mpr hx] using hh
  · exact inverseCompletion_maps_candidate D R U Q x g hg

attribute [local irreducible] householder

theorem inverseCompletion_action_joint_measurable :
    Measurable (fun p : (E × E) × E ↦ inverseCompletion D R U Q p.1.1 p.1.2 p.2) := by
  change Measurable (fun p : (E × E) × E ↦
    householder (Q (inverseCandidate D R U p.1.1 p.1.2) - p.1.1) (Q p.2))
  let c : (E × E) × E → E := fun p ↦ inverseCandidate D R U p.1.1 p.1.2
  have hc : Measurable c := (inverseCandidate_measurable D R U).comp measurable_fst
  have ha : Measurable (fun p : (E × E) × E ↦ Q (c p) - p.1.1) :=
    (Q.continuous.measurable.comp hc).sub (measurable_fst.comp measurable_fst)
  exact (householder_joint_measurable (E := E)).comp
    (ha.prodMk (Q.continuous.measurable.comp measurable_snd))

end NCConcave16991.MixedHaar
