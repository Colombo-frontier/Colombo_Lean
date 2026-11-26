import NCConcave16991.MixedHaarInverseCandidate
import NCConcave16991.MixedHaarHouseholder

/-! # An explicit orthogonal inverse-reveal update preserving all old data -/

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (D R : Submodule ℝ E) (U : D ≃ₗᵢ[ℝ] R) (Q : E ≃ₗᵢ[ℝ] E)

def inverseCompletion (x g : E) : E ≃ₗᵢ[ℝ] E :=
  Q.trans (householder (Q (inverseCandidate D R U x g) - x))

theorem inverseCandidate_image_difference_orthogonal
    (hQ : PartialIsometry.ExtendsPartial D R U Q) (x g : E) :
    Q (inverseCandidate D R U x g) - x ∈ Rᗮ := by
  have hk : Q (knownInverse D R U x) = R.starProjection x := by
    have hh := hQ (U.symm (R.orthogonalProjectionOnto x))
    simpa only [knownInverse, U.apply_symm_apply, Submodule.starProjection_apply] using hh
  have hg : Q (residual D g) ∈ Rᗮ :=
    PartialIsometry.extension_mem_orthogonal D R U Q hQ ⟨residual D g,residual_mem_orthogonal D g⟩
  rw [inverseCandidate, map_add, map_smul, hk]
  have he : R.starProjection x + (‖residual R x‖ / ‖residual D g‖) • Q (residual D g) - x =
      (‖residual R x‖ / ‖residual D g‖) • Q (residual D g) - residual R x := by
    unfold residual
    abel
  rw [he]
  exact Rᗮ.sub_mem (Rᗮ.smul_mem _ hg) (residual_mem_orthogonal R x)

theorem inverseCompletion_extends (hQ : PartialIsometry.ExtendsPartial D R U Q) (x g : E) :
    PartialIsometry.ExtendsPartial D R U (inverseCompletion D R U Q x g) := by
  intro z
  change householder (Q (inverseCandidate D R U x g) - x) (Q (z : E)) = (U z : E)
  rw [hQ z]
  apply householder_fixes
  have hh := (R.mem_orthogonal _).mp (inverseCandidate_image_difference_orthogonal D R U Q hQ x g)
    (U z : E) (U z).property
  exact inner_eq_zero_symm.mp hh

theorem inverseCompletion_maps_candidate (x g : E) (hg : residual D g ≠ 0) :
    inverseCompletion D R U Q x g (inverseCandidate D R U x g) = x := by
  apply householder_swap
  rw [Q.norm_map, inverseCandidate_norm D R U x g hg]

theorem inverseCompletion_inverse_eq (x g : E) (hg : residual D g ≠ 0) :
    (inverseCompletion D R U Q x g).symm x = inverseCandidate D R U x g := by
  apply (inverseCompletion D R U Q x g).injective
  rw [LinearIsometryEquiv.apply_symm_apply, inverseCompletion_maps_candidate D R U Q x g hg]

theorem inverseCompletion_inverse_mem_old_sup_gaussian (x g : E) (hg : residual D g ≠ 0) :
    (inverseCompletion D R U Q x g).symm x ∈ D ⊔ Submodule.span ℝ ({g} : Set E) := by
  rw [inverseCompletion_inverse_eq D R U Q x g hg]
  exact inverseCandidate_mem_old_sup_gaussian D R U x g

end NCConcave16991.MixedHaar
