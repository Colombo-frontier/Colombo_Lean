import NCConcave16991.MixedHaarCanonicalGroup
import Mathlib.Topology.Homeomorph.Lemmas

/-! # The tail orthogonal group is exactly the canonical prefix stabilizer -/

noncomputable section

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def tailRecoverIsometry {k : ℕ} (r : Fin (k + 1)) (Q : prefixStabilizer r) :
    EuclideanSpace ℝ (Fin (k - r.val)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k - r.val)) :=
  ((tailIsometry r).trans (PartialIsometry.complementRestriction (prefixSpan r) (prefixSpan r)
    (.refl ℝ _) (Haar.orthogonalLinearIsometryEquiv Q.val) Q.property)).trans (tailIsometry r).symm

def tailRecover {k : ℕ} (r : Fin (k + 1)) (Q : prefixStabilizer r) : Haar.OrthogonalGroup (k - r.val) :=
  orthogonalOfIsometry (tailRecoverIsometry r Q)

theorem tailRecover_action {k : ℕ} (r : Fin (k + 1)) (Q : prefixStabilizer r)
    (v : EuclideanSpace ℝ (Fin (k - r.val))) :
    Haar.orthogonalLinearIsometryEquiv (tailRecover r Q) v =
      (tailIsometry r).symm (PartialIsometry.complementRestriction (prefixSpan r) (prefixSpan r)
        (.refl ℝ _) (Haar.orthogonalLinearIsometryEquiv Q.val) Q.property (tailIsometry r v)) := by
  rw [tailRecover,orthogonalOfIsometry_action]
  rfl

theorem tailRecover_tailOrthogonal {k : ℕ} (r : Fin (k + 1))
    (V : Haar.OrthogonalGroup (k - r.val)) :
    tailRecover r ⟨tailOrthogonal r V,tailOrthogonal_mem_stabilizer r V⟩ = V := by
  apply orthogonal_eq_of_action_eq
  intro v
  rw [tailRecover_action]
  have he : PartialIsometry.complementRestriction (prefixSpan r) (prefixSpan r) (.refl ℝ _)
      (Haar.orthogonalLinearIsometryEquiv (tailOrthogonal r V)) (tailOrthogonal_mem_stabilizer r V)
      (tailIsometry r v) = tailIsometry r (Haar.orthogonalLinearIsometryEquiv V v) := by
    apply Subtype.ext
    exact tailOrthogonal_on_tail r V v
  rw [he,LinearIsometryEquiv.symm_apply_apply]

theorem tailOrthogonal_tailRecover {k : ℕ} (r : Fin (k + 1)) (Q : prefixStabilizer r) :
    tailOrthogonal r (tailRecover r Q) = Q.val := by
  apply orthogonal_eq_of_action_eq
  intro x
  rw [tailOrthogonal_apply,tailRecover_action,LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply]
  exact (PartialIsometry.extension_apply (prefixSpan r) (prefixSpan r) (.refl ℝ _)
    (Haar.orthogonalLinearIsometryEquiv Q.val) Q.property x).symm

def tailStabilizerEquiv {k : ℕ} (r : Fin (k + 1)) :
    Haar.OrthogonalGroup (k - r.val) ≃* prefixStabilizer r where
  toFun V := ⟨tailOrthogonal r V,tailOrthogonal_mem_stabilizer r V⟩
  invFun := tailRecover r
  left_inv := tailRecover_tailOrthogonal r
  right_inv Q := Subtype.ext (tailOrthogonal_tailRecover r Q)
  map_mul' U V := Subtype.ext (tailOrthogonal_mul r U V)

theorem tailStabilizerEquiv_continuous {k : ℕ} (r : Fin (k + 1)) :
    Continuous (tailStabilizerEquiv r) :=
  (tailOrthogonal_continuous r).subtype_mk _

theorem tailStabilizerEquiv_symm_continuous {k : ℕ} (r : Fin (k + 1)) :
    Continuous (tailStabilizerEquiv r).symm :=
  (tailStabilizerEquiv_continuous r).continuous_symm_of_equiv_compact_to_t2

end NCConcave16991.MixedHaar
