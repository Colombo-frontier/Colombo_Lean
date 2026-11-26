import NCConcave16991.MixedHaarCanonicalSuccessorSpan
import NCConcave16991.MixedHaarCanonicalEquiv
import NCConcave16991.MixedHaarStabilizerGaussian
import Mathlib.Algebra.Module.Submodule.EqLocus

/-! # The next-rank Haar source is the old tail's first-point stabilizer -/

noncomputable section

namespace NCConcave16991.MixedHaar

open Set

set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] prefixSpan tailIsometry tailOrthogonal Haar.orthogonalLinearIsometryEquiv

def successorPrefixHom {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k) :
    Haar.OrthogonalGroup (k - (nextRank r hr).val) →* prefixStabilizer r where
  toFun V := ⟨tailOrthogonal (nextRank r hr) V,fun x ↦
    tailOrthogonal_fixes_prefix (nextRank r hr) V
      ⟨x.val,prefixSpan_mono r (nextRank r hr) (by change r.val ≤ r.val + 1; omega) x.property⟩⟩
  map_one' := Subtype.ext (tailOrthogonal_one (nextRank r hr))
  map_mul' U V := Subtype.ext (tailOrthogonal_mul (nextRank r hr) U V)

def successorTailHom {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k) :
    Haar.OrthogonalGroup (k - (nextRank r hr).val) →* Haar.OrthogonalGroup (k - r.val) :=
  (tailStabilizerEquiv r).symm.toMonoidHom.comp (successorPrefixHom r hr)

theorem tailOrthogonal_successorTailHom {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k)
    (V : Haar.OrthogonalGroup (k - (nextRank r hr).val)) :
    tailOrthogonal r (successorTailHom r hr V) = tailOrthogonal (nextRank r hr) V :=
  tailOrthogonal_tailRecover r (successorPrefixHom r hr V)

theorem successorTailHom_fixes_first {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k)
    (V : Haar.OrthogonalGroup (k - (nextRank r hr).val)) :
    Haar.orthogonalLinearIsometryEquiv (successorTailHom r hr V) (firstTailVector r hr) = firstTailVector r hr := by
  have hh := tailOrthogonal_fixes_prefix (nextRank r hr) V
    ⟨(tailIsometry r (firstTailVector r hr)).val,firstTailVector_mem_next r hr⟩
  rw [← tailOrthogonal_successorTailHom r hr V,tailOrthogonal_on_tail] at hh
  exact (tailIsometry r).injective (Subtype.ext hh)

def successorPointHom {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k) :
    Haar.OrthogonalGroup (k - (nextRank r hr).val) →* pointStabilizer (firstTailVector r hr) where
  toFun V := ⟨successorTailHom r hr V,fun _ ↦ successorTailHom_fixes_first r hr V⟩
  map_one' := Subtype.ext (successorTailHom r hr).map_one
  map_mul' U V := Subtype.ext ((successorTailHom r hr).map_mul U V)

theorem successorPrefixHom_continuous {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k) :
    Continuous (successorPrefixHom r hr) := (tailOrthogonal_continuous (nextRank r hr)).subtype_mk _

theorem successorTailHom_continuous {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k) :
    Continuous (successorTailHom r hr) :=
  (tailStabilizerEquiv_symm_continuous r).comp (successorPrefixHom_continuous r hr)

theorem successorPointHom_continuous {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k) :
    Continuous (successorPointHom r hr) := (successorTailHom_continuous r hr).subtype_mk _

theorem successorPointHom_surjective {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k) :
    Function.Surjective (successorPointHom r hr) := by
  intro U
  let Q := tailOrthogonal r U.val
  let K := LinearMap.eqLocus (Haar.orthogonalLinearIsometryEquiv Q).toLinearMap (LinearMap.id : Space k →ₗ[ℝ] Space k)
  have hD : prefixSpan r ≤ K := fun y hy ↦ tailOrthogonal_fixes_prefix r U.val ⟨y,hy⟩
  have ha : (tailIsometry r (firstTailVector r hr)).val ∈ K := by
    change Haar.orthogonalLinearIsometryEquiv (tailOrthogonal r U.val) _ = _
    rw [tailOrthogonal_on_tail,U.property 0]
    rfl
  have hnext : prefixSpan (nextRank r hr) ≤ K := by
    rw [prefixSpan_next]
    apply sup_le hD
    apply Submodule.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact ha
  have hQ : Q ∈ prefixStabilizer (nextRank r hr) := fun x ↦ hnext x.property
  let V := tailRecover (nextRank r hr) ⟨Q,hQ⟩
  refine ⟨V,?_⟩
  apply Subtype.ext
  have he : successorPrefixHom r hr V = ⟨tailOrthogonal r U.val,tailOrthogonal_mem_stabilizer r U.val⟩ := by
    apply Subtype.ext
    exact tailOrthogonal_tailRecover (nextRank r hr) ⟨Q,hQ⟩
  change tailRecover r (successorPrefixHom r hr V) = U.val
  rw [he,tailRecover_tailOrthogonal]

end NCConcave16991.MixedHaar
