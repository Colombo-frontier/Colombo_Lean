import NCConcave16991.MixedHaarFrameUpdate
import NCConcave16991.MixedHaarCanonicalSuccessorGroup

/-! # The literal active frame completion is the local sphere-frame kernel -/

noncomputable section

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] prefixSpan tailIsometry tailOrthogonal householderOrthogonal frameHead frameTail

theorem frameComplete_active_factorization {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k)
    (F G : Haar.OrthogonalGroup k) (x g : Space k) (z : FrameTape k) :
    frameComplete (frameUpdateActiveAt r hr F G x g) z =
      G * tailOrthogonal r
        (householderOrthogonal (firstTailVector r hr - normalize (frameTail r G x)) *
          successorTailHom r hr (z (nextRank r hr)) *
          (householderOrthogonal (firstTailVector r hr - normalize (frameTail r F g)))⁻¹) * F⁻¹ := by
  change (G * tailOrthogonal r (householderOrthogonal (firstTailVector r hr - normalize (frameTail r G x)))) *
    tailOrthogonal (nextRank r hr) (z (nextRank r hr)) *
      (F * tailOrthogonal r (householderOrthogonal (firstTailVector r hr - normalize (frameTail r F g))))⁻¹ = _
  rw [← tailOrthogonal_successorTailHom r hr (z (nextRank r hr)),tailOrthogonal_mul,tailOrthogonal_mul]
  have hi (U : Haar.OrthogonalGroup (k - r.val)) : tailOrthogonal r U⁻¹ = (tailOrthogonal r U)⁻¹ :=
    (tailOrthogonalHom r).map_inv U
  rw [hi,mul_inv_rev]
  simp only [mul_assoc]

end NCConcave16991.MixedHaar
