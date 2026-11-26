import NCConcave16991.MixedHaarFrameUpdateGeometry
import NCConcave16991.MixedHaarCanonicalSuccessorSpan

/-! # The actual frame domain grows by its observed inverse answer only -/

noncomputable section

namespace NCConcave16991.MixedHaar

open Set

set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] prefixSpan tailIsometry tailOrthogonal householderOrthogonal frameHead frameTail
  Haar.orthogonalLinearIsometryEquiv

theorem liftedPrefix_mono {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k)
    (Q : Haar.OrthogonalGroup k) (V : Haar.OrthogonalGroup (k - r.val)) :
    (prefixSpan r).map (Haar.orthogonalLinearIsometryEquiv Q).toLinearEquiv.toLinearMap ≤
      (prefixSpan (nextRank r hr)).map (Haar.orthogonalLinearIsometryEquiv (Q * tailOrthogonal r V)).toLinearEquiv.toLinearMap := by
  intro x hx
  obtain ⟨y,hy,he⟩ := hx
  refine ⟨y,prefixSpan_mono r (nextRank r hr) (by change r.val ≤ r.val + 1; omega) hy,?_⟩
  change Haar.orthogonalLinearIsometryEquiv (Q * tailOrthogonal r V) y = x
  rw [Haar.action_mul,tailOrthogonal_fixes_prefix r V ⟨y,hy⟩]
  exact he

theorem frameUpdateActiveAt_domain_eq {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k)
    (F G : Haar.OrthogonalGroup k) (x g : Space k)
    (hq : frameTail r G x ≠ 0) (hh : frameTail r F g ≠ 0) :
    frameDomain (frameUpdateActiveAt r hr F G x g) = frameDomain (r,F,G) ⊔
      Submodule.span ℝ ({frameCandidateAt r F G x g} : Set (Space k)) := by
  let L := Haar.orthogonalLinearIsometryEquiv (F * tailOrthogonal r (tailTurn r hr (frameTail r F g)))
  let W := frameDomain (r,F,G) ⊔ Submodule.span ℝ ({frameCandidateAt r F G x g} : Set (Space k))
  let K := W.comap L.toLinearMap
  have hD : prefixSpan r ≤ K := by
    intro y hy
    change L y ∈ W
    change Haar.orthogonalLinearIsometryEquiv (F * tailOrthogonal r _) y ∈ W
    rw [Haar.action_mul,tailOrthogonal_fixes_prefix r _ ⟨y,hy⟩]
    exact Submodule.mem_sup_left ⟨y,hy,rfl⟩
  have hhead : L (frameHead r G x) ∈ W := hD (frameHead_mem r G x)
  have hcand : frameCandidateAt r F G x g ∈ W := Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
  have htimes : ‖frameTail r G x‖ • L (tailIsometry r (firstTailVector r hr) : Space k) ∈ W := by
    have he := frameNewFormal_maps r hr F G x g hh
    change L (frameNewCoordinates r hr G x) = _ at he
    rw [frameNewCoordinates,map_add,map_smul] at he
    rw [eq_sub_of_add_eq' he]
    exact W.sub_mem hcand hhead
  have haxis : (tailIsometry r (firstTailVector r hr)).val ∈ K := by
    change L (tailIsometry r (firstTailVector r hr) : Space k) ∈ W
    have hc := W.smul_mem (‖frameTail r G x‖)⁻¹ htimes
    simpa only [smul_smul,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hq),one_smul] using hc
  have hnext : prefixSpan (nextRank r hr) ≤ K := by
    rw [prefixSpan_next]
    apply sup_le hD
    apply Submodule.span_le.mpr
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact haxis
  apply le_antisymm
  · intro y hy
    obtain ⟨v,hv,he⟩ := hy
    have hv' : L v ∈ W := hnext hv
    exact he ▸ hv'
  · apply sup_le
    · exact liftedPrefix_mono r hr F (tailTurn r hr (frameTail r F g))
    · apply Submodule.span_le.mpr
      intro y hy
      obtain rfl := Set.mem_singleton_iff.mp hy
      exact ⟨frameNewCoordinates r hr G x,frameNewCoordinates_mem r hr G x,frameNewFormal_maps r hr F G x g hh⟩

theorem frameUpdateActiveAt_domain_le_old_sup_gaussian {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k)
    (F G : Haar.OrthogonalGroup k) (x g : Space k)
    (hq : frameTail r G x ≠ 0) (hh : frameTail r F g ≠ 0) :
    frameDomain (frameUpdateActiveAt r hr F G x g) ≤ frameDomain (r,F,G) ⊔ Submodule.span ℝ ({g} : Set (Space k)) := by
  rw [frameUpdateActiveAt_domain_eq r hr F G x g hq hh]
  apply sup_le le_sup_left
  apply Submodule.span_le.mpr
  intro y hy
  obtain rfl := Set.mem_singleton_iff.mp hy
  exact frameCandidate_mem_old_sup_gaussian (r,F,G) x g

theorem frameUpdate_domain_mono {k : ℕ} (s : FrameState k) (x g : Space k) :
    frameDomain s ≤ frameDomain (frameUpdate s x g) := by
  unfold frameUpdate frameUpdateAt
  split_ifs with hr hq
  · exact le_rfl
  · exact liftedPrefix_mono s.1 hr s.2.1 (tailTurn s.1 hr (frameTail s.1 s.2.1 g))
  · exact le_rfl

end NCConcave16991.MixedHaar
