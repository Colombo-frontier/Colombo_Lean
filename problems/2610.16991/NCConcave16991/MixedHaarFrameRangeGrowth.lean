import NCConcave16991.MixedHaarFrameForward

/-! # A forward reveal adds its requested formal vector to the frame domain -/

noncomputable section

namespace NCConcave16991.MixedHaar

open Set

set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] prefixSpan tailIsometry tailOrthogonal householderOrthogonal frameHead frameTail
  Haar.orthogonalLinearIsometryEquiv

theorem frameUpdateActiveAt_range_eq {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k)
    (F G : Haar.OrthogonalGroup k) (x g : Space k) (hq : frameTail r G x ≠ 0) :
    frameRange (frameUpdateActiveAt r hr F G x g) = frameRange (r,F,G) ⊔ Submodule.span ℝ ({x} : Set (Space k)) := by
  let L := Haar.orthogonalLinearIsometryEquiv (G * tailOrthogonal r (tailTurn r hr (frameTail r G x)))
  let W := frameRange (r,F,G) ⊔ Submodule.span ℝ ({x} : Set (Space k))
  let K := W.comap L.toLinearMap
  have hD : prefixSpan r ≤ K := by
    intro y hy
    change L y ∈ W
    change Haar.orthogonalLinearIsometryEquiv (G * tailOrthogonal r _) y ∈ W
    rw [Haar.action_mul,tailOrthogonal_fixes_prefix r _ ⟨y,hy⟩]
    exact Submodule.mem_sup_left ⟨y,hy,rfl⟩
  have hhead : L (frameHead r G x) ∈ W := hD (frameHead_mem r G x)
  have hx : x ∈ W := Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
  have htimes : ‖frameTail r G x‖ • L (tailIsometry r (firstTailVector r hr) : Space k) ∈ W := by
    have he := frameNewPhysical_maps r hr G x hq
    change L (frameNewCoordinates r hr G x) = _ at he
    rw [frameNewCoordinates,map_add,map_smul] at he
    rw [eq_sub_of_add_eq' he]
    exact W.sub_mem hx hhead
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
    exact he ▸ (hnext hv : L v ∈ W)
  · apply sup_le
    · exact liftedPrefix_mono r hr G (tailTurn r hr (frameTail r G x))
    · apply Submodule.span_le.mpr
      intro y hy
      have hyx : y = x := Set.mem_singleton_iff.mp hy
      subst y
      exact ⟨frameNewCoordinates r hr G x,frameNewCoordinates_mem r hr G x,frameNewPhysical_maps r hr G x hq⟩

theorem frameForwardUpdate_domain_le {k : ℕ} (s : FrameState k) (x g : Space k) :
    frameDomain (frameForwardUpdate s x g) ≤ frameDomain s ⊔ Submodule.span ℝ ({x} : Set (Space k)) := by
  unfold frameForwardUpdate frameUpdate frameUpdateAt
  split_ifs with hr hq
  · exact le_sup_left
  · change s.1.val < k at hr
    change ¬ frameTail s.1 s.2.1 x = 0 at hq
    change frameRange (frameUpdateActiveAt s.1 hr s.2.2 s.2.1 x g) ≤ _
    rw [frameUpdateActiveAt_range_eq s.1 hr s.2.2 s.2.1 x g hq]
    exact le_rfl
  · exact le_sup_left

theorem frameUpdate_domain_le_old_sup_gaussian {k : ℕ} (s : FrameState k) (x g : Space k)
    (hh : frameTail s.1 s.2.1 g ≠ 0) :
    frameDomain (frameUpdate s x g) ≤ frameDomain s ⊔ Submodule.span ℝ ({g} : Set (Space k)) := by
  unfold frameUpdate frameUpdateAt
  split_ifs with hr hq
  · exact le_sup_left
  · exact frameUpdateActiveAt_domain_le_old_sup_gaussian s.1 hr s.2.1 s.2.2 x g hq hh
  · exact le_sup_left

end NCConcave16991.MixedHaar
