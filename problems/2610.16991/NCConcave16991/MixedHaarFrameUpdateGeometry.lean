import NCConcave16991.MixedHaarFrameUpdate

/-! # The updated full completion has the actual inverse candidate -/

noncomputable section

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] prefixSpan tailIsometry tailOrthogonal householderOrthogonal frameHead frameTail
  Haar.orthogonalLinearIsometryEquiv

def tailTurn {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k) (h : Space (k - r.val)) : Haar.OrthogonalGroup (k - r.val) :=
  householderOrthogonal (firstTailVector r hr - normalize h)

theorem tailTurn_first {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k)
    (h : Space (k - r.val)) (hh : h ≠ 0) :
    Haar.orthogonalLinearIsometryEquiv (tailTurn r hr h) (firstTailVector r hr) = normalize h := by
  rw [tailTurn,householderOrthogonal,orthogonalOfIsometry_action]
  exact householder_swap _ _ ((firstTailVector_unit r hr).trans (normalize_norm hh).symm)

theorem norm_smul_normalize {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (h : E) : ‖h‖ • normalize h = h := by
  by_cases hh : h = 0
  · simp [hh,normalize]
  · simp only [normalize,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hh),one_smul]

theorem frameHead_mem {k : ℕ} (r : Fin (k + 1)) (Q : Haar.OrthogonalGroup k) (x : Space k) :
    frameHead r Q x ∈ prefixSpan r := by
  unfold frameHead
  exact ((prefixSpan r).orthogonalProjectionOnto (Haar.orthogonalLinearIsometryEquiv Q⁻¹ x)).property

theorem frameTail_decomposition {k : ℕ} (r : Fin (k + 1)) (Q : Haar.OrthogonalGroup k) (x : Space k) :
    frameHead r Q x + (tailIsometry r (frameTail r Q x) : Space k) = Haar.orthogonalLinearIsometryEquiv Q⁻¹ x := by
  unfold frameHead frameTail
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (prefixSpan r).starProjection_add_starProjection_orthogonal _

theorem frameCandidate_tail {k : ℕ} (r : Fin (k + 1)) (F G : Haar.OrthogonalGroup k) (x g : Space k) :
    frameTail r F (frameCandidateAt r F G x g) = ‖frameTail r G x‖ • normalize (frameTail r F g) := by
  have hc : Haar.orthogonalLinearIsometryEquiv F⁻¹ (frameCandidateAt r F G x g) =
      frameHead r G x + ‖frameTail r G x‖ • (tailIsometry r (normalize (frameTail r F g)) : Space k) := by
    rw [frameCandidateAt,← Haar.action_mul,inv_mul_cancel,Haar.action_one]
  have hz : (prefixSpan r)ᗮ.orthogonalProjectionOnto (frameHead r G x) = 0 :=
    (prefixSpan r).orthogonalProjectionOnto_orthogonal_apply_eq_zero (frameHead_mem r G x)
  have ht : (prefixSpan r)ᗮ.orthogonalProjectionOnto
      (tailIsometry r (normalize (frameTail r F g)) : Space k) = tailIsometry r (normalize (frameTail r F g)) :=
    (prefixSpan r)ᗮ.orthogonalProjectionOnto_mem_subspace_eq_self _
  conv_lhs => unfold frameTail
  rw [hc,map_add,map_smul,hz,zero_add,ht,map_smul,LinearIsometryEquiv.symm_apply_apply]

theorem normalize_positive_smul {k : ℕ} (c : ℝ) (hc : 0 < c) (h : Space k) :
    normalize (c • h) = normalize h := by
  by_cases hh : h = 0
  · simp [hh,normalize]
  · simp only [normalize,norm_smul,Real.norm_eq_abs,abs_of_pos hc,smul_smul]
    congr 1
    field_simp [hc.ne',norm_ne_zero_iff.mpr hh]

theorem normalize_normalized {k : ℕ} (h : Space k) : normalize (normalize h) = normalize h := by
  by_cases hh : h = 0
  · simp [hh,normalize]
  · rw [normalize,normalize_norm hh]
    simp only [inv_one,one_smul]

theorem frameCandidate_normalized_tail {k : ℕ} (s : FrameState k) (x g : Space k)
    (hq : frameTail s.1 s.2.2 x ≠ 0) :
    normalize (frameTail s.1 s.2.1 (frameCandidate s x g)) = normalize (frameTail s.1 s.2.1 g) := by
  rw [frameCandidate,frameCandidate_tail,normalize_positive_smul _ (norm_pos_iff.mpr hq),normalize_normalized]

def frameNewCoordinates {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k)
    (G : Haar.OrthogonalGroup k) (x : Space k) : Space k :=
  frameHead r G x + ‖frameTail r G x‖ • (tailIsometry r (firstTailVector r hr) : Space k)

theorem frameNewCoordinates_mem {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k)
    (G : Haar.OrthogonalGroup k) (x : Space k) : frameNewCoordinates r hr G x ∈ prefixSpan (nextRank r hr) :=
  (prefixSpan (nextRank r hr)).add_mem
    (prefixSpan_mono r (nextRank r hr) (by change r.val ≤ r.val + 1; omega) (frameHead_mem r G x))
    ((prefixSpan (nextRank r hr)).smul_mem _ (firstTailVector_mem_next r hr))

theorem frameNewPhysical_maps {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k)
    (G : Haar.OrthogonalGroup k) (x : Space k) (hq : frameTail r G x ≠ 0) :
    Haar.orthogonalLinearIsometryEquiv (G * tailOrthogonal r (tailTurn r hr (frameTail r G x)))
      (frameNewCoordinates r hr G x) = x := by
  have hf := tailOrthogonal_fixes_prefix r (tailTurn r hr (frameTail r G x)) ⟨frameHead r G x,frameHead_mem r G x⟩
  have ht := tailOrthogonal_on_tail r (tailTurn r hr (frameTail r G x)) (firstTailVector r hr)
  rw [tailTurn_first r hr _ hq] at ht
  have hs : ‖frameTail r G x‖ • (tailIsometry r (normalize (frameTail r G x)) : Space k) =
      (tailIsometry r (frameTail r G x) : Space k) := by
    have hh := congrArg (fun v : (prefixSpan r)ᗮ ↦ v.val)
      ((tailIsometry r).map_smul ‖frameTail r G x‖ (normalize (frameTail r G x)))
    simpa only [norm_smul_normalize,Submodule.coe_smul] using hh.symm
  rw [Haar.action_mul,frameNewCoordinates,map_add,map_smul,hf,ht,hs,frameTail_decomposition,
    ← Haar.action_mul,mul_inv_cancel,Haar.action_one]

theorem frameNewFormal_maps {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k)
    (F G : Haar.OrthogonalGroup k) (x g : Space k) (hh : frameTail r F g ≠ 0) :
    Haar.orthogonalLinearIsometryEquiv (F * tailOrthogonal r (tailTurn r hr (frameTail r F g)))
      (frameNewCoordinates r hr G x) = frameCandidateAt r F G x g := by
  have hf := tailOrthogonal_fixes_prefix r (tailTurn r hr (frameTail r F g)) ⟨frameHead r G x,frameHead_mem r G x⟩
  have ht := tailOrthogonal_on_tail r (tailTurn r hr (frameTail r F g)) (firstTailVector r hr)
  rw [tailTurn_first r hr _ hh] at ht
  rw [Haar.action_mul,frameNewCoordinates,map_add,map_smul,hf,ht]
  rfl

theorem frameUpdateActiveAt_inverse {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k)
    (F G : Haar.OrthogonalGroup k) (x g : Space k) (z : FrameTape k)
    (hq : frameTail r G x ≠ 0) (hh : frameTail r F g ≠ 0) :
    Haar.orthogonalLinearIsometryEquiv (frameComplete (frameUpdateActiveAt r hr F G x g) z)⁻¹ x =
      frameCandidateAt r F G x g := by
  let v : prefixSpan (nextRank r hr) := ⟨frameNewCoordinates r hr G x,frameNewCoordinates_mem r hr G x⟩
  have he := frameComplete_prefix (frameUpdateActiveAt r hr F G x g) z v
  change Haar.orthogonalLinearIsometryEquiv (frameComplete (frameUpdateActiveAt r hr F G x g) z)
    (Haar.orthogonalLinearIsometryEquiv (F * tailOrthogonal r (tailTurn r hr (frameTail r F g))) v.val) =
      Haar.orthogonalLinearIsometryEquiv (G * tailOrthogonal r (tailTurn r hr (frameTail r G x))) v.val at he
  rw [frameNewFormal_maps r hr F G x g hh,frameNewPhysical_maps r hr G x hq] at he
  rw [orthogonal_action_inv]
  apply (Haar.orthogonalLinearIsometryEquiv (frameComplete (frameUpdateActiveAt r hr F G x g) z)).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact he.symm

theorem frameUpdate_inverse {k : ℕ} (s : FrameState k) (x g : Space k) (z : FrameTape k)
    (hr : s.1.val < k) (hq : frameTail s.1 s.2.2 x ≠ 0) (hh : frameTail s.1 s.2.1 g ≠ 0) :
    Haar.orthogonalLinearIsometryEquiv (frameComplete (frameUpdate s x g) z)⁻¹ x = frameCandidate s x g := by
  unfold frameUpdate frameUpdateAt
  rw [dif_pos hr,if_neg hq]
  exact frameUpdateActiveAt_inverse s.1 hr s.2.1 s.2.2 x g z hq hh

theorem frameComplete_inverse_of_tail_zero {k : ℕ} (s : FrameState k) (x g : Space k) (z : FrameTape k)
    (hq : frameTail s.1 s.2.2 x = 0) :
    Haar.orthogonalLinearIsometryEquiv (frameComplete s z)⁻¹ x = frameCandidate s x g := by
  have hsplit := frameTail_decomposition s.1 s.2.2 x
  simp only [hq,map_zero,Submodule.coe_zero,add_zero] at hsplit
  have hh := frameComplete_prefix s z ⟨frameHead s.1 s.2.2 x,frameHead_mem s.1 s.2.2 x⟩
  have hx : Haar.orthogonalLinearIsometryEquiv s.2.2 (frameHead s.1 s.2.2 x) = x := by
    rw [hsplit,← Haar.action_mul,mul_inv_cancel,Haar.action_one]
  have hcand : frameCandidate s x g = Haar.orthogonalLinearIsometryEquiv s.2.1 (frameHead s.1 s.2.2 x) := by
    simp only [frameCandidate,frameCandidateAt,hq,norm_zero,zero_smul,add_zero]
  rw [orthogonal_action_inv,hcand]
  apply (Haar.orthogonalLinearIsometryEquiv (frameComplete s z)).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (hh.trans hx).symm

theorem frameUpdate_eq_self_of_tail_zero {k : ℕ} (s : FrameState k) (x g : Space k)
    (hq : frameTail s.1 s.2.2 x = 0) : frameUpdate s x g = s := by
  unfold frameUpdate frameUpdateAt
  split_ifs <;> simp_all

theorem frameUpdate_candidate_invariant {k : ℕ} (s : FrameState k) (x g : Space k) :
    frameUpdate s x (frameCandidate s x g) = frameUpdate s x g := by
  by_cases hr : s.1.val < k
  · by_cases hq : frameTail s.1 s.2.2 x = 0
    · rw [frameUpdate_eq_self_of_tail_zero s x _ hq,frameUpdate_eq_self_of_tail_zero s x _ hq]
    · unfold frameUpdate frameUpdateAt
      rw [dif_pos hr,if_neg hq,dif_pos hr,if_neg hq]
      unfold frameUpdateActiveAt
      rw [frameCandidate_normalized_tail s x g hq]
  · unfold frameUpdate frameUpdateAt
    rw [dif_neg hr,dif_neg hr]

end NCConcave16991.MixedHaar
