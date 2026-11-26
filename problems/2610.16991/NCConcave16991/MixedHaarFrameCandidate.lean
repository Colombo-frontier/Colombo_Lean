import NCConcave16991.MixedHaarFrameState
import NCConcave16991.MixedHaarNormalizedGaussian
import NCConcave16991.MixedHaarSphereOrbit

/-! # The measurable inverse candidate belongs to old formal span plus one Gaussian -/

noncomputable section

namespace NCConcave16991.MixedHaar

open Set MeasureTheory

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] tailIsometry prefixSpan Haar.orthogonalLinearIsometryEquiv

def frameHead {k : ℕ} (r : Fin (k + 1)) (Q : Haar.OrthogonalGroup k) (x : Space k) : Space k :=
  (prefixSpan r).starProjection (Haar.orthogonalLinearIsometryEquiv Q⁻¹ x)

def frameTail {k : ℕ} (r : Fin (k + 1)) (Q : Haar.OrthogonalGroup k) (x : Space k) : Space (k - r.val) :=
  (tailIsometry r).symm ((prefixSpan r)ᗮ.orthogonalProjectionOnto (Haar.orthogonalLinearIsometryEquiv Q⁻¹ x))

theorem frameHead_continuous {k : ℕ} (r : Fin (k + 1)) :
    Continuous (fun p : Haar.OrthogonalGroup k × Space k ↦ frameHead r p.1 p.2) := by
  have hc : Continuous (fun p : Haar.OrthogonalGroup k × Space k ↦ Haar.orthogonalLinearIsometryEquiv p.1⁻¹ p.2) :=
    sphereAction_joint_continuous.comp (continuous_fst.inv.prodMk continuous_snd)
  convert (prefixSpan r).starProjection.continuous.comp hc using 1
  rfl

theorem frameTail_continuous {k : ℕ} (r : Fin (k + 1)) :
    Continuous (fun p : Haar.OrthogonalGroup k × Space k ↦ frameTail r p.1 p.2) := by
  have hc : Continuous (fun p : Haar.OrthogonalGroup k × Space k ↦ Haar.orthogonalLinearIsometryEquiv p.1⁻¹ p.2) :=
    sphereAction_joint_continuous.comp (continuous_fst.inv.prodMk continuous_snd)
  have hp : Continuous (fun p : Haar.OrthogonalGroup k × Space k ↦
      (prefixSpan r)ᗮ.orthogonalProjectionOnto (Haar.orthogonalLinearIsometryEquiv p.1⁻¹ p.2)) :=
    (prefixSpan r)ᗮ.orthogonalProjectionOnto.continuous.comp hc
  convert (tailIsometry r).symm.continuous.comp hp using 1
  rfl

def frameCandidateAt {k : ℕ} (r : Fin (k + 1)) (F G : Haar.OrthogonalGroup k) (x g : Space k) : Space k :=
  Haar.orthogonalLinearIsometryEquiv F (frameHead r G x +
    ‖frameTail r G x‖ • (tailIsometry r (normalize (frameTail r F g)) : Space k))

def frameCandidate {k : ℕ} (s : FrameState k) (x g : Space k) : Space k := frameCandidateAt s.1 s.2.1 s.2.2 x g

theorem frameCandidateAt_measurable {k : ℕ} (r : Fin (k + 1)) :
    Measurable (fun p : (Haar.OrthogonalGroup k × Haar.OrthogonalGroup k) × (Space k × Space k) ↦
      frameCandidateAt r p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hF : Measurable (fun p : (Haar.OrthogonalGroup k × Haar.OrthogonalGroup k) × (Space k × Space k) ↦ p.1.1) :=
    measurable_fst.comp measurable_fst
  have hG : Measurable (fun p : (Haar.OrthogonalGroup k × Haar.OrthogonalGroup k) × (Space k × Space k) ↦ p.1.2) :=
    measurable_snd.comp measurable_fst
  have hx : Measurable (fun p : (Haar.OrthogonalGroup k × Haar.OrthogonalGroup k) × (Space k × Space k) ↦ p.2.1) :=
    measurable_fst.comp measurable_snd
  have hg : Measurable (fun p : (Haar.OrthogonalGroup k × Haar.OrthogonalGroup k) × (Space k × Space k) ↦ p.2.2) :=
    measurable_snd.comp measurable_snd
  have hq := (frameTail_continuous r).measurable.comp (hG.prodMk hx)
  have hh := (frameTail_continuous r).measurable.comp (hF.prodMk hg)
  have hb := (frameHead_continuous r).measurable.comp (hG.prodMk hx)
  exact sphereAction_joint_measurable.comp (hF.prodMk (hb.add
    (hq.norm.smul (measurable_subtype_coe.comp ((tailIsometry r).continuous.measurable.comp
      (normalize_measurable.comp hh))))))

theorem frameCandidate_measurable {k : ℕ} :
    Measurable (fun p : FrameState k × (Space k × Space k) ↦ frameCandidate p.1 p.2.1 p.2.2) := by
  exact measurable_finite_indexed (fun p : FrameState k × (Space k × Space k) ↦ p.1.1)
    (measurable_fst.comp measurable_fst)
    (fun r p ↦ frameCandidateAt r p.1.2.1 p.1.2.2 p.2.1 p.2.2)
    (fun r ↦ (frameCandidateAt_measurable r).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

theorem frameCandidate_mem_old_sup_gaussian {k : ℕ} (s : FrameState k) (x g : Space k) :
    frameCandidate s x g ∈ frameDomain s ⊔ Submodule.span ℝ ({g} : Set (Space k)) := by
  let D := prefixSpan s.1
  let F := Haar.orthogonalLinearIsometryEquiv s.2.1
  let g₀ := Haar.orthogonalLinearIsometryEquiv s.2.1⁻¹ g
  let W := frameDomain s ⊔ Submodule.span ℝ ({g} : Set (Space k))
  have hknown (Q : Haar.OrthogonalGroup k) (y : Space k) : F (frameHead s.1 Q y) ∈ W := by
    apply Submodule.mem_sup_left
    exact ⟨frameHead s.1 Q y,(D.orthogonalProjectionOnto _).property,rfl⟩
  have hsplit : D.starProjection g₀ + (Dᗮ.orthogonalProjectionOnto g₀ : Space k) = g₀ := by
    exact D.starProjection_add_starProjection_orthogonal g₀
  have hF : F g₀ = g := by
    change Haar.orthogonalLinearIsometryEquiv s.2.1 (Haar.orthogonalLinearIsometryEquiv s.2.1⁻¹ g) = g
    rw [← Haar.action_mul,mul_inv_cancel,Haar.action_one]
  have horth : F (tailIsometry s.1 (frameTail s.1 s.2.1 g) : Space k) ∈ W := by
    have he : F (tailIsometry s.1 (frameTail s.1 s.2.1 g) : Space k) = g - F (frameHead s.1 s.2.1 g) := by
      have hh := congrArg F hsplit
      rw [map_add,hF] at hh
      change F (tailIsometry s.1 ((tailIsometry s.1).symm (Dᗮ.orthogonalProjectionOnto g₀)) : Space k) = _
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact eq_sub_of_add_eq' hh
    rw [he]
    exact W.sub_mem (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))) (hknown s.2.1 g)
  change F (frameHead s.1 s.2.2 x +
    ‖frameTail s.1 s.2.2 x‖ • (tailIsometry s.1 (normalize (frameTail s.1 s.2.1 g)) : Space k)) ∈ W
  simp only [normalize,map_add,map_smul,Submodule.coe_smul,smul_smul]
  exact W.add_mem (hknown s.2.2 x) (W.smul_mem _ horth)

end NCConcave16991.MixedHaar
