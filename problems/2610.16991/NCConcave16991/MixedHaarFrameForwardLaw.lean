import NCConcave16991.MixedHaarFrameLocalLaw
import NCConcave16991.MixedHaarFrameForward

/-! # Exact full-frame forward-reveal law, derived from the inverse completion -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 300000

attribute [local irreducible] frameTail frameHead frameComplete frameCandidate
  prefixSpan tailIsometry tailOrthogonal Haar.orthogonalLinearIsometryEquiv

variable {k : ℕ}

def frameForwardStaticStep (s : FrameState k) (x : Space k) (Q : Haar.OrthogonalGroup k) : FrameState k :=
  frameForwardUpdate s x (Haar.orthogonalLinearIsometryEquiv Q x)

theorem frameForwardStaticStep_measurable (s : FrameState k) (x : Space k) :
    Measurable (frameForwardStaticStep s x) := by
  unfold frameForwardStaticStep
  exact frameForwardUpdate_measurable.comp (measurable_const.prodMk (measurable_const.prodMk
    (Haar.continuous_orthogonalLinearIsometryEquiv_apply x).measurable))

theorem frameForwardJoint_measurable (s : FrameState k) (x : Space k) :
    Measurable (fun p : Space k × FrameTape k ↦
      (frameForwardUpdate s x p.1,frameComplete (frameForwardUpdate s x p.1) p.2)) := by
  have hn : Measurable (fun p : Space k × FrameTape k ↦ frameForwardUpdate s x p.1) :=
    frameForwardUpdate_measurable.comp (measurable_const.prodMk (measurable_const.prodMk measurable_fst))
  exact hn.prodMk (frameComplete_measurable.comp (hn.prodMk measurable_snd))

theorem frameComplete_forward_update_preserving (s : FrameState k) (x : Space k) :
    MeasurePreserving
      (fun p : Space k × FrameTape k ↦ frameComplete (frameForwardUpdate s x p.1) p.2)
      ((stdGaussian (Space k)).prod (frameTapeLaw k)) (frameCompletionLaw s) := by
  have hsource := (MeasurePreserving.id (stdGaussian (Space k))).prod (frameTapeInv_preserving k)
  have hgen := frameComplete_update_preserving (frameSwap s) x
  have h := (frameCompletionLaw_swap_inverse s).comp (hgen.comp hsource)
  convert h using 1
  funext p
  have hs : frameComplete (frameUpdate (frameSwap s) x p.1) (frameTapeInv p.2) =
      (frameComplete (frameForwardUpdate s x p.1) p.2)⁻¹ :=
    frameComplete_swap_inv (frameForwardUpdate s x p.1) p.2
  simpa only [Function.comp_def,Prod.map,id_eq,inv_inv] using (congrArg Inv.inv hs).symm

theorem frameForwardUpdate_recover_updated_ae (s : FrameState k) (x : Space k) :
    ∀ᵐ p : Space k × FrameTape k ∂(stdGaussian (Space k)).prod (frameTapeLaw k),
      frameForwardStaticStep s x (frameComplete (frameForwardUpdate s x p.1) p.2) =
        frameForwardUpdate s x p.1 := by
  by_cases hr : s.1.val < k
  · by_cases hq : frameTail s.1 s.2.1 x = 0
    · have hz (g : Space k) : frameForwardUpdate s x g = s := by
        unfold frameForwardUpdate
        rw [frameUpdate_eq_self_of_tail_zero (frameSwap s) x g hq,frameSwap_involutive]
      exact Filter.Eventually.of_forall (fun p ↦ by unfold frameForwardStaticStep; rw [hz,hz])
    · have hn := frameTail_ne_zero_ae s.1 s.2.2 (firstTailVector s.1 hr) (firstTailVector_unit s.1 hr)
      have hp : MeasurePreserving (Prod.fst : Space k × FrameTape k → Space k)
          ((stdGaussian (Space k)).prod (frameTapeLaw k)) (stdGaussian (Space k)) := measurePreserving_fst
      filter_upwards [hp.quasiMeasurePreserving.ae hn] with p hh
      unfold frameForwardStaticStep
      rw [frameForwardUpdate_answer s x p.1 p.2 hr hq hh]
      exact frameForwardUpdate_candidate_invariant s x p.1
  · have hz (g : Space k) : frameForwardUpdate s x g = s := by
      unfold frameForwardUpdate frameUpdate frameUpdateAt
      have hr' : ¬ (frameSwap s).1.val < k := hr
      rw [dif_neg hr']
      rfl
    exact Filter.Eventually.of_forall (fun p ↦ by unfold frameForwardStaticStep; rw [hz,hz])

theorem frameForward_local_jointLaw (s : FrameState k) (x : Space k) :
    ((stdGaussian (Space k)).prod (frameTapeLaw k)).map
        (fun p ↦ (frameForwardUpdate s x p.1,frameComplete (frameForwardUpdate s x p.1) p.2)) =
      (frameCompletionLaw s).map (fun Q ↦ (frameForwardStaticStep s x Q,Q)) := by
  let μ := (stdGaussian (Space k)).prod (frameTapeLaw k)
  let complete := fun p : Space k × FrameTape k ↦ frameComplete (frameForwardUpdate s x p.1) p.2
  let observe := fun Q : Haar.OrthogonalGroup k ↦ (frameForwardStaticStep s x Q,Q)
  have ho : Measurable observe := (frameForwardStaticStep_measurable s x).prodMk measurable_id
  have hg := frameComplete_forward_update_preserving s x
  have heq : (fun p : Space k × FrameTape k ↦ (frameForwardUpdate s x p.1,complete p)) =ᵐ[μ]
      observe ∘ complete := by
    filter_upwards [frameForwardUpdate_recover_updated_ae s x] with p hp
    exact Prod.ext hp.symm rfl
  rw [Measure.map_congr heq]
  have hm := Measure.map_map (μ := μ) ho hg.measurable
  rw [← hm,hg.map_eq]

theorem frameForward_local_jointLaw_tape (s : FrameState k) (x : Space k) :
    ((stdGaussian (Space k)).prod (frameTapeLaw k)).map
        (fun p ↦ (frameForwardUpdate s x p.1,frameComplete (frameForwardUpdate s x p.1) p.2)) =
      (frameTapeLaw k).map (fun z ↦
        (frameForwardStaticStep s x (frameComplete s z),frameComplete s z)) := by
  rw [frameForward_local_jointLaw]
  have hc := frameComplete_preserving s
  have ho := (frameForwardStaticStep_measurable s x).prodMk measurable_id
  have hm := Measure.map_map (μ := frameTapeLaw k) ho hc.measurable
  rw [hc.map_eq] at hm
  simpa only [Function.comp_def,id_eq] using hm

end NCConcave16991.MixedHaar
