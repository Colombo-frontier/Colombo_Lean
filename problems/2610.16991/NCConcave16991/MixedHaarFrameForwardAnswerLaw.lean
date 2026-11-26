import NCConcave16991.MixedHaarFrameForwardLaw
import NCConcave16991.MixedHaarFrameAnswerLaw

/-! # The recorded forward answer has the genuine static full-frame joint law -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 100000

attribute [local irreducible] frameTail frameHead frameComplete frameCandidate
  prefixSpan tailIsometry tailOrthogonal Haar.orthogonalLinearIsometryEquiv

variable {k : ℕ}

theorem frameForward_answer_ae (s : FrameState k) (x : Space k) :
    ∀ᵐ p : Space k × FrameTape k ∂(stdGaussian (Space k)).prod (frameTapeLaw k),
      Haar.orthogonalLinearIsometryEquiv (frameComplete (frameForwardUpdate s x p.1) p.2) x =
        frameForwardCandidate s x p.1 := by
  by_cases hr : s.1.val < k
  · by_cases hq : frameTail s.1 s.2.1 x = 0
    · have hz (g : Space k) : frameForwardUpdate s x g = s := by
        unfold frameForwardUpdate
        rw [frameUpdate_eq_self_of_tail_zero (frameSwap s) x g hq,frameSwap_involutive]
      exact Filter.Eventually.of_forall (fun p ↦ by
        rw [hz]
        exact frameForwardComplete_answer_of_tail_zero s x p.1 p.2 hq)
    · have hn := frameTail_ne_zero_ae s.1 s.2.2 (firstTailVector s.1 hr) (firstTailVector_unit s.1 hr)
      have hp : MeasurePreserving (Prod.fst : Space k × FrameTape k → Space k)
          ((stdGaussian (Space k)).prod (frameTapeLaw k)) (stdGaussian (Space k)) := measurePreserving_fst
      filter_upwards [hp.quasiMeasurePreserving.ae hn] with p hh
      exact frameForwardUpdate_answer s x p.1 p.2 hr hq hh
  · have hq := frameTail_eq_zero_of_not_lt s.1 s.2.1 x hr
    have hz (g : Space k) : frameForwardUpdate s x g = s := by
      unfold frameForwardUpdate
      rw [frameUpdate_eq_self_of_tail_zero (frameSwap s) x g hq,frameSwap_involutive]
    exact Filter.Eventually.of_forall (fun p ↦ by
      rw [hz]
      exact frameForwardComplete_answer_of_tail_zero s x p.1 p.2 hq)

theorem frameForward_reveal_measurable (s : FrameState k) (x : Space k) :
    Measurable (fun p : Space k × FrameTape k ↦
      (frameForwardCandidate s x p.1,
        (frameForwardUpdate s x p.1,frameComplete (frameForwardUpdate s x p.1) p.2))) := by
  have ha : Measurable (fun p : Space k × FrameTape k ↦ frameForwardCandidate s x p.1) :=
    frameForwardCandidate_measurable.comp (measurable_const.prodMk (measurable_const.prodMk measurable_fst))
  exact ha.prodMk (frameForwardJoint_measurable s x)

theorem frameForward_answer_local_jointLaw (s : FrameState k) (x : Space k) :
    ((stdGaussian (Space k)).prod (frameTapeLaw k)).map
        (fun p ↦ (frameForwardCandidate s x p.1,
          (frameForwardUpdate s x p.1,frameComplete (frameForwardUpdate s x p.1) p.2))) =
      (frameCompletionLaw s).map (fun Q ↦
        (Haar.orthogonalLinearIsometryEquiv Q x,(frameForwardStaticStep s x Q,Q))) := by
  let μ := (stdGaussian (Space k)).prod (frameTapeLaw k)
  let complete := fun p : Space k × FrameTape k ↦ frameComplete (frameForwardUpdate s x p.1) p.2
  let observe := fun Q : Haar.OrthogonalGroup k ↦
    (Haar.orthogonalLinearIsometryEquiv Q x,(frameForwardStaticStep s x Q,Q))
  have ho : Measurable observe := (Haar.continuous_orthogonalLinearIsometryEquiv_apply x).measurable.prodMk
    ((frameForwardStaticStep_measurable s x).prodMk measurable_id)
  have hg := frameComplete_forward_update_preserving s x
  have heq : (fun p : Space k × FrameTape k ↦
      (frameForwardCandidate s x p.1,(frameForwardUpdate s x p.1,complete p))) =ᵐ[μ]
        observe ∘ complete := by
    filter_upwards [frameForward_answer_ae s x,frameForwardUpdate_recover_updated_ae s x] with p hp hs
    exact Prod.ext hp.symm (Prod.ext hs.symm rfl)
  rw [Measure.map_congr heq]
  have hm := Measure.map_map (μ := μ) ho hg.measurable
  rw [← hm,hg.map_eq]

theorem frameForward_answer_local_jointLaw_tape (s : FrameState k) (x : Space k) :
    ((stdGaussian (Space k)).prod (frameTapeLaw k)).map
        (fun p ↦ (frameForwardCandidate s x p.1,
          (frameForwardUpdate s x p.1,frameComplete (frameForwardUpdate s x p.1) p.2))) =
      (frameTapeLaw k).map (fun z ↦
        (Haar.orthogonalLinearIsometryEquiv (frameComplete s z) x,
          (frameForwardStaticStep s x (frameComplete s z),frameComplete s z))) := by
  rw [frameForward_answer_local_jointLaw]
  have hc := frameComplete_preserving s
  have ho := (Haar.continuous_orthogonalLinearIsometryEquiv_apply x).measurable.prodMk
    ((frameForwardStaticStep_measurable s x).prodMk measurable_id)
  have hm := Measure.map_map (μ := frameTapeLaw k) ho hc.measurable
  rw [hc.map_eq] at hm
  simpa only [Function.comp_def,id_eq] using hm

end NCConcave16991.MixedHaar
