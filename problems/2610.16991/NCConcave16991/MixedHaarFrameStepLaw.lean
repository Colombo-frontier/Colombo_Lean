import NCConcave16991.MixedHaarFrameStep
import NCConcave16991.MixedHaarFrameForwardAnswerLaw
import NCConcave16991.MixedHaarFrameGaussianGood

/-! # The mixed frame request interpreter has the exact actual static reply law -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000

attribute [local irreducible] frameTail frameHead frameComplete frameCandidate
  prefixSpan tailIsometry tailOrthogonal Haar.orthogonalLinearIsometryEquiv

variable {k : ℕ}

def frameStaticStep (s : FrameState k) (q : FrameRequest k) (Q : Haar.OrthogonalGroup k) : FrameState k × Space k :=
  q.elim (fun a ↦ (frameForwardStaticStep s a Q,Haar.orthogonalLinearIsometryEquiv Q a))
    (fun b ↦ (frameInverseStaticStep s b Q,Haar.orthogonalLinearIsometryEquiv Q⁻¹ b))

theorem frameStaticStep_measurable :
    Measurable (fun p : FrameState k × (FrameRequest k × Haar.OrthogonalGroup k) ↦
      frameStaticStep p.1 p.2.1 p.2.2) := by
  classical
  have hq : Measurable (fun p : FrameState k × (FrameRequest k × Haar.OrthogonalGroup k) ↦ p.2.1) :=
    measurable_fst.comp measurable_snd
  have hQ : Measurable (fun p : FrameState k × (FrameRequest k × Haar.OrthogonalGroup k) ↦ p.2.2) :=
    measurable_snd.comp measurable_snd
  have ha : Measurable (frameRequestForward (k := k)) := measurable_id.sumElim measurable_const
  have hb : Measurable (frameRequestInverse (k := k)) := measurable_const.sumElim measurable_id
  have hi : Measurable (frameIsForward (k := k)) := measurable_const.sumElim measurable_const
  have haf := sphereAction_joint_measurable.comp (hQ.prodMk (ha.comp hq))
  have hbf := sphereAction_joint_measurable.comp (hQ.inv.prodMk (hb.comp hq))
  have hf := (frameForwardUpdate_measurable.comp
    (measurable_fst.prodMk ((ha.comp hq).prodMk haf))).prodMk haf
  have hg := (frameUpdate_measurable.comp
    (measurable_fst.prodMk ((hb.comp hq).prodMk hbf))).prodMk hbf
  have ht : Measurable (fun _ : FrameState k × (FrameRequest k × Haar.OrthogonalGroup k) ↦ true) := measurable_const
  have hset : MeasurableSet {p : FrameState k × (FrameRequest k × Haar.OrthogonalGroup k) |
      frameIsForward p.2.1 = true} := measurableSet_eq_fun (hi.comp hq) ht
  have hh : Measurable (fun p : FrameState k × (FrameRequest k × Haar.OrthogonalGroup k) ↦
      if frameIsForward p.2.1 = true then
        (frameForwardUpdate p.1 (frameRequestForward p.2.1)
          (Haar.orthogonalLinearIsometryEquiv p.2.2 (frameRequestForward p.2.1)),
            Haar.orthogonalLinearIsometryEquiv p.2.2 (frameRequestForward p.2.1))
      else (frameUpdate p.1 (frameRequestInverse p.2.1)
        (Haar.orthogonalLinearIsometryEquiv p.2.2⁻¹ (frameRequestInverse p.2.1)),
          Haar.orthogonalLinearIsometryEquiv p.2.2⁻¹ (frameRequestInverse p.2.1))) := Measurable.ite hset hf hg
  convert hh using 1
  funext p
  cases p.2.1 <;> rfl

theorem frameStaticStep_fixed_measurable (s : FrameState k) (q : FrameRequest k) :
    Measurable (frameStaticStep s q) :=
  frameStaticStep_measurable.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))

/-- Genuine local law for one arbitrary forward or inverse request, including
the actual reply used by the public control state. -/
theorem frameStep_local_jointLaw (s : FrameState k) (q : FrameRequest k) :
    ((stdGaussian (Space k)).prod (frameTapeLaw k)).map (frameStepCompletion s q) =
      (frameTapeLaw k).map (fun z ↦ (frameStaticStep s q (frameComplete s z),frameComplete s z)) := by
  let reorder := fun p : Space k × (FrameState k × Haar.OrthogonalGroup k) ↦ ((p.2.1,p.1),p.2.2)
  have ho : Measurable reorder :=
    ((measurable_fst.comp measurable_snd).prodMk measurable_fst).prodMk (measurable_snd.comp measurable_snd)
  have hc := (frameComplete_preserving s).measurable
  cases q with
  | inl a =>
      have he : frameStepCompletion s (.inl a) = (fun p : Space k × FrameTape k ↦
          ((frameForwardUpdate s a p.1,frameForwardCandidate s a p.1),
            frameComplete (frameForwardUpdate s a p.1) p.2)) := by
        funext p
        unfold frameStepCompletion frameStep
        rfl
      rw [he]
      have hs : Measurable (fun z : FrameTape k ↦
          (Haar.orthogonalLinearIsometryEquiv (frameComplete s z) a,
            (frameForwardStaticStep s a (frameComplete s z),frameComplete s z))) :=
        ((Haar.continuous_orthogonalLinearIsometryEquiv_apply a).measurable.comp hc).prodMk
          (((frameForwardStaticStep_measurable s a).comp hc).prodMk hc)
      have h := congrArg (Measure.map reorder) (frameForward_answer_local_jointLaw_tape s a)
      rw [Measure.map_map ho (frameForward_reveal_measurable s a),Measure.map_map ho hs] at h
      simpa only [Function.comp_def,reorder,frameStepCompletion,frameStep,frameStaticStep,Sum.elim_inl] using h
  | inr b =>
      have he : frameStepCompletion s (.inr b) = (fun p : Space k × FrameTape k ↦
          ((frameUpdate s b p.1,frameCandidate s b p.1),frameComplete (frameUpdate s b p.1) p.2)) := by
        funext p
        unfold frameStepCompletion frameStep
        rfl
      rw [he]
      have hs : Measurable (fun z : FrameTape k ↦
          (Haar.orthogonalLinearIsometryEquiv (frameComplete s z)⁻¹ b,
            (frameInverseStaticStep s b (frameComplete s z),frameComplete s z))) :=
        ((Haar.continuous_orthogonalLinearIsometryEquiv_apply b).measurable.comp (hc.inv)).prodMk
          (((frameInverseStaticStep_measurable s b).comp hc).prodMk hc)
      have h := congrArg (Measure.map reorder) (frameInverse_answer_local_jointLaw_tape s b)
      rw [Measure.map_map ho (frameInverse_reveal_measurable s b),Measure.map_map ho hs] at h
      simpa only [Function.comp_def,reorder,frameStepCompletion,frameStep,frameStaticStep,Sum.elim_inr] using h

theorem frameNone_reply_local_jointLaw (s : FrameState k) :
    ((stdGaussian (Space k)).prod (frameTapeLaw k)).map
        (fun p : Space k × FrameTape k ↦ ((s,(0 : Space k)),frameComplete s p.2)) =
      (frameTapeLaw k).map (fun z ↦ ((s,(0 : Space k)),frameComplete s z)) := by
  have hs : MeasurePreserving (Prod.snd : Space k × FrameTape k → FrameTape k)
      ((stdGaussian (Space k)).prod (frameTapeLaw k)) (frameTapeLaw k) := measurePreserving_snd
  have ho : Measurable (fun z : FrameTape k ↦ ((s,(0 : Space k)),frameComplete s z)) :=
    measurable_const.prodMk (frameComplete_preserving s).measurable
  have hm := Measure.map_map (μ := (stdGaussian (Space k)).prod (frameTapeLaw k)) ho hs.measurable
  rw [hs.map_eq] at hm
  simpa only [Function.comp_def] using hm.symm

theorem frameStep_public_local_jointLaw {A : Type*} [MeasurableSpace A]
    (s : FrameState k) (q : FrameRequest k) (publicUpdate : FrameState k × Space k → A)
    (hu : Measurable publicUpdate) :
    ((stdGaussian (Space k)).prod (frameTapeLaw k)).map
        (fun p : Space k × FrameTape k ↦
          (publicUpdate (frameStep s q p.1),frameComplete (frameStep s q p.1).1 p.2)) =
      (frameTapeLaw k).map (fun z ↦
        (publicUpdate (frameStaticStep s q (frameComplete s z)),frameComplete s z)) := by
  let output := fun p : (FrameState k × Space k) × Haar.OrthogonalGroup k ↦ (publicUpdate p.1,p.2)
  have ho : Measurable output := (hu.comp measurable_fst).prodMk measurable_snd
  have hl : Measurable (frameStepCompletion s q) := frameStepCompletion_measurable.comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hc := (frameComplete_preserving s).measurable
  have hr : Measurable (fun z : FrameTape k ↦ (frameStaticStep s q (frameComplete s z),frameComplete s z)) :=
    ((frameStaticStep_fixed_measurable s q).comp hc).prodMk hc
  have h := congrArg (Measure.map output) (frameStep_local_jointLaw s q)
  rw [Measure.map_map ho hl,Measure.map_map ho hr] at h
  simpa only [Function.comp_def,output,frameStepCompletion] using h

theorem frameGaussianGood_stepLegal (s : FrameState k) (q : FrameRequest k) (g : Space k)
    (hg : frameGaussianGood s g) : FrameStepLegal s q g := by
  cases q with
  | inl a => trivial
  | inr b =>
      intro hr hq
      rcases hg with hfull | htail
      · omega
      · exact htail

theorem frameStepLegal_ae (s : FrameState k) (q : FrameRequest k) :
    ∀ᵐ g ∂stdGaussian (Space k), FrameStepLegal s q g := by
  filter_upwards [frameGaussianGood_ae s] with g hg
  exact frameGaussianGood_stepLegal s q g hg

end NCConcave16991.MixedHaar
