import NCConcave16991.MixedHaarFrameStepLaw

/-! # A total mixed kernel with unconditional domain growth and the same actual law -/

noncomputable section

open Set MeasureTheory ProbabilityTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000

attribute [local irreducible] frameTail frameHead frameComplete prefixSpan tailIsometry tailOrthogonal

variable {k : ℕ}

def frameSafeStep (s : FrameState k) (q : FrameRequest k) (g : Space k) : FrameState k × Space k := by
  classical
  exact if frameGaussianGood s g then frameStep s q g else (s,(frameStep s q g).2)

theorem frameSafeStep_measurable :
    Measurable (fun p : FrameState k × (FrameRequest k × Space k) ↦ frameSafeStep p.1 p.2.1 p.2.2) := by
  classical
  have hstep := frameStep_measurable (k := k)
  have hgood : MeasurableSet {p : FrameState k × (FrameRequest k × Space k) |
      frameGaussianGood p.1 p.2.2} := frameGaussianGood_measurableSet.preimage
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  unfold frameSafeStep
  exact Measurable.ite hgood hstep (measurable_fst.prodMk (measurable_snd.comp hstep))

theorem frameSafeStep_reply (s : FrameState k) (q : FrameRequest k) (g : Space k) :
    (frameSafeStep s q g).2 = (frameStep s q g).2 := by
  classical
  unfold frameSafeStep
  split_ifs <;> rfl

theorem frameSafeStep_domain_le (s : FrameState k) (q : FrameRequest k) (g : Space k) :
    frameDomain (frameSafeStep s q g).1 ≤
      frameDomain s ⊔ Submodule.span ℝ ({frameStepBirth q g} : Set (Space k)) := by
  classical
  unfold frameSafeStep
  split_ifs with hg
  · exact frameStep_domain_le s q g (frameGaussianGood_stepLegal s q g hg)
  · exact le_sup_left

def frameSafeStepCompletion (s : FrameState k) (q : FrameRequest k) (p : Space k × FrameTape k) :
    (FrameState k × Space k) × Haar.OrthogonalGroup k :=
  (frameSafeStep s q p.1,frameComplete (frameSafeStep s q p.1).1 p.2)

attribute [local irreducible] frameSafeStep frameSafeStepCompletion

theorem frameSafeStepCompletion_measurable :
    Measurable (fun p : FrameState k × (FrameRequest k × (Space k × FrameTape k)) ↦
      frameSafeStepCompletion p.1 p.2.1 p.2.2) := by
  have hd : Measurable (fun p : FrameState k × (FrameRequest k × (Space k × FrameTape k)) ↦
      frameSafeStep p.1 p.2.1 p.2.2.1) := frameSafeStep_measurable.comp
    (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd))))
  convert hd.prodMk (frameComplete_measurable.comp ((measurable_fst.comp hd).prodMk
    (measurable_snd.comp (measurable_snd.comp measurable_snd)))) using 1
  funext p
  unfold frameSafeStepCompletion
  rfl

theorem frameSafeStep_local_jointLaw (s : FrameState k) (q : FrameRequest k) :
    ((stdGaussian (Space k)).prod (frameTapeLaw k)).map (frameSafeStepCompletion s q) =
      (frameTapeLaw k).map (fun z ↦ (frameStaticStep s q (frameComplete s z),frameComplete s z)) := by
  have hp : MeasurePreserving (Prod.fst : Space k × FrameTape k → Space k)
      ((stdGaussian (Space k)).prod (frameTapeLaw k)) (stdGaussian (Space k)) := measurePreserving_fst
  have heq : frameSafeStepCompletion s q =ᵐ[(stdGaussian (Space k)).prod (frameTapeLaw k)]
      frameStepCompletion s q := by
    filter_upwards [hp.quasiMeasurePreserving.ae (frameGaussianGood_ae s)] with p hg
    simp only [frameSafeStepCompletion,frameSafeStep,if_pos hg,frameStepCompletion]
  rw [Measure.map_congr heq]
  exact frameStep_local_jointLaw s q

end NCConcave16991.MixedHaar
