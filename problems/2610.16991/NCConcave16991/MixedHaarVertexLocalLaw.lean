import NCConcave16991.MixedHaarVertexStep

/-! # A single native coordinate of the mixed vertex kernel has the exact static law -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 300000

attribute [local irreducible] nativeCoordinates frameSafeStep frameComplete

variable {I : Type*} [Fintype I] (E : I → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]

def nativeLocalStepCompletion (i : I) (s : FrameState (nativeDimension E i)) (q : NativeRequest E)
    (p : E i × FrameTape (nativeDimension E i)) :
    (FrameState (nativeDimension E i) × E i) × Haar.OrthogonalGroup (nativeDimension E i) :=
  (nativeLocalStep E i s q p.1,frameComplete (nativeLocalStep E i s q p.1).1 p.2)

theorem nativeLocalStepCompletion_fixed_measurable (i : I) (s : FrameState (nativeDimension E i))
    (q : NativeRequest E) : Measurable (nativeLocalStepCompletion E i s q) := by
  have hd : Measurable (fun p : E i × FrameTape (nativeDimension E i) ↦ nativeLocalStep E i s q p.1) :=
    (nativeLocalStep_measurable E i).comp
    (measurable_const.prodMk (measurable_const.prodMk
      (measurable_fst : Measurable (Prod.fst : E i × FrameTape (nativeDimension E i) → E i))))
  convert hd.prodMk (frameComplete_measurable.comp ((measurable_fst.comp hd).prodMk measurable_snd)) using 1
  funext p
  unfold nativeLocalStepCompletion
  rfl

theorem nativeLocalStaticCompletion_fixed_measurable (i : I) (s : FrameState (nativeDimension E i))
    (q : NativeRequest E) : Measurable (fun z : FrameTape (nativeDimension E i) ↦
      (nativeLocalStaticStep E i s q (frameComplete s z),frameComplete s z)) := by
  have hc := (frameComplete_preserving s).measurable
  exact ((nativeLocalStaticStep_measurable E i).comp
    (measurable_const.prodMk (measurable_const.prodMk hc))).prodMk hc

theorem nativeLocalStep_local_jointLaw (i : I) (s : FrameState (nativeDimension E i)) (q : NativeRequest E) :
    ((stdGaussian (E i)).prod (frameTapeLaw (nativeDimension E i))).map (nativeLocalStepCompletion E i s q) =
      (frameTapeLaw (nativeDimension E i)).map (fun z ↦
        (nativeLocalStaticStep E i s q (frameComplete s z),frameComplete s z)) := by
  classical
  by_cases hi : q.1 = i
  · let qr := nativeCoordinateRequest E i q
    let source := Prod.map (nativeCoordinates E i) (id : FrameTape (nativeDimension E i) → FrameTape (nativeDimension E i))
    have hcoordinate : MeasurePreserving (nativeCoordinates E i) (stdGaussian (E i))
        (stdGaussian (Space (nativeDimension E i))) :=
      ⟨(nativeCoordinates E i).continuous.measurable,stdGaussian_map _⟩
    have hsource := hcoordinate.prod (MeasurePreserving.id (frameTapeLaw (nativeDimension E i)))
    let decode := fun p : (FrameState (nativeDimension E i) × Space (nativeDimension E i)) ×
        Haar.OrthogonalGroup (nativeDimension E i) ↦ ((p.1.1,(nativeCoordinates E i).symm p.1.2),p.2)
    have hd : Measurable decode :=
      ((measurable_fst.comp measurable_fst).prodMk ((nativeCoordinates E i).symm.continuous.measurable.comp
        (measurable_snd.comp measurable_fst))).prodMk measurable_snd
    have hl : Measurable (frameSafeStepCompletion s qr) := frameSafeStepCompletion_measurable.comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have hc := (frameComplete_preserving s).measurable
    have hr : Measurable (fun z : FrameTape (nativeDimension E i) ↦
        (frameStaticStep s qr (frameComplete s z),frameComplete s z)) :=
      ((frameStaticStep_fixed_measurable s qr).comp hc).prodMk hc
    have h := congrArg (Measure.map decode) (frameSafeStep_local_jointLaw s qr)
    rw [Measure.map_map hd hl,Measure.map_map hd hr] at h
    have ht := Measure.map_map (μ := (stdGaussian (E i)).prod (frameTapeLaw (nativeDimension E i)))
      (hd.comp hl) hsource.measurable
    rw [hsource.map_eq] at ht
    have hfinal := ht.symm.trans h
    unfold nativeLocalStepCompletion
    simp only [nativeLocalStep,nativeLocalStaticStep,if_pos hi]
    simpa only [Function.comp_def,Prod.map,id_eq,decode,frameSafeStepCompletion,qr] using hfinal
  · have hs : MeasurePreserving (Prod.snd : E i × FrameTape (nativeDimension E i) → FrameTape (nativeDimension E i))
        ((stdGaussian (E i)).prod (frameTapeLaw (nativeDimension E i))) (frameTapeLaw (nativeDimension E i)) :=
      measurePreserving_snd
    have ho : Measurable (fun z : FrameTape (nativeDimension E i) ↦ ((s,(0 : E i)),frameComplete s z)) :=
      measurable_const.prodMk (frameComplete_preserving s).measurable
    have hm := Measure.map_map (μ := (stdGaussian (E i)).prod (frameTapeLaw (nativeDimension E i))) ho hs.measurable
    rw [hs.map_eq] at hm
    unfold nativeLocalStepCompletion
    simp only [nativeLocalStep,nativeLocalStaticStep,if_neg hi]
    simpa only [Function.comp_def] using hm.symm

end NCConcave16991.MixedHaar
