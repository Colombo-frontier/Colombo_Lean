import NCConcave16991.MixedHaarNativeRequest
import NCConcave16991.MixedHaarFrameSafeStep
import NCConcave16991.MixedHaarVertexFrame

/-! # A native finite-vertex mixed reveal kernel with sparse replies -/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 300000

attribute [local irreducible] nativeCoordinates frameSafeStep frameComplete vertexFrameComplete
  Haar.orthogonalLinearIsometryEquiv

variable {I : Type*} [Fintype I] (E : I → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]

def nativeLocalStep (i : I) (s : FrameState (nativeDimension E i)) (q : NativeRequest E) (g : E i) :
    FrameState (nativeDimension E i) × E i := by
  classical
  exact if q.1 = i then
    let d := frameSafeStep s (nativeCoordinateRequest E i q) (nativeCoordinates E i g)
    (d.1,(nativeCoordinates E i).symm d.2)
  else (s,0)

theorem nativeLocalStep_measurable (i : I) :
    Measurable (fun p : FrameState (nativeDimension E i) × (NativeRequest E × E i) ↦
      nativeLocalStep E i p.1 p.2.1 p.2.2) := by
  classical
  have hq : Measurable (fun p : FrameState (nativeDimension E i) × (NativeRequest E × E i) ↦
      nativeCoordinateRequest E i p.2.1) :=
    (nativeCoordinateRequest_measurable E i).comp (measurable_fst.comp measurable_snd)
  have hg : Measurable (fun p : FrameState (nativeDimension E i) × (NativeRequest E × E i) ↦
      nativeCoordinates E i p.2.2) :=
    (nativeCoordinates E i).continuous.measurable.comp (measurable_snd.comp measurable_snd)
  have hd := frameSafeStep_measurable.comp (measurable_fst.prodMk (hq.prodMk hg))
  have ha := (measurable_fst.comp hd).prodMk
    ((nativeCoordinates E i).symm.continuous.measurable.comp (measurable_snd.comp hd))
  have hset : MeasurableSet {p : FrameState (nativeDimension E i) × (NativeRequest E × E i) | p.2.1.1 = i} :=
    (nativeRequest_index_measurableSet E i).preimage (measurable_fst.comp measurable_snd)
  unfold nativeLocalStep
  exact Measurable.ite hset ha (measurable_fst.prodMk measurable_const)

def nativeLocalStaticStep (i : I) (s : FrameState (nativeDimension E i)) (q : NativeRequest E)
    (Q : Haar.OrthogonalGroup (nativeDimension E i)) : FrameState (nativeDimension E i) × E i := by
  classical
  exact if q.1 = i then
    let d := frameStaticStep s (nativeCoordinateRequest E i q) Q
    (d.1,(nativeCoordinates E i).symm d.2)
  else (s,0)

theorem nativeLocalStaticStep_measurable (i : I) :
    Measurable (fun p : FrameState (nativeDimension E i) × (NativeRequest E × Haar.OrthogonalGroup (nativeDimension E i)) ↦
      nativeLocalStaticStep E i p.1 p.2.1 p.2.2) := by
  classical
  have hq : Measurable (fun p : FrameState (nativeDimension E i) ×
      (NativeRequest E × Haar.OrthogonalGroup (nativeDimension E i)) ↦ nativeCoordinateRequest E i p.2.1) :=
    (nativeCoordinateRequest_measurable E i).comp (measurable_fst.comp measurable_snd)
  have hd := frameStaticStep_measurable.comp
    (measurable_fst.prodMk (hq.prodMk (measurable_snd.comp measurable_snd)))
  have ha := (measurable_fst.comp hd).prodMk
    ((nativeCoordinates E i).symm.continuous.measurable.comp (measurable_snd.comp hd))
  have hset : MeasurableSet {p : FrameState (nativeDimension E i) ×
      (NativeRequest E × Haar.OrthogonalGroup (nativeDimension E i)) | p.2.1.1 = i} :=
    (nativeRequest_index_measurableSet E i).preimage (measurable_fst.comp measurable_snd)
  unfold nativeLocalStaticStep
  exact Measurable.ite hset ha (measurable_fst.prodMk measurable_const)

def vertexStep (s : VertexFrame (nativeDimension E)) (q : NativeRequest E) (g : NativeReply E) :
    VertexFrame (nativeDimension E) × NativeReply E :=
  (fun i ↦ (nativeLocalStep E i (s i) q (g i)).1,fun i ↦ (nativeLocalStep E i (s i) q (g i)).2)

def vertexStaticStep (s : VertexFrame (nativeDimension E)) (q : NativeRequest E) (Q : NativeOrthogonal E) :
    VertexFrame (nativeDimension E) × NativeReply E :=
  (fun i ↦ (nativeLocalStaticStep E i (s i) q (Q i)).1,fun i ↦ (nativeLocalStaticStep E i (s i) q (Q i)).2)

theorem vertexStep_measurable :
    Measurable (fun p : VertexFrame (nativeDimension E) × (NativeRequest E × NativeReply E) ↦
      vertexStep E p.1 p.2.1 p.2.2) := by
  have hd (i : I) : Measurable (fun p : VertexFrame (nativeDimension E) × (NativeRequest E × NativeReply E) ↦
      nativeLocalStep E i (p.1 i) p.2.1 (p.2.2 i)) := by
    have hm : Measurable (fun p : VertexFrame (nativeDimension E) × (NativeRequest E × NativeReply E) ↦
        (p.1 i,(p.2.1,p.2.2 i))) :=
      (((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))))
    simpa only [Function.comp_def] using (nativeLocalStep_measurable E i).comp hm
  exact (measurable_pi_iff.mpr (fun i ↦ measurable_fst.comp (hd i))).prodMk
    (measurable_pi_iff.mpr (fun i ↦ measurable_snd.comp (hd i)))

theorem vertexStaticStep_measurable :
    Measurable (fun p : VertexFrame (nativeDimension E) × (NativeRequest E × NativeOrthogonal E) ↦
      vertexStaticStep E p.1 p.2.1 p.2.2) := by
  have hd (i : I) : Measurable (fun p : VertexFrame (nativeDimension E) × (NativeRequest E × NativeOrthogonal E) ↦
      nativeLocalStaticStep E i (p.1 i) p.2.1 (p.2.2 i)) := by
    have hm : Measurable (fun p : VertexFrame (nativeDimension E) × (NativeRequest E × NativeOrthogonal E) ↦
        (p.1 i,(p.2.1,p.2.2 i))) :=
      (((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))))
    simpa only [Function.comp_def] using (nativeLocalStaticStep_measurable E i).comp hm
  exact (measurable_pi_iff.mpr (fun i ↦ measurable_fst.comp (hd i))).prodMk
    (measurable_pi_iff.mpr (fun i ↦ measurable_snd.comp (hd i)))

theorem vertexStaticStep_reply (s : VertexFrame (nativeDimension E)) (q : NativeRequest E) (Q : NativeOrthogonal E) :
    (vertexStaticStep E s q Q).2 = nativeRequestAnswer E Q q := by
  classical
  funext i
  simp only [vertexStaticStep,nativeLocalStaticStep,nativeRequestAnswer]
  split_ifs <;> simp only [frameStaticStep_reply]

def vertexStepCompletion (s : VertexFrame (nativeDimension E)) (q : NativeRequest E)
    (p : NativeReply E × VertexFrameTape (nativeDimension E)) :
    (VertexFrame (nativeDimension E) × NativeReply E) × NativeOrthogonal E :=
  (vertexStep E s q p.1,vertexFrameComplete (nativeDimension E) (vertexStep E s q p.1).1 p.2)

attribute [local irreducible] vertexStep vertexStaticStep vertexStepCompletion

theorem vertexStepCompletion_measurable :
    Measurable (fun p : VertexFrame (nativeDimension E) ×
      (NativeRequest E × (NativeReply E × VertexFrameTape (nativeDimension E))) ↦
        vertexStepCompletion E p.1 p.2.1 p.2.2) := by
  have hd : Measurable (fun p : VertexFrame (nativeDimension E) ×
      (NativeRequest E × (NativeReply E × VertexFrameTape (nativeDimension E))) ↦
        vertexStep E p.1 p.2.1 p.2.2.1) := (vertexStep_measurable E).comp (measurable_fst.prodMk
    ((measurable_fst.comp measurable_snd).prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd))))
  have hc := (vertexFrameComplete_measurable (nativeDimension E)).comp
    ((measurable_fst.comp hd).prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  convert hd.prodMk hc using 1
  funext p
  unfold vertexStepCompletion
  rfl

end NCConcave16991.MixedHaar
