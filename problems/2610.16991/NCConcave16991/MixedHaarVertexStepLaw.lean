import NCConcave16991.MixedHaarVertexLocalLaw
import NCConcave16991.MixedHaarProductLaw

/-! # Actual native Gaussian vertex reveals retain the complete static Haar-family law -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000

attribute [local irreducible] nativeCoordinates frameComplete vertexFrameComplete vertexStep vertexStaticStep

variable {I : Type*} [Fintype I] (E : I → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]

def nativeGaussianFamilyLaw : Measure (NativeReply E) := Measure.pi (fun i ↦ stdGaussian (E i))

instance nativeGaussianFamilyLaw_probability : IsProbabilityMeasure (nativeGaussianFamilyLaw E) := by
  unfold nativeGaussianFamilyLaw
  infer_instance

theorem vertexStep_local_jointLaw (s : VertexFrame (nativeDimension E)) (q : NativeRequest E) :
    ((nativeGaussianFamilyLaw E).prod (vertexFrameTapeLaw (nativeDimension E))).map
        (vertexStepCompletion E s q) =
      (vertexFrameTapeLaw (nativeDimension E)).map (fun z ↦
        (vertexStaticStep E s q (vertexFrameComplete (nativeDimension E) s z),
          vertexFrameComplete (nativeDimension E) s z)) := by
  let τ := fun i ↦ stdGaussian (E i)
  let ν := fun i ↦ frameTapeLaw (nativeDimension E i)
  let f := fun i ↦ nativeLocalStepCompletion E i (s i) q
  let g := fun i (z : FrameTape (nativeDimension E i)) ↦
    (nativeLocalStaticStep E i (s i) q (frameComplete (s i) z),frameComplete (s i) z)
  have hf (i : I) : Measurable (f i) := nativeLocalStepCompletion_fixed_measurable E i (s i) q
  have hg (i : I) : Measurable (g i) := nativeLocalStaticCompletion_fixed_measurable E i (s i) q
  have h := independent_joint_laws τ ν f g hf hg (fun i ↦ nativeLocalStep_local_jointLaw E i (s i) q)
  let regroup := fun p : (∀ i, FrameState (nativeDimension E i) × E i) × NativeOrthogonal E ↦
    ((fun i ↦ (p.1 i).1,fun i ↦ (p.1 i).2),p.2)
  have hreg : Measurable regroup :=
    ((measurable_pi_iff.mpr (fun i ↦ measurable_fst.comp ((measurable_pi_apply i).comp measurable_fst))).prodMk
      (measurable_pi_iff.mpr (fun i ↦ measurable_snd.comp ((measurable_pi_apply i).comp measurable_fst)))).prodMk measurable_snd
  let left := fun p : NativeReply E × VertexFrameTape (nativeDimension E) ↦
    (fun i ↦ (f i (p.1 i,p.2 i)).1,fun i ↦ (f i (p.1 i,p.2 i)).2)
  let right := fun z : VertexFrameTape (nativeDimension E) ↦
    (fun i ↦ (g i (z i)).1,fun i ↦ (g i (z i)).2)
  have hl : Measurable left :=
    (measurable_pi_iff.mpr (fun i ↦ measurable_fst.comp ((hf i).comp
      (((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd))))).prodMk
    (measurable_pi_iff.mpr (fun i ↦ measurable_snd.comp ((hf i).comp
      (((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)))))
  have hr : Measurable right :=
    (measurable_pi_iff.mpr (fun i ↦ measurable_fst.comp ((hg i).comp (measurable_pi_apply i)))).prodMk
      (measurable_pi_iff.mpr (fun i ↦ measurable_snd.comp ((hg i).comp (measurable_pi_apply i))))
  have hh := congrArg (Measure.map regroup) h
  rw [Measure.map_map hreg hl,Measure.map_map hreg hr] at hh
  have hleft : regroup ∘ left = vertexStepCompletion E s q := by
    funext p
    unfold regroup left f nativeLocalStepCompletion vertexStepCompletion vertexStep vertexFrameComplete
    rfl
  have hright : regroup ∘ right = (fun z : VertexFrameTape (nativeDimension E) ↦
      (vertexStaticStep E s q (vertexFrameComplete (nativeDimension E) s z),
        vertexFrameComplete (nativeDimension E) s z)) := by
    funext z
    unfold regroup right g vertexStaticStep vertexFrameComplete
    rfl
  rw [hleft,hright] at hh
  exact hh

/-- Minimal reply/final-matrix law for the arbitrary fixed-program sampler. -/
theorem vertexStep_answer_local_jointLaw (s : VertexFrame (nativeDimension E)) (q : NativeRequest E) :
    ((nativeGaussianFamilyLaw E).prod (vertexFrameTapeLaw (nativeDimension E))).map
        (fun p : NativeReply E × VertexFrameTape (nativeDimension E) ↦
          ((vertexStep E s q p.1).2,
            vertexFrameComplete (nativeDimension E) (vertexStep E s q p.1).1 p.2)) =
      (vertexFrameTapeLaw (nativeDimension E)).map (fun z ↦
        (nativeRequestAnswer E (vertexFrameComplete (nativeDimension E) s z) q,
          vertexFrameComplete (nativeDimension E) s z)) := by
  let output := fun p : (VertexFrame (nativeDimension E) × NativeReply E) × NativeOrthogonal E ↦ (p.1.2,p.2)
  have ho : Measurable output := (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hl : Measurable (vertexStepCompletion E s q) := (vertexStepCompletion_measurable E).comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hc := (vertexFrameComplete_preserving (nativeDimension E) s).measurable
  have hr : Measurable (fun z : VertexFrameTape (nativeDimension E) ↦
      (vertexStaticStep E s q (vertexFrameComplete (nativeDimension E) s z),
        vertexFrameComplete (nativeDimension E) s z)) :=
    ((vertexStaticStep_measurable E).comp (measurable_const.prodMk (measurable_const.prodMk hc))).prodMk hc
  have h := congrArg (Measure.map output) (vertexStep_local_jointLaw E s q)
  rw [Measure.map_map ho hl,Measure.map_map ho hr] at h
  have he : output ∘ vertexStepCompletion E s q = (fun p : NativeReply E × VertexFrameTape (nativeDimension E) ↦
      ((vertexStep E s q p.1).2,vertexFrameComplete (nativeDimension E) (vertexStep E s q p.1).1 p.2)) := by
    funext p
    unfold output vertexStepCompletion
    rfl
  rw [he] at h
  simpa only [Function.comp_def,output,vertexStaticStep_reply] using h

end NCConcave16991.MixedHaar
