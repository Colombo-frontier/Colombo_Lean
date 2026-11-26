import NCConcave16991.MixedHaarFrameState
import NCConcave16991.MixedHaarProductLaw

/-! # The actual finite family of public frames and independent completion tape -/

noncomputable section

open MeasureTheory

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] frameComplete tailOrthogonal

variable {I : Type*} [Fintype I] (k : I → ℕ)

abbrev VertexFrame := ∀ i, FrameState (k i)
abbrev VertexFrameTape := ∀ i, FrameTape (k i)
abbrev VertexOrthogonal := ∀ i, Haar.OrthogonalGroup (k i)

def vertexFrameTapeLaw : Measure (VertexFrameTape k) := Measure.pi (fun i ↦ frameTapeLaw (k i))

instance vertexFrameTapeLaw_probability : IsProbabilityMeasure (vertexFrameTapeLaw k) := by
  unfold vertexFrameTapeLaw
  infer_instance

def vertexFrameComplete (s : VertexFrame k) (z : VertexFrameTape k) : VertexOrthogonal k :=
  fun i ↦ frameComplete (s i) (z i)

theorem vertexFrameComplete_measurable :
    Measurable (fun p : VertexFrame k × VertexFrameTape k ↦ vertexFrameComplete k p.1 p.2) := by
  apply measurable_pi_iff.mpr
  intro i
  change Measurable (fun p : VertexFrame k × VertexFrameTape k ↦ frameComplete (p.1 i) (p.2 i))
  have hm : Measurable (fun p : VertexFrame k × VertexFrameTape k ↦ (p.1 i,p.2 i)) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)
  exact (frameComplete_measurable (k := k i)).comp hm

def vertexCompletionLaw (s : VertexFrame k) : Measure (VertexOrthogonal k) :=
  Measure.pi (fun i ↦ (frameTapeLaw (k i)).map (frameComplete (s i)))

instance vertexCompletionLaw_probability (s : VertexFrame k) : IsProbabilityMeasure (vertexCompletionLaw k s) := by
  unfold vertexCompletionLaw
  infer_instance

theorem vertexFrameComplete_preserving (s : VertexFrame k) :
    MeasurePreserving (vertexFrameComplete k s) (vertexFrameTapeLaw k) (vertexCompletionLaw k s) := by
  have hp (i : I) : MeasurePreserving (frameComplete (s i)) (frameTapeLaw (k i))
      ((frameTapeLaw (k i)).map (frameComplete (s i))) := by
    refine ⟨?_,rfl⟩
    exact (frameComplete_measurable (k := k i)).comp (measurable_const.prodMk measurable_id)
  exact measurePreserving_pi _ _ hp

end NCConcave16991.MixedHaar
