import NCConcave16991.MixedHaarVertexFrame
import NCConcave16991.MixedHaarFrameInitial

/-! # Initial independent vertex completions are the genuine static Haar family -/

noncomputable section

open MeasureTheory

namespace NCConcave16991.MixedHaar

variable {I : Type*} [Fintype I] (k : I → ℕ)

def initialVertexFrame : VertexFrame k := fun i ↦ initialFrameState (k i)
def vertexHaarLaw : Measure (VertexOrthogonal k) := Measure.pi (fun i ↦ Haar.haarLaw (k i))

instance vertexHaarLaw_probability : IsProbabilityMeasure (vertexHaarLaw k) := by
  unfold vertexHaarLaw
  infer_instance

theorem initial_vertexFrameComplete_preserving :
    MeasurePreserving (vertexFrameComplete k (initialVertexFrame k)) (vertexFrameTapeLaw k) (vertexHaarLaw k) :=
  measurePreserving_pi _ _ (fun i ↦ initial_frameComplete_preserving (k i))

end NCConcave16991.MixedHaar
