import NCConcave16991.MixedHaarProgramLaw
import NCConcave16991.MixedHaarVertexStepLaw
import NCConcave16991.MixedHaarVertexInitial

/-! # Actual native finite-vertex Gaussian execution equals static product Haar -/

noncomputable section

open MeasureTheory

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true

variable {I : Type} [Fintype I] (E : I → Type)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
  {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω] {T : ℕ}

def nativeProgramSampler (P : OracleProgram.Fixed (NativeRequest E) (NativeReply E) X Ω T)
    (seed : Ω) : RevealTape (NativeReply E) (VertexFrameTape (nativeDimension E)) T → X × NativeOrthogonal E :=
  programGaussianEval P (vertexStep E) (vertexFrameComplete (nativeDimension E)) seed
    (initialVertexFrame (nativeDimension E))

attribute [local irreducible] vertexStep vertexFrameComplete nativeRequestAnswer nativeCoordinates

theorem nativeProgram_joint_law (P : OracleProgram.Fixed (NativeRequest E) (NativeReply E) X Ω T) (seed : Ω) :
    (revealTapeLaw (nativeGaussianFamilyLaw E) (vertexFrameTapeLaw (nativeDimension E)) T).map
        (nativeProgramSampler E P seed) =
      (vertexHaarLaw (nativeDimension E)).map (fun Q ↦ (OracleProgram.eval P (nativeRequestAnswer E Q) seed,Q)) := by
  have hh := programGaussianEval_joint_law P (vertexStep E) (vertexFrameComplete (nativeDimension E))
    (nativeRequestAnswer E) (nativeGaussianFamilyLaw E) (vertexFrameTapeLaw (nativeDimension E))
    (vertexStep_measurable E) (vertexFrameComplete_measurable (nativeDimension E))
    (nativeRequestAnswer_measurable E) (vertexStep_answer_local_jointLaw E) seed (initialVertexFrame (nativeDimension E))
  have hp := initial_vertexFrameComplete_preserving (nativeDimension E)
  have hg : Measurable (fun Q : NativeOrthogonal E ↦ (OracleProgram.eval P (nativeRequestAnswer E Q) seed,Q)) :=
    ((OracleProgram.eval_joint_measurable P (nativeRequestAnswer E) (nativeRequestAnswer_measurable E)).comp
      (measurable_id.prodMk measurable_const)).prodMk measurable_id
  have hm := Measure.map_map (μ := vertexFrameTapeLaw (nativeDimension E)) hg hp.measurable
  rw [hp.map_eq] at hm
  have he : (fun z ↦ (OracleProgram.eval P (nativeRequestAnswer E
      (vertexFrameComplete (nativeDimension E) (initialVertexFrame (nativeDimension E)) z)) seed,
        vertexFrameComplete (nativeDimension E) (initialVertexFrame (nativeDimension E)) z)) =
      (fun Q : NativeOrthogonal E ↦ (OracleProgram.eval P (nativeRequestAnswer E Q) seed,Q)) ∘
        vertexFrameComplete (nativeDimension E) (initialVertexFrame (nativeDimension E)) := rfl
  rw [he,← hm] at hh
  exact hh

theorem nativeProgram_hidden_preserving (P : OracleProgram.Fixed (NativeRequest E) (NativeReply E) X Ω T) (seed : Ω) :
    MeasurePreserving (fun p ↦ (nativeProgramSampler E P seed p).2)
      (revealTapeLaw (nativeGaussianFamilyLaw E) (vertexFrameTapeLaw (nativeDimension E)) T)
      (vertexHaarLaw (nativeDimension E)) := by
  have hp := programGaussianEval_hidden_preserving P (vertexStep E) (vertexFrameComplete (nativeDimension E))
    (nativeRequestAnswer E) (nativeGaussianFamilyLaw E) (vertexFrameTapeLaw (nativeDimension E))
    (vertexStep_measurable E) (vertexFrameComplete_measurable (nativeDimension E))
    (nativeRequestAnswer_measurable E) (vertexStep_answer_local_jointLaw E) seed (initialVertexFrame (nativeDimension E))
  rw [(initial_vertexFrameComplete_preserving (nativeDimension E)).map_eq] at hp
  exact hp

end NCConcave16991.MixedHaar
