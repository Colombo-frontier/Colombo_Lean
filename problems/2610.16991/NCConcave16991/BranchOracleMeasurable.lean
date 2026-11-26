import NCConcave16991.BranchOracleContinuity
import NCConcave16991.BranchOraclePipeContinuous

/-! # The complete explicit first-jet renderer is jointly measurable -/

namespace NCConcave16991.BranchOracle
noncomputable section
open GlobalHard
open scoped BigOperators InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {M N : ℕ} (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)]

abbrev GlobalActionCoordinates := ∀ j, PipeActionCoordinates (V j)
abbrev RendererInput := (SourceParameters V × GlobalHard.Joint V) × GlobalActionCoordinates V

def coordinateArray (a : GlobalActionCoordinates V) : ∀ j, PipeActionData (V j) := fun j ↦ coordinateData (V j) (a j)

def pipePartValue (d r μ : ℝ) (q : GlobalHard.Joint V × GlobalActionCoordinates V) : ℝ :=
  ∑ j, renderPipeValue (ι := ι) (V j) d r μ (pipeProj V j q.1) (coordinateData (V j) (q.2 j))

def pipePartDerivative (d r μ : ℝ) (q : GlobalHard.Joint V × GlobalActionCoordinates V) : GlobalHard.Joint V →L[ℝ] ℝ :=
  ∑ j, (renderPipeDerivative (ι := ι) (V j) d r μ (pipeProj V j q.1) (coordinateData (V j) (q.2 j))).comp (pipeProj V j)

theorem pipePartValue_continuous (d r μ : ℝ) : Continuous (pipePartValue (ι := ι) V d r μ) := by
  apply continuous_finset_sum
  intro j _
  have hq : Continuous (fun q : GlobalHard.Joint V × GlobalActionCoordinates V ↦ (pipeProj V j q.1, q.2 j)) :=
    ((pipeProj V j).continuous.comp continuous_fst).prodMk ((continuous_apply j).comp continuous_snd)
  convert (renderPipeValue_continuous (ι := ι) (V j) d r μ).comp hq using 1 <;> rfl

theorem pipePartDerivative_continuous (d r μ : ℝ) : Continuous (pipePartDerivative (ι := ι) V d r μ) := by
  apply continuous_finset_sum
  intro j _
  have hq : Continuous (fun q : GlobalHard.Joint V × GlobalActionCoordinates V ↦ (pipeProj V j q.1, q.2 j)) :=
    ((pipeProj V j).continuous.comp continuous_fst).prodMk ((continuous_apply j).comp continuous_snd)
  exact ((renderPipeDerivative_continuous (ι := ι) (V j) d r μ).comp hq).clm_comp continuous_const

def renderEncodedValue (d r μ : ℝ) (q : RendererInput V) : ℝ :=
  renderComponentValue (ι := ι) V q.1.1.1 q.1.1.2 d r μ q.1.2 (coordinateArray V q.2)

def renderEncodedGradient (d r μ : ℝ) (q : RendererInput V) : GlobalHard.Joint V :=
  renderComponentGradient (ι := ι) V q.1.1.1 q.1.1.2 d r μ q.1.2 (coordinateArray V q.2)

variable [∀ j k, FiniteDimensional ℝ (V j k)]
  [LocallyCompactSpace (GlobalHard.Joint V)]
  [MeasurableSpace (SourceParameters V)] [OpensMeasurableSpace (SourceParameters V)]
  [MeasurableSpace (GlobalHard.Joint V)] [BorelSpace (GlobalHard.Joint V)]
  [MeasurableSpace (GlobalActionCoordinates V)] [OpensMeasurableSpace (GlobalActionCoordinates V)]

theorem renderEncodedValue_measurable (d r μ : ℝ) : Measurable (renderEncodedValue (ι := ι) V d r μ) := by
  have hq : Continuous (fun q : RendererInput V ↦ (q.1.2, q.2)) := continuous_fst.snd.prodMk continuous_snd
  have hp := ((pipePartValue_continuous (ι := ι) V d r μ).comp hq).measurable
  have ho := ((outerPublic_joint_continuous V).comp (continuous_fst : Continuous (fun q : RendererInput V ↦ q.1))).measurable
  exact hp.add ho

theorem renderEncodedDerivative_measurable (d r μ : ℝ) :
    Measurable (fun q : RendererInput V ↦
      renderComponentDerivative (ι := ι) V q.1.1.1 q.1.1.2 d r μ q.1.2 (coordinateArray V q.2)) := by
  have hq : Continuous (fun q : RendererInput V ↦ (q.1.2, q.2)) := continuous_fst.snd.prodMk continuous_snd
  have hp := ((pipePartDerivative_continuous (ι := ι) V d r μ).comp hq).measurable
  have ho := (outerPublic_fderiv_measurable V).comp (measurable_fst : Measurable (fun q : RendererInput V ↦ q.1))
  exact hp.add ho

theorem renderEncodedGradient_measurable (d r μ : ℝ) : Measurable (renderEncodedGradient (ι := ι) V d r μ) :=
  (InnerProductSpace.toDual ℝ (GlobalHard.Joint V)).symm.continuous.measurable.comp
    (renderEncodedDerivative_measurable V d r μ)

theorem renderEncodedFirstJet_measurable (d r μ : ℝ) :
    Measurable (fun q : RendererInput V ↦
      (renderEncodedValue (ι := ι) V d r μ q, renderEncodedGradient (ι := ι) V d r μ q)) :=
  (renderEncodedValue_measurable V d r μ).prodMk (renderEncodedGradient_measurable V d r μ)

end
end NCConcave16991.BranchOracle
