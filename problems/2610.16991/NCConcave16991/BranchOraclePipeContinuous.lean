import NCConcave16991.BranchOraclePipe

/-! # Joint continuity of the explicit matrix-action pipe renderer -/

namespace NCConcave16991.BranchOracle
noncomputable section
open PipeSmoothness
open scoped BigOperators InnerProductSpace

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {N : ℕ} (V : Fin (N + 1) → Type*)
  [∀ k, NormedAddCommGroup (V k)] [∀ k, InnerProductSpace ℝ (V k)] [∀ k, CompleteSpace (V k)]

abbrev PipeActionCoordinates := (∀ t : Fin N, V t.succ) × (∀ t : Fin N, V t.castSucc)

def coordinateData (a : PipeActionCoordinates V) : PipeActionData V := ⟨a.1, a.2⟩

theorem renderPipeValue_continuous (d r μ : ℝ) :
    Continuous (fun q : PipeSmoothness.Joint V × PipeActionCoordinates V ↦
      renderPipeValue (ι := ι) V d r μ q.1 (coordinateData V q.2)) := by
  apply Continuous.add
  · exact ((pipePublicBilinear (ι := ι) V d r μ).continuous.clm_apply continuous_id).comp continuous_fst
  · apply continuous_finset_sum
    intro t _
    exact ((wProj (V := V) t.succ).continuous.comp continuous_fst).inner ((continuous_apply t).comp continuous_snd.fst)

theorem renderPipeDerivative_continuous (d r μ : ℝ) :
    Continuous (fun q : PipeSmoothness.Joint V × PipeActionCoordinates V ↦
      renderPipeDerivative (ι := ι) V d r μ q.1 (coordinateData V q.2)) := by
  apply Continuous.add
  · exact ((pipePublicBilinear (ι := ι) V d r μ).continuous.comp continuous_fst).add
      ((pipePublicBilinear (ι := ι) V d r μ).flip.continuous.comp continuous_fst)
  · apply continuous_finset_sum
    intro t _
    exact (((innerSL ℝ).continuous.comp ((continuous_apply t).comp continuous_snd.snd)).clm_comp continuous_const).add
      (((innerSL ℝ).continuous.comp ((continuous_apply t).comp continuous_snd.fst)).clm_comp continuous_const)

theorem renderPipeGradient_continuous (d r μ : ℝ) :
    Continuous (fun q : PipeSmoothness.Joint V × PipeActionCoordinates V ↦
      renderPipeGradient (ι := ι) V d r μ q.1 (coordinateData V q.2)) :=
  (InnerProductSpace.toDual ℝ (PipeSmoothness.Joint V)).symm.continuous.comp (renderPipeDerivative_continuous V d r μ)

end
end NCConcave16991.BranchOracle
