import NCConcave16991.BranchOracleRequestMeasurable

/-! # The standard Borel structures of the literal finite branch products -/

namespace NCConcave16991.BranchOracle
noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 5000
set_option maxSynthPendingDepth 32

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (M m : ℕ)

theorem macroJoint_borelSpace : BorelSpace (GlobalHard.Joint (MacroSpaces (ι := ι) E M m)) := inferInstance

theorem macroSources_borelSpace : BorelSpace (SourceParameters (MacroSpaces (ι := ι) E M m)) := inferInstance

theorem macroActions_borelSpace : BorelSpace (GlobalActionCoordinates (MacroSpaces (ι := ι) E M m)) := inferInstance

end
end NCConcave16991.BranchOracle
