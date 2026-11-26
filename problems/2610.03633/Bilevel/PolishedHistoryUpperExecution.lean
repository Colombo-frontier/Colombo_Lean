import Bilevel.PolishedHistoryUpperDenote

/-! The public solver's cost and risk are those of the actual history-kernel
program, transported only through the measurable raw/packed channel. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveGeometry PrimitiveQuery OracleCode Stateful CachedBudgetCalibration CachedParameterChoice
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable {G : Geometry} {μ L ρ Δ R₀ σf σg : ℝ}
variable (I : Instance G μ L ρ Δ R₀ σf σg)

theorem Instance.public_cost_le_denote (ε : ℝ) :
    let Λ := CachedUpper.universalCurvature L μ L L L ρ
    I.cost (publicAlgorithmAt G μ L ρ Δ ε R₀ σf σg I.x₀ I.yinit)≤
      ∫⁻ y,(y.2.2:ℝ≥0∞) ∂(CachedUpper.algorithm I.oracle μ L L L ρ Λ Δ ε R₀ I.x₀ I.yinit).law ((),I.initialHistory) := by
  let Λ := CachedUpper.universalCurvature L μ L L L ρ
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  let m := publicMachineAt G μ L ρ Δ ε R₀ σf σg I.x₀ I.yinit
  let c := CachedOracleCode.selectedAlgorithm (X:=G.X) (Y:=G.Y)
    μ L L L ρ σf σg Λ Δ ε R₀ I.x₀ I.yinit
  let ξ := StochasticOuter.uniformLaw (outerCount Λ Δ ε)
  change (∫⁻ w,HistoryProgram.totalCalls m.program w
    ∂HistoryProgram.trajectoryLaw (BorelAdaptive.channelProgram m.program
      (fun q => pack q.1 q.2) PrimitiveQuery.decode packLinear.continuous.measurable decode_measurable)
      I.historyOracle ξ m.start I.initialHistory)≤_
  rw [I.packed_trajectoryLaw m.program ξ m.start]
  have hc := PolishedCompiledHistory.compiled_stopped_calls_le
    (Q:=of (G.X×G.Y)) (O:=of (FullResponse G.X G.Y))
    (A:=of (Fin (outerCount Λ Δ ε))) (B:=of G.X) (H:=of I.History)
    I.rawOracle (0,0) (0,0) c ξ I.initialHistory
  exact hc.trans_eq (I.denote_selected_calls_integral ε I.initialHistory)

theorem Instance.public_risk_le_denote (ε : ℝ)
    (hcost : (∫⁻ y,(y.2.2:ℝ≥0∞) ∂(CachedUpper.algorithm I.oracle μ L L L ρ
      (CachedUpper.universalCurvature L μ L L L ρ) Δ ε R₀ I.x₀ I.yinit).law ((),I.initialHistory))≠⊤) :
    let Λ := CachedUpper.universalCurvature L μ L L L ρ
    letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
    I.risk (publicAlgorithmAt G μ L ρ Δ ε R₀ σf σg I.x₀ I.yinit)≤
      ∫⁻ z,ENNReal.ofReal (I.loss (CachedUpper.output Λ Δ ε I.x₀ z))
        ∂StochasticOuter.outputLaw (outerCount Λ Δ ε)
          ((CachedUpper.algorithm I.oracle μ L L L ρ Λ Δ ε R₀ I.x₀ I.yinit).law ((),I.initialHistory)) := by
  let Λ := CachedUpper.universalCurvature L μ L L L ρ
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  let m := publicMachineAt G μ L ρ Δ ε R₀ σf σg I.x₀ I.yinit
  let c := CachedOracleCode.selectedAlgorithm (X:=G.X) (Y:=G.Y)
    μ L L L ρ σf σg Λ Δ ε R₀ I.x₀ I.yinit
  let ξ := StochasticOuter.uniformLaw (outerCount Λ Δ ε)
  have hc : (∫⁻ j,∫⁻ y,(y.2.2:ℝ≥0∞)
      ∂(OracleCode.History.denote (H:=of I.History) I.oracle.law I.oracle.update I.oracle.update_measurable c).law
        (j,I.initialHistory) ∂ξ)≠⊤ := by
    rwa [I.denote_selected_calls_integral ε I.initialHistory]
  change (∫⁻ w,ENNReal.ofReal (I.loss (HistoryProgram.stoppedOutput m.program w))
    ∂HistoryProgram.trajectoryLaw (BorelAdaptive.channelProgram m.program
      (fun q => pack q.1 q.2) PrimitiveQuery.decode packLinear.continuous.measurable decode_measurable)
      I.historyOracle ξ m.start I.initialHistory)≤_
  rw [I.packed_trajectoryLaw m.program ξ m.start]
  have hb := PolishedCompiledHistory.compiled_stopped_loss_le
    (Q:=of (G.X×G.Y)) (O:=of (FullResponse G.X G.Y))
    (A:=of (Fin (outerCount Λ Δ ε))) (B:=of G.X) (H:=of I.History)
    I.rawOracle (0,0) (0,0) c ξ I.initialHistory hc I.loss I.loss_measurable
  exact hb.trans_eq (I.denote_selected_loss_integral ε I.initialHistory)

end Bilevel.PolishedHistory
