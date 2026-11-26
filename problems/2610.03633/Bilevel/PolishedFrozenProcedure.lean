import Bilevel.PolishedFrozenEstimator
import Bilevel.PolishedFrozenEvents
import Bilevel.PolishedFrozenCode
import Bilevel.CachedOracleHistoryOuter

/-! History-dependent denotation of the literal frozen-tilt code. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.PolishedFrozenProcedure
open Stateful PrimitiveGeometry CachedOuterProcedure CachedBudgetCalibration CachedParameterChoice
variable {X Y : Type} {History : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]
  [MeasurableSpace History] {σf σg : ℝ}
  (O : HistorySFO (Query:=X × Y) (History:=History) (X:=X) (Y:=Y) σf σg)

def reuseEstimateStep (μ Lg Cf t D r δ Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) : Procedure (State X Y) History (State X Y) :=
  ((reuseEstimator O μ Lg t D r δ q).reparam
    (fun s : State X Y => (estimatorInput Cf Λ cap x₀ yinit n s,s.2.2.1))
    ((estimatorInput_measurable Cf Λ cap x₀ yinit n).prodMk (by fun_prop))).map
    (fun z => (put z.1.1 n z.2,z.1.2))
    (((put_measurable n).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
      (measurable_snd.comp measurable_fst))

def refreshIteration (μ Lg Cf t D r rA δ η Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) : Procedure (State X Y) History (State X Y) :=
  (CachedOuterProcedure.refreshAt O μ Lg Cf D rA η Λ cap q x₀ yinit n).bind
    ((reuseEstimateStep O μ Lg Cf t D r δ Λ cap q x₀ yinit n).reparam Prod.snd measurable_snd)

def liveIteration (μ Lg Cf t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) : Procedure (State X Y) History (State X Y) :=
  Procedure.choose (fun k => if k=0 then CachedOuterProcedure.estimateStep O μ Lg Cf t D r δ Λ cap q x₀ yinit n
    else refreshIteration O μ Lg Cf t D r rA δ η Λ cap q x₀ yinit n)
    (refreshIndex Λ cap radius x₀ n) (refreshIndex_measurable Λ cap radius x₀ n)

def iteration (μ Lg Cf t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) : Procedure (State X Y) History (State X Y) :=
  Procedure.choose (fun k => if k=0 then Procedure.pure id measurable_id else
    liveIteration O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n)
    (PolishedFrozenCode.liveIndex (Y:=Y) Λ cap x₀ n) (PolishedFrozenCode.liveIndex_measurable (Y:=Y) Λ cap x₀ n)

def run (μ Lg Cf t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) : ℕ → Procedure Unit History (State X Y)
  | 0 => Procedure.pure (fun _ => initialState x₀) measurable_const
  | n+1 => (run μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).bind
      ((iteration O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).reparam Prod.snd measurable_snd)

def algorithm (μ Lf Lg Cf ρ Λ Δ ε R₀ : ℝ) (x₀ : X) (yinit : Y) : Procedure Unit History (State X Y) :=
  let k := Lg/μ
  let E := CachedUpper.bias μ Lg Cf ρ
  let t := tilt E ε
  run O μ Lg Cf t (CachedUpper.initialRadius μ Lg Cf t Λ Δ ε R₀)
    (lowerRadius Lg E ε) (anchorRadius Lf Lg k E ε) (gradientRadius E ε) (upperRadius k ε)
    Λ (energyCap Λ Δ ε) (refreshRadius Λ (anchorSmoothness Lf k) Δ ε)
    (CachedUpper.repetitions Λ Δ ε) x₀ yinit (outerCount Λ Δ ε)

end Bilevel.PolishedFrozenProcedure

namespace Bilevel.PolishedFrozenCode.History
open Stateful PrimitiveGeometry OracleCode CachedOracleCode.History
variable {X Y : Type} {H : OracleCode.Space}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]
  {σf σg : ℝ}
  (O : HistorySFO (Query:=X × Y) (History:=H) (X:=X) (Y:=Y) σf σg)

omit [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem denote_reuseEstimator (μ Lg t D r δ : ℝ) (q : ℕ) [NeZero q] :
    OracleCode.History.denote (H:=H) O.law O.update O.update_measurable
      (reuseEstimator (X:=X) (Y:=Y) μ Lg σg t D r δ q)=
      PolishedFrozenProcedure.reuseEstimator O μ Lg t D r δ q := by
  simp only [reuseEstimator,reuseTranscript,reusePair,reuseFirst,reuseLast,
    CachedOracleCode.tilted,CachedOracleCode.firstGradient,CachedOracleCode.lastGradient,CachedOracleCode.gxMean,
    OracleCode.History.denote_map,OracleCode.History.denote,OracleCode.History.denote_amplify,
    denote_tiltedSolve O,denote_gxBatch O,
    PolishedFrozenProcedure.reuseEstimator,PolishedFrozenProcedure.reuseTranscript,PolishedFrozenProcedure.reusePair,
    PolishedFrozenProcedure.reuseFirst,PolishedFrozenProcedure.reuseLast,
    CachedEstimatorProcedure.tilted,CachedEstimatorProcedure.firstGradient,CachedEstimatorProcedure.lastGradient,
    CachedEstimatorProcedure.gxMean]

omit [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem denote_reuseEstimateStep (μ Lg Cf t D r δ Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) :
    OracleCode.History.denote (H:=H) O.law O.update O.update_measurable
      (reuseEstimateStep μ Lg Cf σg t D r δ Λ cap q x₀ yinit n)=
      PolishedFrozenProcedure.reuseEstimateStep O μ Lg Cf t D r δ Λ cap q x₀ yinit n := by
  simp only [reuseEstimateStep,OracleCode.History.denote_map,OracleCode.History.denote,denote_reuseEstimator O,
    PolishedFrozenProcedure.reuseEstimateStep]

theorem denote_iteration (μ Lg Cf t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) :
    OracleCode.History.denote (H:=H) O.law O.update O.update_measurable
      (iteration μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n)=
      PolishedFrozenProcedure.iteration O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n := by
  simp only [iteration,liveIteration,refreshIteration,OracleCode.History.denote,apply_ite,
    denote_refreshAt O,denote_estimateStep O,denote_reuseEstimateStep O,
    PolishedFrozenProcedure.iteration,PolishedFrozenProcedure.liveIteration,PolishedFrozenProcedure.refreshIteration]

theorem denote_run (μ Lg Cf t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) :
    OracleCode.History.denote (H:=H) O.law O.update O.update_measurable
      (run μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n)=
      PolishedFrozenProcedure.run O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run,OracleCode.History.denote,ih,denote_iteration O,PolishedFrozenProcedure.run]

theorem denote_algorithm (μ Lf Lg Cf ρ Λ Δ ε R₀ : ℝ) (x₀ : X) (yinit : Y) :
    OracleCode.History.denote (H:=H) O.law O.update O.update_measurable
      (algorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit)=
      PolishedFrozenProcedure.algorithm O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit := by
  unfold algorithm PolishedFrozenProcedure.algorithm
  exact denote_run O _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end Bilevel.PolishedFrozenCode.History
