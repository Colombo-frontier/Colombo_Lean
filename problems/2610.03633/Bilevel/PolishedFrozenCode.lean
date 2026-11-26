import Bilevel.CachedOracleCodeAlgorithm

/-! Literal frozen-anchor algorithm control flow: on refresh the computed
untilted lower point is reused by the difference estimator; cap rejection
causes immediate return, represented by pure normalization thereafter. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.PolishedFrozenCode
open Stateful PrimitiveGeometry OracleCode CachedOuterProcedure CachedOracleCode
open CachedBudgetCalibration CachedParameterChoice
variable {X Y : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]

def reusePair (μ Lg σg t D r : ℝ) (q : ℕ) [NeZero q] :
    Flow (X:=X) (Y:=Y) (CachedEstimatorProcedure.Input X Y×Y) (Y×Y) :=
  map (.reparam (tilted μ Lg σg t D r q) Prod.fst measurable_fst)
    (fun z => (z.1.2,z.2)) (by fun_prop)

def reuseFirst (σg δ : ℝ) (q : ℕ) [NeZero q] :
    Flow (X:=X) (Y:=Y) ((CachedEstimatorProcedure.Input X Y×Y)×(Y×Y)) ((Y×Y)×X) :=
  .reparam (firstGradient σg δ q) (fun z => (z.1.1,z.2)) (by fun_prop)

def reuseLast (σg δ : ℝ) (q : ℕ) [NeZero q] :
    Flow (X:=X) (Y:=Y) ((CachedEstimatorProcedure.Input X Y×Y)×((Y×Y)×X))
      (CachedEstimatorProcedure.Transcript X Y) :=
  .reparam (lastGradient σg δ q) (fun z => (z.1.1,z.2)) (by fun_prop)

def reuseTranscript (μ Lg σg t D r δ : ℝ) (q : ℕ) [NeZero q] :
    Flow (X:=X) (Y:=Y) (CachedEstimatorProcedure.Input X Y×Y) (CachedEstimatorProcedure.Transcript X Y) :=
  .bind (.bind (reusePair μ Lg σg t D r q) (reuseFirst σg δ q)) (reuseLast σg δ q)

def reuseEstimator (μ Lg σg t D r δ : ℝ) (q : ℕ) [NeZero q] :
    Flow (X:=X) (Y:=Y) (CachedEstimatorProcedure.Input X Y×Y) X :=
  map (reuseTranscript μ Lg σg t D r δ q)
    (fun z => CachedEstimatorProcedure.estimate t z.1.1 z.2)
    (by unfold CachedEstimatorProcedure.estimate;fun_prop)

def reuseEstimateStep (μ Lg Cf σg t D r δ Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) : Flow (X:=X) (Y:=Y) (State X Y) (State X Y) :=
  map (.reparam (reuseEstimator μ Lg σg t D r δ q)
    (fun s : State X Y => (estimatorInput Cf Λ cap x₀ yinit n s,s.2.2.1))
    ((estimatorInput_measurable Cf Λ cap x₀ yinit n).prodMk (by fun_prop)))
    (fun z => (put z.1.1 n z.2,z.1.2))
    (((put_measurable n).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
      (measurable_snd.comp measurable_fst))

def refreshIteration (μ Lg Cf σf σg t D r rA δ η Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) : Flow (X:=X) (Y:=Y) (State X Y) (State X Y) :=
  .bind (CachedOracleCode.refreshAt μ Lg Cf σf σg D rA η Λ cap q x₀ yinit n)
    (.reparam (reuseEstimateStep μ Lg Cf σg t D r δ Λ cap q x₀ yinit n) Prod.snd measurable_snd)

def liveIteration (μ Lg Cf σf σg t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) : Flow (X:=X) (Y:=Y) (State X Y) (State X Y) :=
  .choose (fun k => if k=0 then CachedOracleCode.estimateStep μ Lg Cf σg t D r δ Λ cap q x₀ yinit n
    else refreshIteration μ Lg Cf σf σg t D r rA δ η Λ cap q x₀ yinit n)
    (refreshIndex Λ cap radius x₀ n) (refreshIndex_measurable Λ cap radius x₀ n)

def liveIndex (Λ cap : ℝ) (x₀ : X) (n : ℕ) (s : State X Y) : ℕ :=
  if (CappedExecution.run Λ cap x₀ s.1 n).stopped then 0 else 1

omit [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [BorelSpace Y] [SecondCountableTopology Y] [MeasurableSpace (Joint X Y)]
  [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem liveIndex_measurable (Λ cap : ℝ) (x₀ : X) (n : ℕ) :
    Measurable (liveIndex (Y:=Y) Λ cap x₀ n) := by
  have hm := (CappedExecution.run_measurable Λ cap x₀ (fun i (s : State X Y) => s.1 i)
    (fun i => (measurable_pi_apply i).comp measurable_fst) n).2.2
  exact measurable_const.ite (hm (measurableSet_singleton true)) measurable_const

def iteration (μ Lg Cf σf σg t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) : Flow (X:=X) (Y:=Y) (State X Y) (State X Y) :=
  .choose (fun k => if k=0 then .pure id measurable_id else
    liveIteration μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n)
    (liveIndex Λ cap x₀ n) (liveIndex_measurable Λ cap x₀ n)

def run (μ Lg Cf σf σg t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) : ℕ → Flow (X:=X) (Y:=Y) Unit (State X Y)
  | 0 => .pure (fun _ => initialState x₀) measurable_const
  | n+1 => .bind (run μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n)
      (.reparam (iteration μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n) Prod.snd measurable_snd)

def algorithm (μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ : ℝ) (x₀ : X) (yinit : Y) :
    Flow (X:=X) (Y:=Y) Unit (State X Y) :=
  let k := Lg/μ
  let E := CachedUpper.bias μ Lg Cf ρ
  let t := tilt E ε
  run μ Lg Cf σf σg t (CachedUpper.initialRadius μ Lg Cf t Λ Δ ε R₀)
    (lowerRadius Lg E ε) (anchorRadius Lf Lg k E ε) (gradientRadius E ε) (upperRadius k ε)
    Λ (energyCap Λ Δ ε) (refreshRadius Λ (anchorSmoothness Lf k) Δ ε)
    (CachedUpper.repetitions Λ Δ ε) x₀ yinit (outerCount Λ Δ ε)

def selectedAlgorithm (μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ : ℝ) (x₀ : X) (yinit : Y) :
    Flow (X:=X) (Y:=Y) (Fin (outerCount Λ Δ ε)) X :=
  OracleCode.map (.reparam (algorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit)
    (fun _ => ()) measurable_const) (CachedOracleCode.selected Λ Δ ε x₀)
    (CachedOracleCode.selected_measurable Λ Δ ε x₀)

end Bilevel.PolishedFrozenCode
