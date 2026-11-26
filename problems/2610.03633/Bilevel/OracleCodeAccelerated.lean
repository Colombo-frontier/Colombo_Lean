import Bilevel.OracleCodeBatch
import Bilevel.ParameterizedStatefulAcceleratedSolver

/-! The actual accelerated batches and finite geometric schedule as causal
oracle syntax. Frozen adaptive parameters remain ordinary program data. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.OracleCode
open Stateful AcceleratedInner
variable {Q O Param : Space} {E : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (r : O → E) (hr : Measurable r)
  (loc : Param × E → Q) (hloc : Measurable loc)
  (shift : Param → E) (hshift : Measurable shift)

def acceleratedStep (μ M α : ℝ) (B : ℕ) :
    Code Q O (of (Param × (E × E))) (of (E × E)) :=
  map (.reparam (batch (E:=of E) r hr B) (ParameterizedStatefulAccelerated.queryAt loc α)
    (ParameterizedStatefulAccelerated.queryAt_measurable loc hloc α))
    (ParameterizedStatefulAccelerated.update shift μ M α)
    (ParameterizedStatefulAccelerated.update_measurable shift hshift μ M α)

def acceleratedRun (μ M α : ℝ) (B : ℕ) : ℕ →
    Code Q O (of (Param × (E × E))) (of (E × E))
  | 0 => .pure Prod.snd measurable_snd
  | n+1 => .bind (acceleratedRun μ M α B n)
      (.reparam (acceleratedStep r hr loc hloc shift hshift μ M α B)
        ParameterizedStatefulAccelerated.continueInput ParameterizedStatefulAccelerated.continueInput_measurable)

def acceleratedStages (μ M α σ U : ℝ) : ℕ →
    Code Q O (of (Param × (E × E))) (of (E × E))
  | 0 => .pure Prod.snd measurable_snd
  | n+1 => .bind (acceleratedStages μ M α σ U n)
      (.reparam (acceleratedRun r hr loc hloc shift hshift μ M α
        (stageBatch M α σ (stageBudget U (n+1))) (stageLength α))
        ParameterizedStatefulAccelerated.continueInput ParameterizedStatefulAccelerated.continueInput_measurable)

def acceleratedSolve (μ M α σ R radius : ℝ) : Code Q O (of (Param × E)) (of E) :=
  if R≤radius then .pure Prod.snd measurable_snd else
    map (.reparam (acceleratedStages r hr loc hloc shift hshift μ M α σ (M*R^2)
      (dyadicStageCount (M*R^2) (μ*radius^2/4)))
      (fun z : Param × E => (z.1,(z.2,z.2))) (by fun_prop))
      (fun z : (Param × E) × (E × E) => z.2.1) (measurable_fst.comp measurable_snd)

variable (K : Kernel Q O) [IsMarkovKernel K] {σ : ℝ}
  (H : HistoryOracle (Query:=Q) (History:=Unit) (Obs:=O) (E:=E) σ)
  (hK : ∀ q,H.law (q,())=K q)

include hK in
theorem denote_acceleratedStep (μ M α : ℝ) (B : ℕ) :
    denote K (acceleratedStep H.read H.read_measurable loc hloc shift hshift μ M α B)=
      ParameterizedStatefulAccelerated.step H loc hloc shift hshift μ M α B := by
  simp only [acceleratedStep,denote_map,denote,denote_batch (E:=of E) K H hK,ParameterizedStatefulAccelerated.step]

include hK in
theorem denote_acceleratedRun (μ M α : ℝ) (B n : ℕ) :
    denote K (acceleratedRun H.read H.read_measurable loc hloc shift hshift μ M α B n)=
      ParameterizedStatefulAccelerated.run H loc hloc shift hshift μ M α B n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [acceleratedRun,denote,ih,denote_acceleratedStep loc hloc shift hshift K H hK,
        ParameterizedStatefulAccelerated.run]

include hK in
theorem denote_acceleratedStages (μ M α U : ℝ) (n : ℕ) :
    denote K (acceleratedStages H.read H.read_measurable loc hloc shift hshift μ M α σ U n)=
      ParameterizedStatefulAccelerated.stages H loc hloc shift hshift μ M α U n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [acceleratedStages,denote,ih,denote_acceleratedRun loc hloc shift hshift K H hK,
        ParameterizedStatefulAccelerated.stages]

include hK in
theorem denote_acceleratedSolve (μ M α R radius : ℝ) :
    denote K (acceleratedSolve H.read H.read_measurable loc hloc shift hshift μ M α σ R radius)=
      ParameterizedStatefulAccelerated.solve H loc hloc shift hshift μ M α R radius := by
  unfold acceleratedSolve ParameterizedStatefulAccelerated.solve
  split_ifs
  · rfl
  · simp only [denote_map,denote,denote_acceleratedStages loc hloc shift hshift K H hK]

end Bilevel.OracleCode
