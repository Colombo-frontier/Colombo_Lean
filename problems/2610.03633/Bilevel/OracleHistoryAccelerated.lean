import Bilevel.OracleHistoryBatch
import Bilevel.OracleCodeAccelerated

/-! Exact history semantics for the existing public accelerated-solver code.
This equality preserves every updated history and original-call count. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.OracleCode.History
open Stateful AcceleratedInner
set_option autoImplicit false
variable {Q O Param H : Space} {E : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (loc : Param × E → Q) (hloc : Measurable loc)
  (shift : Param → E) (hshift : Measurable shift) {σ : ℝ}
  (Z : HistoryOracle (Query:=Q) (History:=H) (Obs:=O) (E:=E) σ)

theorem denote_acceleratedStep (μ M α : ℝ) (B : ℕ) :
    denote Z.law Z.update Z.update_measurable
      (acceleratedStep Z.read Z.read_measurable loc hloc shift hshift μ M α B)=
      ParameterizedStatefulAccelerated.step Z loc hloc shift hshift μ M α B := by
  simp only [acceleratedStep,denote_map,denote,denote_batch (E:=of E) Z,
    ParameterizedStatefulAccelerated.step]

theorem denote_acceleratedRun (μ M α : ℝ) (B n : ℕ) :
    denote Z.law Z.update Z.update_measurable
      (acceleratedRun Z.read Z.read_measurable loc hloc shift hshift μ M α B n)=
      ParameterizedStatefulAccelerated.run Z loc hloc shift hshift μ M α B n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [acceleratedRun,denote,ih,denote_acceleratedStep loc hloc shift hshift Z,
        ParameterizedStatefulAccelerated.run]

theorem denote_acceleratedStages (μ M α U : ℝ) (n : ℕ) :
    denote Z.law Z.update Z.update_measurable
      (acceleratedStages Z.read Z.read_measurable loc hloc shift hshift μ M α σ U n)=
      ParameterizedStatefulAccelerated.stages Z loc hloc shift hshift μ M α U n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [acceleratedStages,denote,ih,denote_acceleratedRun loc hloc shift hshift Z,
        ParameterizedStatefulAccelerated.stages]

theorem denote_acceleratedSolve (μ M α R radius : ℝ) :
    denote Z.law Z.update Z.update_measurable
      (acceleratedSolve Z.read Z.read_measurable loc hloc shift hshift μ M α σ R radius)=
      ParameterizedStatefulAccelerated.solve Z loc hloc shift hshift μ M α R radius := by
  unfold acceleratedSolve ParameterizedStatefulAccelerated.solve
  split_ifs
  · rfl
  · simp only [denote_map,denote,denote_acceleratedStages loc hloc shift hshift Z]

end Bilevel.OracleCode.History
