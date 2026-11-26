import Bilevel.OracleCodeHistory
import Bilevel.OracleCodeBatch

/-! Batch syntax has exactly the history-threaded original-call semantics.
The history and its update remain hidden from the public code. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.OracleCode.History
open Stateful
set_option autoImplicit false
variable {Q O E H : Space}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [BorelSpace E] [SecondCountableTopology E] {σ : ℝ}
  (Z : HistoryOracle (Query:=Q) (History:=H) (Obs:=O) (E:=E) σ)

theorem denote_sumStep :
    denote Z.law Z.update Z.update_measurable (sumStep Z.read Z.read_measurable)=Z.sumStep := by
  simp only [sumStep,denote_map,denote,denote_read_eq Z,HistoryOracle.sumStep,HistoryOracle.step]

theorem denote_sum (n : ℕ) :
    denote Z.law Z.update Z.update_measurable (sum Z.read Z.read_measurable n)=Z.sum n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sum,denote,ih,denote_sumStep Z,HistoryOracle.sum]

theorem denote_batch (n : ℕ) :
    denote Z.law Z.update Z.update_measurable (batch Z.read Z.read_measurable n)=Z.batch n := by
  simp only [batch,denote_map,denote_sum Z,HistoryOracle.batch]

end Bilevel.OracleCode.History
