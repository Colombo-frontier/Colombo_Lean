import Bilevel.OracleCodeRead
import Bilevel.StatefulBatch

/-! The concrete history-kernel batches expressed using only full oracle
calls and measurable deterministic arithmetic. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.OracleCode
open Stateful
variable {Q O E : Space}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [BorelSpace E] [SecondCountableTopology E]

def sumStep (r : O → E) (hr : Measurable r) : Code Q O (prod Q E) E :=
  map (.reparam (read r hr) Prod.fst measurable_fst)
    (fun z => z.1.2-(-1:ℝ) • z.2) (by fun_prop)

def sum (r : O → E) (hr : Measurable r) : ℕ → Code Q O Q E
  | 0 => .pure (fun _ => 0) measurable_const
  | n+1 => .bind (sum r hr n) (sumStep r hr)

def batch (r : O → E) (hr : Measurable r) (n : ℕ) : Code Q O Q E :=
  map (sum r hr n) (fun z => (n:ℝ)⁻¹ • z.2) (by fun_prop)

variable (K : Kernel Q O) [IsMarkovKernel K] {σ : ℝ}
  (H : HistoryOracle (Query:=Q) (History:=Unit) (Obs:=O) (E:=E) σ)
  (hK : ∀ q,H.law (q,())=K q)

include hK in
theorem denote_sumStep : denote K (sumStep H.read H.read_measurable)=H.sumStep := by
  simp only [sumStep,denote_map,denote,denote_read_eq K H hK,HistoryOracle.sumStep,HistoryOracle.step]

include hK in
theorem denote_sum (n : ℕ) : denote K (sum H.read H.read_measurable n)=H.sum n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sum,denote,ih,denote_sumStep K H hK,HistoryOracle.sum]

include hK in
theorem denote_batch (n : ℕ) : denote K (batch H.read H.read_measurable n)=H.batch n := by
  simp only [batch,denote_map,denote_sum K H hK,HistoryOracle.batch]

end Bilevel.OracleCode
