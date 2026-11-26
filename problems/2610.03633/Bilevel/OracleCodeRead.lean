import Bilevel.OracleCode

/-! Reading a component after one full original oracle reply. This adapter
preserves the one-call counter and is independent of the oracle truth. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.OracleCode
open Stateful
variable {Q O E : Space}

def read (r : O → E) (hr : Measurable r) : Code Q O Q E :=
  map .call (fun z => r z.2) (hr.comp measurable_snd)

theorem procedure_ext {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (p q : Procedure A Unit B) (h : p.law=q.law) : p=q := by
  cases p
  cases q
  cases h
  rfl

theorem denote_read_law (K : Kernel Q O) [IsMarkovKernel K]
    (r : O → E) (hr : Measurable r) (q : Q) :
    (denote K (read r hr)).law (q,())=(K q).map (fun o => (r o,(),1)) := by
  rw [read,denote_map,Procedure.map_law]
  change Measure.map (fun z : Outcome O Unit => (r z.1,z.2))
    ((K.comap Prod.fst measurable_fst).map (fun o => (o,(),1)) (q,()))=_
  rw [Kernel.map_apply _ (by fun_prop),Kernel.comap_apply,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]
  [SecondCountableTopology E] {σ : ℝ}

omit [BorelSpace E] [SecondCountableTopology E] in
theorem denote_read_eq (K : Kernel Q O) [IsMarkovKernel K]
    (H : HistoryOracle (Query:=Q) (History:=Unit) (Obs:=O) (E:=E) σ)
    (hK : ∀ q,H.law (q,())=K q) :
    denote K (read H.read H.read_measurable)=H.call := by
  apply procedure_ext
  ext z s hs
  rcases z with ⟨q,u⟩
  cases u
  rw [denote_read_law,HistoryOracle.call_law,hK]

end Bilevel.OracleCode
