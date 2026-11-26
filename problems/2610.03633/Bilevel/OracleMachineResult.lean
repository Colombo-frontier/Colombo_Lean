import Bilevel.OracleMachineRun
import Bilevel.OracleCodeLaw
import Bilevel.BorelAdaptiveExtendedCalls

/-! A pathwise compiler certificate identifies the actual stopped Borel
output and original call count with the previously verified kernel law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.OracleCode.Machine
open Stateful BorelAdaptive
variable {Q O A B : Space} {Seed : Type}
  (m : Machine Q O A B) (c : Code Q O A B) (hc : Correct m c)
  (response : Q → Seed → O) (a : A) (s : ℕ → Seed)

include hc in
theorem terminated : Terminated m.program (fun _ : Unit => response) ((),m.start a,s) :=
  ⟨(eval response c (a,s)).1.2.2,(hc Seed response s a).1⟩

include hc in
theorem stopTime_eq : stopTime m.program (fun _ : Unit => response) ((),m.start a,s)=
    (eval response c (a,s)).1.2.2 := by
  let sample : Sample Unit m.state Seed := ((),m.start a,s)
  have ht : Terminated m.program (fun _ : Unit => response) sample := terminated m c hc response a s
  have h := hc Seed response s a
  apply Nat.le_antisymm
  · rw [stopTime,dif_pos ht]
    exact Nat.find_min' ht h.1
  · by_contra hn
    have hlt := Nat.lt_of_not_ge hn
    have hn' := h.2.1 _ hlt
    have hh := stopTime_halted m.program (fun _ : Unit => response) sample ht
    exact Bool.noConfusion (hn'.symm.trans hh)

include hc in
theorem stoppedOutput_eq : stoppedOutput m.program (fun _ : Unit => response) ((),m.start a,s)=
    (eval response c (a,s)).1.1 := by
  rw [stoppedOutput,cappedOutput,stopTime_eq m c hc response a s]
  exact (hc Seed response s a).2.2

include hc in
theorem totalCalls_eq : totalCalls m.program (fun _ : Unit => response) ((),m.start a,s)=
    ((eval response c (a,s)).1.2.2:ℝ≥0∞) := by
  rw [totalCalls,if_pos (terminated m c hc response a s),stopTime_eq m c hc response a s]

def result : Outcome B Unit :=
  (stoppedOutput m.program (fun _ : Unit => response) ((),m.start a,s),(),
    stopTime m.program (fun _ : Unit => response) ((),m.start a,s))

include hc in
theorem result_eq : result m response a s=(eval response c (a,s)).1 := by
  rw [result,stoppedOutput_eq m c hc response a s,stopTime_eq m c hc response a s]

variable [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
  (hr : Measurable (Function.uncurry response)) (K : Kernel Q O) [IsMarkovKernel K]
  (hK : ∀ q,K q=ν.map (response q))

include hc hr hK in
theorem result_law : (IndependentStream.law ν).map (result m response a)=
    (denote K c).law (a,()) := by
  have h := congrArg (Measure.map Prod.fst) (eval_law ν response hr K hK c a)
  have hm : Measurable (fun s => eval response c (a,s)) :=
    (eval_measurable response hr c).comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_map measurable_fst hm,Measure.map_fst_prod] at h
  simpa only [Function.comp_def,measure_univ,one_smul,← result_eq m c hc response a] using h

end Bilevel.OracleCode.Machine
