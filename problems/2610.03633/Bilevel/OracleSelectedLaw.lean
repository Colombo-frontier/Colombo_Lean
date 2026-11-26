import Bilevel.OracleCompiler

/-! An independent private output index can be added to a causal oracle
program without changing its calls. The law below concerns its actual
stopped output and actual stopping time. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.OracleCode
open Stateful
variable {Q O I B C : Space}

def selectedCode (c : Code Q O (of Unit) B) (f : prod I B → C) (hf : Measurable f) :
    Code Q O I C := map (.reparam c (fun _ => ()) measurable_const) f hf

def selectedOutcome (f : prod I B → C) (z : I × Outcome B Unit) : Outcome C Unit :=
  (f (z.1,z.2.1),(),z.2.2.2)

theorem selectedOutcome_measurable (f : prod I B → C) (hf : Measurable f) :
    Measurable (selectedOutcome f) :=
  (hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
    (measurable_const.prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd)))

variable {Seed : Type} [MeasurableSpace Seed]
  (response : Q → Seed → O) (q₀ : Q) (o₀ : O)
  (c : Code Q O (of Unit) B) (f : prod I B → C) (hf : Measurable f)

omit [MeasurableSpace Seed] in
theorem selected_result (i : I) (s : IndependentStream.Stream Seed) :
    Machine.result (compile q₀ o₀ (selectedCode c f hf)) response i s=
      selectedOutcome f (i,Machine.result (compile q₀ o₀ c) response () s) := by
  rw [Machine.result_eq _ _ (compile_correct q₀ o₀ _),
    Machine.result_eq _ _ (compile_correct q₀ o₀ _)]
  simp only [selectedCode,map,eval,Procedure.combine,selectedOutcome,Nat.add_zero]

theorem compiled_result_measurable
    (hr : Measurable (Function.uncurry response)) (a : Unit) :
    Measurable (Machine.result (compile q₀ o₀ c) response a) := by
  have he : Machine.result (compile q₀ o₀ c) response a=
      fun s => (eval response c (a,s)).1 := by
    funext s
    exact Machine.result_eq _ _ (compile_correct q₀ o₀ c) response a s
  rw [he]
  exact measurable_fst.comp ((eval_measurable response hr c).comp
    (measurable_const.prodMk measurable_id))

theorem selected_law (ξ : Measure I) [IsProbabilityMeasure ξ]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hr : Measurable (Function.uncurry response)) (K : Kernel Q O) [IsMarkovKernel K]
    (hK : ∀ q,K q=ν.map (response q)) :
    (ξ.prod (IndependentStream.law ν)).map
      (fun z => Machine.result (compile q₀ o₀ (selectedCode c f hf)) response z.1 z.2)=
    (ξ.prod ((denote K c).law ((),()))).map (selectedOutcome f) := by
  have hm := compiled_result_measurable response q₀ o₀ c hr ()
  have hp := Measure.map_prod_map ξ (IndependentStream.law ν) measurable_id hm
  rw [Measure.map_id,compiled_law ν response hr K hK q₀ o₀ c ()] at hp
  have hh := congrArg (Measure.map (selectedOutcome f)) hp
  rw [Measure.map_map (selectedOutcome_measurable f hf) (measurable_id.prodMap hm)] at hh
  simpa only [Function.comp_def,Prod.map,selected_result response q₀ o₀ c f hf] using hh.symm

end Bilevel.OracleCode
