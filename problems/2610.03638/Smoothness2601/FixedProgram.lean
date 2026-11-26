import Smoothness2601.AdaptiveModel
import Bilevel.StatefulProcedureLaws
import Mathlib.Probability.Kernel.Composition.CompMap

/-! Public finite oracle programs. The program contains neither a Population,
an Oracle, nor a hidden-history type. Its state and all instructions are
measurable public data. Oracle interpretation is a separate operation. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open Bilevel.Stateful Bilevel.PrimitiveGeometry
namespace Smoothness2601.FixedProgram

structure Program (Query Reply Param Out : Type) [MeasurableSpace Query]
    [MeasurableSpace Reply] [MeasurableSpace Param] [MeasurableSpace Out] where
  State : Type
  [stateMeasurable : MeasurableSpace State]
  horizon : ℕ
  init : Param → State
  init_measurable : Measurable init
  query : ℕ → State → Query
  query_measurable : ∀ k, Measurable (query k)
  update : ℕ → State × Reply → State
  update_measurable : ∀ k, Measurable (update k)
  output : State → Out
  output_measurable : Measurable output

attribute [instance] Program.stateMeasurable

namespace Program
variable {Query Reply Param Out Next : Type}
  [MeasurableSpace Query] [MeasurableSpace Reply] [MeasurableSpace Param]
  [MeasurableSpace Out] [MeasurableSpace Next]

def pure (fallback : Query) (f : Param → Out) (hf : Measurable f) :
    Program Query Reply Param Out where
  State := Out
  horizon := 0
  init := f
  init_measurable := hf
  query := fun _ _ => fallback
  query_measurable := fun _ => measurable_const
  update := fun _ z => z.1
  update_measurable := fun _ => measurable_fst
  output := id
  output_measurable := measurable_id

def call (initialReply : Reply) (q : Param → Query) (hq : Measurable q) :
    Program Query Reply Param Reply where
  State := Param × Reply
  horizon := 1
  init := fun p => (p,initialReply)
  init_measurable := measurable_id.prodMk measurable_const
  query := fun _ s => q s.1
  query_measurable := fun _ => hq.comp measurable_fst
  update := fun _ z => (z.1.1,z.2)
  update_measurable := fun _ => (measurable_fst.comp measurable_fst).prodMk measurable_snd
  output := Prod.snd
  output_measurable := measurable_snd

def map (P : Program Query Reply Param Out) (f : Out → Next) (hf : Measurable f) :
    Program Query Reply Param Next where
  State := P.State
  horizon := P.horizon
  init := P.init
  init_measurable := P.init_measurable
  query := P.query
  query_measurable := P.query_measurable
  update := P.update
  update_measurable := P.update_measurable
  output := f ∘ P.output
  output_measurable := hf.comp P.output_measurable

def reparam {Input : Type} [MeasurableSpace Input]
    (P : Program Query Reply Param Out) (f : Input → Param) (hf : Measurable f) :
    Program Query Reply Input Out where
  State := P.State
  horizon := P.horizon
  init := P.init ∘ f
  init_measurable := P.init_measurable.comp hf
  query := P.query
  query_measurable := P.query_measurable
  update := P.update
  update_measurable := P.update_measurable
  output := P.output
  output_measurable := P.output_measurable

/-- Both components are public programs. The continuation is initd from
the first output, including when either component has zero calls. -/
def bind (P : Program Query Reply Param Out) (Q : Program Query Reply (Param × Out) Next) :
    Program Query Reply Param Next where
  State := Param × P.State × Q.State
  horizon := P.horizon + Q.horizon
  init := fun p => (p,P.init p,Q.init (p,P.output (P.init p)))
  init_measurable := measurable_id.prodMk
    (P.init_measurable.prodMk (Q.init_measurable.comp
      (measurable_id.prodMk (P.output_measurable.comp P.init_measurable))))
  query := fun k s => if k < P.horizon then P.query k s.2.1
    else Q.query (k-P.horizon) s.2.2
  query_measurable := by
    intro k
    split_ifs
    · exact (P.query_measurable k).comp (measurable_fst.comp measurable_snd)
    · exact (Q.query_measurable _).comp (measurable_snd.comp measurable_snd)
  update := fun k z => if k < P.horizon then
      let t := P.update k (z.1.2.1,z.2)
      (z.1.1,t,Q.init (z.1.1,P.output t))
    else (z.1.1,z.1.2.1,Q.update (k-P.horizon) (z.1.2.2,z.2))
  update_measurable := by
    intro k
    split_ifs
    · exact (measurable_fst.comp measurable_fst).prodMk
        (((P.update_measurable k).comp
          ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)).prodMk
        (Q.init_measurable.comp ((measurable_fst.comp measurable_fst).prodMk
          (P.output_measurable.comp ((P.update_measurable k).comp
            ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd))))))
    · exact (measurable_fst.comp measurable_fst).prodMk
        ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
          ((Q.update_measurable _).comp
            ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)))
  output := fun s => Q.output s.2.2
  output_measurable := Q.output_measurable.comp (measurable_snd.comp measurable_snd)

def loop (P : Program Query Reply Param Param) (fallback : Query) : ℕ → Program Query Reply Param Param
  | 0 => pure fallback id measurable_id
  | n+1 => (loop P fallback n).bind (P.reparam Prod.snd measurable_snd)

theorem loop_horizon (P : Program Query Reply Param Param) (fallback : Query) (n : ℕ) :
    (P.loop fallback n).horizon = n * P.horizon := by
  induction n with
  | zero => simp only [loop, pure, Nat.zero_mul]
  | succ n ih => simpa only [loop, bind, reparam, Nat.succ_mul] using congrArg (· + P.horizon) ih

variable {History : Type} [MeasurableSpace History]
  (P : Program Query Reply Param Out)

def stepInput (k : ℕ) (s : P.State × History) : Query × History := (P.query k s.1,s.2)
theorem stepInput_measurable (k : ℕ) : Measurable (P.stepInput (History := History) k) :=
  ((P.query_measurable k).comp measurable_fst).prodMk measurable_snd

def stepFinish (k : ℕ) (z : (P.State × History) × (Reply × History)) : P.State × History :=
  (P.update k (z.1.1,z.2.1),z.2.2)
theorem stepFinish_measurable (k : ℕ) : Measurable (P.stepFinish (History := History) k) :=
  ((P.update_measurable k).comp
    ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))).prodMk
    (measurable_snd.comp measurable_snd)

def step (K : Kernel (Query × History) (Reply × History)) (k : ℕ) :
    Kernel (P.State × History) (P.State × History) :=
  KernelMap.dependent (K.comap (P.stepInput k) (P.stepInput_measurable k))
    (P.stepFinish k)

instance step_markov (K : Kernel (Query × History) (Reply × History)) [IsMarkovKernel K] (k : ℕ) :
    IsMarkovKernel (P.step K k) := KernelMap.dependent_markov _ _ (P.stepFinish_measurable k)

def execution (K : Kernel (Query × History) (Reply × History)) :
    ℕ → Kernel (P.State × History) (P.State × History)
  | 0 => Kernel.id
  | n+1 => P.step K n ∘ₖ execution K n

instance execution_markov (K : Kernel (Query × History) (Reply × History)) [IsMarkovKernel K]
    (n : ℕ) : IsMarkovKernel (P.execution K n) := by
  induction n with
  | zero => change IsMarkovKernel Kernel.id; infer_instance
  | succ n ih =>
    letI := ih
    change IsMarkovKernel (P.step K n ∘ₖ P.execution K n)
    infer_instance

def initHistory (z : Param × History) : P.State × History := (P.init z.1,z.2)
theorem initHistory_measurable : Measurable (P.initHistory (History := History)) :=
  (P.init_measurable.comp measurable_fst).prodMk measurable_snd

def record (s : P.State × History) : Outcome Out History := (P.output s.1,s.2,P.horizon)
theorem record_measurable : Measurable (P.record (History := History)) :=
  (P.output_measurable.comp measurable_fst).prodMk (measurable_snd.prodMk measurable_const)

def interpret (K : Kernel (Query × History) (Reply × History)) [IsMarkovKernel K] :
    Procedure Param History Out where
  law := ((P.execution K P.horizon).comap P.initHistory P.initHistory_measurable).map P.record
  markov := Kernel.IsMarkovKernel.map _ P.record_measurable

theorem interpret_calls (K : Kernel (Query × History) (Reply × History)) [IsMarkovKernel K] :
    (P.interpret K).CallsEq (fun _ => P.horizon) := by
  intro p h
  rw [interpret, Kernel.map_apply _ P.record_measurable]
  apply (ae_map_iff P.record_measurable.aemeasurable
    ((measurable_snd.comp measurable_snd) (measurableSet_singleton P.horizon))).mpr
  exact Filter.Eventually.of_forall (fun _ => rfl)

end Program

section Compile
variable {X Y : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

/-- Compilation is independent of population and oracle. -/
def compile (P : Program (Adaptive.Query X Y) (Joint X Y) (X × Y) X) : Adaptive.Algorithm X Y where
  Memory := P.State
  initialLaw := Kernel.deterministic P.init P.init_measurable
  initialMarkov := inferInstance
  query := P.query
  query_measurable := P.query_measurable
  update := P.update
  update_measurable := P.update_measurable
  output := P.output
  output_measurable := P.output_measurable

variable {b : Budgets} {population : Population (X := X) (Y := Y) b}
  {History : Type} [MeasurableSpace History]
  (P : Program (Adaptive.Query X Y) (Joint X Y) (X × Y) X)
  (O : Adaptive.Oracle population History)

omit [BorelSpace X] [SecondCountableTopology X] [BorelSpace Y] [SecondCountableTopology Y] in
theorem compile_execution (n : ℕ) :
    Adaptive.execution (compile P) O n = P.execution O.law n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Adaptive.step (compile P) O n ∘ₖ Adaptive.execution (compile P) O n =
      P.step O.law n ∘ₖ P.execution O.law n
    rw [ih]
    rfl

omit [BorelSpace X] [SecondCountableTopology X] [BorelSpace Y] [SecondCountableTopology Y] in
/-- Semantic compiler correctness: the actual Adaptive output law equals the
public program interpreter's output marginal, for every valid oracle/history. -/
theorem compile_output (h : History) (input : X × Y) :
    Adaptive.outputKernel (compile P) O P.horizon h input =
      ((P.interpret O.law).law (input,h)).map Prod.fst := by
  have hi : Adaptive.initialState (compile P) h input = Measure.dirac (P.init input,h) := by
    have hm : Measurable (fun s : P.State => (s,h)) := measurable_id.prodMk measurable_const
    change ((Kernel.deterministic P.init P.init_measurable).map (fun s : P.State => (s,h))) input = _
    rw [Kernel.map_apply _ hm]
    change (Measure.dirac (P.init input)).map (fun s => (s,h)) = _
    rw [Measure.map_dirac hm]
  have hmout : Measurable (fun s : P.State × History => P.output s.1) :=
    P.output_measurable.comp measurable_fst
  unfold Adaptive.outputKernel
  change ((Adaptive.execution (compile P) O P.horizon ∘ₖ Adaptive.initialState (compile P) h).map
    (fun s : P.State × History => P.output s.1)) input = _
  rw [Kernel.map_apply _ hmout]
  erw [Kernel.comp_apply (Adaptive.execution (compile P) O P.horizon)
      (Adaptive.initialState (compile P) h) input,
    hi, Measure.dirac_bind (Adaptive.execution (compile P) O P.horizon).measurable,
    compile_execution]
  rw [Program.interpret, Kernel.map_apply _ P.record_measurable, Kernel.comap_apply,
    Measure.map_map measurable_fst P.record_measurable]
  rfl

end Compile
end Smoothness2601.FixedProgram
