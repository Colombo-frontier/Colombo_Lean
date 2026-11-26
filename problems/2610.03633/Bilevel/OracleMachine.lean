import Bilevel.OracleCode
import Bilevel.BorelAdaptiveRunShift
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-! Concrete Borel oracle machines for the causal constructors. Pure
computation is normalized between original calls, including at bind boundaries.
There are no dummy queries on branches which perform no oracle calls. -/
noncomputable section
open MeasureTheory
namespace Bilevel.OracleCode
open BorelAdaptive
variable {Q O A B C : Space}

structure Machine (Q O A B : Space) where
  state : Space
  start : A → state
  start_measurable : Measurable start
  program : Program state Q O B

namespace Machine

def pure (q₀ : Q) (f : A → B) (hf : Measurable f) : Machine Q O A B where
  state := A
  start := id
  start_measurable := measurable_id
  program := {
    query := fun _ => q₀
    query_measurable := measurable_const
    update := Prod.fst
    update_measurable := measurable_fst
    halt := fun _ => true
    halt_measurable := measurable_const
    output := f
    output_measurable := hf }

def call (o₀ : O) : Machine Q O Q O where
  state := of (Q × Bool × O)
  start := fun q => (q,false,o₀)
  start_measurable := measurable_id.prodMk (measurable_const.prodMk measurable_const)
  program := {
    query := Prod.fst
    query_measurable := measurable_fst
    update := fun z => (z.1.1,true,z.2)
    update_measurable := (measurable_fst.comp measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd)
    halt := fun z => z.2.1
    halt_measurable := measurable_fst.comp measurable_snd
    output := fun z => z.2.2
    output_measurable := measurable_snd.comp measurable_snd }

def reparam (p : Machine Q O A B) {I : Space} (f : I → A) (hf : Measurable f) :
    Machine Q O I B where
  state := p.state
  start := p.start ∘ f
  start_measurable := p.start_measurable.comp hf
  program := p.program

abbrev BindState (p : Machine Q O A B) (q : Machine Q O (prod A B) C) :=
  (A × p.state) ⊕ q.state

def enter (p : Machine Q O A B) (q : Machine Q O (prod A B) C)
    (z : A × p.state) : BindState p q :=
  if p.program.halt z.2 then Sum.inr (q.start (z.1,p.program.output z.2)) else Sum.inl z

theorem enter_measurable (p : Machine Q O A B) (q : Machine Q O (prod A B) C) :
    Measurable (enter p q) := by
  have hs : MeasurableSet {z : A × p.state | p.program.halt z.2=true} :=
    (p.program.halt_measurable.comp measurable_snd) (measurableSet_singleton true)
  exact (measurable_inr.comp (q.start_measurable.comp
    (measurable_fst.prodMk (p.program.output_measurable.comp measurable_snd)))).ite hs measurable_inl

def bindUpdate (p : Machine Q O A B) (q : Machine Q O (prod A B) C) :
    BindState p q × O → BindState p q := fun z =>
  match z.1 with
  | Sum.inl u => enter p q (u.1,p.program.update (u.2,z.2))
  | Sum.inr v => Sum.inr (q.program.update (v,z.2))

theorem bindUpdate_measurable (p : Machine Q O A B) (q : Machine Q O (prod A B) C) :
    Measurable (bindUpdate p q) := by
  have hl : Measurable (fun z : (A × p.state) × O =>
      enter p q (z.1.1,p.program.update (z.1.2,z.2))) :=
    (enter_measurable p q).comp ((measurable_fst.comp measurable_fst).prodMk
      (p.program.update_measurable.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  have hr : Measurable (fun z : q.state × O => Sum.inr (q.program.update z) :
      q.state × O → BindState p q) := measurable_inr.comp q.program.update_measurable
  convert (hl.sumElim hr).comp (MeasurableEquiv.sumProdDistrib (A × p.state) q.state O).measurable using 1
  funext z
  rcases z with ⟨u,o⟩
  cases u <;> rfl

def bind (p : Machine Q O A B) (q : Machine Q O (prod A B) C) : Machine Q O A C where
  state := of (BindState p q)
  start := fun a => enter p q (a,p.start a)
  start_measurable := (enter_measurable p q).comp (measurable_id.prodMk p.start_measurable)
  program := {
    query := Sum.elim (fun z => p.program.query z.2) q.program.query
    query_measurable := (p.program.query_measurable.comp measurable_snd).sumElim q.program.query_measurable
    update := bindUpdate p q
    update_measurable := bindUpdate_measurable p q
    halt := Sum.elim (fun _ => false) q.program.halt
    halt_measurable := measurable_const.sumElim q.program.halt_measurable
    output := Sum.elim (fun z => q.program.output (q.start (z.1,p.program.output z.2))) q.program.output
    output_measurable := (q.program.output_measurable.comp (q.start_measurable.comp
      (measurable_fst.prodMk (p.program.output_measurable.comp measurable_snd)))).sumElim q.program.output_measurable }

end Machine
end Bilevel.OracleCode
