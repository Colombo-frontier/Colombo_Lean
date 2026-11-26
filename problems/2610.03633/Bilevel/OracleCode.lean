import Bilevel.StatefulProcedureLaws
import Bilevel.HistoryOracle
import Bilevel.IndependentStreamTail

/-! A deliberately restricted causal oracle language. Only a genuine full
oracle call introduces randomness. The concrete cached algorithm will be
certified by this syntax, not by asserting that every kernel is realizable. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.OracleCode

structure Space where
  carrier : Type
  measurableSpace : MeasurableSpace carrier

instance : CoeSort Space Type := ⟨Space.carrier⟩
instance (A : Space) : MeasurableSpace A := A.measurableSpace

abbrev of (A : Type) [MeasurableSpace A] : Space := ⟨A,inferInstance⟩
abbrev prod (A B : Space) : Space := of (A × B)

inductive Code (Q O : Space) : Space → Space → Type 1
  | pure {A B : Space} (f : A → B) (hf : Measurable f) : Code Q O A B
  | call : Code Q O Q O
  | bind {A B C : Space} (p : Code Q O A B) (q : Code Q O (prod A B) C) : Code Q O A C
  | reparam {A B I : Space} (p : Code Q O A B) (f : I → A) (hf : Measurable f) : Code Q O I B
  | choose {A B : Space} (p : ℕ → Code Q O A B) (n : A → ℕ) (hn : Measurable n) : Code Q O A B

open Stateful
variable {Q O A B C : Space}

def call (K : Kernel Q O) [IsMarkovKernel K] : Procedure Q Unit O where
  law := (K.comap Prod.fst measurable_fst).map (fun o => (o,(),1))
  markov := Kernel.IsMarkovKernel.map _ (by fun_prop)

def denote (K : Kernel Q O) [IsMarkovKernel K] : {A B : Space} → Code Q O A B → Procedure A Unit B
  | _,_,.pure f hf => Procedure.pure f hf
  | _,_,.call => call K
  | _,_,.bind p q => (denote K p).bind (denote K q)
  | _,_,.reparam p f hf => (denote K p).reparam f hf
  | _,_,.choose p n hn => Procedure.choose (fun i => denote K (p i)) n hn

variable {Seed : Type*} [MeasurableSpace Seed]

def eval (response : Q → Seed → O) : {A B : Space} → Code Q O A B →
    A × IndependentStream.Stream Seed → Outcome B Unit × IndependentStream.Stream Seed
  | _,_,.pure f _,z => ((f z.1,(),0),z.2)
  | _,_,.call,z => ((response z.1 (z.2 0),(),1),IndependentStream.tail z.2)
  | _,_,.bind p q,z =>
      let u := eval response p z
      let v := eval response q ((z.1,u.1.1),u.2)
      (Procedure.combine (u.1,v.1),v.2)
  | _,_,.reparam p f _,z => eval response p (f z.1,z.2)
  | _,_,.choose p n _,z => eval response (p (n z.1)) z

theorem eval_measurable (response : Q → Seed → O)
    (hr : Measurable (Function.uncurry response)) (c : Code Q O A B) :
    Measurable (eval response c) := by
  induction c with
  | pure f hf =>
      exact ((hf.comp measurable_fst).prodMk (measurable_const.prodMk measurable_const)).prodMk measurable_snd
  | call =>
      exact ((hr.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))).prodMk
        (measurable_const.prodMk measurable_const)).prodMk (IndependentStream.tail_measurable.comp measurable_snd)
  | bind p q hp hq =>
      have hv := hq.comp ((measurable_fst.prodMk (measurable_fst.comp (measurable_fst.comp hp))).prodMk
        (measurable_snd.comp hp))
      exact (Procedure.combine_measurable.comp ((measurable_fst.comp hp).prodMk
        (measurable_fst.comp hv))).prodMk (measurable_snd.comp hv)
  | reparam p f hf hp =>
      exact hp.comp ((hf.comp measurable_fst).prodMk measurable_snd)
  | @choose A B p n hn hp =>
      have hm : Measurable (fun z : (A × IndependentStream.Stream Seed) × ℕ =>
          eval response (p z.2) z.1) := measurable_from_prod_countable hp
      exact hm.comp (measurable_id.prodMk (hn.comp measurable_fst))

def map (p : Code Q O A B) (f : (prod A B) → C) (hf : Measurable f) : Code Q O A C :=
  .bind p (.pure f hf)

theorem denote_map (K : Kernel Q O) [IsMarkovKernel K] (p : Code Q O A B)
    (f : (prod A B) → C) (hf : Measurable f) :
    denote K (map p f hf) = (denote K p).map f hf := rfl

end Bilevel.OracleCode
