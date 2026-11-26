import Bilevel.TransportAugmentedRun
import Bilevel.BorelAdaptiveExecution

/-! Compilation of an arbitrary Borel adaptive program into the literal
frozen-batch transport controller. The program update consumes a full reply
computed from its current query, OLD auxiliary store, OLD network generators,
and this batch's transport answers. Halting is absorbing. -/
noncomputable section
open MeasureTheory
universe u v w x y
namespace Bilevel.TransportProgram
open EuclideanGaussian TransportRound TransportNetwork TransportAugmented
set_option autoImplicit false
set_option maxHeartbeats 900000
variable {C : Type u} {S : Type v} {Q : Type w} {O : Type x} {Y : Type y}
  [MeasurableSpace C] [MeasurableSpace S] [MeasurableSpace Q] [MeasurableSpace O] [MeasurableSpace Y]
  {n D p Tnet k T B : ℕ}

abbrev Input (Q : Type w) (n D p k T t : ℕ) :=
  Q × (TransportAuxiliaryFrame.Store k T D ×
    (Generators n D (size n p 1 1 t) ×
      (Fin (n*(size n p 1 1 t+p)+n*(size n p 1 1 t+p)) → Space D)))

def replyInput (A : BorelAdaptive.Program S Q O Y) (t : ℕ)
    (h : StepData (CommonState C S k T D) n D (size n p 1 1 t) p Tnet × TransportAuxiliaryFrame.Store k T D) :
    Input Q n D p k T t :=
  (A.query h.1.1.1.2.1,(h.1.1.1.2.2,(h.1.1.2,h.1.2.2)))

theorem replyInput_measurable (A : BorelAdaptive.Program S Q O Y) (t : ℕ) :
    Measurable (replyInput (C:=C) (n:=n) (D:=D) (p:=p) (Tnet:=Tnet) (k:=k) (T:=T) A t) := by
  have hst : Measurable (fun h : StepData (CommonState C S k T D) n D (size n p 1 1 t) p Tnet ×
      TransportAuxiliaryFrame.Store k T D => h.1.1.1.2) :=
    measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))
  exact (A.query_measurable.comp (measurable_fst.comp hst)).prodMk
    ((measurable_snd.comp hst).prodMk
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_fst))))

def controller (A : BorelAdaptive.Program S Q O Y)
    (networkQueries : Q → Queries n D p) (hnet : Measurable networkQueries)
    (auxiliaryQueries : Q → Fin B → Space D) (haux : Measurable auxiliaryQueries)
    (networkOutput : Y → Queries n D p) (hno : Measurable networkOutput)
    (auxiliaryOutput : Y → Space D) (hao : Measurable auxiliaryOutput)
    (evaluate : ∀ t,Input Q n D p k T t → O) (heval : ∀ t,Measurable (evaluate t)) :
    Controller C S n D p Tnet k T B where
  choose _ h := networkQueries (A.query h.1.2.1)
  choose_measurable _ := hnet.comp (A.query_measurable.comp
    (measurable_fst.comp (measurable_snd.comp measurable_fst)))
  auxiliaryQueries _ h := auxiliaryQueries (A.query h.1.2.1)
  auxiliaryQueries_measurable _ b := (measurable_pi_apply b).comp (haux.comp
    (A.query_measurable.comp (measurable_fst.comp (measurable_snd.comp measurable_fst))))
  respond t h := if A.halt h.1.1.1.2.1 then h.1.1.1.2.1 else
    A.update (h.1.1.1.2.1,evaluate t (replyInput A t h))
  respond_measurable t := by
    have hs : Measurable (fun h : StepData (CommonState C S k T D) n D (size n p 1 1 t) p Tnet ×
        TransportAuxiliaryFrame.Store k T D => h.1.1.1.2.1) :=
      measurable_fst.comp (measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_fst)))
    exact hs.ite ((A.halt_measurable.comp hs) (measurableSet_singleton true))
      (A.update_measurable.comp (hs.prodMk ((heval t).comp (replyInput_measurable A t))))
  networkOutput h := networkOutput (A.output h.2.1)
  networkOutput_measurable := hno.comp (A.output_measurable.comp (measurable_fst.comp measurable_snd))
  auxiliaryOutput h := auxiliaryOutput (A.output h.2.1)
  auxiliaryOutput_measurable := hao.comp (A.output_measurable.comp (measurable_fst.comp measurable_snd))

end Bilevel.TransportProgram
