import Bilevel.TransportAugmentedStore
import Bilevel.TransportAuxiliaryFrameActual
import Bilevel.TransportRoundTerminal

/-! One actual augmented transport execution. The network controller may
keep full auxiliary orientations as independent initial context, but its
queries and algorithm update use only the concrete old/new prefix stores. -/
noncomputable section
open MeasureTheory
universe u v
namespace Bilevel.TransportAugmented
open EuclideanGaussian TransportNetwork TransportRound
set_option autoImplicit false

abbrev CommonState (C : Type u) (S : Type v) (k T D : ℕ) :=
  TransportAuxiliaryFrame.State C S k T D

abbrev NetworkMemory (C : Type u) (S : Type v) (k T D : ℕ) :=
  TransportAuxiliaryFrame.Columns k T D × CommonState C S k T D

structure Controller (C : Type u) (S : Type v) [MeasurableSpace C] [MeasurableSpace S]
    (n D p Tnet k T B : ℕ) where
  choose : ∀ t, CommonState C S k T D × Generators n D (TransportRound.size n p 1 1 t) →
    TransportRound.Queries n D p
  choose_measurable : ∀ t, Measurable (choose t)
  auxiliaryQueries : ∀ t, CommonState C S k T D × Generators n D (TransportRound.size n p 1 1 t) →
    Fin B → Space D
  auxiliaryQueries_measurable : ∀ t b, Measurable (fun h => auxiliaryQueries t h b)
  respond : ∀ t, TransportRound.StepData (CommonState C S k T D) n D
    (TransportRound.size n p 1 1 t) p Tnet × TransportAuxiliaryFrame.Store k T D → S
  respond_measurable : ∀ t, Measurable (respond t)
  networkOutput : CommonState C S k T D → TransportRound.Queries n D p
  networkOutput_measurable : Measurable networkOutput
  auxiliaryOutput : CommonState C S k T D → Space D
  auxiliaryOutput_measurable : Measurable auxiliaryOutput

variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  {n D p Tnet k T B : ℕ}

def networkChoose (A : Controller C S n D p Tnet k T B) (t : ℕ)
    (h : NetworkMemory C S k T D × Generators n D (TransportRound.size n p 1 1 t)) :=
  A.choose t (h.1.2,h.2)

theorem networkChoose_measurable (A : Controller C S n D p Tnet k T B) (t : ℕ) :
    Measurable (networkChoose A t) :=
  (A.choose_measurable t).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

def stripData (t : ℕ) (h : TransportRound.StepData (NetworkMemory C S k T D) n D
    (TransportRound.size n p 1 1 t) p Tnet) :
    TransportRound.StepData (CommonState C S k T D) n D (TransportRound.size n p 1 1 t) p Tnet :=
  ((h.1.1.2,h.1.2),h.2)

def networkRespond (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (t : ℕ)
    (h : TransportRound.StepData (NetworkMemory C S k T D) n D
      (TransportRound.size n p 1 1 t) p Tnet) : NetworkMemory C S k T D :=
  let next := TransportAuxiliaryFrame.advance P t h.1.1.2.2.2
    (TransportAuxiliaryFrame.replies P t h.1.1.1)
  (h.1.1.1,(h.1.1.2.1,(A.respond t (stripData t h,next),next)))

theorem networkRespond_measurable (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (t : ℕ) : Measurable (networkRespond P A t) := by
  let Z := TransportRound.StepData (NetworkMemory C S k T D) n D (TransportRound.size n p 1 1 t) p Tnet
  have hm : Measurable (fun h : Z => h.1.1) := measurable_fst.comp measurable_fst
  have hU : Measurable (fun h : Z => h.1.1.1) := measurable_fst.comp hm
  have hs : Measurable (fun h : Z => h.1.1.2) := measurable_snd.comp hm
  have hd : Measurable (stripData (C:=C) (S:=S) (n:=n) (D:=D) (p:=p) (Tnet:=Tnet) (k:=k) (T:=T) t) :=
    (hs.prodMk (measurable_snd.comp measurable_fst)).prodMk measurable_snd
  have hn := (TransportAuxiliaryFrame.advance_measurable P t).comp
    ((measurable_snd.comp (measurable_snd.comp hs)).prodMk
      ((TransportAuxiliaryFrame.replies_measurable P t).comp hU))
  exact hU.prodMk ((measurable_fst.comp hs).prodMk
    (((A.respond_measurable t).comp (hd.prodMk hn)).prodMk hn))

def networkOutput (A : Controller C S n D p Tnet k T B) (h : NetworkMemory C S k T D) :=
  A.networkOutput h.2

theorem networkOutput_measurable (A : Controller C S n D p Tnet k T B) :
    Measurable (networkOutput A) := A.networkOutput_measurable.comp measurable_snd

def networkRun (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet ≤ D)
    (names : ℕ → Vertex n → Fin 1 → Option (Fin Tnet))
    (initial : NetworkMemory C S k T D × Generators n D 1) (z : Latent n D) (N : ℕ) :=
  TransportRound.run Tnet hTnet (networkChoose A) (networkRespond P A) names initial z N

theorem networkRun_measurable (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet ≤ D)
    (names : ℕ → Vertex n → Fin 1 → Option (Fin Tnet)) (N : ℕ) :
    Measurable (fun q : (NetworkMemory C S k T D × Generators n D 1) × Latent n D =>
      networkRun P A hTnet names q.1 q.2 N) :=
  TransportRound.run_measurable Tnet hTnet (networkChoose A) (networkChoose_measurable A)
    (networkRespond P A) (networkRespond_measurable P A) names N

end Bilevel.TransportAugmented
