import Bilevel.TransportProgramController

/-! Exact adaptive state coupling for the compiled frozen-batch machine.
The only local premise is equality of the full computed reply along the
same actual controller run; geometry-specific modules discharge it on
their measured projection event. No independence of the queries is used. -/
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
  (A : BorelAdaptive.Program S Q O Y)
  (networkQueries : Q → Queries n D p) (hnet : Measurable networkQueries)
  (auxiliaryQueries : Q → Fin B → Space D) (haux : Measurable auxiliaryQueries)
  (networkOutput : Y → Queries n D p) (hno : Measurable networkOutput)
  (auxiliaryOutput : Y → Space D) (hao : Measurable auxiliaryOutput)
  (evaluate : ∀ t,Input Q n D p k T t → O) (heval : ∀ t,Measurable (evaluate t))

def batchReply (t : ℕ)
    (st : NetworkMemory C S k T D × Generators n D (size n p 1 1 t)) (z : Latent n D) : O :=
  evaluate t (A.query st.1.2.2.1,(st.1.2.2.2,
    (st.2,batch (augment st.2 (networkQueries (A.query st.1.2.2.1))) z)))

theorem compiled_round_state (P : TransportAuxiliaryFrame.Schedule k T) (hTnet : Tnet≤D)
    (t : ℕ) (names : Vertex n → Fin 1 → Option (Fin Tnet))
    (st : NetworkMemory C S k T D × Generators n D (size n p 1 1 t)) (z : Latent n D) :
    (round Tnet hTnet
      (networkChoose (controller (Tnet:=Tnet) A networkQueries hnet auxiliaryQueries haux networkOutput hno auxiliaryOutput hao evaluate heval) t)
      (networkRespond P (controller (Tnet:=Tnet) A networkQueries hnet auxiliaryQueries haux networkOutput hno auxiliaryOutput hao evaluate heval) t)
      names st z).1.2.2.1=
      if A.halt st.1.2.2.1 then st.1.2.2.1 else
        A.update (st.1.2.2.1,batchReply A networkQueries evaluate t st z) := rfl

theorem compiled_run_eq_original {I : Type*}
    (P : TransportAuxiliaryFrame.Schedule k T) (hTnet : Tnet≤D)
    (names : ℕ → Vertex n → Fin 1 → Option (Fin Tnet))
    (initial : NetworkMemory C S k T D × Generators n D 1) (z : Latent n D)
    (response : I → Q → Unit → O) (i : I) (N : ℕ)
    (hlocal : ∀ t<N,
      let st := networkRun P
        (controller (Tnet:=Tnet) A networkQueries hnet auxiliaryQueries haux networkOutput hno auxiliaryOutput hao evaluate heval)
        hTnet names initial z t
      A.halt st.1.2.2.1=false →
        batchReply A networkQueries evaluate t st z=response i (A.query st.1.2.2.1) ()) :
    (networkRun P
      (controller (Tnet:=Tnet) A networkQueries hnet auxiliaryQueries haux networkOutput hno auxiliaryOutput hao evaluate heval)
      hTnet names initial z N).1.2.2.1=
        BorelAdaptive.run A response i (fun _ => ()) initial.1.2.2.1 N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have he := ih (fun t ht => hlocal t (by omega))
    rw [BorelAdaptive.run,BorelAdaptive.step,←he]
    change (round (H:=NetworkMemory C S k T D) Tnet hTnet _ _ _ _ _).1.2.2.1=_
    rw [compiled_round_state A networkQueries hnet auxiliaryQueries haux networkOutput hno auxiliaryOutput hao evaluate heval]
    let st := networkRun P
      (controller (Tnet:=Tnet) A networkQueries hnet auxiliaryQueries haux networkOutput hno auxiliaryOutput hao evaluate heval)
      hTnet names initial z N
    change (if A.halt st.1.2.2.1 then st.1.2.2.1 else
      A.update (st.1.2.2.1,batchReply A networkQueries evaluate N st z))=
      (if A.halt st.1.2.2.1 then st.1.2.2.1 else A.update (st.1.2.2.1,response i (A.query st.1.2.2.1) ()))
    by_cases hh : A.halt st.1.2.2.1=true
    · simp only [hh,ite_true]
    · have hf := Bool.eq_false_of_not_eq_true hh
      simp only [hf,Bool.false_eq_true,ite_false]
      exact congrArg (fun o => A.update (st.1.2.2.1,o)) (hlocal N (by omega) hf)

end Bilevel.TransportProgram
