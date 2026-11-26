import Bilevel.TransportAugmentedRun

/-! The auxiliary-frame view of the SAME augmented execution. Its immutable
context contains the complete network. Its mutable state contains only the
algorithm memory and the actual padded finite network generator ledger. -/
noncomputable section
open MeasureTheory
universe u v
namespace Bilevel.TransportAugmented
open EuclideanGaussian TransportNetwork TransportRound
set_option autoImplicit false

variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  {n D p Tnet k T B : ℕ}

abbrev AuxiliaryState (C : Type u) (S : Type v) (n D k T : ℕ) :=
  TransportAuxiliaryFrame.State (C × Latent n D) (S × FlatGenerators n D) k T D

def prepare (t : ℕ) (s : AuxiliaryState C S n D k T) :
    CommonState C S k T D × Generators n D (size n p 1 1 t) :=
  ((s.1.1,(s.2.1.1,s.2.2)),restrict (size n p 1 1 t) s.2.1.2)

theorem prepare_measurable (t : ℕ) :
    Measurable (prepare (C:=C) (S:=S) (n:=n) (D:=D) (p:=p) (k:=k) (T:=T) t) := by
  exact ((measurable_fst.comp measurable_fst).prodMk
    ((measurable_fst.comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))).prodMk
        ((restrict_measurable n D (size n p 1 1 t)).comp
          (measurable_snd.comp (measurable_fst.comp measurable_snd)))

def auxiliaryRespond (A : Controller C S n D p Tnet k T B) (hTnet : Tnet ≤ D)
    (names : ℕ → Vertex n → Fin 1 → Option (Fin Tnet)) (t : ℕ)
    (z : AuxiliaryState C S n D k T × TransportAuxiliaryFrame.Store k T D) : S × FlatGenerators n D :=
  let h := prepare (p:=p) t z.1
  let q := A.choose t h
  let frozen := augment h.2 q
  let y := batch frozen z.1.1.2
  (A.respond t ((h,queryAnswers Tnet hTnet q z.1.1.2,y),z.2),
    flatten (augment (outputs frozen y) (disclosures Tnet hTnet (names t) z.1.1.2)))

theorem auxiliaryRespond_measurable (A : Controller C S n D p Tnet k T B) (hTnet : Tnet ≤ D)
    (names : ℕ → Vertex n → Fin 1 → Option (Fin Tnet)) (t : ℕ) :
    Measurable (auxiliaryRespond A hTnet names t) := by
  let Z := AuxiliaryState C S n D k T × TransportAuxiliaryFrame.Store k T D
  have hs : Measurable (fun z : Z => prepare (p:=p) t z.1) := (prepare_measurable t).comp measurable_fst
  have hn : Measurable (fun z : Z => z.1.1.2) := measurable_snd.comp (measurable_fst.comp measurable_fst)
  have hq := (A.choose_measurable t).comp hs
  have hf := (augment_measurable n D (size n p 1 1 t) p).comp
    ((measurable_snd.comp hs).prodMk hq)
  have hy := (batch_joint_measurable n D (size n p 1 1 t+p)).comp (hf.prodMk hn)
  have ha := (queryAnswers_measurable (p:=p) Tnet hTnet).comp (hq.prodMk hn)
  have hd := (disclosures_measurable Tnet hTnet (names t)).comp hn
  have ho := (outputs_measurable n D (size n p 1 1 t+p)).comp (hf.prodMk hy)
  have hg := (augment_measurable n D
    ((size n p 1 1 t+p)+(n*(size n p 1 1 t+p)+n*(size n p 1 1 t+p))) 1).comp (ho.prodMk hd)
  exact ((A.respond_measurable t).comp ((hs.prodMk (ha.prodMk hy)).prodMk measurable_snd)).prodMk
    ((flatten_measurable n D (size n p 1 1 (t+1))).comp hg)

def auxiliaryDriver (A : Controller C S n D p Tnet k T B) (hTnet : Tnet ≤ D)
    (names : ℕ → Vertex n → Fin 1 → Option (Fin Tnet)) :
    TransportAuxiliaryFrame.Driver (C × Latent n D) (S × FlatGenerators n D) k T D B where
  queries t s := A.auxiliaryQueries t (prepare t s)
  queries_measurable t b := (A.auxiliaryQueries_measurable t b).comp (prepare_measurable t)
  respond := auxiliaryRespond A hTnet names
  respond_measurable := auxiliaryRespond_measurable A hTnet names
  output s := A.auxiliaryOutput (s.1.1,(s.2.1.1,s.2.2))
  output_measurable := A.auxiliaryOutput_measurable.comp
    ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_fst.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd)))

def encode {m : ℕ} (z : Latent n D) (q : NetworkMemory C S k T D × Generators n D m) :
    AuxiliaryState C S n D k T :=
  ((q.1.2.1,z),((q.1.2.2.1,flatten q.2),q.1.2.2.2))

omit [MeasurableSpace C] [MeasurableSpace S] in
theorem prepare_encode (t : ℕ) (z : Latent n D)
    (q : NetworkMemory C S k T D × Generators n D (size n p 1 1 t)) :
    prepare (p:=p) t (encode z q)=(q.1.2,q.2) := by
  simp only [prepare,encode,restrict_flatten]

theorem auxiliary_step_eq_network (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet ≤ D)
    (names : ℕ → Vertex n → Fin 1 → Option (Fin Tnet)) (t : ℕ)
    (z : Latent n D) (q : NetworkMemory C S k T D × Generators n D (size n p 1 1 t)) :
    TransportAuxiliaryFrame.step P (auxiliaryDriver A hTnet names) t (encode z q) q.1.1 =
      encode z (TransportRound.round Tnet hTnet (networkChoose A t) (networkRespond P A t) (names t) q z) := by
  simp only [TransportAuxiliaryFrame.step,auxiliaryDriver,auxiliaryRespond,prepare_encode,
    TransportRound.round,networkChoose,networkRespond,stripData,encode,prepare,restrict_flatten]

end Bilevel.TransportAugmented
