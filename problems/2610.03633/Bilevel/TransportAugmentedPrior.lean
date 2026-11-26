import Bilevel.TransportAugmentedReplay

/-! The same original prior has two exact presentations: auxiliary-frame
replay sees the full network as context; network observation sees all
auxiliary orientations as independent initial memory. -/
noncomputable section
open MeasureTheory
universe u v
namespace Bilevel.TransportAugmented
open EuclideanGaussian TransportNetwork TransportRound
set_option autoImplicit false
set_option maxHeartbeats 800000
variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  {n D p Tnet k T B : ℕ}

def initialMemory (hT : T+1 ≤ D) (initial : C → S)
    (q : C × (Fin (k+1) → OrthogonalHaar.Group D)) : NetworkMemory C S (k+1) T D :=
  ((fun i => HaarFrame.frame D (T+1) hT (q.2 i)),
    (q.1,(initial q.1,TransportAuxiliaryFrame.initialStore (k+1) T D)))

theorem initialMemory_measurable (hT : T+1 ≤ D) (initial : C → S) (hi : Measurable initial) :
    Measurable (initialMemory (k:=k) hT initial) := by
  refine Measurable.prodMk ?_ (measurable_fst.prodMk ((hi.comp measurable_fst).prodMk measurable_const))
  apply measurable_pi_lambda
  intro i
  exact (HaarFrame.frame_measurable D (T+1) hT).comp ((measurable_pi_apply i).comp measurable_snd)

def memoryLaw (ρ : Measure C) (hT : T+1 ≤ D) (initial : C → S) :
    Measure (NetworkMemory C S (k+1) T D) :=
  (ρ.prod (Measure.pi (fun _ : Fin (k+1) => OrthogonalHaar.law D))).map (initialMemory hT initial)

def networkView (hT : T+1 ≤ D) (initial : C → S)
    (s : C × TransportNetworkAuxiliary.Sample n D (k+1)) : NetworkMemory C S (k+1) T D × Latent n D :=
  (initialMemory hT initial (s.1,s.2.2),s.2.1)

theorem networkView_preserving (ρ : Measure C) [IsProbabilityMeasure ρ]
    (hT : T+1 ≤ D) (initial : C → S) (hi : Measurable initial) :
    MeasurePreserving (networkView (n:=n) (k:=k) hT initial)
      (ρ.prod (TransportNetworkAuxiliary.law n D (k+1)))
      ((memoryLaw ρ hT initial).prod (TransportNetwork.law n D)) := by
  let ν := Measure.pi (fun _ : Fin (k+1) => OrthogonalHaar.law D)
  have hs := (MeasurePreserving.id ρ).prod
    (Measure.measurePreserving_swap (μ:=TransportNetwork.law n D) (ν:=ν))
  have ha := (measurePreserving_prodAssoc ρ ν (TransportNetwork.law n D)).symm
    (MeasurableEquiv.prodAssoc : (C × (Fin (k+1) → OrthogonalHaar.Group D)) × Latent n D ≃ᵐ
      C × ((Fin (k+1) → OrthogonalHaar.Group D) × Latent n D))
  have hm : MeasurePreserving (initialMemory (k:=k) hT initial) (ρ.prod ν) (memoryLaw ρ hT initial) :=
    ⟨initialMemory_measurable hT initial hi,rfl⟩
  have hh := (hm.prod (MeasurePreserving.id (TransportNetwork.law n D))).comp (ha.comp hs)
  convert hh using 1

def masterRun (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet ≤ D) (hT : T+1 ≤ D)
    (initial : C → S) (s : C × TransportNetworkAuxiliary.Sample n D (k+1)) (N : ℕ) :=
  networkRun P A hTnet (prefixNames n Tnet)
    ((networkView hT initial s).1,seed Tnet hTnet s.2.1) s.2.1 N

def auxiliaryInitial (hTnet : Tnet ≤ D) (initial : C → S) (q : C × Latent n D) :
    S × FlatGenerators n D := (initial q.1,flatten (seed Tnet hTnet q.2))

theorem auxiliaryInitial_measurable (hTnet : Tnet ≤ D) (initial : C → S) (hi : Measurable initial) :
    Measurable (auxiliaryInitial (n:=n) hTnet initial) := by
  exact (hi.comp measurable_fst).prodMk
    ((flatten_measurable n D 1).comp ((seed_measurable Tnet hTnet).comp measurable_snd))

theorem original_auxiliary_eq_master (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet ≤ D) (hT : T+1 ≤ D)
    (initial : C → S) (s : C × TransportNetworkAuxiliary.Sample n D (k+1)) (N : ℕ) :
    TransportAuxiliaryFrame.originalRun P (auxiliaryDriver A hTnet (prefixNames n Tnet)) hT
      (auxiliaryInitial hTnet initial) s N = encode s.2.1 (masterRun P A hTnet hT initial s N) :=
  auxiliary_run_eq_network P A hTnet (prefixNames n Tnet)
    ((networkView hT initial s).1,seed Tnet hTnet s.2.1) s.2.1 N

end Bilevel.TransportAugmented
