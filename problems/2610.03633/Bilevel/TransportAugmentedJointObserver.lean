import Bilevel.TransportAugmentedNetworkObserver

/-! A simultaneous observer for ONE actual network-plus-auxiliary run,
including every frozen query batch and both arbitrary terminal readouts.
The network and auxiliary events are combined on their original common
prior; neither independence of events nor replay agreement is assumed. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v
namespace Bilevel.TransportAugmented
open EuclideanGaussian TransportNetwork TransportRound
set_option autoImplicit false
set_option maxHeartbeats 800000
variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  {n D p Tnet k T B : ℕ}

def JointGood (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet ≤ D) (hT : T+1 ≤ D)
    (hB : 0 < B) (initial : C → S) (M : ℕ) (networkCap auxiliaryCap : ℝ)
    (s : C × TransportNetworkAuxiliary.Sample n D (k+1)) : Prop :=
  NetworkGood P A hTnet hT initial M networkCap s ∧
    ∀ i,TransportAuxiliaryFrame.OriginalObserved P (auxiliaryDriver A hTnet (prefixNames n Tnet))
      hT i hB M (auxiliaryInitial hTnet initial) auxiliaryCap s

theorem jointGood_measurable (ρ : Measure C) [IsProbabilityMeasure ρ]
    (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet ≤ D) (hT : T+1 ≤ D)
    (hB : 0 < B) (initial : C → S) (hi : Measurable initial) (M : ℕ) (networkCap auxiliaryCap : ℝ) :
    MeasurableSet {s | JointGood P A hTnet hT hB initial M networkCap auxiliaryCap s} :=
  (networkGood_measurable ρ P A hTnet hT initial hi M networkCap).inter
    (TransportAuxiliaryFrame.allObserved_measurable ρ P (auxiliaryDriver A hTnet (prefixNames n Tnet))
      hT hB M (auxiliaryInitial hTnet initial) (auxiliaryInitial_measurable hTnet initial hi) auxiliaryCap)

theorem joint_observer (ρ : Measure C) [IsProbabilityMeasure ρ]
    (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet ≤ D) (hT : T+1 ≤ D)
    (hn : 0 < n) (hpos : 0 < Tnet) (hB : 0 < B) (initial : C → S) (hi : Measurable initial)
    (M r : ℕ) {networkCap δ e : ℝ} (hb : 0 < networkCap) (hδ : 0 < δ)
    (hDnet : observerDimension n p Tnet (M+1) networkCap δ ≤ D)
    (he : 0 < e) (he2 : e ≤ 2) (hDaux : (2*(M*B)+1)+(M*B)+(r+1) ≤ D)
    (hsmall : ((M*B:ℕ):ℝ)*(((2*(M*B)+1:ℕ):ℝ)*e) ≤ 1/2) :
    (ρ.prod (TransportNetworkAuxiliary.law n D (k+1)))
      {s | ¬JointGood P A hTnet hT hB initial M networkCap (2*((2*(M*B)+1:ℕ):ℝ)*e) s} ≤
      ENNReal.ofReal δ + ((k+1:ℕ):ℝ≥0∞)*
        (((2*(M*B)+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery (T+1) r e) := by
  have hnet := network_failure_original ρ P A hTnet hT hn hpos initial hi M hb hδ hDnet
  have haux := TransportAuxiliaryFrame.allObserved_failure ρ P
    (auxiliaryDriver A hTnet (prefixNames n Tnet)) hT hB M r
    (auxiliaryInitial hTnet initial) (auxiliaryInitial_measurable hTnet initial hi) e he he2 hDaux hsmall
  have hset : {s : C × TransportNetworkAuxiliary.Sample n D (k+1) |
      ¬JointGood P A hTnet hT hB initial M networkCap (2*((2*(M*B)+1:ℕ):ℝ)*e) s} =
      {s | ¬NetworkGood P A hTnet hT initial M networkCap s} ∪
      {s | ¬∀ i,TransportAuxiliaryFrame.OriginalObserved P (auxiliaryDriver A hTnet (prefixNames n Tnet))
        hT i hB M (auxiliaryInitial hTnet initial) (2*((2*(M*B)+1:ℕ):ℝ)*e) s} := by
    ext s
    simp only [JointGood,Set.mem_setOf_eq,Set.mem_union,not_and_or]
  rw [hset]
  exact (measure_union_le _ _).trans (add_le_add hnet haux)

theorem master_auxiliary_query_mem (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet ≤ D) (hT : T+1 ≤ D)
    (i : Fin (k+1)) (hB : 0 < B) (initial : C → S)
    (s : C × TransportNetworkAuxiliary.Sample n D (k+1)) (M : ℕ) (b : Fin B) :
    A.auxiliaryQueries M ((masterRun P A hTnet hT initial s M).1.2,
      (masterRun P A hTnet hT initial s M).2) b ∈
      TransportAuxiliaryFrame.preSpace P (auxiliaryDriver A hTnet (prefixNames n Tnet)) i hB M
        (TransportAuxiliaryFrame.otherColumns hT i (fun l => s.2.2 (i.succAbove l)))
        (TransportAuxiliaryFrame.originalColumns hT s.2)
        (TransportAuxiliaryFrame.originalInitial (auxiliaryInitial hTnet initial) s) := by
  have h := TransportAuxiliaryFrame.original_query_mem P (auxiliaryDriver A hTnet (prefixNames n Tnet))
    hT i hB (auxiliaryInitial hTnet initial) s M b
  rw [original_auxiliary_eq_master] at h
  change A.auxiliaryQueries M (prepare M (encode s.2.1 _)) b ∈ _ at h
  rw [prepare_encode] at h
  exact h

theorem master_auxiliary_output_mem (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet ≤ D) (hT : T+1 ≤ D)
    (i : Fin (k+1)) (hB : 0 < B) (initial : C → S)
    (s : C × TransportNetworkAuxiliary.Sample n D (k+1)) (M : ℕ) :
    A.auxiliaryOutput (masterRun P A hTnet hT initial s M).1.2 ∈
      TransportAuxiliaryFrame.terminalSpace P (auxiliaryDriver A hTnet (prefixNames n Tnet)) i hB M
        (TransportAuxiliaryFrame.otherColumns hT i (fun l => s.2.2 (i.succAbove l)))
        (TransportAuxiliaryFrame.originalColumns hT s.2)
        (TransportAuxiliaryFrame.originalInitial (auxiliaryInitial hTnet initial) s) := by
  have h := TransportAuxiliaryFrame.original_output_mem P (auxiliaryDriver A hTnet (prefixNames n Tnet))
    hT i hB (auxiliaryInitial hTnet initial) s M
  rw [original_auxiliary_eq_master] at h
  exact h

end Bilevel.TransportAugmented
