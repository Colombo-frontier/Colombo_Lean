import Bilevel.TransportAugmentedJointObserver
import Bilevel.TransportAugmentedBatch
import Bilevel.TransportAugmentedDimension

/-! Each selected auxiliary frame may use its own terminal coordinate.
These policies have identical actual runs; only the final observation
differs. Their events are united on the common original prior. -/
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

def FrameObserved (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet ≤ D) (hT : T+1 ≤ D)
    (hB : 0 < B) (initial : C → S) (M : ℕ) (cap : ℝ)
    (output : Fin (k+1) → CommonState C S (k+1) T D → Space D)
    (ho : ∀ i,Measurable (output i)) (i : Fin (k+1))
    (s : C × TransportNetworkAuxiliary.Sample n D (k+1)) : Prop :=
  TransportAuxiliaryFrame.OriginalObserved P
    (auxiliaryDriver (withAuxiliaryOutput A (output i) (ho i)) hTnet (prefixNames n Tnet))
    hT i hB M (auxiliaryInitial hTnet initial) cap s

theorem frameObserved_measurable (ρ : Measure C) [IsProbabilityMeasure ρ]
    (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet ≤ D) (hT : T+1 ≤ D)
    (hB : 0 < B) (initial : C → S) (hi : Measurable initial) (M : ℕ) (cap : ℝ)
    (output : Fin (k+1) → CommonState C S (k+1) T D → Space D)
    (ho : ∀ i,Measurable (output i)) (i : Fin (k+1)) :
    MeasurableSet {s | FrameObserved P A hTnet hT hB initial M cap output ho i s} :=
  TransportAuxiliaryFrame.originalObserved_measurable ρ P
    (auxiliaryDriver (withAuxiliaryOutput A (output i) (ho i)) hTnet (prefixNames n Tnet))
    hT i hB M (auxiliaryInitial hTnet initial) (auxiliaryInitial_measurable hTnet initial hi) cap

theorem allFrameObserved_failure (ρ : Measure C) [IsProbabilityMeasure ρ]
    (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet ≤ D) (hT : T+1 ≤ D)
    (hB : 0 < B) (initial : C → S) (hi : Measurable initial) (M r : ℕ)
    (output : Fin (k+1) → CommonState C S (k+1) T D → Space D)
    (ho : ∀ i,Measurable (output i)) (e : ℝ) (he : 0 < e) (he2 : e ≤ 2)
    (hD : (2*(M*B)+1)+(M*B)+(r+1) ≤ D)
    (hsmall : ((M*B:ℕ):ℝ)*(((2*(M*B)+1:ℕ):ℝ)*e) ≤ 1/2) :
    (ρ.prod (TransportNetworkAuxiliary.law n D (k+1)))
      {s | ¬∀ i,FrameObserved P A hTnet hT hB initial M (2*((2*(M*B)+1:ℕ):ℝ)*e) output ho i s} ≤
      ((k+1:ℕ):ℝ≥0∞)*(((2*(M*B)+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery (T+1) r e) := by
  classical
  have hp (i : Fin (k+1)) := TransportAuxiliaryFrame.originalObserved_failure ρ P
    (auxiliaryDriver (withAuxiliaryOutput A (output i) (ho i)) hTnet (prefixNames n Tnet))
    hT i hB M r (auxiliaryInitial hTnet initial) (auxiliaryInitial_measurable hTnet initial hi) e he he2 hD hsmall
  have hh := measure_exists_fin_le (ρ.prod (TransportNetworkAuxiliary.law n D (k+1)))
    (fun i s => ¬FrameObserved P A hTnet hT hB initial M (2*((2*(M*B)+1:ℕ):ℝ)*e) output ho i s)
    _ hp
  simpa only [not_forall] using hh

def CompleteGood (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet ≤ D) (hT : T+1 ≤ D)
    (hB : 0 < B) (initial : C → S) (M : ℕ) (networkCap auxiliaryCap : ℝ)
    (output : Fin (k+1) → CommonState C S (k+1) T D → Space D)
    (ho : ∀ i,Measurable (output i)) (s : C × TransportNetworkAuxiliary.Sample n D (k+1)) : Prop :=
  NetworkGood P A hTnet hT initial M networkCap s ∧
    ∀ i,FrameObserved P A hTnet hT hB initial M auxiliaryCap output ho i s

theorem completeGood_measurable (ρ : Measure C) [IsProbabilityMeasure ρ]
    (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet ≤ D) (hT : T+1 ≤ D)
    (hB : 0 < B) (initial : C → S) (hi : Measurable initial) (M : ℕ) (networkCap auxiliaryCap : ℝ)
    (output : Fin (k+1) → CommonState C S (k+1) T D → Space D)
    (ho : ∀ i,Measurable (output i)) :
    MeasurableSet {s | CompleteGood P A hTnet hT hB initial M networkCap auxiliaryCap output ho s} := by
  apply (networkGood_measurable ρ P A hTnet hT initial hi M networkCap).inter
  convert MeasurableSet.iInter (fun i =>
    frameObserved_measurable ρ P A hTnet hT hB initial hi M auxiliaryCap output ho i) using 1
  ext s
  simp only [Set.mem_iInter,Set.mem_setOf_eq]
  rfl

theorem complete_observer (ρ : Measure C) [IsProbabilityMeasure ρ]
    (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet ≤ D) (hT : T+1 ≤ D)
    (hn : 0 < n) (hpos : 0 < Tnet) (hB : 0 < B) (initial : C → S) (hi : Measurable initial)
    (M r : ℕ) (output : Fin (k+1) → CommonState C S (k+1) T D → Space D)
    (ho : ∀ i,Measurable (output i)) {networkCap δ e : ℝ} (hb : 0 < networkCap) (hδ : 0 < δ)
    (hDnet : observerDimension n p Tnet (M+1) networkCap δ ≤ D)
    (he : 0 < e) (he2 : e ≤ 2) (hDaux : (2*(M*B)+1)+(M*B)+(r+1) ≤ D)
    (hsmall : ((M*B:ℕ):ℝ)*(((2*(M*B)+1:ℕ):ℝ)*e) ≤ 1/2) :
    (ρ.prod (TransportNetworkAuxiliary.law n D (k+1)))
      {s | ¬CompleteGood P A hTnet hT hB initial M networkCap (2*((2*(M*B)+1:ℕ):ℝ)*e) output ho s} ≤
      ENNReal.ofReal δ + ((k+1:ℕ):ℝ≥0∞)*
        (((2*(M*B)+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery (T+1) r e) := by
  have hnet := network_failure_original ρ P A hTnet hT hn hpos initial hi M hb hδ hDnet
  have haux := allFrameObserved_failure ρ P A hTnet hT hB initial hi M r output ho e he he2 hDaux hsmall
  have hset : {s : C × TransportNetworkAuxiliary.Sample n D (k+1) |
      ¬CompleteGood P A hTnet hT hB initial M networkCap (2*((2*(M*B)+1:ℕ):ℝ)*e) output ho s} =
      {s | ¬NetworkGood P A hTnet hT initial M networkCap s} ∪
      {s | ¬∀ i,FrameObserved P A hTnet hT hB initial M (2*((2*(M*B)+1:ℕ):ℝ)*e) output ho i s} := by
    ext s
    simp only [CompleteGood,Set.mem_setOf_eq,Set.mem_union,not_and_or]
  rw [hset]
  exact (measure_union_le _ _).trans (add_le_add hnet haux)

theorem selected_output_mem (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet ≤ D) (hT : T+1 ≤ D)
    (i : Fin (k+1)) (hB : 0 < B) (initial : C → S)
    (output : Fin (k+1) → CommonState C S (k+1) T D → Space D)
    (ho : ∀ i,Measurable (output i))
    (s : C × TransportNetworkAuxiliary.Sample n D (k+1)) (M : ℕ) :
    output i (masterRun P A hTnet hT initial s M).1.2 ∈
      TransportAuxiliaryFrame.terminalSpace P
        (auxiliaryDriver (withAuxiliaryOutput A (output i) (ho i)) hTnet (prefixNames n Tnet)) i hB M
        (TransportAuxiliaryFrame.otherColumns hT i (fun l => s.2.2 (i.succAbove l)))
        (TransportAuxiliaryFrame.originalColumns hT s.2)
        (TransportAuxiliaryFrame.originalInitial (auxiliaryInitial hTnet initial) s) :=
  master_auxiliary_output_mem P (withAuxiliaryOutput A (output i) (ho i)) hTnet hT i hB initial s M

end Bilevel.TransportAugmented
