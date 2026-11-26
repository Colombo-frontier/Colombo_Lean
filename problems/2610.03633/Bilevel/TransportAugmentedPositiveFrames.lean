import Bilevel.TransportAnalyticalAuxiliarySpace

/-! The same augmented observer for any positive number of auxiliary
frames. No cardinal reindexing or change of prior/run is introduced.
Successor elimination is confined to these adapter proofs. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v
namespace Bilevel.TransportAugmented
open EuclideanGaussian TransportNetwork TransportRound ProjectionGeometry
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  {n D p Tnet k T B : ℕ}

def initialMemoryAny (hT : T+1≤D) (initial : C → S)
    (q : C × (Fin k → OrthogonalHaar.Group D)) : NetworkMemory C S k T D :=
  ((fun i => HaarFrame.frame D (T+1) hT (q.2 i)),
    (q.1,(initial q.1,TransportAuxiliaryFrame.initialStore k T D)))

def masterRunAny (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet≤D) (hT : T+1≤D)
    (initial : C → S) (s : C × TransportNetworkAuxiliary.Sample n D k) (N : ℕ) :=
  networkRun P A hTnet (prefixNames n Tnet)
    (initialMemoryAny hT initial (s.1,s.2.2),seed Tnet hTnet s.2.1) s.2.1 N

def NetworkGoodAny (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet≤D) (hT : T+1≤D)
    (initial : C → S) (N : ℕ) (cap : ℝ) (s : C × TransportNetworkAuxiliary.Sample n D k) : Prop :=
  ProjectionGood hTnet (networkChoose A) (networkRespond P A) N cap
    (initialMemoryAny hT initial (s.1,s.2.2)) s.2.1 ∧
  TerminalGood hTnet (networkChoose A) (networkRespond P A) (networkOutput A) N cap
    (initialMemoryAny hT initial (s.1,s.2.2)) s.2.1

def FrameObservedAny (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet≤D) (hT : T+1≤D)
    (hB : 0<B) (initial : C → S) (N : ℕ) (cap : ℝ)
    (output : Fin k → CommonState C S k T D → Space D)
    (ho : ∀ i,Measurable (output i)) (i : Fin k)
    (s : C × TransportNetworkAuxiliary.Sample n D k) : Prop := by
  cases k with
  | zero => exact False
  | succ j => exact FrameObserved P A hTnet hT hB initial N cap output ho i s

def CompleteGoodAny (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet≤D) (hT : T+1≤D)
    (hB : 0<B) (initial : C → S) (N : ℕ) (networkCap auxiliaryCap : ℝ)
    (output : Fin k → CommonState C S k T D → Space D)
    (ho : ∀ i,Measurable (output i)) (s : C × TransportNetworkAuxiliary.Sample n D k) : Prop :=
  NetworkGoodAny P A hTnet hT initial N networkCap s ∧
    ∀ i,FrameObservedAny P A hTnet hT hB initial N auxiliaryCap output ho i s

def analyticalAuxSpaceAny (A : Controller C S n D p Tnet k T B) (t : ℕ)
    (s : CommonState C S k T D × Generators n D (size n p 1 1 t)) :
    Submodule ℝ (Space D) :=
  Submodule.span ℝ (Set.range (fun a : Fin k × Fin (T+1) => (s.1.2.2 a.1).2 a.2)) ⊔
    Submodule.span ℝ (Set.range (A.auxiliaryQueries t s))

theorem masterRunAny_succ (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet≤D) (hT : T+1≤D)
    (initial : C → S) (s : C × TransportNetworkAuxiliary.Sample n D (k+1)) (N : ℕ) :
    masterRunAny P A hTnet hT initial s N=masterRun P A hTnet hT initial s N := rfl

theorem masterRunAny_enlargeBatch (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet≤D) (hT : T+1≤D)
    (initial : C → S) (s : C × TransportNetworkAuxiliary.Sample n D k) (N : ℕ) :
    masterRunAny P (enlargeBatch A) hTnet hT initial s N=masterRunAny P A hTnet hT initial s N := rfl

theorem completeGoodAny_measurable (hk : 0<k) (ρ : Measure C) [IsProbabilityMeasure ρ]
    (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet≤D) (hT : T+1≤D)
    (hB : 0<B) (initial : C → S) (hi : Measurable initial) (N : ℕ) (networkCap auxiliaryCap : ℝ)
    (output : Fin k → CommonState C S k T D → Space D) (ho : ∀ i,Measurable (output i)) :
    MeasurableSet {s | CompleteGoodAny P A hTnet hT hB initial N networkCap auxiliaryCap output ho s} := by
  cases k with
  | zero => omega
  | succ j => exact completeGood_measurable ρ P A hTnet hT hB initial hi N networkCap auxiliaryCap output ho

theorem complete_observer_any (hk : 0<k) (ρ : Measure C) [IsProbabilityMeasure ρ]
    (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet≤D) (hT : T+1≤D)
    (hn : 0<n) (hpos : 0<Tnet) (hB : 0<B) (initial : C → S) (hi : Measurable initial)
    (N r : ℕ) (output : Fin k → CommonState C S k T D → Space D) (ho : ∀ i,Measurable (output i))
    {networkCap δ e : ℝ} (hb : 0<networkCap) (hδ : 0<δ)
    (hDnet : observerDimension n p Tnet (N+1) networkCap δ≤D)
    (he : 0<e) (he2 : e≤2) (hDaux : (2*(N*B)+1)+(N*B)+(r+1)≤D)
    (hsmall : ((N*B:ℕ):ℝ)*(((2*(N*B)+1:ℕ):ℝ)*e)≤1/2) :
    (ρ.prod (TransportNetworkAuxiliary.law n D k))
      {s | ¬CompleteGoodAny P A hTnet hT hB initial N networkCap (2*((2*(N*B)+1:ℕ):ℝ)*e) output ho s}≤
      ENNReal.ofReal δ+(k:ℝ≥0∞)*(((2*(N*B)+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery (T+1) r e) := by
  cases k with
  | zero => omega
  | succ j => exact complete_observer ρ P A hTnet hT hn hpos hB initial hi N r output ho hb hδ hDnet he he2 hDaux hsmall

theorem analyticalAuxSpaceAny_retained (A : Controller C S n D p Tnet k T B) (t : ℕ)
    (s : CommonState C S k T D × Generators n D (size n p 1 1 t)) (j : Fin k) (col : Fin (T+1)) :
    (s.1.2.2 j).2 col∈analyticalAuxSpaceAny A t s :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨(j,col),rfl⟩)

theorem analyticalAuxSpaceAny_query (A : Controller C S n D p Tnet k T B) (t : ℕ)
    (s : CommonState C S k T D × Generators n D (size n p 1 1 t)) (b : Fin B) :
    A.auxiliaryQueries t s b∈analyticalAuxSpaceAny A t s :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨b,rfl⟩)

theorem analyticalAuxSpaceAny_projection (hk : 0<k) (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet≤D) (hT : T+1≤D)
    (i : Fin k) (hB : 0<k*(T+1)+B) (initial : C → S)
    (output : Fin k → CommonState C S k T D → Space D) (ho : ∀ i,Measurable (output i)) (cap : ℝ)
    (s : C × TransportNetworkAuxiliary.Sample n D k) (N t : ℕ) (ht : t<N)
    (h : FrameObservedAny P (enlargeBatch A) hTnet hT hB initial N cap output ho i s)
    (col : Fin (T+1)) (hc : P.count t i≤col.val) :
    ‖(analyticalAuxSpaceAny A t ((masterRunAny P A hTnet hT initial s t).1.2,
      (masterRunAny P A hTnet hT initial s t).2)).orthogonalProjection
        (TransportNetworkAuxiliary.auxiliaryFrame (T+1) hT i s.2 col)‖≤Real.sqrt cap := by
  cases k with
  | zero => omega
  | succ j => exact analyticalAuxSpace_projection P A hTnet hT i hB initial output ho cap s N t ht h col hc

end Bilevel.TransportAugmented
