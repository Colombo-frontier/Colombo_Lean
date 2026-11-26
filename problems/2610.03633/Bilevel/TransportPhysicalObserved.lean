import Bilevel.TransportPhysicalExecution
import Bilevel.TransportPhysicalOutput
import Bilevel.TransportAugmentedBudgetProbability

/-! Literal same-prior execution and inclusion of each queried coordinate
in its prebatch analytical space. The common auxiliary space contains all
ordinary lower points before the frozen network answers are returned. -/
noncomputable section
open MeasureTheory
universe u v
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiExtensionCalibration
  EndpointTransportResponse TransportRound TransportNetwork PrimitiveGeometry PartialLegendre
  TransportAugmented ChiExtension ChiHierarchyExecution
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  (macroN J n D s : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0≤D)
  (hA : auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) J+1≤D)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km ν : ℝ) (fine : ChiFine.Parameters)
  (index radialIndex : Fin J → Fin s) (fineIndex : Fin s)
  (ρ R : ℕ → ℝ) (dn : ℝ) (b : Normals s) (m δ c₀ cend : ℝ)
  [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]
  [MeasurableSpace (PhysicalOutput J D)] [BorelSpace (PhysicalOutput J D)]
  [MeasurableSpace (PhysicalQuery J n D s)] [BorelSpace (PhysicalQuery J n D s)]
  (P : BorelAdaptive.Program S (PhysicalQuery J n D s) (PhysicalReply J n D s) (PhysicalOutput J D))
  (start : C → S)


def physicalObserved (τ : ℝ) (N : ℕ)
    (ω : C × PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D) : Prop :=
  let counts := sourceCounts macroN cn ratios resolutions
  let ctl := physicalController (C:=C) macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P
  let cap := sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km τ
  CompleteGoodAny (auxiliaryRoundSchedule counts J (n+1) (Nat.succ_pos n)) (enlargeBatch ctl) hT hA
    (by omega) start N (Real.sqrt cap/EndpointTransportMatrix.gamma n) cap
    (physicalObserverOutput counts P) (physicalObserverOutput_measurable counts P) ω

theorem physicalObserved_measurable (σ : Measure C) [IsProbabilityMeasure σ]
    (hs : Measurable start) (τ : ℝ) (N : ℕ) :
    MeasurableSet {ω | physicalObserved macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start τ N ω} := by
  let counts := sourceCounts macroN cn ratios resolutions
  let ctl := physicalController (C:=C) macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P
  let cap := sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km τ
  have hk : 0<Fintype.card (FrameIndex counts J) := Fintype.card_pos_iff.mpr ⟨Sum.inl ()⟩
  exact completeGoodAny_measurable hk σ
    (auxiliaryRoundSchedule counts J (n+1) (Nat.succ_pos n)) (enlargeBatch ctl) hT hA
    (by omega) start hs N (Real.sqrt cap/EndpointTransportMatrix.gamma n) cap
    (physicalObserverOutput counts P) (physicalObserverOutput_measurable counts P)

theorem physicalObserved_energy (τ : ℝ) (N t : ℕ) (ht : t<N)
    (ω : C × PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D)
    (hobs : physicalObserved macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start τ N ω)
    (i : FrameIndex (sourceCounts macroN cn ratios resolutions) J) :
    let counts := sourceCounts macroN cn ratios resolutions
    let ctl := physicalController (C:=C) macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P
    let st := physicalRun macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start ω t
    GenieProtocol.BoundedEnergy (analyticalAuxSpaceAny ctl t (st.1.2,st.2))
      (prefixSet (retained counts J (t/(n+1)) i))
      (TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity counts J+1) hA (enumerate counts J i) ω.2)
      (sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km τ) := by
  let counts := sourceCounts macroN cn ratios resolutions
  let ctl := physicalController (C:=C) macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P
  let schedule := auxiliaryRoundSchedule counts J (n+1) (Nat.succ_pos n)
  have hk : 0<Fintype.card (FrameIndex counts J) := Fintype.card_pos_iff.mpr ⟨Sum.inl ()⟩
  have hB : 0<Fintype.card (FrameIndex counts J)*(auxiliaryCapacity counts J+1)+(J+1) := by omega
  have h := analyticalAuxSpaceAny_energy hk schedule ctl hT hA (enumerate counts J i) hB start
    (physicalObserverOutput counts P) (physicalObserverOutput_measurable counts P)
    (sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km τ) ω N t ht
    (hobs.2 (enumerate counts J i))
  simpa only [TransportAuxiliaryFrame.knownPrefix,schedule,auxiliaryRoundSchedule_count,prefixSet] using h

theorem physicalObserved_failure (σ : Measure C) [IsProbabilityMeasure σ]
    (hs : Measurable start) (τ η : ℝ) (N : ℕ)
    (hpos : 0<capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0)
    (hcap : 0<sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km τ)
    (hη : 0<η)
    (hbudget : ObserverBudget (n+1) 1 (capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0)
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) J))
      (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) J)
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) J)*
        (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) J+1)+(J+1)) D N
      (Real.sqrt (sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km τ)/EndpointTransportMatrix.gamma n)
      (sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km τ) η) :
    (σ.prod (TransportNetworkAuxiliary.law (n+1) D
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) J))))
      {ω | ¬physicalObserved macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start τ N ω}≤ENNReal.ofReal η := by
  let counts := sourceCounts macroN cn ratios resolutions
  let ctl := physicalController (C:=C) macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P
  have hk : 0<Fintype.card (FrameIndex counts J) := Fintype.card_pos_iff.mpr ⟨Sum.inl ()⟩
  exact complete_observer_of_budget hk σ
    (auxiliaryRoundSchedule counts J (n+1) (Nat.succ_pos n)) (enlargeBatch ctl) hT hA
    (Nat.succ_pos n) hpos (by omega) start hs N
    (physicalObserverOutput counts P) (physicalObserverOutput_measurable counts P)
    (div_pos (Real.sqrt_pos.mpr hcap) (gamma_positive n)) hη hbudget

end Bilevel.TransportHierarchy
