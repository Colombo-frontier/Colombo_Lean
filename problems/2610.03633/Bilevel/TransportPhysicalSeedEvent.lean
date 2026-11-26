import Bilevel.TransportPhysicalObserved
import Bilevel.TransportPhysicalBudget
import Bilevel.BorelAdaptivePrior
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


def physicalSeedGood (τ : ℝ) (N : ℕ)
    (z : BorelAdaptive.Sample (PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D) C Unit) : Prop :=
  physicalObserved macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P (fun q : C × (ℕ → Unit) => start q.1) τ N (z.2,z.1)

theorem physicalSeedGood_measurable (σ : Measure (C × (ℕ → Unit))) [IsProbabilityMeasure σ]
    (hs : Measurable start) (τ : ℝ) (N : ℕ) :
    MeasurableSet {z | physicalSeedGood macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start τ N z} :=
  (measurable_snd.prodMk measurable_fst)
    (physicalObserved_measurable macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P (fun q : C × (ℕ → Unit) => start q.1) σ
      (hs.comp measurable_fst) τ N)

theorem physicalSeedGood_failure (σ : Measure (C × (ℕ → Unit))) [IsProbabilityMeasure σ]
    (hs : Measurable start) (τ β : ℝ) (hβ : 0<β)
    (hc : 0<sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km τ) (N : ℕ)
    (hbudget : physicalBudget macroN J n D cn ratios resolutions initial weight CR ζ Km τ β N) :
    ((TransportNetworkAuxiliary.law (n+1) D
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) J))).prod σ)
      {z | ¬physicalSeedGood macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start τ N z}≤ENNReal.ofReal β := by
  letI : IsProbabilityMeasure (TransportNetworkAuxiliary.law (n+1) D
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) J))) :=
    TransportNetworkAuxiliary.probability _ _ _
  letI : IsFiniteMeasure (TransportNetworkAuxiliary.law (n+1) D
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) J))) := inferInstance
  letI : SigmaFinite (TransportNetworkAuxiliary.law (n+1) D
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) J))) :=
    IsFiniteMeasure.toSigmaFinite _
  letI : SFinite (TransportNetworkAuxiliary.law (n+1) D
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) J))) := inferInstance
  have hm := (physicalObserved_measurable macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P (fun q : C × (ℕ → Unit) => start q.1) σ
    (hs.comp measurable_fst) τ N).compl
  have he := (Measure.measurePreserving_swap
    (μ:=TransportNetworkAuxiliary.law (n+1) D (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) J)))
    (ν:=σ)).measure_preimage hm.nullMeasurableSet
  have hp := physicalObserved_failure macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P (fun q : C × (ℕ → Unit) => start q.1) σ
    (hs.comp measurable_fst) τ β N (capacity_pos _ (J+1) 0) hc hβ hbudget
  exact he.trans_le hp

end Bilevel.TransportHierarchy
