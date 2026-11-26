import Bilevel.TransportQuadraticProbability
import Bilevel.TransportQuadraticBudget
import Bilevel.BorelAdaptivePrior

/-! The exact same observed event on the original instance-first prior.
The private seed is independent of the sampled hard instance; dummy Unit
oracle draws permit the existing extended-call stopping-time interface. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
  ChiHierarchyExecution EndpointTransportResponse TransportRound TransportNetwork
  PrimitiveGeometry PartialLegendre TransportAugmented
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  (macroN n D : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) 1 0≤D)
  (hA : auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) 0+1≤D)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km ν ρ R δ c : ℝ)
  [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]
  [MeasurableSpace (QuadraticOutput D)] [BorelSpace (QuadraticOutput D)]
  [MeasurableSpace (QuadraticQuery n D)] [BorelSpace (QuadraticQuery n D)]
  (P : BorelAdaptive.Program S (QuadraticQuery n D) (QuadraticReply n D) (QuadraticOutput D))
  (start : C → S)

def quadraticSeedGood (τ : ℝ) (N : ℕ)
    (z : BorelAdaptive.Sample (PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D) C Unit) : Prop :=
  quadraticObserved macroN n D cn ratios resolutions hdim hAll hT hA initial weight
    A Kminus ζ CR Km ν ρ R δ c P (fun q : C × (ℕ → Unit) => start q.1) τ N (z.2,z.1)

theorem quadraticSeedGood_measurable (σ : Measure (C × (ℕ → Unit))) [IsProbabilityMeasure σ]
    (hs : Measurable start) (τ : ℝ) (N : ℕ) :
    MeasurableSet {z | quadraticSeedGood macroN n D cn ratios resolutions hdim hAll hT hA initial weight
      A Kminus ζ CR Km ν ρ R δ c P start τ N z} :=
  (measurable_snd.prodMk measurable_fst)
    (quadraticObserved_measurable macroN n D cn ratios resolutions hdim hAll hT hA initial weight
      A Kminus ζ CR Km ν ρ R δ c P (fun q : C × (ℕ → Unit) => start q.1) σ
      (hs.comp measurable_fst) τ N)

theorem quadraticSeedGood_failure (σ : Measure (C × (ℕ → Unit))) [IsProbabilityMeasure σ]
    (hs : Measurable start) (τ β : ℝ) (hβ : 0<β)
    (hc : 0<sourcePublicCap macroN 0 initial ratios resolutions weight CR ζ Km τ) (N : ℕ)
    (hbudget : quadraticBudget macroN n D cn ratios resolutions initial weight CR ζ Km τ β N) :
    ((TransportNetworkAuxiliary.law (n+1) D
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) 0))).prod σ)
      {z | ¬quadraticSeedGood macroN n D cn ratios resolutions hdim hAll hT hA initial weight
        A Kminus ζ CR Km ν ρ R δ c P start τ N z}≤ENNReal.ofReal β := by
  letI : IsProbabilityMeasure (TransportNetworkAuxiliary.law (n+1) D
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) 0))) :=
    TransportNetworkAuxiliary.probability _ _ _
  letI : IsFiniteMeasure (TransportNetworkAuxiliary.law (n+1) D
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) 0))) := inferInstance
  letI : SigmaFinite (TransportNetworkAuxiliary.law (n+1) D
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) 0))) :=
    IsFiniteMeasure.toSigmaFinite _
  letI : SFinite (TransportNetworkAuxiliary.law (n+1) D
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) 0))) := inferInstance
  have hm := (quadraticObserved_measurable macroN n D cn ratios resolutions hdim hAll hT hA initial weight
    A Kminus ζ CR Km ν ρ R δ c P (fun q : C × (ℕ → Unit) => start q.1) σ
    (hs.comp measurable_fst) τ N).compl
  have he := (Measure.measurePreserving_swap
    (μ:=TransportNetworkAuxiliary.law (n+1) D (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) 0)))
    (ν:=σ)).measure_preimage hm.nullMeasurableSet
  have hp := quadraticObserved_failure macroN n D cn ratios resolutions hdim hAll hT hA initial weight
    A Kminus ζ CR Km ν ρ R δ c P (fun q : C × (ℕ → Unit) => start q.1) σ
    (hs.comp measurable_fst) τ β hβ hc N hbudget
  exact he.trans_le hp

end Bilevel.TransportHierarchy
