import Bilevel.TransportQuadraticCappedBarrier
import Bilevel.TransportQuadraticOriginalBorel
import Bilevel.BorelAdaptiveExpectedInformation

/-! Actual expected original-query lower bound for the fixed-dimensional
quadratic source family. All reply, coupling, observer probability and
terminal-output premises are discharged by the actual compiler; only the
construction's scalar barrier and public dimension arithmetic remain. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
  ChiHierarchyExecution EndpointTransportResponse TransportRound TransportNetwork
  PrimitiveGeometry PartialLegendre TransportAugmented
set_option autoImplicit false
set_option maxHeartbeats 1500000

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

include hA in
theorem quadratic_expected_queries
    (σ : Measure (C × (ℕ → Unit))) [IsProbabilityMeasure σ] (hs : Measurable start)
    (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)
    (τ ε : ℝ) (hτ : 0<τ) (hε : 0<ε)
    (loss : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D × QuadraticOutput D → ℝ)
    (hloss : Measurable loss) (hpos : ∀ z,0≤loss z)
    (hbarrier : ∀ s x,
      (sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll s initial Km).coordinates x.fst (Fin.last macroN)< initial.width →
      8*ε≤loss (s,x))
    (hbudget : ∀ N : ℕ,N≤(n+1)*capacity (sourceCounts macroN cn ratios resolutions) 1 0 →
      quadraticBudget macroN n D cn ratios resolutions initial weight CR ζ Km τ (1/8) N)
    (haccuracy : ∀ s,
      (∫⁻ z,ENNReal.ofReal (loss (BorelAdaptive.seededStopped P
        (fun sample query (_ : Unit) => quadraticOriginalReply macroN n D cn ratios resolutions hdim hAll hT
          initial weight A Kminus ζ CR Km ν ρ R δ c sample query) start (s,z))) ∂σ)≤ENNReal.ofReal ε) :
    ∃ s : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D,
      ENNReal.ofReal (((n+1)*capacity (sourceCounts macroN cn ratios resolutions) 1 0:ℕ)/512)≤
        ∫⁻ z,BorelAdaptive.seededCalls P
          (fun sample query (_ : Unit) => quadraticOriginalReply macroN n D cn ratios resolutions hdim hAll hT
            initial weight A Kminus ζ CR Km ν ρ R δ c sample query) start (s,z) ∂σ := by
  let I := PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D
  let law := TransportNetworkAuxiliary.law (n+1) D (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) 0))
  letI : IsProbabilityMeasure law := TransportNetworkAuxiliary.probability _ _ _
  let original : I → QuadraticQuery n D → Unit → QuadraticReply n D := fun sample query _ =>
    quadraticOriginalReply macroN n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R δ c sample query
  have hargs : Measurable (fun z : I × (QuadraticQuery n D × Unit) => (z.1,z.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hOrig := (quadraticOriginalReply_measurable macroN n D cn ratios resolutions hdim hAll hT
    initial weight A Kminus ζ CR Km ν ρ R hl hw hr hη hη1 hweight hζ hCR hKm δ c).comp hargs
  let T := (n+1)*capacity (sourceCounts macroN cn ratios resolutions) 1 0
  have hTpos : 0<T := Nat.mul_pos (Nat.succ_pos n) (capacity_pos _ 1 0)
  have hTr : (0:ℝ)<T := Nat.cast_pos.mpr hTpos
  have hc := (sourcePublicCap_budgets macroN 0 initial ratios resolutions weight CR ζ Km τ
    hl hw hr hη hweight hCR hζ hKm hτ).1
  let bad := fun N : ℕ => {z : BorelAdaptive.Sample I C Unit |
    ¬quadraticSeedGood macroN n D cn ratios resolutions hdim hAll hT hA initial weight
      A Kminus ζ CR Km ν ρ R δ c P start τ N z}
  let activation := fun _ : ℕ => (∅ : Set (BorelAdaptive.Sample I C Unit))
  have hinfo : ∀ N : ℕ,(N:ℝ)≤(T:ℝ)/(16*1) →
      MeasurableSet (bad N) ∧ MeasurableSet (activation N) ∧
      (law.prod σ).real (bad N)≤1/8 ∧ (law.prod σ).real (activation N)≤1/16 ∧
      (∀ᵐ z ∂law.prod σ,z∉bad N → z∉activation N →
        8*ε≤loss (BorelAdaptive.seededCapped P original start N z)) := by
    intro N hN
    have hlt : (N:ℝ)<T := by nlinarith
    have hltN : N<T := Nat.cast_lt.mp hlt
    refine ⟨(quadraticSeedGood_measurable macroN n D cn ratios resolutions hdim hAll hT hA initial weight
      A Kminus ζ CR Km ν ρ R δ c P start σ hs τ N).compl,MeasurableSet.empty,?_,by simp [activation],?_⟩
    · have hp := quadraticSeedGood_failure macroN n D cn ratios resolutions hdim hAll hT hA initial weight
        A Kminus ζ CR Km ν ρ R δ c P start σ hs τ (1/8) (by norm_num) hc N (hbudget N hltN.le)
      have hh := ENNReal.toReal_mono (by finiteness : ENNReal.ofReal (1/8:ℝ)≠⊤) hp
      simpa only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤1/8)] using hh
    · exact Filter.Eventually.of_forall (fun z hz _ =>
        quadraticCapped_barrier macroN n D cn ratios resolutions hdim hAll hT hA initial weight
          A Kminus ζ CR Km ν ρ R δ c P start hl hw hr hη hη1 hweight hζ hCR hKm
          τ ε hτ N hltN loss hbarrier z (not_not.mp hz))
  obtain ⟨s,_,hcost⟩ := BorelAdaptive.fixed_instance_expected_seededCalls P original hOrig start hs law σ
    (fun _ => True) (Filter.Eventually.of_forall (fun _ => trivial)) loss
    (hloss.comp (BorelAdaptive.seededStopped_measurable P original hOrig start hs)) hpos
    T hTpos 1 ε (by norm_num) hε bad activation hinfo (fun s _ => haccuracy s)
  refine ⟨s,?_⟩
  simpa only [mul_one] using hcost

end Bilevel.TransportHierarchy
