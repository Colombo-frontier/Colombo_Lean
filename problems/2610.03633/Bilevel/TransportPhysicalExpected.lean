import Bilevel.TransportPhysicalCappedBarrier
import Bilevel.TransportPhysicalOriginalBorel
import Bilevel.BorelAdaptiveExpectedInformation
import Bilevel.TransportPhysicalSeedEvent
import Bilevel.TransportPhysicalTerminal
import Bilevel.TransportPhysicalObservedGeometry
import Bilevel.TransportPhysicalObservedHessian
import Bilevel.TransportPhysicalOriginalAnalytic
import Bilevel.EndpointTransportObservableJointReply
import Bilevel.ChiCanonicalMacroFuture
import Bilevel.TransportHierarchySourceCertificate
import Bilevel.TransportHierarchyStoreKnown
import Bilevel.TransportPhysicalOutput
import Bilevel.TransportAugmentedBudgetProbability

/-! Literal same-prior execution and inclusion of each queried coordinate
in its prebatch analytical space. The common auxiliary space contains all
ordinary lower points before the frozen network answers are returned. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
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



variable
    (hcomplete : ∀ (dim' : ℕ) (Q : Rotations n dim')
      (U : Space macroN →ₗᵢ[ℝ] Block dim')
      (V : ∀ j,List ℕ → Space (sourceChainIndex cn (ratios j) (resolutions j)) →ₗᵢ[ℝ] Block dim'),
      let M' := ChiOuter.sourceMacroNode macroN initial Km U
      let G' := sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR V
      let rad' := fun j => weight j*(G' j []).nu
      let R' := fun j => (G' j []).radius
      ContDiff ℝ 3 (physicalHierarchyExtension Q M' G' fine J s index radialIndex fineIndex rad' R' dn) ∧
      ∀ z,‖iteratedFDeriv ℝ 2 (physicalHierarchyExtension Q M' G' fine J s index radialIndex fineIndex rad' R' dn) z‖≤(1:ℝ)/12)
    (hρ : ∀ (sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D) j,
      ρ j=weight j*(sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT sample initial weight A Kminus ζ CR j []).nu)
    (hR : ∀ (sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D) j,
      R j=(sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT sample initial weight A Kminus ζ CR j []).radius)
    (hF : ∀ sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D,
      LipschitzWith (⟨1/12,by norm_num⟩ : NNReal) (gradient (physicalOriginalPotential macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn sample)))
    (hℓ : ∀ sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D,
      fine.ℓ=(sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT sample initial weight A Kminus ζ CR J []).ell)
    (hβ : ∀ sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D,
      fine.β=(sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT sample initial weight A Kminus ζ CR J []).width)
    (hJ : 0<J)
    (hl : 0 < initial.curvature) (hw : 0 < initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)

include hA hcomplete hρ hR hℓ hβ hJ hl hw hr hη hη1 hweight hζ hCR hKm in
theorem physical_expected_queries
    (σ : Measure (C × (ℕ → Unit))) [IsProbabilityMeasure σ] (hs : Measurable start)
    (τ ε : ℝ) (hτ : 0<τ) (hε : 0<ε)
    (loss : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D × PhysicalOutput J D → ℝ)
    (hloss : Measurable loss) (hpos : ∀ z,0≤loss z)
    (hbarrier : ∀ sample x,
      (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll sample initial Km).coordinates x.fst.fst (Fin.last macroN)< initial.width →
      8*ε≤loss (sample,x))
    (hbudget : ∀ N : ℕ,N≤(n+1)*capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0 →
      physicalBudget macroN J n D cn ratios resolutions initial weight CR ζ Km τ (1/8) N)
    (haccuracy : ∀ sample,
      (∫⁻ z,ENNReal.ofReal (loss (BorelAdaptive.seededStopped P
        (fun sample query (_ : Unit) => physicalOriginalReply macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend ⟨1/12,by norm_num⟩ (by change (1:ℝ)/12<1;norm_num) hF sample query) start (sample,z))) ∂σ)≤ENNReal.ofReal ε) :
    ∃ sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D,
      ENNReal.ofReal (((n+1)*capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0:ℕ)/512)≤
        ∫⁻ z,BorelAdaptive.seededCalls P
          (fun sample query (_ : Unit) => physicalOriginalReply macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend ⟨1/12,by norm_num⟩ (by change (1:ℝ)/12<1;norm_num) hF sample query) start (sample,z) ∂σ := by
  let I := PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D
  let law := TransportNetworkAuxiliary.law (n+1) D (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) J))
  letI : IsProbabilityMeasure law := TransportNetworkAuxiliary.probability _ _ _
  let original : I → PhysicalQuery J n D s → Unit → PhysicalReply J n D s := fun sample query _ =>
    physicalOriginalReply macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend ⟨1/12,by norm_num⟩ (by change (1:ℝ)/12<1;norm_num) hF sample query
  have hargs : Measurable (fun z : I × (PhysicalQuery J n D s × Unit) => (z.1,z.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hreg (sample : I) : ContDiff ℝ 3 (physicalOriginalPotential macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn sample) :=
    physicalExtension_contDiff (physicalOriginalCore_hessian macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn
      hcomplete sample (hρ sample) (hR sample)).1
  have hOrig := (physicalOriginalReply_measurable macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend
    hl hw hr hη hη1 hweight hζ hCR hKm hℓ hβ ⟨1/12,by norm_num⟩
    (by change (1:ℝ)/12<1;norm_num) hF hJ hreg).comp hargs
  let T := (n+1)*capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0
  have hTpos : 0<T := Nat.mul_pos (Nat.succ_pos n) (capacity_pos _ (J+1) 0)
  have hTr : (0:ℝ)<T := Nat.cast_pos.mpr hTpos
  have hc := (sourcePublicCap_budgets macroN J initial ratios resolutions weight CR ζ Km τ
    hl hw hr hη hweight hCR hζ hKm hτ).1
  let bad := fun N : ℕ => {z : BorelAdaptive.Sample I C Unit |
    ¬physicalSeedGood macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start τ N z}
  let activation := fun _ : ℕ => (∅ : Set (BorelAdaptive.Sample I C Unit))
  have hinfo : ∀ N : ℕ,(N:ℝ)≤(T:ℝ)/(16*1) →
      MeasurableSet (bad N) ∧ MeasurableSet (activation N) ∧
      (law.prod σ).real (bad N)≤1/8 ∧ (law.prod σ).real (activation N)≤1/16 ∧
      (∀ᵐ z ∂law.prod σ,z∉bad N → z∉activation N →
        8*ε≤loss (BorelAdaptive.seededCapped P original start N z)) := by
    intro N hN
    have hlt : (N:ℝ)<T := by nlinarith
    have hltN : N<T := Nat.cast_lt.mp hlt
    refine ⟨(physicalSeedGood_measurable macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start σ hs τ N).compl,MeasurableSet.empty,?_,by simp [activation],?_⟩
    · have hp := physicalSeedGood_failure macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start σ hs τ (1/8) (by norm_num) hc N (hbudget N hltN.le)
      have hh := ENNReal.toReal_mono (by finiteness : ENNReal.ofReal (1/8:ℝ)≠⊤) hp
      simpa only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤1/8)] using hh
    · exact Filter.Eventually.of_forall (fun z hz _ =>
        physicalCapped_barrier macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start hcomplete hρ hR hF hℓ hβ hJ hl hw hr hη hη1 hweight hζ hCR hKm
          τ ε hτ N hltN loss hbarrier z (not_not.mp hz))
  obtain ⟨s,_,hcost⟩ := BorelAdaptive.fixed_instance_expected_seededCalls P original hOrig start hs law σ
    (fun _ => True) (Filter.Eventually.of_forall (fun _ => trivial)) loss
    (hloss.comp (BorelAdaptive.seededStopped_measurable P original hOrig start hs)) hpos
    T hTpos 1 ε (by norm_num) hε bad activation hinfo (fun s _ => haccuracy s)
  refine ⟨s,?_⟩
  simpa only [mul_one] using hcost

end Bilevel.TransportHierarchy
