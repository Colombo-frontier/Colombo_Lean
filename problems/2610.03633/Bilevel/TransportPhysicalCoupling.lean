import Bilevel.TransportPhysicalObservedReply
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

include hcomplete hρ hR hℓ hβ hJ hl hw hr hη hη1 hweight hζ hCR hKm in
theorem physicalObserved_state_eq_original
    (τ : ℝ) (hτ : 0<τ) (N t : ℕ) (ht : t≤N)
    (ω : C × PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D)
    (hobs : physicalObserved macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start τ N ω) :
    (physicalRun macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start ω t).1.2.2.1=
      BorelAdaptive.run P
        (fun sample query (_ : Unit) => physicalOriginalReply macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend ⟨1/12,by norm_num⟩
          (by change (1:ℝ)/12<1;norm_num) hF sample query)
        ω.2 (fun _ => ()) (start ω.1) t := by
  let counts := sourceCounts macroN cn ratios resolutions
  let schedule := auxiliaryRoundSchedule counts J (n+1) (Nat.succ_pos n)
  let evaluate := physicalEvaluate macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend
  have h := TransportProgram.compiled_run_eq_original P
    physicalNetworkQueries physicalNetworkQueries_measurable
    physicalAuxiliaryQueries physicalAuxiliaryQueries_measurable
    physicalNetworkOutput physicalNetworkOutput_measurable
    physicalAuxiliaryOutput physicalAuxiliaryOutput_measurable
    evaluate (physicalEvaluate_measurable macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend)
    schedule hT (prefixNames (n+1) (capacity counts (J+1) 0))
    (initialMemoryAny hA start (ω.1,ω.2.2),seed (capacity counts (J+1) 0) hT ω.2.1) ω.2.1
    (fun sample query (_ : Unit) => physicalOriginalReply macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend ⟨1/12,by norm_num⟩
      (by change (1:ℝ)/12<1;norm_num) hF sample query) ω.2 t (by
      intro j hj
      dsimp only
      intro _
      exact physicalObserved_reply macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start hcomplete hρ hR hF hℓ hβ hJ
        hl hw hr hη hη1 hweight hζ hCR hKm τ hτ N j (lt_of_lt_of_le hj ht) ω hobs)
  exact h

end Bilevel.TransportHierarchy
