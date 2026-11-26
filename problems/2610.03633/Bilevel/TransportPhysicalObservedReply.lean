import Bilevel.TransportPhysicalObservedCertificate
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
theorem physicalObserved_reply
    (τ : ℝ) (hτ : 0<τ) (N t : ℕ) (ht : t<N)
    (ω : C × PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D)
    (hobs : physicalObserved macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start τ N ω) :
    let st := physicalRun macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start ω t
    let w := P.query st.1.2.2.1
    physicalEvaluate macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend t
      (w,(st.1.2.2.2,(st.2,batch (augment st.2 (physicalNetworkQueries w)) ω.2.1)))=
      physicalOriginalReply macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend ⟨1/12,by norm_num⟩
        (by change (1:ℝ)/12<1;norm_num) hF ω.2 w := by
  let counts := sourceCounts macroN cn ratios resolutions
  let schedule := auxiliaryRoundSchedule counts J (n+1) (Nat.succ_pos n)
  let ctl := physicalController (C:=C) macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P
  let st := physicalRun macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start ω t
  let M := sourcePhysicalMacro macroN J n D cn ratios resolutions hAll ω.2 initial Km
  let G := sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT ω.2 initial weight A Kminus ζ CR
  let data := hierarchyStoreData counts J 1 t st.1.2.2.2 st.2
  let w := P.query st.1.2.2.1
  let WM := analyticalAuxSpaceAny ctl t (st.1.2,st.2)
  let Z := terminalPreSpace counts J hT (networkChoose ctl) (networkRespond schedule ctl)
    (initialMemoryAny hA start (ω.1,ω.2.2)) ω.2.1 t
  let K : NNReal := ⟨1/12,by norm_num⟩
  have hK : K<1 := by change (1:ℝ)/12<1;norm_num
  have hc := physicalObserved_certificate macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start hl hw hr hη hη1 hweight hζ hCR hKm
    τ hτ N t ht ω (hℓ ω.2) (hβ ω.2) hobs
  have hq := physicalObserved_query_geometry macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start hl hw hr hη hη1 hweight hζ hCR hKm
    τ hτ N t ht ω hobs
  have hp := physicalRun_prefix_hessian macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start hcomplete ω t (hρ ω.2) (hR ω.2)
  have ho := physicalOriginalCore_hessian macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn hcomplete ω.2 (hρ ω.2) (hR ω.2)
  have geo := sourcePhysical_geometry macroN J n D cn ratios resolutions hdim hAll hT ω.2
    initial weight A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm
  have hg := physicalExtension_gradient_lipschitz (U:=Blocks J (Block D)) (D:=D) hp.1 K hp.2
  have he := observable_physical_joint_reply M ν G fine hJ index radialIndex fineIndex ρ R dn b
    (fun i => by rw [hR ω.2];exact (geo.2.2.1 (i.val+1) []).2.1)
    (fun q => counter counts (J+1) q 0 []) (canonicalCounter counts J)
    (fun q => canonicalCounter counts J (q+1)) (t/(n+1),data) ω.2.1 (fun _ => WM) Z hc geo.1 geo.2.1
    (fun i hi => canonicalCounter_macro_future counts J (t/(n+1)) i hi)
    K K hK hK ho.1 ho.2 (hF ω.2) hg
    ((parentScale initial ratios resolutions (J+1)).width/16) hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2
    m δ c₀ cend st.2 (physicalNetworkQueries w) (0 : Fin 1) w
    (physicalNetworkQueries_physical w) hq.1 hq.2.1
  dsimp only
  rw [physicalEvaluate_template_independent macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend ω.2 t]
  exact he

end Bilevel.TransportHierarchy
