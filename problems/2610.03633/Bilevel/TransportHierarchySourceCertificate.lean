import Bilevel.TransportHierarchyStoreData
import Bilevel.TransportHierarchySourceProjectionBundle
import Bilevel.EndpointTransportObservablePrefix
import Bilevel.ChiCanonicalFrontierAdvance

/-! Literal source physical hierarchy certificate from actual prebatch
network projections, auxiliary energies, and retained-column membership.
No gradient support, inverse equality, or extra future leaf is assumed. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiExtensionCalibration
  ChiHierarchyHaar ChiHierarchyExecution TransportRound TransportNetwork EndpointTransportResponse
  PrimitiveGeometry PartialLegendre
set_option maxHeartbeats 400000
set_option autoImplicit false

theorem sourcePhysical_observable_certificate {H : Type*} (macroN J n D p : ℕ)
    (cn : ℝ) (ratios resolutions : ℕ → ℝ)
    (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
    (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤D)
    (hT : capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0≤D)
    (hA : auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) J+1≤D)
    (s : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D)
    (choose : ∀ t,H × Generators (n+1) D (size (n+1) p 1 1 t) → Queries (n+1) D p)
    (respond : ∀ t,StepData H (n+1) D (size (n+1) p 1 1 t) p
      (capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0) → H)
    (memory : H) (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)
    (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)
    (P : ChiFine.Parameters) (τ : ℝ) (hτ : 0<τ) (N t : ℕ) (ht : t<N)
    (W : Fin J → Submodule ℝ (EuclideanGaussian.Space D)) :
    let counts := sourceCounts macroN cn ratios resolutions
    let M := sourcePhysicalMacro macroN J n D cn ratios resolutions hAll s initial Km
    let G := sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR
    let C := TransportAuxiliaryFrame.actualStore (auxiliaryRoundSchedule counts J (n+1) (Nat.succ_pos n)) t
      (fun a => TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity counts J+1) hA a s)
    let g := (run (capacity counts (J+1) 0) hT choose respond (prefixNames (n+1) (capacity counts (J+1) 0))
      (memory,seed (capacity counts (J+1) 0) hT s.1) s.1 t).2
    let data := hierarchyStoreData counts J p t C g
    let q := t/(n+1)
    let cap := sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km τ
    P.ℓ=(G J []).ell → P.β=(G J []).width →
    (∀ j I,∀ hj : j<J,∀ k : Fin ((G j I).n+1),k.val<canonicalCounter counts J q j I →
      (G j I).frame (basis k)∈W ⟨j,hj⟩) →
    (∀ j I,∀ hj : j<J,GenieProtocol.BoundedEnergy (W ⟨j,hj⟩) (prefixSet (canonicalCounter counts J q j I))
      (TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity counts J+1) hA
        (enumerate counts J (Sum.inr (canonicalNode counts J ⟨j,Nat.lt_succ_of_lt hj⟩ I))) s) cap) →
    ProjectionGood hT choose respond N (Real.sqrt cap/EndpointTransportMatrix.gamma n) memory s.1 →
    ObservablePhysicalPrefixCertificate (physicalRotations s.1) M G P W
      (terminalPreSpace counts J hT choose respond memory s.1 t)
      (counter counts (J+1) q 0 []) (canonicalCounter counts J q) (canonicalCounter counts J (q+1))
      data.1 data.2.1 data.2.2.1 data.2.2.2 := by
  dsimp only
  intro hℓ hβ hknown hE hnet
  let counts := sourceCounts macroN cn ratios resolutions
  let G := sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR
  let q := t/(n+1)
  have hgeo := sourcePhysical_projection_certificate_bundle macroN J n D p cn ratios resolutions hdim hAll hT hA s
    choose respond memory initial weight A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm P τ hτ N t ht W
    hℓ hβ hknown hE hnet
  have hp := hierarchyStoreData_prefix counts J hdim hT hAll hA s choose respond memory t
  refine ⟨hgeo.1,?_,?_,?_,?_,?_,?_,?_,hgeo.2⟩
  · simpa only [sourcePhysicalMacro_frame] using hp.1
  · simpa only [sourcePhysicalGeometry_frame] using hp.2.1
  · intro I
    exact (canonicalCounter_success_bounds counts J q J I).1
  · simpa only [sourcePhysicalGeometry_frame] using hp.2.2.1
  · simpa only [sourcePhysicalGeometry_frame] using hp.2.2.2
  · intro I k hk
    simpa only [sourcePhysicalGeometry_frame,physicalFamily_terminal] using
      terminalSource_mem_preSpace counts J hT choose respond memory s.1 t I k hk
  · intro i hi
    exact canonical_frontierAdvance G counts (fun _ _ => rfl) J q i hi

end Bilevel.TransportHierarchy
