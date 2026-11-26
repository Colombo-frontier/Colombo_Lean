import Bilevel.TransportHierarchySourceBulkMargins
import Bilevel.TransportHierarchySourceTerminalFacts
import Bilevel.EndpointTransportSourcePrefixGeometry
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

theorem sourcePhysical_projection_certificate_bundle {H : Type*} (macroN J n D p : ℕ)
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
    let G := sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR
    let q := t/(n+1)
    let cap := sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km τ
    P.ℓ=(G J []).ell → P.β=(G J []).width →
    (∀ j I,∀ hj : j<J,∀ k : Fin ((G j I).n+1),k.val<canonicalCounter counts J q j I →
      (G j I).frame (basis k)∈W ⟨j,hj⟩) →
    (∀ j I,∀ hj : j<J,GenieProtocol.BoundedEnergy (W ⟨j,hj⟩) (prefixSet (canonicalCounter counts J q j I))
      (TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity counts J+1) hA
        (enumerate counts J (Sum.inr (canonicalNode counts J ⟨j,Nat.lt_succ_of_lt hj⟩ I))) s) cap) →
    ProjectionGood hT choose respond N (Real.sqrt cap/EndpointTransportMatrix.gamma n) memory s.1 →
    PhysicalPrefixGeometry (physicalRotations s.1) G P W
      (terminalPreSpace counts J hT choose respond memory s.1 t) (canonicalCounter counts J q) ∧
    (∀ j I,∀ hj : j<J,∀ k : Fin ((G j I).n+1),canonicalCounter counts J q j I≤k.val →
      (G j I).radius*‖(W ⟨j,hj⟩).orthogonalProjection ((G j I).frame (basis k))‖≤(G j I).width/8) := by
  dsimp only
  intro hℓ hβ hknown hE hnet
  let counts := sourceCounts macroN cn ratios resolutions
  let G := sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR
  let q := t/(n+1)
  let Z := terminalPreSpace counts J hT choose respond memory s.1 t
  have hm := sourcePhysical_ancestor_margins macroN J n D cn ratios resolutions hdim hAll hT hA s
    initial weight A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm q W τ hτ hE
  have hf := sourcePhysical_terminal_facts macroN J n D p cn ratios resolutions hdim hAll hT s
    choose respond memory initial weight A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm τ hτ N t ht hnet
  refine ⟨?_,hm⟩
  exact source_physical_prefix_geometry (physicalRotations s.1)
    initial ratios resolutions weight A Kminus ζ cn CR (physicalFamily hdim hT s)
    hl hw hr hη hη1 hweight hζ hCR P W Z (canonicalCounter counts J q)
    hℓ hβ hknown hm
    (fun I k hk => hf.1 I k (lt_of_lt_of_le hk (canonicalCounter_success_bounds counts J q J I).1))
    hf.2.1 hf.2.2 (fun k hk I i hi => canonicalCounter_future counts J q k hk I i hi)

end Bilevel.TransportHierarchy
