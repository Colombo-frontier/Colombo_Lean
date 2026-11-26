import Bilevel.TransportPhysicalObserved
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



theorem physicalObserved_certificate
    (hl : 0 < initial.curvature) (hw : 0 < initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)
    (τ : ℝ) (hτ : 0<τ) (N t : ℕ) (ht : t<N)
    (ω : C × PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D)
    (hℓ : fine.ℓ=(sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT ω.2 initial weight A Kminus ζ CR J []).ell)
    (hβ : fine.β=(sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT ω.2 initial weight A Kminus ζ CR J []).width)
    (hobs : physicalObserved macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start τ N ω) :
    let counts := sourceCounts macroN cn ratios resolutions
    let schedule := auxiliaryRoundSchedule counts J (n+1) (Nat.succ_pos n)
    let ctl := physicalController (C:=C) macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P
    let st := physicalRun macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start ω t
    let M := sourcePhysicalMacro macroN J n D cn ratios resolutions hAll ω.2 initial Km
    let G := sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT ω.2 initial weight A Kminus ζ CR
    let data := hierarchyStoreData counts J 1 t st.1.2.2.2 st.2
    ObservablePhysicalPrefixCertificate (J:=J) (physicalRotations ω.2.1) M G fine
      (fun _ => analyticalAuxSpaceAny ctl t (st.1.2,st.2))
      (terminalPreSpace counts J hT (networkChoose ctl) (networkRespond schedule ctl)
        (initialMemoryAny hA start (ω.1,ω.2.2)) ω.2.1 t)
      (counter counts (J+1) (t/(n+1)) 0 [])
      (canonicalCounter counts J (t/(n+1))) (canonicalCounter counts J (t/(n+1)+1))
      data.1 data.2.1 data.2.2.1 data.2.2.2 := by
  let counts := sourceCounts macroN cn ratios resolutions
  let schedule := auxiliaryRoundSchedule counts J (n+1) (Nat.succ_pos n)
  let ctl := physicalController (C:=C) macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P
  let st := physicalRun macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start ω t
  let WM := analyticalAuxSpaceAny ctl t (st.1.2,st.2)
  have hpfx := physicalRun_prefix macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start ω t
  have hp := hierarchyStoreData_prefix counts J hdim hT hAll hA ω.2
    (networkChoose ctl) (networkRespond schedule ctl) (initialMemoryAny hA start (ω.1,ω.2.2)) t
  have hknown (j : ℕ) (I : List ℕ) (hj : j<J)
      (k : Fin (sourceChainIndex cn (ratios j) (resolutions j)+1))
      (hk : k.val<canonicalCounter counts J (t/(n+1)) j I) :
      physicalFamily hdim hT ω.2 j I (basis k)∈WM := by
    have hh := hp.2.1 j I hj k hk
    rw [←hh]
    change hierarchyOrdinaryReadout counts J _ j I k∈WM
    rw [←hpfx]
    exact hierarchyOrdinaryReadout_mem counts J ctl t (st.1.2,st.2) j I k
  have hE (j : ℕ) (I : List ℕ) (hj : j<J) :
      GenieProtocol.BoundedEnergy WM (prefixSet (canonicalCounter counts J (t/(n+1)) j I))
        (TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity counts J+1) hA
          (enumerate counts J (Sum.inr (canonicalNode counts J ⟨j,Nat.lt_succ_of_lt hj⟩ I))) ω.2)
        (sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km τ) := by
    have hh := physicalObserved_energy macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start τ N t ht ω hobs
      (Sum.inr (canonicalNode counts J ⟨j,Nat.lt_succ_of_lt hj⟩ I))
    simpa only [canonicalCounter,dif_pos (Nat.le_of_lt hj)] using hh
  have hc := sourcePhysical_observable_certificate macroN J n D 1 cn ratios resolutions hdim hAll hT hA ω.2
    (networkChoose ctl) (networkRespond schedule ctl) (initialMemoryAny hA start (ω.1,ω.2.2))
    initial weight A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm fine τ hτ N t ht
    (fun _ => WM) hℓ hβ hknown hE hobs.1.1
  dsimp only
  rw [hpfx]
  exact hc

end Bilevel.TransportHierarchy
