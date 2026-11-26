import Bilevel.TransportPhysicalObserved
import Bilevel.TransportHierarchySourceMargins
import Bilevel.EndpointTransportNormalKnown
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



theorem physicalObserved_query_geometry
    (hl : 0 < initial.curvature) (hw : 0 < initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)
    (τ : ℝ) (hτ : 0<τ) (N t : ℕ) (ht : t<N)
    (ω : C × PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D)
    (hobs : physicalObserved macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start τ N ω) :
    let counts := sourceCounts macroN cn ratios resolutions
    let schedule := auxiliaryRoundSchedule counts J (n+1) (Nat.succ_pos n)
    let ctl := physicalController (C:=C) macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P
    let st := physicalRun macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start ω t
    let M := sourcePhysicalMacro macroN J n D cn ratios resolutions hAll ω.2 initial Km
    let G := sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT ω.2 initial weight A Kminus ζ CR
    let w := P.query st.1.2.2.1
    let ξ := (parentScale initial ratios resolutions (J+1)).width/16
    w.snd∈physicalNormalKnown (fun _ : Fin J => analyticalAuxSpaceAny ctl t (st.1.2,st.2))
      (terminalPreSpace counts J hT (networkChoose ctl) (networkRespond schedule ctl)
        (initialMemoryAny hA start (ω.1,ω.2.2)) ω.2.1 t) s ∧
      (∀ k : Fin (M.n+1),counter counts (J+1) (t/(n+1)) 0 []≤k.val →
        |M.coordinates w.fst.fst.fst k|≤M.width/8) ∧
      0<ξ ∧ ξ≤M.width/16 ∧ (∀ j I,j≤J → ξ≤(G j I).width/16) := by
  let counts := sourceCounts macroN cn ratios resolutions
  let schedule := auxiliaryRoundSchedule counts J (n+1) (Nat.succ_pos n)
  let ctl := physicalController (C:=C) macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P
  let st := physicalRun macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start ω t
  let WM := analyticalAuxSpaceAny ctl t (st.1.2,st.2)
  have qi := physicalRun_query_membership macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start ω t
  have hE := physicalObserved_energy macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start τ N t ht ω hobs (Sum.inl ())
  have hblind := sourcePhysical_macro_blind macroN J n D cn ratios resolutions hAll ω.2
    initial weight ζ CR Km hA hl hw hr hη hweight hζ hCR hKm τ hτ (t/(n+1)) WM
    (P.query st.1.2.2.1).fst.fst.fst qi.1 hE
  have hξ := sourcePhysical_uniform_germ_radius macroN J n D cn ratios resolutions hdim hAll hT ω.2
    initial weight A Kminus ζ CR Km hl hw hr hη hη1
  dsimp only
  refine ⟨?_,hblind,hξ.1,hξ.2.1,hξ.2.2⟩
  apply (mem_physicalNormalKnown _ _ _).mpr
  refine ⟨?_,qi.2.2⟩
  intro i
  simpa only [block,dif_pos i.isLt,PiLp.proj_apply] using qi.2.1 i

end Bilevel.TransportHierarchy
