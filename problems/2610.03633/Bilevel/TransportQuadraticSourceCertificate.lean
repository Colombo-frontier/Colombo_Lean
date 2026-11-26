import Bilevel.TransportQuadraticSourceColumns
import Bilevel.TransportHierarchySourceProjection
import Bilevel.EndpointTransportQuadraticProjectionGerm
import Bilevel.TransportPublicCapBounds

/-! The literal physical source has the correct complete disclosed upper
germ on the actual network/auxiliary good event at the SAME current query.
All prefix timing, reachable-branch and scalar-margin premises are derived.
Only observer events and query membership remain for execution coupling. -/
noncomputable section
open scoped Topology
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
  ChiHierarchyHaar ChiHierarchyExecution TransportRound TransportNetwork EndpointTransportResponse
  PrimitiveGeometry PartialLegendre
set_option maxHeartbeats 1600000
set_option autoImplicit false

theorem sourceQuadratic_prefix_germ {H : Type*} (macroN n D p : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
    (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
    (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤D)
    (hT : capacity (sourceCounts macroN cn ratios resolutions) 1 0≤D)
    (hA : auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) 0+1≤D)
    (s : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D)
    (choose : ∀ t,H × Generators (n+1) D (size (n+1) p 1 1 t) → Queries (n+1) D p)
    (respond : ∀ t,StepData H (n+1) D (size (n+1) p 1 1 t) p
      (capacity (sourceCounts macroN cn ratios resolutions) 1 0) → H)
    (memory : H) (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)
    (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)
    (ν ρ R τ : ℝ) (hτ : 0<τ) (N t : ℕ) (ht : t<N)
    (WM : Submodule ℝ (EuclideanGaussian.Space D))
    (z : Joint (EuclideanGaussian.Space D) (Physical n D)) (hzM : z.fst∈WM)
    (hzT : z.snd (Fin.last (n+1))∈terminalPreSpace (sourceCounts macroN cn ratios resolutions) 0
      hT choose respond memory s.1 t (Fin.last (n+1)))
    (hE : GenieProtocol.BoundedEnergy WM
      (prefixSet (counter (sourceCounts macroN cn ratios resolutions) 1 (t/(n+1)) 0 []))
      (TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) 0+1)
        hA (enumerate (sourceCounts macroN cn ratios resolutions) 0 (Sum.inl ())) s)
      (sourcePublicCap macroN 0 initial ratios resolutions weight CR ζ Km τ))
    (hnet : ProjectionGood hT choose respond N
      (Real.sqrt (sourcePublicCap macroN 0 initial ratios resolutions weight CR ζ Km τ)/EndpointTransportMatrix.gamma n)
      memory s.1) :
    let counts := sourceCounts macroN cn ratios resolutions
    let M := sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll s initial Km
    let G := sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR
    let C := TransportAuxiliaryFrame.actualStore (auxiliaryRoundSchedule counts 0 (n+1) (Nat.succ_pos n)) t
      (fun a => TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity counts 0+1) hA a s)
    let g := (run (capacity counts 1 0) hT choose respond (prefixNames (n+1) (capacity counts 1 0))
      (memory,seed (capacity counts 1 0) hT s.1) s.1 t).2
    let data := quadraticSourceData macroN n D p t cn ratios resolutions C g
    quadraticCore (physicalRotations s.1) M ν G ρ R =ᶠ[𝓝 z]
      prefixQuadraticCore (physicalRotations s.1) M ν G ρ R (counter counts 1 (t/(n+1)) 0 [])
        (fun i => canonicalCounter counts 0 (t/(n+1)) 0 [i.val]) data.1 data.2.1 data.2.2 := by
  dsimp only
  let M := sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll s initial Km
  let G := sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR
  have geo := sourcePhysical_geometry macroN 0 n D cn ratios resolutions hdim hAll hT s
    initial weight A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm
  have hc := sourcePublicCap_budgets macroN 0 initial ratios resolutions weight CR ζ Km τ
    hl hw hr hη hweight hCR hζ hKm hτ
  have hp := quadraticSourceData_prefix macroN n D p cn ratios resolutions hdim hAll hT hA s
    choose respond memory initial weight A Kminus ζ CR Km t
  let counts := sourceCounts macroN cn ratios resolutions
  let C := TransportAuxiliaryFrame.actualStore (auxiliaryRoundSchedule counts 0 (n+1) (Nat.succ_pos n)) t
    (fun a => TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity counts 0+1) hA a s)
  let g := (run (capacity counts 1 0) hT choose respond (prefixNames (n+1) (capacity counts 1 0))
    (memory,seed (capacity counts 1 0) hT s.1) s.1 t).2
  let data := quadraticSourceData macroN n D p t cn ratios resolutions C g
  let WT := terminalPreSpace counts 0 hT choose respond memory s.1 t (Fin.last (n+1))
  have hmproj : ∀ k : Fin (macroN+1),counter counts 1 (t/(n+1)) 0 []≤k.val →
      M.radius*‖WM.orthogonalProjection (M.frame (basis k))‖≤M.width/8 := by
    intro k hk
    exact sourcePhysical_macro_projection macroN 0 n D cn ratios resolutions hAll hA s initial Km
      WM (t/(n+1)) _ hc.1.le hE geo.2.1.le (hc.2.2 (Sum.inl ())) k hk
  have htproj : ∀ i : Fin (macroN+1),∀ k : Fin (sourceChainIndex cn (ratios 0) (resolutions 0)+1),
      canonicalCounter counts 0 (t/(n+1)) 0 [i.val]≤k.val →
      (EndpointTransportMatrix.gamma n*(G 0 [i.val]).radius)*
        ‖WT.orthogonalProjection (physicalRotations s.1 (Fin.last (n+1)) ((G 0 [i.val]).frame (basis k)))‖≤
          (G 0 [i.val]).width/8 := by
    intro i k hk
    have hbudget : (G 0 [i.val]).radius*
        Real.sqrt (sourcePublicCap macroN 0 initial ratios resolutions weight CR ζ Km τ)≤(G 0 [i.val]).width/8 := by
      dsimp only [G]
      rw [sourcePhysicalGeometry_radius,sourcePhysicalGeometry_width]
      exact hc.2.2 (Sum.inr (Sum.inl (0 : Fin 1)))
    exact sourcePhysical_terminal_projection macroN 0 n D cn ratios resolutions hdim hT s
      choose respond memory initial weight A Kminus ζ CR N t ht _ hnet [i.val] k hk
      (geo.2.2.1 0 [i.val]).2.1.le hbudget
  have hfinal := quadraticCore_prefix_germ_of_projections (physicalRotations s.1) M ν G ρ R
    (counter counts 1 (t/(n+1)) 0 [])
    (fun i => canonicalCounter counts 0 (t/(n+1)) 0 [i.val]) data.1 data.2.1 data.2.2
    hp.1 hp.2.1 hp.2.2 geo.1 geo.2.1
    (fun I => (geo.2.2.1 0 I).1) (fun I => (geo.2.2.1 0 I).2.1)
    (fun I => (geo.2.2.1 0 I).2.2.2.1) (fun I => (geo.2.2.1 0 I).2.2.2.2)
    (fun I => geo.2.2.2 0 I)
    (fun i hi => canonicalCounter_macro_future counts 0 (t/(n+1)) i hi)
    WM WT z hzM hzT hmproj htproj
  exact hfinal

end Bilevel.TransportHierarchy
