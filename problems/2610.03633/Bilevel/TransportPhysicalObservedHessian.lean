import Bilevel.TransportPhysicalObserved
import Bilevel.TransportHierarchyStoreHessianPublic
import Bilevel.EndpointTransportNormalKnown
import Bilevel.TransportPhysicalOutput
import Bilevel.TransportAugmentedBudgetProbability

/-! Uniform core certificates imply the analytic Hessian certificate of the
actual compiled old store. No projection or reply hypothesis is required. -/
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



theorem physicalRun_prefix_hessian
    (hcomplete : ∀ (dim' : ℕ) (Q : Rotations n dim')
      (U : Space macroN →ₗᵢ[ℝ] Block dim')
      (V : ∀ j,List ℕ → Space (sourceChainIndex cn (ratios j) (resolutions j)) →ₗᵢ[ℝ] Block dim'),
      let M' := ChiOuter.sourceMacroNode macroN initial Km U
      let G' := sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR V
      let rad' := fun j => weight j*(G' j []).nu
      let R' := fun j => (G' j []).radius
      ContDiff ℝ 3 (physicalHierarchyExtension Q M' G' fine J s index radialIndex fineIndex rad' R' dn) ∧
      ∀ z,‖iteratedFDeriv ℝ 2 (physicalHierarchyExtension Q M' G' fine J s index radialIndex fineIndex rad' R' dn) z‖≤(1:ℝ)/12)
    (ω : C × PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D) (t : ℕ)
    (hρ : ∀ j,ρ j=weight j*(sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT ω.2 initial weight A Kminus ζ CR j []).nu)
    (hR : ∀ j,R j=(sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT ω.2 initial weight A Kminus ζ CR j []).radius) :
    let counts := sourceCounts macroN cn ratios resolutions
    let st := physicalRun macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start ω t
    let M := sourcePhysicalMacro macroN J n D cn ratios resolutions hAll ω.2 initial Km
    let G := sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT ω.2 initial weight A Kminus ζ CR
    let data := hierarchyStoreData counts J 1 t st.1.2.2.2 st.2
    let f := prefixPhysicalHierarchyExtension M G fine index radialIndex fineIndex ρ R dn
      (counter counts (J+1) (t/(n+1)) 0 []) (canonicalCounter counts J (t/(n+1)))
      (canonicalCounter counts J (t/(n+1)+1)) data.1 data.2.1 data.2.2.1 data.2.2.2
    ContDiff ℝ 3 f ∧ ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(1:ℝ)/12 := by
  let counts := sourceCounts macroN cn ratios resolutions
  let schedule := auxiliaryRoundSchedule counts J (n+1) (Nat.succ_pos n)
  let ctl := physicalController (C:=C) macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P
  have h := sourcePhysical_store_hessian_public macroN J n D 1 s cn ratios resolutions hdim hAll hT hA ω.2
    (networkChoose ctl) (networkRespond schedule ctl) (initialMemoryAny hA start (ω.1,ω.2.2))
    initial weight A Kminus ζ CR Km ρ R fine index radialIndex fineIndex dn hcomplete hρ hR t
  have hpfx := physicalRun_prefix macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start ω t
  dsimp only at h ⊢
  rw [hpfx]
  exact h

end Bilevel.TransportHierarchy
