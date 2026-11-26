import Bilevel.TransportHierarchyStoreHessian
import Bilevel.TransportHierarchySourceGeometry
import Bilevel.EndpointTransportObservablePrefixHessian

/-! Actual old stores imply the global prefix Hessian bound. The uniform
core certificate is the analytic one from the physical witness; no Gram
conditions or hidden completion vectors remain as execution hypotheses. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiExtensionCalibration
  ChiHierarchyHaar TransportRound TransportNetwork EndpointTransportResponse ChiExtension
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem sourcePhysical_store_hessian_public {H : Type*} (macroN J n D p s : ℕ)
    (cn : ℝ) (ratios resolutions : ℕ → ℝ)
    (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
    (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤D)
    (hT : capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0≤D)
    (hA : auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) J+1≤D)
    (sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D)
    (choose : ∀ t,H × Generators (n+1) D (size (n+1) p 1 1 t) → Queries (n+1) D p)
    (respond : ∀ t,StepData H (n+1) D (size (n+1) p 1 1 t) p
      (capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0) → H)
    (memory : H) (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)
    (ρ R : ℕ → ℝ) (P : ChiFine.Parameters) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (dn : ℝ)
    (hcomplete : ∀ (dim' : ℕ) (Q : Rotations n dim')
      (U : Space macroN →ₗᵢ[ℝ] Block dim')
      (V : ∀ j,List ℕ → Space (sourceChainIndex cn (ratios j) (resolutions j)) →ₗᵢ[ℝ] Block dim'),
      let M' := ChiOuter.sourceMacroNode macroN initial Km U
      let G' := sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR V
      let rad' := fun j => weight j*(G' j []).nu
      let R' := fun j => (G' j []).radius
      ContDiff ℝ 3 (physicalHierarchyExtension Q M' G' P J s index radialIndex fineIndex rad' R' dn) ∧
      ∀ z,‖iteratedFDeriv ℝ 2 (physicalHierarchyExtension Q M' G' P J s index radialIndex fineIndex rad' R' dn) z‖≤(1:ℝ)/12)
    (hρ : ∀ j,ρ j=weight j*(sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT sample initial weight A Kminus ζ CR j []).nu)
    (hR : ∀ j,R j=(sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT sample initial weight A Kminus ζ CR j []).radius)
    (t : ℕ) :
    let counts := sourceCounts macroN cn ratios resolutions
    let M := sourcePhysicalMacro macroN J n D cn ratios resolutions hAll sample initial Km
    let G := sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT sample initial weight A Kminus ζ CR
    let C := TransportAuxiliaryFrame.actualStore (auxiliaryRoundSchedule counts J (n+1) (Nat.succ_pos n)) t
      (fun a => TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity counts J+1) hA a sample)
    let g := (run (capacity counts (J+1) 0) hT choose respond (prefixNames (n+1) (capacity counts (J+1) 0))
      (memory,seed (capacity counts (J+1) 0) hT sample.1) sample.1 t).2
    let data := hierarchyStoreData counts J p t C g
    let q := t/(n+1)
    let f := prefixPhysicalHierarchyExtension M G P index radialIndex fineIndex
      ρ R dn
      (counter counts (J+1) q 0 []) (canonicalCounter counts J q) (canonicalCounter counts J (q+1))
      data.1 data.2.1 data.2.2.1 data.2.2.2
    ContDiff ℝ 3 f ∧ ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(1:ℝ)/12 := by
  have h := sourcePhysical_store_hessian macroN J n D p s cn ratios resolutions hdim hAll hT hA sample
    choose respond memory initial weight A Kminus ζ CR Km P index radialIndex fineIndex dn hcomplete t
  dsimp only at h ⊢
  simpa only [funext hρ,funext hR] using h

end Bilevel.TransportHierarchy
