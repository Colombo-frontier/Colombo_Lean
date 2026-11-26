import Bilevel.TransportHierarchyStoreGram
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

theorem sourcePhysical_store_hessian {H : Type*} (macroN J n D p s : ℕ)
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
    (P : ChiFine.Parameters) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (dn : ℝ)
    (hcomplete : ∀ (dim' : ℕ) (Q : Rotations n dim')
      (U : Space macroN →ₗᵢ[ℝ] Block dim')
      (V : ∀ j,List ℕ → Space (sourceChainIndex cn (ratios j) (resolutions j)) →ₗᵢ[ℝ] Block dim'),
      let M' := ChiOuter.sourceMacroNode macroN initial Km U
      let G' := sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR V
      let rad' := fun j => weight j*(G' j []).nu
      let R' := fun j => (G' j []).radius
      ContDiff ℝ 3 (physicalHierarchyExtension Q M' G' P J s index radialIndex fineIndex rad' R' dn) ∧
      ∀ z,‖iteratedFDeriv ℝ 2 (physicalHierarchyExtension Q M' G' P J s index radialIndex fineIndex rad' R' dn) z‖≤(1:ℝ)/12)
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
      (fun j => weight j*(G j []).nu) (fun j => (G j []).radius) dn
      (counter counts (J+1) q 0 []) (canonicalCounter counts J q) (canonicalCounter counts J (q+1))
      data.1 data.2.1 data.2.2.1 data.2.2.2
    ContDiff ℝ 3 f ∧ ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(1:ℝ)/12 := by
  let counts := sourceCounts macroN cn ratios resolutions
  have hp := hierarchyStoreData_prefix counts J hdim hT hAll hA sample choose respond memory t
  have hgram := hierarchyStoreData_gram counts J hdim hT hAll hA sample choose respond memory t
  dsimp only at hp hgram ⊢
  let q : EndpointTransportMatrix.Index n → ℕ := fun v => if v=0 then t/(n+1)+1 else t/(n+1)
  have hzero : q 0=t/(n+1)+1 := by simp [q]
  have hlast : q (Fin.last (n+1))=t/(n+1) := by
    have hne : Fin.last (n+1)≠(0 : EndpointTransportMatrix.Index n) := by
      intro he
      have hv := congrArg Fin.val he
      change n+1=0 at hv
      omega
    exact if_neg hne
  have hh := observable_source_prefix_hessian (n:=n) (J:=J) macroN cn ratios resolutions
    (hAll (Sum.inl ())) hdim hT initial weight A Kminus ζ CR Km
    (physicalMacroFrame hAll sample) (physicalFamily hdim hT sample) P index radialIndex fineIndex dn sample.1 q
    (counter counts (J+1) (t/(n+1)) 0 []) _ hgram.1 _
    (fun j I hj => by rw [hlast];exact hgram.2.1 j I hj) _ _
    (fun I k hk => by rw [hzero] at hk;simpa only [physicalFamily_terminal] using hp.2.2.1 I k hk)
    (fun I k hk => by rw [hlast] at hk;simpa only [physicalFamily_terminal] using hp.2.2.2 I k hk)
    hcomplete
  simpa only [hzero,hlast] using hh

end Bilevel.TransportHierarchy
