import Bilevel.TransportHierarchySourceGeometry
import Bilevel.TransportHierarchyAuxiliaryReadout
import Bilevel.TransportHierarchyEndpointReadout
import Bilevel.EndpointTransportPrefixContinuity

/-! Exact depth-zero disclosed scalar data from the current auxiliary
store and finite network generator store. The source endpoint advances
one GLOBAL terminal coordinate; only reachable macro branches use it. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
  ChiHierarchyHaar TransportRound TransportNetwork EndpointTransportResponse
set_option maxHeartbeats 1000000

def quadraticSourceData (macroN n D p t : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
    (C : TransportAuxiliaryFrame.Store
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) 0))
      (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) 0) D)
    (g : Generators (n+1) D (size (n+1) p 1 1 t)) :
    (Fin (macroN+1) → EuclideanGaussian.Space D) ×
      ((Fin (macroN+1) → Fin (sourceChainIndex cn (ratios 0) (resolutions 0)+1) → Physical n D) ×
       (Fin (macroN+1) → Fin (sourceChainIndex cn (ratios 0) (resolutions 0)+1) → Physical n D)) :=
  (auxiliaryStoreReadout (sourceCounts macroN cn ratios resolutions) 0 C (Sum.inl ()),
    (fun i => endpointReadout (sourceCounts macroN cn ratios resolutions) 0 p t g 0 [i.val],
     fun i => endpointReadout (sourceCounts macroN cn ratios resolutions) 0 p t g (Fin.last (n+1)) [i.val]))

theorem quadraticSourceData_measurable (macroN n D p t : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
    [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)] :
    Measurable (fun z : TransportAuxiliaryFrame.Store
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) 0))
      (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) 0) D ×
        Generators (n+1) D (size (n+1) p 1 1 t) =>
          quadraticSourceData macroN n D p t cn ratios resolutions z.1 z.2) := by
  apply Measurable.prodMk
  · exact ((measurable_pi_apply (Sum.inl ())).comp
      (auxiliaryStoreReadout_measurable (sourceCounts macroN cn ratios resolutions) 0)).comp measurable_fst
  · apply Measurable.prodMk <;> apply measurable_pi_lambda <;> intro i
    · exact ((measurable_pi_apply [i.val]).comp
        (endpointReadout_measurable (sourceCounts macroN cn ratios resolutions) 0 p t 0)).comp measurable_snd
    · exact ((measurable_pi_apply [i.val]).comp
        (endpointReadout_measurable (sourceCounts macroN cn ratios resolutions) 0 p t (Fin.last (n+1)))).comp measurable_snd

variable {H : Type*} (macroN n D p : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) 1 0≤D)
  (hA : auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) 0+1≤D)
  (s : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D)
  (choose : ∀ t,H × Generators (n+1) D (size (n+1) p 1 1 t) → Queries (n+1) D p)
  (respond : ∀ t,StepData H (n+1) D (size (n+1) p 1 1 t) p
    (capacity (sourceCounts macroN cn ratios resolutions) 1 0) → H)
  (memory : H) (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)

theorem quadraticSourceData_prefix (t : ℕ) :
    let counts := sourceCounts macroN cn ratios resolutions
    let M := sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll s initial Km
    let G := sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR
    let C := TransportAuxiliaryFrame.actualStore (auxiliaryRoundSchedule counts 0 (n+1) (Nat.succ_pos n)) t
      (fun a => TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity counts 0+1) hA a s)
    let g := (run (capacity counts 1 0) hT choose respond (prefixNames (n+1) (capacity counts 1 0))
      (memory,seed (capacity counts 1 0) hT s.1) s.1 t).2
    let data := quadraticSourceData macroN n D p t cn ratios resolutions C g
    let q := t/(n+1)
    (∀ k : Fin (macroN+1),k.val<counter counts 1 q 0 [] → data.1 k=M.frame (basis k)) ∧
    (∀ i : Fin (macroN+1),i.val≤counter counts 1 q 0 [] →
      ∀ k : Fin (sourceChainIndex cn (ratios 0) (resolutions 0)+1),
        k.val<canonicalCounter counts 0 q 0 [i.val]+1 →
        data.2.1 i k=endpointFrame (physicalRotations s.1) (G 0 [i.val]).frame 0 (basis k)) ∧
    (∀ i : Fin (macroN+1),∀ k : Fin (sourceChainIndex cn (ratios 0) (resolutions 0)+1),
      k.val<canonicalCounter counts 0 q 0 [i.val] →
        data.2.2 i k=endpointFrame (physicalRotations s.1) (G 0 [i.val]).frame (Fin.last (n+1)) (basis k)) := by
  dsimp only
  constructor
  · intro k hk
    exact auxiliaryStoreReadout_macro hAll hA (n+1) (Nat.succ_pos n) s t k hk
  constructor
  · intro i hi k hk
    have hk' := canonical_reachable_source_prefix
      (sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR)
      (sourceCounts macroN cn ratios resolutions) (fun _ _ => rfl) (t/(n+1)) i hi k hk
    have hh := endpointSourceReadout_prefix (sourceCounts macroN cn ratios resolutions) 0 hT
      choose respond memory s.1 t [i.val] k hk'
    simpa only [quadraticSourceData,sourcePhysicalGeometry_frame,physicalFamily_terminal] using hh
  · intro i k hk
    have hh := endpointTargetReadout_prefix (sourceCounts macroN cn ratios resolutions) 0 hT
      choose respond memory s.1 t [i.val] k hk
    simpa only [quadraticSourceData,sourcePhysicalGeometry_frame,physicalFamily_terminal] using hh

end Bilevel.TransportHierarchy
