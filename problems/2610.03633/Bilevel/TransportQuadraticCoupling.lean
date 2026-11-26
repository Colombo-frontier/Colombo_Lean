import Bilevel.TransportQuadraticObservedReply

/-! Exact original/compiled adaptive states and outputs on the same measured event.
Every program state is preserved, including absorbing halt states. -/
noncomputable section
open MeasureTheory
universe u v
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
  ChiHierarchyExecution EndpointTransportResponse TransportRound TransportNetwork
  PrimitiveGeometry PartialLegendre TransportAugmented
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem quadraticObserved_state_eq_original {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
    (macroN n D : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
    (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
    (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤D)
    (hT : capacity (sourceCounts macroN cn ratios resolutions) 1 0≤D)
    (hA : auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) 0+1≤D)
    (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km ν ρ R δ c : ℝ)
    [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]
    [MeasurableSpace (QuadraticOutput D)] [BorelSpace (QuadraticOutput D)]
    [MeasurableSpace (QuadraticQuery n D)] [BorelSpace (QuadraticQuery n D)]
    (P : BorelAdaptive.Program S (QuadraticQuery n D) (QuadraticReply n D) (QuadraticOutput D))
    (start : C → S) (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)
    (τ : ℝ) (hτ : 0<τ) (N t : ℕ) (ht : t≤N)
    (s : C × PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D)
    (hobs : quadraticObserved macroN n D cn ratios resolutions hdim hAll hT hA initial weight
      A Kminus ζ CR Km ν ρ R δ c P start τ N s) :
    (quadraticRun macroN n D cn ratios resolutions hdim hAll hT hA initial weight
      A Kminus ζ CR Km ν ρ R δ c P start s t).1.2.2.1=
      BorelAdaptive.run P
        (fun sample query (_ : Unit) => quadraticOriginalReply macroN n D cn ratios resolutions hdim hAll hT
          initial weight A Kminus ζ CR Km ν ρ R δ c sample query)
        s.2 (fun _ => ()) (start s.1) t := by
  let counts := sourceCounts macroN cn ratios resolutions
  let schedule := auxiliaryRoundSchedule counts 0 (n+1) (Nat.succ_pos n)
  let evaluate := quadraticEvaluate macroN n D cn ratios resolutions hdim hAll hT initial weight
    A Kminus ζ CR Km ν ρ R δ c
  have h := TransportProgram.compiled_run_eq_original P
    quadraticNetworkQueries quadraticNetworkQueries_measurable
    quadraticAuxiliaryQueries quadraticAuxiliaryQueries_measurable
    quadraticNetworkOutput quadraticNetworkOutput_measurable
    quadraticAuxiliaryOutput quadraticAuxiliaryOutput_measurable
    evaluate (quadraticEvaluate_measurable macroN n D cn ratios resolutions hdim hAll hT initial weight
      A Kminus ζ CR Km ν ρ R δ c)
    schedule hT (prefixNames (n+1) (capacity counts 1 0))
    (initialMemoryAny hA start (s.1,s.2.2),seed (capacity counts 1 0) hT s.2.1) s.2.1
    (fun sample query (_ : Unit) => quadraticOriginalReply macroN n D cn ratios resolutions hdim hAll hT
      initial weight A Kminus ζ CR Km ν ρ R δ c sample query) s.2 t (by
      intro j hj
      dsimp only
      intro _
      exact quadraticObserved_reply macroN n D cn ratios resolutions hdim hAll hT hA initial weight
        A Kminus ζ CR Km ν ρ R δ c P start hl hw hr hη hη1 hweight hζ hCR hKm τ hτ N j
        (lt_of_lt_of_le hj ht) s hobs)
  exact h

end Bilevel.TransportHierarchy
