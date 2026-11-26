import Bilevel.TransportQuadraticEvaluator
import Bilevel.TransportProgramCoupling
import Bilevel.TransportAugmentedAnyStore

/-! An arbitrary adaptive program is compiled into the actual common
network/auxiliary execution for the quadratic source. Every coefficient
and template is public; the compiler receives no sampled orientation. -/
noncomputable section
open MeasureTheory
universe u v
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
  EndpointTransportResponse TransportRound TransportNetwork PrimitiveGeometry PartialLegendre
  TransportAugmented
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  (macroN n D : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) 1 0≤D)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km ν ρ R δ c : ℝ)
  [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]
  [MeasurableSpace (QuadraticOutput D)] [BorelSpace (QuadraticOutput D)]
  [MeasurableSpace (QuadraticQuery n D)] [BorelSpace (QuadraticQuery n D)]

def quadraticController (P : BorelAdaptive.Program S (QuadraticQuery n D) (QuadraticReply n D) (QuadraticOutput D)) :
    Controller C S (n+1) D 1 (capacity (sourceCounts macroN cn ratios resolutions) 1 0)
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) 0))
      (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) 0) 1 :=
  TransportProgram.controller P quadraticNetworkQueries quadraticNetworkQueries_measurable
    quadraticAuxiliaryQueries quadraticAuxiliaryQueries_measurable
    quadraticNetworkOutput quadraticNetworkOutput_measurable
    quadraticAuxiliaryOutput quadraticAuxiliaryOutput_measurable
    (quadraticEvaluate macroN n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R δ c)
    (quadraticEvaluate_measurable macroN n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R δ c)

theorem quadraticController_network_query
    (P : BorelAdaptive.Program S (QuadraticQuery n D) (QuadraticReply n D) (QuadraticOutput D))
    (t : ℕ)
    (st : CommonState C S (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) 0))
      (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) 0) D × Generators (n+1) D (size (n+1) 1 1 1 t))
    (v : EndpointTransportMatrix.Index n) :
    (quadraticController macroN n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R δ c P).choose t st v 0=
      (P.query st.1.2.1).snd v := rfl

theorem quadraticController_auxiliary_query
    (P : BorelAdaptive.Program S (QuadraticQuery n D) (QuadraticReply n D) (QuadraticOutput D))
    (t : ℕ)
    (st : CommonState C S (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) 0))
      (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) 0) D × Generators (n+1) D (size (n+1) 1 1 1 t)) :
    (quadraticController macroN n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R δ c P).auxiliaryQueries t st 0=
      (P.query st.1.2.1).fst.fst := rfl

end Bilevel.TransportHierarchy
