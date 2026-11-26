import Bilevel.TransportPhysicalEvaluator
import Bilevel.TransportProgramCoupling
import Bilevel.TransportAugmentedAnyStore

/-! Compiling every Borel adaptive program into the same physical network
and auxiliary-frame execution. The full original query is fixed before
the network batch, including all ordinary lower coordinates. -/
noncomputable section
open MeasureTheory
universe u v
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
  EndpointTransportResponse TransportRound TransportNetwork PrimitiveGeometry PartialLegendre
  TransportAugmented ChiExtension
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  (macroN J n D s : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0≤D)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km ν : ℝ) (fine : ChiFine.Parameters)
  (index radialIndex : Fin J → Fin s) (fineIndex : Fin s)
  (ρ R : ℕ → ℝ) (dn : ℝ) (b : Normals s) (m δ c₀ cend : ℝ)
  [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]
  [MeasurableSpace (PhysicalOutput J D)] [BorelSpace (PhysicalOutput J D)]
  [MeasurableSpace (PhysicalQuery J n D s)] [BorelSpace (PhysicalQuery J n D s)]

def physicalController (P : BorelAdaptive.Program S (PhysicalQuery J n D s) (PhysicalReply J n D s) (PhysicalOutput J D)) :
    Controller C S (n+1) D 1 (capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0)
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) J))
      (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) J) (J+1) :=
  TransportProgram.controller P physicalNetworkQueries physicalNetworkQueries_measurable
    physicalAuxiliaryQueries physicalAuxiliaryQueries_measurable
    physicalNetworkOutput physicalNetworkOutput_measurable
    physicalAuxiliaryOutput physicalAuxiliaryOutput_measurable
    (physicalEvaluate macroN J n D s cn ratios resolutions hdim hAll hT initial weight
      A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend)
    (physicalEvaluate_measurable macroN J n D s cn ratios resolutions hdim hAll hT initial weight
      A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend)

theorem physicalController_network_query
    (P : BorelAdaptive.Program S (PhysicalQuery J n D s) (PhysicalReply J n D s) (PhysicalOutput J D))
    (t : ℕ)
    (st : CommonState C S (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) J))
      (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) J) D × Generators (n+1) D (size (n+1) 1 1 1 t))
    (v : EndpointTransportMatrix.Index n) :
    (physicalController macroN J n D s cn ratios resolutions hdim hAll hT initial weight
      A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P).choose t st v 0=
      (P.query st.1.2.1).snd.fst.snd v := rfl

theorem physicalController_auxiliary_query
    (P : BorelAdaptive.Program S (PhysicalQuery J n D s) (PhysicalReply J n D s) (PhysicalOutput J D))
    (t : ℕ)
    (st : CommonState C S (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) J))
      (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) J) D × Generators (n+1) D (size (n+1) 1 1 1 t))
    (a : Fin (J+1)) :
    (physicalController macroN J n D s cn ratios resolutions hdim hAll hT initial weight
      A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P).auxiliaryQueries t st a=
      physicalAuxiliaryQueries (P.query st.1.2.1) a := rfl

end Bilevel.TransportHierarchy
