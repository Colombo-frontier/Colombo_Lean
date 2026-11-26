import Bilevel.TransportPhysicalCompiler

/-! Literal same-prior execution and inclusion of each queried coordinate
in its prebatch analytical space. The common auxiliary space contains all
ordinary lower points before the frozen network answers are returned. -/
noncomputable section
open MeasureTheory
universe u v
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiExtensionCalibration
  EndpointTransportResponse TransportRound TransportNetwork PrimitiveGeometry PartialLegendre
  TransportAugmented ChiExtension
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

def physicalRun (ω : C × PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D) (t : ℕ) :=
  masterRunAny (auxiliaryRoundSchedule (sourceCounts macroN cn ratios resolutions) J (n+1) (Nat.succ_pos n))
    (physicalController macroN J n D s cn ratios resolutions hdim hAll hT initial weight
      A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P)
    hT hA start ω t

theorem physicalRun_measurable (hs : Measurable start) (t : ℕ) :
    Measurable (fun ω => physicalRun macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight
      A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start ω t) :=
  masterRunAny_measurable _ _ hT hA start hs t

theorem physicalRun_prefix
    (ω : C × PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D) (t : ℕ) :
    (physicalRun macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight
      A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start ω t).1.2.2.2=
      TransportAuxiliaryFrame.actualStore
        (auxiliaryRoundSchedule (sourceCounts macroN cn ratios resolutions) J (n+1) (Nat.succ_pos n)) t
        (fun i => TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) J+1)
          hA i ω.2) := by
  apply masterRunAny_prefix
  exact Fintype.card_pos_iff.mpr ⟨Sum.inl ()⟩

theorem physicalRun_query_membership
    (ω : C × PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D) (t : ℕ) :
    let counts := sourceCounts macroN cn ratios resolutions
    let schedule := auxiliaryRoundSchedule counts J (n+1) (Nat.succ_pos n)
    let ctl := physicalController (C:=C) macroN J n D s cn ratios resolutions hdim hAll hT initial weight
      A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P
    let st := physicalRun macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight
      A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start ω t
    let w := P.query st.1.2.2.1
    w.fst.fst.fst∈analyticalAuxSpaceAny ctl t (st.1.2,st.2) ∧
      (∀ j : Fin J,block J j.val w.snd.fst.fst∈analyticalAuxSpaceAny ctl t (st.1.2,st.2)) ∧
      (∀ v : EndpointTransportMatrix.Index n,w.snd.fst.snd v∈terminalPreSpace counts J hT
        (networkChoose ctl) (networkRespond schedule ctl)
        (initialMemoryAny hA start (ω.1,ω.2.2)) ω.2.1 t v) := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · exact analyticalAuxSpaceAny_query _ t _ 0
  · intro j
    exact analyticalAuxSpaceAny_query _ t _ j.succ
  · intro v
    exact terminalPreSpace_query (sourceCounts macroN cn ratios resolutions) J hT
      (networkChoose (physicalController (C:=C) macroN J n D s cn ratios resolutions hdim hAll hT initial weight
        A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P))
      (networkRespond (auxiliaryRoundSchedule (sourceCounts macroN cn ratios resolutions) J (n+1) (Nat.succ_pos n))
        (physicalController (C:=C) macroN J n D s cn ratios resolutions hdim hAll hT initial weight
          A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P))
      (initialMemoryAny hA start (ω.1,ω.2.2)) ω.2.1 t v 0

end Bilevel.TransportHierarchy
