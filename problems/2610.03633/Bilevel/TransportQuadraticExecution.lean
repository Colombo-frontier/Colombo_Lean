import Bilevel.TransportQuadraticCompiler

/-! The literal same-prior execution of the quadratic compiler and its
current-query inclusions. Stored prefixes are the scheduled actual frame
prefixes, and both queried points enter the PREBATCH analytical spaces. -/
noncomputable section
open MeasureTheory
universe u v
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
  EndpointTransportResponse TransportRound TransportNetwork PrimitiveGeometry PartialLegendre TransportAugmented
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
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
  (start : C → S)

def quadraticRun (s : C × PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D) (t : ℕ) :=
  masterRunAny (auxiliaryRoundSchedule (sourceCounts macroN cn ratios resolutions) 0 (n+1) (Nat.succ_pos n))
    (quadraticController macroN n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R δ c P)
    hT hA start s t

theorem quadraticRun_measurable (hs : Measurable start) (t : ℕ) :
    Measurable (fun s => quadraticRun macroN n D cn ratios resolutions hdim hAll hT hA initial weight
      A Kminus ζ CR Km ν ρ R δ c P start s t) :=
  masterRunAny_measurable _ _ hT hA start hs t

theorem quadraticRun_prefix
    (s : C × PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D) (t : ℕ) :
    (quadraticRun macroN n D cn ratios resolutions hdim hAll hT hA initial weight
      A Kminus ζ CR Km ν ρ R δ c P start s t).1.2.2.2=
      TransportAuxiliaryFrame.actualStore
        (auxiliaryRoundSchedule (sourceCounts macroN cn ratios resolutions) 0 (n+1) (Nat.succ_pos n)) t
        (fun i => TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) 0+1)
          hA i s.2) := by
  apply masterRunAny_prefix
  exact Fintype.card_pos_iff.mpr ⟨Sum.inl ()⟩

theorem quadraticRun_query_membership
    (s : C × PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D) (t : ℕ) :
    let counts := sourceCounts macroN cn ratios resolutions
    let schedule := auxiliaryRoundSchedule counts 0 (n+1) (Nat.succ_pos n)
    let ctl := quadraticController (C:=C) macroN n D cn ratios resolutions hdim hAll hT initial weight
      A Kminus ζ CR Km ν ρ R δ c P
    let st := quadraticRun macroN n D cn ratios resolutions hdim hAll hT hA initial weight
      A Kminus ζ CR Km ν ρ R δ c P start s t
    let w := P.query st.1.2.2.1
    w.fst.fst∈analyticalAuxSpaceAny ctl t (st.1.2,st.2) ∧
      w.snd (Fin.last (n+1))∈terminalPreSpace counts 0 hT (networkChoose ctl) (networkRespond schedule ctl)
        (initialMemoryAny hA start (s.1,s.2.2)) s.2.1 t (Fin.last (n+1)) := by
  dsimp only
  constructor
  · exact analyticalAuxSpaceAny_query _ t _ 0
  · exact terminalPreSpace_query (sourceCounts macroN cn ratios resolutions) 0 hT
      (networkChoose (quadraticController (C:=C) macroN n D cn ratios resolutions hdim hAll hT initial weight
        A Kminus ζ CR Km ν ρ R δ c P))
      (networkRespond (auxiliaryRoundSchedule (sourceCounts macroN cn ratios resolutions) 0 (n+1) (Nat.succ_pos n))
        (quadraticController (C:=C) macroN n D cn ratios resolutions hdim hAll hT initial weight
          A Kminus ζ CR Km ν ρ R δ c P))
      (initialMemoryAny hA start (s.1,s.2.2)) s.2.1 t (Fin.last (n+1)) 0

end Bilevel.TransportHierarchy
