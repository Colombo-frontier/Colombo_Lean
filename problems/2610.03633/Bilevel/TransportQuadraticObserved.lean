import Bilevel.TransportQuadraticExecution

/-! The measurable SAME-RUN event used by the quadratic compiler. The
auxiliary observer includes every retained column, and its macro energy
uses the exact old scheduled count floor(t/(n+1)). -/
noncomputable section
open MeasureTheory
universe u v
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
  ChiHierarchyExecution EndpointTransportResponse TransportRound TransportNetwork
  PrimitiveGeometry PartialLegendre TransportAugmented
set_option autoImplicit false
set_option maxHeartbeats 1200000

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

def quadraticObserved (τ : ℝ) (N : ℕ)
    (s : C × PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D) : Prop :=
  let counts := sourceCounts macroN cn ratios resolutions
  let ctl := quadraticController (C:=C) macroN n D cn ratios resolutions hdim hAll hT initial weight
    A Kminus ζ CR Km ν ρ R δ c P
  let cap := sourcePublicCap macroN 0 initial ratios resolutions weight CR ζ Km τ
  CompleteGoodAny (auxiliaryRoundSchedule counts 0 (n+1) (Nat.succ_pos n)) (enlargeBatch ctl) hT hA
    (by omega)
    start N (Real.sqrt cap/EndpointTransportMatrix.gamma n) cap
    (fun _ => ctl.auxiliaryOutput) (fun _ => ctl.auxiliaryOutput_measurable) s

theorem quadraticObserved_measurable (σ : Measure C) [IsProbabilityMeasure σ]
    (hs : Measurable start) (τ : ℝ) (N : ℕ) :
    MeasurableSet {s | quadraticObserved macroN n D cn ratios resolutions hdim hAll hT hA initial weight
      A Kminus ζ CR Km ν ρ R δ c P start τ N s} := by
  let counts := sourceCounts macroN cn ratios resolutions
  let ctl := quadraticController (C:=C) macroN n D cn ratios resolutions hdim hAll hT initial weight
    A Kminus ζ CR Km ν ρ R δ c P
  let cap := sourcePublicCap macroN 0 initial ratios resolutions weight CR ζ Km τ
  have hk : 0<Fintype.card (FrameIndex counts 0) := Fintype.card_pos_iff.mpr ⟨Sum.inl ()⟩
  exact completeGoodAny_measurable hk σ
    (auxiliaryRoundSchedule counts 0 (n+1) (Nat.succ_pos n)) (enlargeBatch ctl) hT hA
    (by omega) start hs N (Real.sqrt cap/EndpointTransportMatrix.gamma n) cap
    (fun _ => ctl.auxiliaryOutput) (fun _ => ctl.auxiliaryOutput_measurable)

theorem quadraticObserved_energy (τ : ℝ) (N t : ℕ) (ht : t<N)
    (s : C × PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D)
    (hobs : quadraticObserved macroN n D cn ratios resolutions hdim hAll hT hA initial weight
      A Kminus ζ CR Km ν ρ R δ c P start τ N s) :
    let counts := sourceCounts macroN cn ratios resolutions
    let ctl := quadraticController (C:=C) macroN n D cn ratios resolutions hdim hAll hT initial weight
      A Kminus ζ CR Km ν ρ R δ c P
    let st := quadraticRun macroN n D cn ratios resolutions hdim hAll hT hA initial weight
      A Kminus ζ CR Km ν ρ R δ c P start s t
    GenieProtocol.BoundedEnergy (analyticalAuxSpaceAny ctl t (st.1.2,st.2))
      (prefixSet (counter counts 1 (t/(n+1)) 0 []))
      (TransportNetworkAuxiliary.auxiliaryFrame (auxiliaryCapacity counts 0+1) hA (enumerate counts 0 (Sum.inl ())) s.2)
      (sourcePublicCap macroN 0 initial ratios resolutions weight CR ζ Km τ) := by
  let counts := sourceCounts macroN cn ratios resolutions
  let ctl := quadraticController (C:=C) macroN n D cn ratios resolutions hdim hAll hT initial weight
    A Kminus ζ CR Km ν ρ R δ c P
  let schedule := auxiliaryRoundSchedule counts 0 (n+1) (Nat.succ_pos n)
  have hk : 0<Fintype.card (FrameIndex counts 0) := Fintype.card_pos_iff.mpr ⟨Sum.inl ()⟩
  have hB : 0<Fintype.card (FrameIndex counts 0)*(auxiliaryCapacity counts 0+1)+1 := by omega
  have h := analyticalAuxSpaceAny_energy hk schedule ctl hT hA (enumerate counts 0 (Sum.inl ())) hB start
    (fun _ => ctl.auxiliaryOutput) (fun _ => ctl.auxiliaryOutput_measurable)
    (sourcePublicCap macroN 0 initial ratios resolutions weight CR ζ Km τ) s N t ht
    (hobs.2 (enumerate counts 0 (Sum.inl ())))
  simpa only [TransportAuxiliaryFrame.knownPrefix,schedule,auxiliaryRoundSchedule_macro,prefixSet] using h

end Bilevel.TransportHierarchy
