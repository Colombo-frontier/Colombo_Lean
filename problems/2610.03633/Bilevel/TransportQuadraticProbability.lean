import Bilevel.TransportQuadraticObserved
import Bilevel.TransportAugmentedBudgetProbability

/-! The actual quadratic same-run event has the calibrated failure bound.
No independent concentration or transcript premise is supplied. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
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

theorem quadraticObserved_failure (σ : Measure C) [IsProbabilityMeasure σ]
    (hs : Measurable start) (τ β : ℝ) (hβ : 0<β)
    (hc : 0<sourcePublicCap macroN 0 initial ratios resolutions weight CR ζ Km τ) (N : ℕ)
    (hbudget : ObserverBudget (n+1) 1 (capacity (sourceCounts macroN cn ratios resolutions) 1 0)
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) 0))
      (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) 0)
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) 0)*
        (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) 0+1)+1) D N
      (Real.sqrt (sourcePublicCap macroN 0 initial ratios resolutions weight CR ζ Km τ)/EndpointTransportMatrix.gamma n)
      (sourcePublicCap macroN 0 initial ratios resolutions weight CR ζ Km τ) β) :
    (σ.prod (TransportNetworkAuxiliary.law (n+1) D
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) 0))))
      {s | ¬quadraticObserved macroN n D cn ratios resolutions hdim hAll hT hA initial weight
        A Kminus ζ CR Km ν ρ R δ c P start τ N s}≤ENNReal.ofReal β := by
  let counts := sourceCounts macroN cn ratios resolutions
  let ctl := quadraticController (C:=C) macroN n D cn ratios resolutions hdim hAll hT initial weight
    A Kminus ζ CR Km ν ρ R δ c P
  have hk : 0<Fintype.card (FrameIndex counts 0) := Fintype.card_pos_iff.mpr ⟨Sum.inl ()⟩
  exact complete_observer_of_budget hk σ
    (auxiliaryRoundSchedule counts 0 (n+1) (Nat.succ_pos n)) (enlargeBatch ctl) hT hA
    (Nat.succ_pos n) (capacity_pos counts 1 0) (by omega) start hs N
    (fun _ => ctl.auxiliaryOutput) (fun _ => ctl.auxiliaryOutput_measurable)
    (div_pos (Real.sqrt_pos.mpr hc) (gamma_positive n)) hβ hbudget

end Bilevel.TransportHierarchy
