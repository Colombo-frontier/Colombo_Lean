import Bilevel.TransportAugmentedAnySupport

/-! Literal scheduled store and projection-energy identities for the same
arbitrary-cardinality augmented execution. -/
noncomputable section
open MeasureTheory
universe u v
namespace Bilevel.TransportAugmented
open EuclideanGaussian TransportNetwork TransportRound ProjectionGeometry
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  {n D p Tnet k T B : ℕ}

theorem masterRunAny_prefix (hk : 0<k) (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet≤D) (hT : T+1≤D)
    (initial : C → S) (s : C × TransportNetworkAuxiliary.Sample n D k) (N : ℕ) :
    (masterRunAny P A hTnet hT initial s N).1.2.2.2=
      TransportAuxiliaryFrame.actualStore P N
        (fun i => TransportNetworkAuxiliary.auxiliaryFrame (T+1) hT i s.2) := by
  cases k with
  | zero => omega
  | succ j =>
    have he := congrArg (fun z => z.2.2) (original_auxiliary_eq_master P A hTnet hT initial s N)
    have hp := TransportAuxiliaryFrame.originalRun_prefix P
      (auxiliaryDriver A hTnet (prefixNames n Tnet)) hT (auxiliaryInitial hTnet initial) s N
    exact he.symm.trans hp

theorem analyticalAuxSpaceAny_energy (hk : 0<k) (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet≤D) (hT : T+1≤D)
    (i : Fin k) (hB : 0<k*(T+1)+B) (initial : C → S)
    (output : Fin k → CommonState C S k T D → Space D) (ho : ∀ i,Measurable (output i)) (cap : ℝ)
    (s : C × TransportNetworkAuxiliary.Sample n D k) (N t : ℕ) (ht : t<N)
    (h : FrameObservedAny P (enlargeBatch A) hTnet hT hB initial N cap output ho i s) :
    GenieProtocol.BoundedEnergy
      (analyticalAuxSpaceAny A t ((masterRunAny P A hTnet hT initial s t).1.2,
        (masterRunAny P A hTnet hT initial s t).2))
      (TransportAuxiliaryFrame.knownPrefix P t i)
      (TransportNetworkAuxiliary.auxiliaryFrame (T+1) hT i s.2) cap := by
  cases k with
  | zero => omega
  | succ j => exact analyticalAuxSpace_energy P A hTnet hT i hB initial output ho cap s N t ht h

end Bilevel.TransportAugmented
