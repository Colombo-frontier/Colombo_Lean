import Bilevel.TransportAugmentedPositiveFrames
import Bilevel.OrdinaryFrameEnergy

/-! Borel common runs and actual terminal-coordinate bounds for any
positive finite auxiliary family, with its original indexing unchanged. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
universe u v
namespace Bilevel.TransportAugmented
open EuclideanGaussian TransportNetwork TransportRound ProjectionGeometry
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  {n D p Tnet k T B : ℕ}

theorem initialMemoryAny_measurable (hT : T+1≤D) (initial : C → S) (hi : Measurable initial) :
    Measurable (initialMemoryAny (k:=k) hT initial) := by
  refine Measurable.prodMk ?_ (measurable_fst.prodMk ((hi.comp measurable_fst).prodMk measurable_const))
  apply measurable_pi_lambda
  intro i
  exact (HaarFrame.frame_measurable D (T+1) hT).comp ((measurable_pi_apply i).comp measurable_snd)

theorem masterRunAny_measurable (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet≤D) (hT : T+1≤D)
    (initial : C → S) (hi : Measurable initial) (N : ℕ) :
    Measurable (fun s : C × TransportNetworkAuxiliary.Sample n D k => masterRunAny P A hTnet hT initial s N) := by
  have hm := (initialMemoryAny_measurable (k:=k) hT initial hi).comp
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd) :
      Measurable (fun s : C × TransportNetworkAuxiliary.Sample n D k => (s.1,s.2.2)))
  have hz : Measurable (fun s : C × TransportNetworkAuxiliary.Sample n D k => s.2.1) :=
    measurable_fst.comp measurable_snd
  have hseed := (seed_measurable Tnet hTnet).comp hz
  have h := (networkRun_measurable P A hTnet (prefixNames n Tnet) N).comp ((hm.prodMk hseed).prodMk hz)
  exact h

theorem FrameObservedAny.terminal_inner (hk : 0<k) (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet≤D) (hT : T+1≤D)
    (i : Fin k) (hB : 0<B) (initial : C → S)
    (output : Fin k → CommonState C S k T D → Space D) (ho : ∀ i,Measurable (output i))
    (cap : ℝ) (hcap : 0≤cap) (s : C × TransportNetworkAuxiliary.Sample n D k) (N : ℕ)
    (h : FrameObservedAny P A hTnet hT hB initial N cap output ho i s)
    (col : Fin (T+1)) (hc : P.count N i≤col.val) :
    |⟪TransportNetworkAuxiliary.auxiliaryFrame (T+1) hT i s.2 col,
      output i (masterRunAny P A hTnet hT initial s N).1.2⟫|≤
      Real.sqrt cap*‖output i (masterRunAny P A hTnet hT initial s N).1.2‖ := by
  cases k with
  | zero => omega
  | succ j =>
    have hp := TransportAuxiliaryFrame.originalObserved_projectionGood P
      (auxiliaryDriver (withAuxiliaryOutput A (output i) (ho i)) hTnet (prefixNames n Tnet))
      hT i hB N (auxiliaryInitial hTnet initial) cap s h
    exact OrdinaryFrame.boundedEnergy_inner _ _ _ cap hcap hp.2 _
      (selected_output_mem P A hTnet hT i hB initial output ho s N) col
      (show col∉TransportAuxiliaryFrame.knownPrefix P N i by exact not_lt.mpr hc)

end Bilevel.TransportAugmented
