import Bilevel.TransportRoundFrozenProjection
import Bilevel.TransportRoundDimensionCap
import Bilevel.TransportRoundProbabilityCalibration

/-! A calibrated observer for the actual finite frozen-round NETWORK
controller. It covers stored and pre-transport query-augmented spaces under
the original law. Its conservative ambient dimension is public and finite.
Independent auxiliary-frame frontier release, terminal insertion, and the
nonlinear SFO transcript embedding remain separate obligations. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork TransportNetworkAuxiliary TransportControllerMachine
set_option maxHeartbeats 800000

def observerRank (n p T M : ℕ) (b δ : ℝ) : ℕ :=
  residualRank n p T M (queryTolerance n p M (b/2)) δ

def observerDimension (n p T M : ℕ) (b δ : ℝ) : ℕ :=
  geometryCap n p T M+observerRank n p T M b δ

theorem observerRank_pos (n p T M : ℕ) (b δ : ℝ) : 0<observerRank n p T M b δ :=
  residualRank_pos _ _ _ _ _ _

theorem observerDimension_ge_frame (n p T M : ℕ) (b δ : ℝ) : T≤observerDimension n p T M b δ :=
  (geometryCap_ge_frame n p T M).trans (Nat.le_add_right _ _)

theorem network_observer {n D T p k : ℕ} (H : Memory) (hT : T≤D) (hn : 0<n) (hpos : 0<T)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H) (hr : ∀ t,Measurable (respond t))
    (ρ : Measure H) [IsProbabilityMeasure ρ] (M : ℕ) {b δ : ℝ} (hb : 0<b) (hδ : 0<δ)
    (hD : observerDimension n p T M b δ≤D) :
    (ρ.prod (TransportNetworkAuxiliary.law n D k))
      {s | ¬ProjectionGood hT choose respond M b s.1 s.2.1}≤ENNReal.ofReal δ := by
  let r := observerRank n p T M b δ
  have hrpos : 0<r := observerRank_pos n p T M b δ
  have hdim : geometryCap n p T M+r≤D := hD
  have ha : 0<queryTolerance n p M (b/2) := queryTolerance_pos n p M (by positivity)
  have hp := actual_run_failure_probability (k := k) H hT hpos choose hc respond hr ρ M r hrpos _ ha
    (geometryCap_query hdim) (geometryCap_edge hdim)
  have hsub : {s : H × Sample n D k | ¬ProjectionGood hT choose respond M b s.1 s.2.1}⊆
      {s | (s.1,s.2.1)∈runFailureEvent hT (queryTolerance n p M (b/2)) choose respond M} := by
    intro s hs
    by_contra hnone
    apply hs
    apply projectionGood_of_no_failure hT hn hpos choose respond s.1 s.2.1 M hb
    intro t ht hfail
    exact hnone ⟨t,ht,hfail⟩
  exact ((measure_mono hsub).trans hp).trans (calibrated_runBudget n p T M ha hδ)

end Bilevel.TransportRound
