import Bilevel.TransportControllerMachineForwardProbability

/-! The augmented prior projects to the original network law, also after
adjoining independent private memory. This transfers actual network-only
events without any extra conditional independence premise. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.TransportNetworkAuxiliary
open TransportNetwork

theorem network_projection_preserving (n D k : ℕ) :
    MeasurePreserving (Prod.fst : Sample n D k → Latent n D) (law n D k) (TransportNetwork.law n D) := by
  refine ⟨measurable_fst,?_⟩
  simp [law]

theorem private_network_projection_preserving {H : Type*} [MeasurableSpace H]
    (ρ : Measure H) [IsProbabilityMeasure ρ] (n D k : ℕ) :
    MeasurePreserving (fun s : H × Sample n D k => (s.1,s.2.1))
      (ρ.prod (law n D k)) (ρ.prod (TransportNetwork.law n D)) := by
  letI : IsProbabilityMeasure (law n D k) := probability n D k
  letI : IsFiniteMeasure (law n D k) := inferInstance
  letI : SigmaFinite (law n D k) := inferInstance
  letI : SFinite (law n D k) := inferInstance
  exact (MeasurePreserving.id ρ).prod (network_projection_preserving n D k)

theorem private_network_event {H : Type*} [MeasurableSpace H]
    (ρ : Measure H) [IsProbabilityMeasure ρ] (n D k : ℕ) (A : Set (H × Latent n D)) (hA : MeasurableSet A) :
    (ρ.prod (law n D k)) {s | (s.1,s.2.1)∈A}=(ρ.prod (TransportNetwork.law n D)) A :=
  (private_network_projection_preserving ρ n D k).measure_preimage hA.nullMeasurableSet

end Bilevel.TransportNetworkAuxiliary

namespace Bilevel.TransportRound
open TransportNetwork
set_option maxHeartbeats 800000

theorem runQueryBad_joint_measurable {H : Type*} [MeasurableSpace H] {n D p T : ℕ}
    (hT : T≤D) (a : ℝ)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H) (hr : ∀ t,Measurable (respond t)) (M : ℕ) :
    MeasurableSet {s : H × Latent n D | runQueryBad hT a choose respond (prefixNames n T) (s.1,seed T hT s.2) s.2 M} := by
  have he : {s : H × Latent n D | runQueryBad hT a choose respond (prefixNames n T) (s.1,seed T hT s.2) s.2 M}=
      ⋃ t : ℕ,⋃ (_ : t<M),{s : H × Latent n D |
        TransportRoundQuery.queryPhaseBad T hT a
          (requests (choose t (run T hT choose respond (prefixNames n T) (s.1,seed T hT s.2) s.2 t)))
          (known (run T hT choose respond (prefixNames n T) (s.1,seed T hT s.2) s.2 t).2) s.2} := by
    ext s
    simp [runQueryBad]
  rw [he]
  apply MeasurableSet.iUnion
  intro t
  apply MeasurableSet.iUnion
  intro _
  have hs := runState_joint_measurable hT choose hc respond hr t
  exact requests_bad_joint_measurable hT a _ (measurable_snd.comp hs) _ ((hc t).comp hs) _ measurable_snd

theorem augmented_run_query_failure {H : Type*} [MeasurableSpace H] {n D p T k : ℕ}
    (hT : T≤D) (hpos : 0<T) (a : ℝ) (ha : 0<a) (r : ℕ) (hrank : 0<r)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H) (hr : ∀ t,Measurable (respond t))
    (ρ : Measure H) [IsProbabilityMeasure ρ] (M : ℕ) (hD : queryCap n p 1 1 M+r≤D) :
    (ρ.prod (TransportNetworkAuxiliary.law n D k))
      {s | runQueryBad hT a choose respond (prefixNames n T) (s.1,seed T hT s.2.1) s.2.1 M} ≤
      (M:ℝ≥0∞)*((n+1)*p:ℕ)*ENNReal.ofReal ((T:ℝ)/((r:ℝ)*a)) := by
  have he := TransportNetworkAuxiliary.private_network_event ρ n D k _ (runQueryBad_joint_measurable hT a choose hc respond hr M)
  simp only [Set.mem_setOf_eq] at he
  rw [he]
  exact run_query_failure hT hpos a ha r hrank choose hc respond hr (prefixNames n T) ρ M hD

end Bilevel.TransportRound
