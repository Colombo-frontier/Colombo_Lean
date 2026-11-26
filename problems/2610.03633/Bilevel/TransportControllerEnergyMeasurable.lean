import Bilevel.TransportRoundInitialization
import Bilevel.TransportRoundEnergy

/-! Measurability and initial zero energy for the actual generator-run ledger,
including arbitrary fixed physical-layer copies used for local bookkeeping. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork ProjectionGeometry TransportObserver
set_option maxHeartbeats 600000

theorem generator_energy_measurable (D m T : ℕ) (I : Finset (Fin T)) :
    Measurable (fun p : (Fin m → Space D) × (Fin T → Space D) =>
      frameEnergy (TransportGeneratorStore.span p.1) p.2 I) := by
  have hh : Measurable (fun p : (Fin m → Space D) × (Fin T → Space D) =>
      ∑ i∈I, ‖ProjectionStore.apply D (TransportGeneratorStore.projector D p.1) (p.2 i)‖^2) := by
    apply Finset.measurable_sum
    intro i _
    exact ((ProjectionStore.apply_measurable D _
      ((TransportGeneratorStore.projector_measurable D m).comp measurable_fst) _
      ((measurable_pi_apply i).comp measurable_snd)).norm).pow_const 2
  simpa only [TransportGeneratorStore.projector_correct,ProjectionStore.apply_subspace,frameEnergy,energy] using hh

theorem generator_ledger_measurable {Ω : Type*} [MeasurableSpace Ω] (D m T r : ℕ)
    (g : Ω → Fin r → Fin m → Space D) (hg : Measurable g)
    (f : Ω → Fin r → Fin T → Space D) (hf : Measurable f) (I : Fin r → Finset (Fin T)) :
    Measurable (fun ω => ∑ j : Fin r, frameEnergy (TransportGeneratorStore.span (g ω j)) (f ω j) (I j)) := by
  have hj (j : Fin r) : Measurable (fun ω => frameEnergy (TransportGeneratorStore.span (g ω j)) (f ω j) (I j)) := by
    have hgj : Measurable (fun ω => g ω j) := (measurable_pi_apply j).comp hg
    have hfj : Measurable (fun ω => f ω j) := (measurable_pi_apply j).comp hf
    have he : (fun ω => frameEnergy (TransportGeneratorStore.span (g ω j)) (f ω j) (I j)) =
        (fun p : (Fin m → Space D) × (Fin T → Space D) => frameEnergy (TransportGeneratorStore.span p.1) p.2 (I j)) ∘
          (fun ω => (g ω j,f ω j)) := rfl
    rw [he]
    exact (generator_energy_measurable D m T (I j)).comp (hgj.prodMk hfj)
  exact Finset.measurable_sum Finset.univ (fun j _ => hj j)

theorem run_blind_energy_measurable {H : Type*} [MeasurableSpace H] {n D p : ℕ}
    (T : ℕ) (hT : T≤D)
    (choose : ∀ t, H × Generators n D (size n p 1 1 t) → Queries n D p)
    (hc : ∀ t, Measurable (choose t))
    (respond : ∀ t, StepData H n D (size n p 1 1 t) p T → H)
    (hr : ∀ t, Measurable (respond t)) (h : H) (t : ℕ) (I : Vertex n → Finset (Fin T)) :
    Measurable (fun z : Latent n D => ∑ v, frameEnergy
      (known (run T hT choose respond (prefixNames n T) (h,seed T hT z) z t).2 v) (frame T hT z v) (I v)) := by
  have hs : Measurable (fun z : Latent n D => ((h,seed T hT z),z)) :=
    (measurable_const.prodMk (seed_measurable T hT)).prodMk measurable_id
  have hg : Measurable (fun z : Latent n D => (run T hT choose respond (prefixNames n T) (h,seed T hT z) z t).2) :=
    measurable_snd.comp ((run_measurable T hT choose hc respond hr (prefixNames n T) t).comp hs)
  exact generator_ledger_measurable D (size n p 1 1 t) T (n+1) _ hg _ (frame_measurable n D T hT) I

theorem seed_ledger_zero {n D r : ℕ} (T : ℕ) (hT : T≤D) (hpos : 0<T)
    (z : Latent n D) (layer : Fin r → Vertex n) (I : Fin r → Finset (Fin T))
    (hI : ∀ j i, i∈I j → ¬Protected 0 (layer j) i) :
    TransportRoundEnergy.total (fun j => known (seed T hT z) (layer j))
      (fun j => frame T hT z (layer j)) I=0 := by
  apply Finset.sum_eq_zero
  intro j _
  exact seed_blind_zero T hT hpos z (layer j) (I j) (hI j)

end Bilevel.TransportRound
