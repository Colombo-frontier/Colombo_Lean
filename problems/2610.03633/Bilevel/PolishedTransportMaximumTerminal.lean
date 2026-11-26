import Bilevel.PolishedTransportLocalObserver
import Bilevel.TransportRoundTerminal

/-! Terminal vector insertion in the same high-probability source maximum
event. The observation round adds no original oracle call. -/
noncomputable section
open MeasureTheory
namespace Bilevel.PolishedTransportLocalSpaces
open EuclideanGaussian ProjectionGeometry TransportObserver TransportEdgePosterior
  OrthogonalAction TransportNetwork TransportRound TransportControllerMachine
set_option maxHeartbeats 1400000

theorem terminal_runPairs_eq {H : Type*} {n D p c m T : ℕ} (hT : T ≤ D)
    (choose : ∀ t,H × Generators n D (size n p c m t) → Queries n D p)
    (respond : ∀ t,StepData H n D (size n p c m t) p T → H)
    (names : ℕ → Vertex n → Fin c → Option (Fin T)) (output : H → Queries n D p)
    (M : ℕ) (s : H × Generators n D m) (z : Latent n D) (edge : Edge n) (t : ℕ) (ht : t ≤ M) :
    runPairs hT (terminalChoose choose output M) respond names s z edge t=
      runPairs hT choose respond names s z edge t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have htM : t < M := by omega
    have he : terminalChoose choose output M t=choose t := by
      funext s
      simp only [terminalChoose,if_neg (Nat.ne_of_lt htM)]
    rw [runPairs,runPairs,terminal_run_eq hT choose respond names output s z M t htM.le,
      he,ih htM.le]

theorem maximumGood_original_of_terminal {H : Type*} {n D p T : ℕ} (hT : T ≤ D)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H)
    (output : H → Queries n D p) (memory : H) (z : Latent n D) (M : ℕ) (e : ℝ)
    (hgood : MaximumGood hT (terminalChoose choose output M) respond memory z (M+1) e) :
    MaximumGood hT choose respond memory z M e := by
  constructor
  · intro t ht
    have h := hgood.1 t (by omega)
    unfold runEnergy at h ⊢
    rwa [terminal_run_eq hT choose respond (prefixNames n T) output _ z M t ht] at h
  · intro t ht
    have h := hgood.2 t (by omega)
    dsimp only at h ⊢
    have hg : frozenAt hT (terminalChoose choose output M) respond (prefixNames n T)
        (memory,seed T hT z) z t=frozenAt hT choose respond (prefixNames n T)
          (memory,seed T hT z) z t := by
      unfold frozenAt
      rw [terminal_run_eq hT choose respond (prefixNames n T) output _ z M t ht.le]
      simp only [terminalChoose,if_neg (Nat.ne_of_lt ht)]
    have hp : (fun edge => runPairs hT (terminalChoose choose output M) respond
        (prefixNames n T) (memory,seed T hT z) z edge t)=
        (fun edge => runPairs hT choose respond (prefixNames n T) (memory,seed T hT z) z edge t) :=
      funext (fun edge => terminal_runPairs_eq hT choose respond (prefixNames n T) output M
        _ z edge t ht.le)
    rw [hg,hp] at h
    exact h

theorem complete_actual_maximum_observer {n D T p k : ℕ} (H : Memory) (hT : T ≤ D)
    (hn : 0 < n) (hpos : 0 < T)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p)
    (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H) (hr : ∀ t,Measurable (respond t))
    (output : H → Queries n D p) (ho : Measurable output)
    (ρ : Measure H) [IsProbabilityMeasure ρ] (M : ℕ) {e : ℝ} (he : 0 < e)
    (hD : maximumDimension n p T (M+1) e (1/8) ≤ D) :
    ∃ G : Set (H × TransportNetworkAuxiliary.Sample n D k),MeasurableSet G ∧
      (7 : ℝ)/8 ≤ (ρ.prod (TransportNetworkAuxiliary.law n D k)).real G ∧
      ∀ s ∈ G,MaximumGood hT choose respond s.1 s.2.1 M e ∧
        TransportRoundEnergy.total (known (terminalGenerators hT choose respond output M s.1 s.2.1))
          (frame T hT s.2.1) (oldFuture T M) ≤ e := by
  obtain ⟨G,hG,hprob,hgood⟩ := actual_maximum_observer (k := k) H hT hn hpos
    (terminalChoose choose output M) (terminalChoose_measurable choose hc output ho M)
    respond hr ρ (M+1) he hD
  refine ⟨G,hG,hprob,?_⟩
  intro s hs
  have h := hgood s hs
  refine ⟨maximumGood_original_of_terminal hT choose respond output s.1 s.2.1 M e h,?_⟩
  have ht := (h.2 M (Nat.lt_succ_self M)).1
  rw [terminalGenerators_eq_frozen]
  exact ht

end Bilevel.PolishedTransportLocalSpaces
