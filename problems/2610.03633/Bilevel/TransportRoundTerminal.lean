import Bilevel.TransportRoundNetworkObserver

/-! Arbitrary terminal vectors are inserted after the actual M-round state.
The auxiliary observation round does not alter that state or add an original
SFO call. All bounds use the old prefix at time M. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork TransportNetworkAuxiliary TransportControllerMachine ProjectionGeometry
set_option maxHeartbeats 800000

variable {H : Type*} {n D p c m T : ℕ}

def terminalChoose
    (choose : ∀ t,H × Generators n D (size n p c m t) → Queries n D p)
    (output : H → Queries n D p) (M t : ℕ) : H × Generators n D (size n p c m t) → Queries n D p :=
  fun s => if t=M then output s.1 else choose t s

theorem terminalChoose_measurable [MeasurableSpace H]
    (choose : ∀ t,H × Generators n D (size n p c m t) → Queries n D p)
    (hc : ∀ t,Measurable (choose t)) (output : H → Queries n D p) (ho : Measurable output)
    (M t : ℕ) : Measurable (terminalChoose choose output M t) := by
  unfold terminalChoose
  split_ifs
  · exact ho.comp measurable_fst
  · exact hc t

theorem terminal_run_eq (hT : T≤D)
    (choose : ∀ t,H × Generators n D (size n p c m t) → Queries n D p)
    (respond : ∀ t,StepData H n D (size n p c m t) p T → H)
    (names : ℕ → Vertex n → Fin c → Option (Fin T)) (output : H → Queries n D p)
    (s : H × Generators n D m) (z : Latent n D) (M t : ℕ) (ht : t≤M) :
    run T hT (terminalChoose choose output M) respond names s z t=run T hT choose respond names s z t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hlt : t<M := by omega
    have he : terminalChoose choose output M t=choose t := by
      funext s
      simp only [terminalChoose,if_neg (Nat.ne_of_lt hlt)]
    rw [run,run,he,ih (by omega)]

def terminalGenerators (hT : T≤D)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H)
    (output : H → Queries n D p) (M : ℕ) (memory : H) (z : Latent n D) :
    Generators n D (size n p 1 1 M+p) :=
  let s := run T hT choose respond (prefixNames n T) (memory,seed T hT z) z M
  augment s.2 (output s.1)

theorem terminalGenerators_eq_frozen (hT : T≤D)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H)
    (output : H → Queries n D p) (M : ℕ) (memory : H) (z : Latent n D) :
    terminalGenerators hT choose respond output M memory z=
      frozenAt hT (terminalChoose choose output M) respond (prefixNames n T) (memory,seed T hT z) z M := by
  unfold frozenAt
  rw [terminal_run_eq hT choose respond _ output _ z M M le_rfl]
  simp only [terminalGenerators,terminalChoose,if_pos rfl,ite_true]

theorem terminalGenerators_measurable [MeasurableSpace H] (hT : T≤D)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H) (hr : ∀ t,Measurable (respond t))
    (output : H → Queries n D p) (ho : Measurable output) (M : ℕ) :
    Measurable (fun s : H × Latent n D => terminalGenerators hT choose respond output M s.1 s.2) := by
  have hs := runState_joint_measurable hT choose hc respond hr M
  exact (augment_measurable n D (size n p 1 1 M) p).comp
    ((measurable_snd.comp hs).prodMk (ho.comp (measurable_fst.comp hs)))

def TerminalGood (hT : T≤D)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H)
    (output : H → Queries n D p) (M : ℕ) (b : ℝ) (memory : H) (z : Latent n D) : Prop :=
  ∀ v i,¬Protected M v i →
    ‖project (known (terminalGenerators hT choose respond output M memory z) v) (frame T hT z v i)‖≤b

theorem terminalGood_of_projectionGood (hT : T≤D)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H)
    (output : H → Queries n D p) (M : ℕ) (b : ℝ) (memory : H) (z : Latent n D)
    (hgood : ProjectionGood hT (terminalChoose choose output M) respond (M+1) b memory z) :
    TerminalGood hT choose respond output M b memory z := by
  intro v i hi
  rw [terminalGenerators_eq_frozen]
  exact hgood.2 M (Nat.lt_succ_self _) v i hi

theorem terminal_output_mem (hT : T≤D)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H)
    (output : H → Queries n D p) (M : ℕ) (memory : H) (z : Latent n D)
    (v : Vertex n) (i : Fin p) :
    output (run T hT choose respond (prefixNames n T) (memory,seed T hT z) z M).1 v i∈
      known (terminalGenerators hT choose respond output M memory z) v := by
  unfold terminalGenerators
  rw [augment_span]
  exact Submodule.mem_sup_right (TransportGeneratorStore.generator_mem _ i)

theorem terminalGood_measurable [MeasurableSpace H] (hT : T≤D)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H) (hr : ∀ t,Measurable (respond t))
    (output : H → Queries n D p) (ho : Measurable output) (M : ℕ) (b : ℝ) :
    MeasurableSet {s : H × Latent n D | TerminalGood hT choose respond output M b s.1 s.2} := by
  simp only [TerminalGood,Set.setOf_forall]
  apply MeasurableSet.iInter
  intro v
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _hi
  have hg := terminalGenerators_measurable hT choose hc respond hr output ho M
  have hP := known_projector_measurable _ hg v
  have hf := (measurable_pi_apply i).comp (frame_layer_measurable (Ω:=H × Latent n D) hT Prod.snd measurable_snd v)
  have hproj := ProjectionStore.apply_measurable D _ hP _ hf
  simp only [ProjectionStore.apply_subspace] at hproj
  exact measurableSet_le hproj.norm measurable_const

theorem projectionGood_original_of_terminal (hT : T≤D)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H)
    (output : H → Queries n D p) (M : ℕ) (b : ℝ) (memory : H) (z : Latent n D)
    (hgood : ProjectionGood hT (terminalChoose choose output M) respond (M+1) b memory z) :
    ProjectionGood hT choose respond M b memory z := by
  constructor
  · intro t ht v i hi
    have hh := hgood.1 t (by omega) v i hi
    rw [terminal_run_eq hT choose respond _ output _ z M t ht] at hh
    exact hh
  · intro t ht v i hi
    have hh := hgood.2 t (by omega) v i hi
    unfold frozenAt at hh
    rw [terminal_run_eq hT choose respond _ output _ z M t ht.le] at hh
    simpa only [terminalChoose,if_neg (Nat.ne_of_lt ht),frozenAt] using hh

theorem network_terminal_observer {n D T p k : ℕ} (H : Memory) (hT : T≤D) (hn : 0<n) (hpos : 0<T)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H) (hr : ∀ t,Measurable (respond t))
    (output : H → Queries n D p) (ho : Measurable output)
    (ρ : Measure H) [IsProbabilityMeasure ρ] (M : ℕ) {b δ : ℝ} (hb : 0<b) (hδ : 0<δ)
    (hD : observerDimension n p T (M+1) b δ≤D) :
    (ρ.prod (TransportNetworkAuxiliary.law n D k))
      {s | ¬TerminalGood hT choose respond output M b s.1 s.2.1}≤ENNReal.ofReal δ := by
  have h := network_observer (k:=k) H hT hn hpos (terminalChoose choose output M)
    (terminalChoose_measurable choose hc output ho M) respond hr ρ (M+1) hb hδ hD
  apply le_trans (measure_mono ?_) h
  intro s hs hg
  exact hs (terminalGood_of_projectionGood hT choose respond output M b s.1 s.2.1 hg)

theorem network_observer_with_terminal {n D T p k : ℕ} (H : Memory) (hT : T≤D) (hn : 0<n) (hpos : 0<T)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H) (hr : ∀ t,Measurable (respond t))
    (output : H → Queries n D p) (ho : Measurable output)
    (ρ : Measure H) [IsProbabilityMeasure ρ] (M : ℕ) {b δ : ℝ} (hb : 0<b) (hδ : 0<δ)
    (hD : observerDimension n p T (M+1) b δ≤D) :
    (ρ.prod (TransportNetworkAuxiliary.law n D k))
      {s | ¬(ProjectionGood hT choose respond M b s.1 s.2.1 ∧
        TerminalGood hT choose respond output M b s.1 s.2.1)}≤ENNReal.ofReal δ := by
  have h := network_observer (k:=k) H hT hn hpos (terminalChoose choose output M)
    (terminalChoose_measurable choose hc output ho M) respond hr ρ (M+1) hb hδ hD
  apply le_trans (measure_mono ?_) h
  intro s hs hg
  exact hs ⟨projectionGood_original_of_terminal hT choose respond output M b s.1 s.2.1 hg,
    terminalGood_of_projectionGood hT choose respond output M b s.1 s.2.1 hg⟩

end Bilevel.TransportRound
