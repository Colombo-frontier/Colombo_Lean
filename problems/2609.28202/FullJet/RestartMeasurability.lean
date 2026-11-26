import FullJet.RestartStopping
import FullJet.StoppingMeasurability

open MeasureTheory

namespace FullJet

variable {α Q R X : Type}

theorem restartResume_index_le (trials : ℕ → OracleProgram Q R (Option X))
    (t : ℕ) (P : OracleProgram Q R (Option X)) :
    (restartResume trials t P).1 ≤ t + 1 := by
  cases P with
  | done x => cases x <;> simp [restartResume]
  | ask q k => simp [restartResume]

theorem oracleRun_restart_index_le (trials : ℕ → OracleProgram Q R (Option X))
    (fallback : Q) (oracle : Q → R) (q : ℕ) :
    (oracleRun (restartQuery fallback) (restartUpdate trials) oracle (0, trials 0) q).1 ≤ q := by
  induction q with
  | zero => exact Nat.le_refl _
  | succ q ih =>
    exact (restartResume_index_le _ _ _).trans (Nat.add_le_add_right ih 1)

theorem restartResume_congr (trials trials' : ℕ → OracleProgram Q R (Option X))
    (t : ℕ) (P : OracleProgram Q R (Option X)) (h : trials (t + 1) = trials' (t + 1)) :
    restartResume trials t P = restartResume trials' t P := by
  cases P with
  | done x => cases x <;> simp [restartResume, h]
  | ask q k => rfl

/-- After q replies at most q+1 private coordinates have been inspected. -/
theorem oracleRun_restart_prefix (trials : α → OracleProgram Q R (Option X))
    (fallback : Q) (oracle : Q → R) (seeds seeds' : ℕ → α) (q : ℕ)
    (h : ∀ i ≤ q, seeds i = seeds' i) :
    oracleRun (restartQuery fallback) (restartUpdate (fun t => trials (seeds t))) oracle
      (0, trials (seeds 0)) q =
    oracleRun (restartQuery fallback) (restartUpdate (fun t => trials (seeds' t))) oracle
      (0, trials (seeds' 0)) q := by
  induction q with
  | zero => simp only [oracleRun, h 0 (Nat.le_refl 0)]
  | succ q ih =>
    rw [oracleRun, oracleRun, ih (fun i hi => h i (by omega))]
    apply restartResume_congr
    congr 1
    exact h _ (Nat.add_le_add_right (oracleRun_restart_index_le _ _ _ q) 1)

def extendTrialPrefix (q : ℕ) (a : Fin (q + 1) → α) (i : ℕ) : α :=
  if h : i < q + 1 then a ⟨i, h⟩ else a ⟨0, by omega⟩

/-- Arbitrary internal minimizers cause no selection issue: each finite
observation factors through a finite tuple of discrete random seeds. -/
theorem oracleRun_restart_observable [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {β : Type} [MeasurableSpace β] (trials : α → OracleProgram Q R (Option X))
    (fallback : Q) (oracle : Q → R) (q : ℕ) (g : RestartState Q R X → β) :
    Measurable fun seeds : ℕ → α => g (oracleRun (restartQuery fallback)
      (restartUpdate (fun t => trials (seeds t))) oracle (0, trials (seeds 0)) q) := by
  let seedPrefix : (ℕ → α) → (Fin (q + 1) → α) := fun seeds i => seeds i
  have hp : Measurable seedPrefix := measurable_pi_lambda _ (fun i => measurable_pi_apply (i : ℕ))
  let out : (Fin (q + 1) → α) → β := fun a => g (oracleRun (restartQuery fallback)
    (restartUpdate (fun t => trials (extendTrialPrefix q a t))) oracle
    (0, trials (extendTrialPrefix q a 0)) q)
  have hout : Measurable out := measurable_of_finite _
  have heq : (fun seeds : ℕ → α => g (oracleRun (restartQuery fallback)
      (restartUpdate (fun t => trials (seeds t))) oracle (0, trials (seeds 0)) q)) =
      out ∘ seedPrefix := by
    funext seeds
    apply congrArg g
    apply oracleRun_restart_prefix
    intro i hi
    simp only [extendTrialPrefix, show i < q + 1 by omega, dif_pos, seedPrefix]
  rw [heq]
  exact hout.comp hp

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n p : ℕ}

theorem restartStoppingAlgorithm_measurableOn [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (index : Fin n) (trials : α → OracleProgram (Fin n × E) (JetPacket p E) (Option E))
    (Δ L : ℝ) : (restartStoppingAlgorithm index trials).measurableOn Δ L := by
  constructor
  · intro f hf N
    change MeasurableSet {seeds | restartHalt ((restartStoppingAlgorithm index trials).state f seeds N) = true}
    simp only [restartStoppingAlgorithm_state]
    exact (measurableSet_singleton true).preimage (oracleRun_restart_observable trials (index, 0)
      (fun q => fullJet p (f q.1) q.2) N restartHalt)
  · intro N f hf
    change Measurable fun seeds => ‖fderiv ℝ (average f)
      ((restartResult ((restartStoppingAlgorithm index trials).state f seeds N)).getD 0)‖
    simp only [restartStoppingAlgorithm_state]
    exact oracleRun_restart_observable trials (index, 0) (fun q => fullJet p (f q.1) q.2) N
      (fun state => ‖fderiv ℝ (average f) ((restartResult state).getD 0)‖)

end FullJet
