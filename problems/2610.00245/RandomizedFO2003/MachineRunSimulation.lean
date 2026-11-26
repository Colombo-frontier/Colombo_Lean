import RandomizedFO2003.MachineBlockSimulation

namespace RandomizedFO2003.Accelerated

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The most recent successful block average, defaulting to the initial
point until the first success. This is a total finite computation. -/
def blockOutputSequence (f : E → ℝ) (η θ B : ℝ) (N : ℕ) (initial : E) : ℕ → E
  | 0 => initial
  | j + 1 =>
      let start := restartSequence f η θ B N initial j
      if (N : ℝ) * epochEnergy f η θ start N ≤ B ^ 2 then epochOutput f η θ N start
      else blockOutputSequence f η θ B N initial j

theorem blockOutputSequence_accurate_of_success (f : E → ℝ) (η θ B ε : ℝ) (N : ℕ) (initial : E)
    (hgood : ∀ start, (N : ℝ) * epochEnergy f η θ start N ≤ B ^ 2 →
      ‖gradient f (epochOutput f η θ N start)‖ ≤ ε)
    (M : ℕ) (hsuccess : ∃ j < M,
      (N : ℝ) * epochEnergy f η θ (restartSequence f η θ B N initial j) N ≤ B ^ 2) :
    ‖gradient f (blockOutputSequence f η θ B N initial M)‖ ≤ ε := by
  induction M with
  | zero => obtain ⟨j, hj, _⟩ := hsuccess; omega
  | succ m ih =>
    by_cases hm : (N : ℝ) * epochEnergy f η θ (restartSequence f η θ B N initial m) N ≤ B ^ 2
    · simpa only [blockOutputSequence, if_pos hm] using hgood _ hm
    · rw [blockOutputSequence, if_neg hm]
      apply ih
      obtain ⟨j, hj, hb⟩ := hsuccess
      refine ⟨j, ?_, hb⟩
      have hne : j ≠ m := by intro he; subst j; exact hm hb
      omega

variable {d : ℕ} (f : Model.Space d → ℝ) (η θ B : ℝ) (N : ℕ) (initial : Model.Space d)

/-- The complete state at every block boundary agrees with the analytical
restart sequence and remembered average. -/
theorem machine_run_epochs (hN : 0 < N) (M : ℕ) :
    (acceleratedMachine η θ B N initial).run f (M * N) =
      (restartSequence f η θ B N initial M, fun _ => 0,
        blockOutputSequence f η θ B N initial M) := by
  induction M with
  | zero => simp only [Nat.zero_mul]; rfl
  | succ m ih =>
    rw [machine_run_block f η θ B N initial
      (restartSequence f η θ B N initial m) (blockOutputSequence f η θ B N initial m) hN m ih]
    rfl

/-- Exact output identity after the stated number of actual oracle calls. -/
theorem accelerated_output_transcript (hN : 0 < N) (M : ℕ) :
    (acceleratedMachine η θ B N initial).algorithm.output (M * N) ()
      (Model.transcript (acceleratedMachine η θ B N initial).algorithm f () (M * N)) =
      blockOutputSequence f η θ B N initial M := by
  rw [Model.DeterministicMachine.output_transcript, machine_run_epochs f η θ B N initial hN M]
  rfl

end

end RandomizedFO2003.Accelerated
