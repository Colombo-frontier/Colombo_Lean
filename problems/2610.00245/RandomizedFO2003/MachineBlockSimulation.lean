import RandomizedFO2003.AcceleratedMachine

namespace RandomizedFO2003.Accelerated

noncomputable section

def savedPrefix {E : Type*} [Zero E] (g : ℕ → E) (k : ℕ) : ℕ → E :=
  fun i => if i < k then g i else 0

@[simp] theorem savedPrefix_zero {E : Type*} [Zero E] (g : ℕ → E) :
    savedPrefix g 0 = fun _ => 0 := by funext i; simp [savedPrefix]

theorem savedPrefix_update {E : Type*} [Zero E] (g : ℕ → E) (k : ℕ) :
    Function.update (savedPrefix g k) k (g k) = savedPrefix g (k + 1) := by
  funext i
  by_cases hi : i = k
  · subst i; simp [savedPrefix]
  · rw [Function.update_of_ne hi]
    have he : i < k ↔ i < k + 1 := by omega
    simp [savedPrefix, he]

variable {d : ℕ} (f : Model.Space d → ℝ) (η θ B : ℝ) (N : ℕ)
variable (initial start output : Model.Space d)

theorem machine_step_prefix (t k : ℕ) (hmod : t % N = k) :
    (acceleratedMachine η θ B N initial).step t
      ((start, savedPrefix (fun i => gradient f (epochQuery f η θ start i)) k, output),
        Model.oracle f ((acceleratedMachine η θ B N initial).query t
          (start, savedPrefix (fun i => gradient f (epochQuery f η θ start i)) k, output))) =
    if (t + 1) % N = 0 then blockFinish η θ B N
      (start, savedPrefix (fun i => gradient f (epochQuery f η θ start i)) (k + 1), output)
    else (start, savedPrefix (fun i => gradient f (epochQuery f η θ start i)) (k + 1), output) := by
  have hq : blockQuery η θ N t
      (start, savedPrefix (fun i => gradient f (epochQuery f η θ start i)) k, output) =
      epochQuery f η θ start k := by
    unfold blockQuery
    rw [hmod]
    apply replyQuery_eq_epochQuery
    intro i hi
    simp [savedPrefix, hi]
  change blockStep η θ B N t (_, Model.oracle f (blockQuery η θ N t _)) = _
  rw [hq]
  unfold blockStep blockPush
  simp only [Model.oracle, hmod, savedPrefix_update]

/-- Within a block, the state stores exactly the gradient responses at the
already queried points and retains the previous successful output. -/
theorem machine_run_prefix (j k : ℕ) (hk : k < N)
    (hstart : (acceleratedMachine η θ B N initial).run f (j * N) = (start, (fun _ => 0), output)) :
    (acceleratedMachine η θ B N initial).run f (j * N + k) =
      (start, savedPrefix (fun i => gradient f (epochQuery f η θ start i)) k, output) := by
  induction k with
  | zero => simpa only [Nat.add_zero, savedPrefix_zero] using hstart
  | succ k ih =>
    have hi := ih (by omega)
    have hm : (j * N + k) % N = k := by
      simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt (show k < N by omega)]
    have hm' : (j * N + k + 1) % N = k + 1 := by
      rw [show j * N + k + 1 = j * N + (k + 1) by omega]
      simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hk]
    rw [show j * N + (k + 1) = (j * N + k) + 1 by omega,
      Model.DeterministicMachine.run, hi,
      machine_step_prefix f η θ B N initial start output (j * N + k) k hm]
    simp only [hm', Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]

/-- Exact transition from one block boundary to the next, including the
finite restart selection and the average remembered on successful blocks. -/
theorem machine_run_block (hN : 0 < N) (j : ℕ)
    (hstart : (acceleratedMachine η θ B N initial).run f (j * N) = (start, (fun _ => 0), output)) :
    (acceleratedMachine η θ B N initial).run f ((j + 1) * N) =
      (restartPoint f η θ B N start, fun _ => 0,
        if (N : ℝ) * epochEnergy f η θ start N ≤ B ^ 2 then epochOutput f η θ N start else output) := by
  have hk : N - 1 < N := by omega
  have hi := machine_run_prefix f η θ B N initial start output j (N - 1) hk hstart
  have hsum : N - 1 + 1 = N := by omega
  have ht : (j + 1) * N = (j * N + (N - 1)) + 1 := by
    rw [Nat.add_mul, one_mul]
    omega
  have hm : (j * N + (N - 1)) % N = N - 1 := by
    simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hk]
  have hm' : (j * N + (N - 1) + 1) % N = 0 := by rw [← ht]; simp
  rw [ht, Model.DeterministicMachine.run, hi,
    machine_step_prefix f η θ B N initial start output _ _ hm, hm', if_pos rfl, hsum]
  apply blockFinish_eq_actual f η θ B hN start output
  intro k hk
  simp [savedPrefix, hk]

end

end RandomizedFO2003.Accelerated
