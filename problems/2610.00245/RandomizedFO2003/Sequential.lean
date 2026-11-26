import Mathlib.Tactic

namespace RandomizedFO2003

/-- A zero-based stage index makes the round convention exact. -/
theorem reveal_time_lower_bound (τ : ℕ → ℕ) (m N : ℕ)
    (hstep : ∀ s < N, τ s + m ≤ τ (s + 1)) :
    ∀ s ≤ N, τ 0 + s * m ≤ τ s := by
  intro s hs
  induction s with
  | zero => simp
  | succ s ih =>
    have hprev := ih (by omega)
    have hnext := hstep s (by omega)
    calc
      τ 0 + (s + 1) * m = (τ 0 + s * m) + m := by ring
      _ ≤ τ s + m := Nat.add_le_add_right hprev m
      _ ≤ τ (s + 1) := hnext

/-- N stages, including m rounds for the final solve, require N*m rounds. -/
theorem direct_sum_rounds (τ : ℕ → ℕ) (m N t : ℕ)
    (hN : 0 < N)
    (hstep : ∀ s < N - 1, τ s + m ≤ τ (s + 1))
    (hfinal : τ (N - 1) + m ≤ t) : N * m ≤ t := by
  have h := reveal_time_lower_bound τ m (N - 1) hstep (N - 1) le_rfl
  have heq : (N - 1) * m + m = N * m := by
    rw [← Nat.succ_mul]
    congr 1
    omega
  omega

theorem no_early_success (τ : ℕ → ℕ) (m N t : ℕ) (success : Prop)
    (hN : 0 < N)
    (hstep : ∀ s < N - 1, τ s + m ≤ τ (s + 1))
    (hsolve : success → τ (N - 1) + m ≤ t)
    (hearly : t < N * m) : ¬ success := by
  intro h
  exact (Nat.not_le_of_gt hearly) (direct_sum_rounds τ m N t hN hstep (hsolve h))

/-- An adaptive deterministic run with a response-dependent next state. -/
def run {State Query Response : Type*}
    (query : State → Query) (next : State → Response → State)
    (oracle : Query → Response) (initial : State) : ℕ → State
  | 0 => initial
  | t + 1 => next (run query next oracle initial t)
      (oracle (query (run query next oracle initial t)))

/-- Equality only needs to be verified at the censored run's actual queries. -/
theorem first_exit_identity {State Query Response : Type*}
    (query : State → Query) (next : State → Response → State)
    (trueOracle censoredOracle : Query → Response) (initial : State) (T : ℕ)
    (hlocal : ∀ t < T,
      trueOracle (query (run query next censoredOracle initial t)) =
      censoredOracle (query (run query next censoredOracle initial t))) :
    ∀ t ≤ T, run query next trueOracle initial t =
      run query next censoredOracle initial t := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [run]
    rw [ih (by omega), hlocal t (by omega)]

end RandomizedFO2003
