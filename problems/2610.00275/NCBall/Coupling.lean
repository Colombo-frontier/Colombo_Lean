import Mathlib.Tactic

/-! # A deterministic first-disagreement coupling for adaptive scalar queries

Randomness can be fixed in `policy`. An action may contain a retained sample
handle and a query point. Shadow responses may depend on time and history.
The missing probabilistic task is to instantiate `bad` with early room hits
and bound its probability under the actual shadow experiment.
-/

namespace NCBall

variable {Action : Type*}

def queryHistory (policy : ℕ → List ℝ → Action)
    (oracle : ℕ → List ℝ → Action → ℝ) : ℕ → List ℝ
  | 0 => []
  | t + 1 =>
    let h := queryHistory policy oracle t
    h ++ [oracle t h (policy t h)]

theorem queryHistory_length (policy : ℕ → List ℝ → Action)
    (oracle : ℕ → List ℝ → Action → ℝ) (t : ℕ) :
    (queryHistory policy oracle t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [queryHistory, ih]

/-- Until the first bad shadow query, the real and shadow transcripts agree. -/
theorem histories_eq_of_no_bad (policy : ℕ → List ℝ → Action)
    (realOracle shadowOracle : ℕ → List ℝ → Action → ℝ)
    (bad : ℕ → List ℝ → Action → Prop) (N : ℕ)
    (hagree : ∀ t h a, ¬bad t h a → realOracle t h a = shadowOracle t h a)
    (hsafe : ∀ t < N, ¬bad t (queryHistory policy shadowOracle t)
      (policy t (queryHistory policy shadowOracle t))) :
    ∀ t ≤ N, queryHistory policy realOracle t = queryHistory policy shadowOracle t := by
  intro t
  induction t with
  | zero => simp [queryHistory]
  | succ t ih =>
    intro ht
    simp only [queryHistory, ih (by omega)]
    rw [hagree t _ _ (hsafe t (by omega))]

theorem different_histories_imply_bad (policy : ℕ → List ℝ → Action)
    (realOracle shadowOracle : ℕ → List ℝ → Action → ℝ)
    (bad : ℕ → List ℝ → Action → Prop) (N : ℕ)
    (hagree : ∀ t h a, ¬bad t h a → realOracle t h a = shadowOracle t h a)
    (hne : queryHistory policy realOracle N ≠ queryHistory policy shadowOracle N) :
    ∃ t < N, bad t (queryHistory policy shadowOracle t)
      (policy t (queryHistory policy shadowOracle t)) := by
  by_contra h
  push_neg at h
  exact hne (histories_eq_of_no_bad policy realOracle shadowOracle bad N hagree h N le_rfl)

end NCBall
