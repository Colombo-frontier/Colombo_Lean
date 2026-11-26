import RandomizedFO2003.ConfiguredEpoch

namespace RandomizedFO2003.Accelerated

noncomputable section

/-- Finite exit selection, giving the first failing test when budgets are
monotone. The test at the last index is handled by the caller. -/
def firstExit (budget : ℕ → ℝ) (threshold : ℝ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if budget n ≤ threshold then n + 1 else firstExit budget threshold n

theorem firstExit_le (budget : ℕ → ℝ) (threshold : ℝ) (N : ℕ) :
    firstExit budget threshold N ≤ N := by
  induction N with
  | zero => simp [firstExit]
  | succ n ih =>
    unfold firstExit
    split_ifs
    · exact le_rfl
    · omega

/-- If the final test fails, the selected exit has a passing predecessor
and a failing current test. No monotonicity assumption is needed. -/
theorem firstExit_spec (budget : ℕ → ℝ) (threshold : ℝ)
    (hzero : budget 0 ≤ threshold) (N : ℕ) (hfail : threshold < budget N) :
    ∃ n, firstExit budget threshold N = n + 1 ∧ n + 1 ≤ N ∧
      budget n ≤ threshold ∧ threshold < budget (n + 1) := by
  induction N with
  | zero => linarith
  | succ k ih =>
    by_cases hk : budget k ≤ threshold
    · exact ⟨k, by simp [firstExit, hk], le_rfl, hk, hfail⟩
    · obtain ⟨n, he, hn, hp, hf⟩ := ih (lt_of_not_ge hk)
      exact ⟨n, by simp [firstExit, hk, he], by omega, hp, hf⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def epochExitIndex (f : E → ℝ) (η θ B : ℝ) (start : E) (N : ℕ) : ℕ :=
  firstExit (fun n => (n : ℝ) * epochEnergy f η θ start n) (B ^ 2) N

/-- A block executes a full epoch, then uses its first failing prefix as
the restart point. Discarded later queries cost at most one epoch per restart. -/
def restartPoint (f : E → ℝ) (η θ B : ℝ) (N : ℕ) (start : E) : E :=
  if B ^ 2 < (N : ℝ) * epochEnergy f η θ start N then
    epochPoint f η θ start (epochExitIndex f η θ B start N)
  else start

def restartSequence (f : E → ℝ) (η θ B : ℝ) (N : ℕ) (initial : E) : ℕ → E
  | 0 => initial
  | j + 1 => restartPoint f η θ B N (restartSequence f η θ B N initial j)

@[simp] theorem restartSequence_zero (f : E → ℝ) (η θ B : ℝ) (N : ℕ) (initial : E) :
    restartSequence f η θ B N initial 0 = initial := rfl

@[simp] theorem restartSequence_succ (f : E → ℝ) (η θ B : ℝ) (N : ℕ) (initial : E) (j : ℕ) :
    restartSequence f η θ B N initial (j + 1) =
      restartPoint f η θ B N (restartSequence f η θ B N initial j) := rfl

variable [FiniteDimensional ℝ E] {f : E → ℝ} {ε L ρ : ℝ}
local notation "η₀" => stepSize L
local notation "B₀" => accuracyRadius ε ρ
local notation "N₀" => epochHorizon η₀ ρ B₀
local notation "θ₀" => roundedMomentum η₀ ρ B₀

theorem accuracy_restartPoint_decrease (hf : ContDiff ℝ 2 f)
    (hε : 0 < ε) (hL : 0 < L) (hρ : 0 < ρ) (haccuracy : ε ≤ L ^ 2 / ρ)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (start : E) (hfail : B₀ ^ 2 < (N₀ : ℝ) * epochEnergy f η₀ θ₀ start N₀) :
    f (restartPoint f η₀ θ₀ B₀ N₀ start) - f start ≤ -(ρ * B₀ ^ 3) := by
  obtain ⟨n, he, hn, hp, hc⟩ := firstExit_spec
    (fun k => (k : ℝ) * epochEnergy f η₀ θ₀ start k) (B₀ ^ 2)
    (by simpa using sq_nonneg B₀) N₀ hfail
  rw [restartPoint, if_pos hfail]
  change f (epochPoint f η₀ θ₀ start (firstExit _ _ N₀)) - f start ≤ _
  rw [he]
  exact accuracy_epoch_restart start hf hε hL hρ haccuracy hlip hH n hn hp hc

end

end RandomizedFO2003.Accelerated
