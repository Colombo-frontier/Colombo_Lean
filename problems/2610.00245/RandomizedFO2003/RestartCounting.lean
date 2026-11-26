import RandomizedFO2003.EpochExit

namespace RandomizedFO2003.Accelerated

noncomputable section

/-- Includes the final successful epoch even when no restart is needed. -/
def restartLimit (Δ δ : ℝ) : ℕ := ⌊Δ / δ⌋₊ + 1

theorem restartLimit_drop {Δ δ : ℝ} (hδ : 0 < δ) :
    Δ < (restartLimit Δ δ : ℝ) * δ := by
  have hh := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (Δ / δ))
  simpa only [restartLimit, Nat.cast_add, Nat.cast_one] using hh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E] {f : E → ℝ} {ε L ρ : ℝ}
local notation "η₀" => stepSize L
local notation "B₀" => accuracyRadius ε ρ
local notation "N₀" => epochHorizon η₀ ρ B₀
local notation "θ₀" => roundedMomentum η₀ ρ B₀
local notation "δ₀" => ρ * B₀ ^ 3

variable (hf : ContDiff ℝ 2 f)
    (hε : 0 < ε) (hL : 0 < L) (hρ : 0 < ρ) (haccuracy : ε ≤ L ^ 2 / ρ)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)

include hf hε hL hρ haccuracy hlip hH

theorem restartSequence_drop_of_all_failed (initial : E) (M : ℕ)
    (hall : ∀ j < M, B₀ ^ 2 < (N₀ : ℝ) *
      epochEnergy f η₀ θ₀ (restartSequence f η₀ θ₀ B₀ N₀ initial j) N₀) :
    f (restartSequence f η₀ θ₀ B₀ N₀ initial M) - f initial ≤ -(M : ℝ) * δ₀ := by
  induction M with
  | zero => simp
  | succ m ih =>
    have hi := ih (fun j hj => hall j (by omega))
    have hs := accuracy_restartPoint_decrease hf hε hL hρ haccuracy hlip hH
      (restartSequence f η₀ θ₀ B₀ N₀ initial m) (hall m (by omega))
    rw [restartSequence_succ, Nat.cast_add, Nat.cast_one]
    linarith

/-- A finite initial gap rules out too many consecutive failed epochs.
This uses the pairwise gap condition directly; an attained minimum is unnecessary. -/
theorem exists_successful_epoch {Δ : ℝ} (initial : E)
    (hgap : ∀ x, f initial - f x ≤ Δ) :
    ∃ j < restartLimit Δ δ₀,
      (N₀ : ℝ) * epochEnergy f η₀ θ₀ (restartSequence f η₀ θ₀ B₀ N₀ initial j) N₀ ≤ B₀ ^ 2 := by
  by_contra! hall
  have ht := restartSequence_drop_of_all_failed hf hε hL hρ haccuracy hlip hH
    initial (restartLimit Δ δ₀) hall
  have hg := hgap (restartSequence f η₀ θ₀ B₀ N₀ initial (restartLimit Δ δ₀))
  have hδ : 0 < δ₀ := mul_pos hρ (pow_pos (accuracyRadius_pos hε hρ) 3)
  have hm := restartLimit_drop (Δ := Δ) hδ
  nlinarith

/-- Analytic finite-run convergence, with an explicit bound on the number
of full epoch blocks. Oracle-model implementation and the rate comparison
are separate obligations. -/
theorem exists_accurate_epoch_average {Δ : ℝ} (initial : E)
    (hgap : ∀ x, f initial - f x ≤ Δ) :
    ∃ j < restartLimit Δ δ₀, ∃ q, N₀ / 2 ≤ q ∧ q < N₀ ∧
      ‖gradient f (prefixAverage
        (epochQuery f η₀ θ₀ (restartSequence f η₀ θ₀ B₀ N₀ initial j)) q)‖ ≤ ε := by
  obtain ⟨j, hj, hb⟩ := exists_successful_epoch hf hε hL hρ haccuracy hlip hH initial hgap
  have hp := roundedMomentum_conditions (stepSize_pos hL) hρ (accuracyRadius_pos hε hρ)
    (accuracy_rawMomentum_small hε hL hρ haccuracy)
  obtain ⟨q, hq0, hqN, hmin⟩ := exists_epoch_half_min f η₀ θ₀
    (restartSequence f η₀ θ₀ B₀ N₀ initial j) hp.1
  exact ⟨j, hj, q, hq0, hqN, accuracy_epoch_terminal _ hf hε hL hρ haccuracy hH hq0 hqN hmin hb⟩

end

end RandomizedFO2003.Accelerated
