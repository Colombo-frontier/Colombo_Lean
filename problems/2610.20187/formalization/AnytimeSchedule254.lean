import LogBudget254
import Mathlib.Analysis.MeanInequalities

noncomputable section
open scoped BigOperators
namespace Paper254

def doublingEpoch (t : ℕ) : ℕ := Nat.log 2 (t+1)
def doublingHorizon (t : ℕ) : ℕ := 2 ^ doublingEpoch t
def doublingStart (t : ℕ) : ℕ := doublingHorizon t-1

theorem doubling_bounds (t : ℕ) :
    0 < doublingHorizon t ∧ doublingStart t ≤ t ∧ t-doublingStart t < doublingHorizon t := by
  have hp : 0 < 2 ^ doublingEpoch t := by positivity
  have hlo := Nat.pow_log_le_self 2 (show t+1 ≠ 0 by omega)
  have hhi := Nat.lt_pow_succ_log_self (by omega : 1 < 2) (t+1)
  rw [pow_succ] at hhi
  dsimp [doublingHorizon,doublingStart,doublingEpoch] at *
  omega

/-- The adapter uses only losses since the current dyadic restart.
There is no terminal horizon in its input. -/
def doublingLearner {d : ℕ} {D : ℝ} {W : Domain d D}
    (family : (H : ℕ) → OnlineLearner W H) :
    (t : ℕ) → (Fin t → Loss d) → W.carrier := by
  intro t history
  let s := doublingStart t
  let j : Fin (doublingHorizon t) := ⟨t-s,(doubling_bounds t).2.2⟩
  exact family (doublingHorizon t) j (fun k => history ⟨s+k.val,by
    have hs : s ≤ t := (doubling_bounds t).2.1
    have hk := k.isLt
    dsimp [j] at hk
    omega⟩)

theorem dyadic_horizon_sum (J : ℕ) :
    (∑ j ∈ Finset.range J,(2:ℝ)^j) = 2^J-1 := by
  induction J with
  | zero => simp
  | succ J ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring

theorem doubling_planned_time (T : ℕ) (hT : 0 < T) :
    (∑ j ∈ Finset.range (Nat.log 2 T+1),(2:ℝ)^j) ≤ 2*T := by
  rw [dyadic_horizon_sum,pow_succ]
  have h := Nat.pow_log_le_self 2 hT.ne'
  have hcast : (2:ℝ)^(Nat.log 2 T) ≤ T := by exact_mod_cast h
  linarith

theorem doubling_error_sum (δ : ℝ) (hδ : 0 ≤ δ) (J : ℕ) :
    (∑ j ∈ Finset.range J,δ/(2:ℝ)^(j+1)) ≤ δ := by
  have he : ∀ J : ℕ,(∑ j ∈ Finset.range J,δ/(2:ℝ)^(j+1))=δ*(1-(1/2:ℝ)^J) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ,ih,pow_succ,pow_succ]
      simp only [one_div_pow]
      field_simp
      <;> ring
  rw [he]
  have h := mul_nonneg hδ (show 0 ≤ (1/2:ℝ)^J by positivity)
  nlinarith

end Paper254
#print axioms Paper254.doubling_bounds
#print axioms Paper254.doubling_error_sum
