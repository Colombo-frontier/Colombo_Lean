import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section

namespace RandomizedFO2003.Accelerated

def scalarQuadratic (κ c x : ℝ) : ℝ := c * x + κ / 2 * x ^ 2

def scalarAGDStep (κ c θ e p x : ℝ) : ℝ :=
  let y := x + (1 - θ) * (x - p)
  y - (κ * y + c + e)

def momentumWeight (θ : ℝ) : ℝ := (1 + θ) * (1 - θ) ^ 2 / 2

theorem momentumWeight_nonneg {θ : ℝ} (hθ : 0 ≤ θ) : 0 ≤ momentumWeight θ := by
  unfold momentumWeight
  positivity

theorem scalarQuadratic_difference (κ c x z : ℝ) :
    scalarQuadratic κ c z - scalarQuadratic κ c x =
      (κ * x + c) * (z - x) + κ / 2 * (z - x) ^ 2 := by
  unfold scalarQuadratic
  ring

/-- A sum-of-squares certificate for the nearly-convex scalar mode.
The error e is already multiplied by the algorithm's step size. -/
theorem scalar_nearly_convex_step {κ θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hlow : -θ ≤ κ) (hhigh : κ ≤ 1) (c e p x : ℝ) :
    let z := scalarAGDStep κ c θ e p x
    8 * θ * (scalarQuadratic κ c z - scalarQuadratic κ c x +
      momentumWeight θ * ((z - x) ^ 2 - (x - p) ^ 2)) + 3 * θ ^ 2 * (z - x) ^ 2 ≤ 16 * e ^ 2 := by
  let y := x + (1 - θ) * (x - p)
  let z := scalarAGDStep κ c θ e p x
  have hidentity :
      8 * θ * (scalarQuadratic κ c z - scalarQuadratic κ c x +
        momentumWeight θ * ((z - x) ^ 2 - (x - p) ^ 2)) + 3 * θ ^ 2 * (z - x) ^ 2 - 16 * e ^ 2 =
      -(4 * θ * (κ + θ) * (1 - θ) ^ 2 * (x - p) ^ 2) -
        4 * θ * (1 - κ) * (z - y) ^ 2 - 4 * θ ^ 3 * (1 - θ) * (z - x) ^ 2 -
        (θ * (z - x) + 4 * e) ^ 2 := by
    dsimp [z, y, scalarAGDStep, scalarQuadratic, momentumWeight]
    ring
  have h1 : 0 ≤ 4 * θ * (κ + θ) * (1 - θ) ^ 2 * (x - p) ^ 2 := by
    have : 0 ≤ κ + θ := by linarith
    positivity
  have h2 : 0 ≤ 4 * θ * (1 - κ) * (z - y) ^ 2 := by
    have : 0 ≤ 1 - κ := by linarith
    positivity
  have h3 : 0 ≤ 4 * θ ^ 3 * (1 - θ) * (z - x) ^ 2 := by
    have : 0 ≤ 1 - θ := by linarith
    positivity
  nlinarith [sq_nonneg (θ * (z - x) + 4 * e)]

/-- For a concave scalar mode, the gradient/momentum pairing obeys a
contractive recurrence with squared-error input. No exact-gradient premise
at the initial point is required. -/
theorem scalar_concave_pairing_step {κ θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hlow : -2 ≤ κ) (hneg : κ ≤ 0) (c e p x : ℝ) :
    (scalarAGDStep κ c θ e p x - x) * (κ * x + c) ≤
      (1 - θ) * ((x - p) * (κ * p + c)) + e ^ 2 / 2 := by
  let v := x - p
  let g := κ * x + c
  have hi : (scalarAGDStep κ c θ e p x - x) * (κ * x + c) -
        (1 - θ) * ((x - p) * (κ * p + c)) - e ^ 2 / 2 =
      (1 - θ) * κ * (1 + κ / 2) * v ^ 2 - (1 - θ) / 2 * (κ * v + g) ^ 2 -
        θ / 2 * g ^ 2 - (e + g) ^ 2 / 2 := by
    dsimp [v, g, scalarAGDStep]
    ring
  have hβ : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  have hκ : 0 ≤ 1 + κ / 2 := by linarith
  have h1 : (1 - θ) * κ * (1 + κ / 2) * v ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hβ hneg) hκ) (sq_nonneg _)
  have h2 : 0 ≤ (1 - θ) / 2 * (κ * v + g) ^ 2 := by positivity
  have h3 : 0 ≤ θ / 2 * g ^ 2 := by positivity
  nlinarith [sq_nonneg (e + g)]

/-- A nonnegative comparison sequence for the concave-mode pairing. -/
def errorBudget (θ : ℝ) (e : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (1 - θ) * errorBudget θ e n + (e n) ^ 2 / 2

theorem errorBudget_nonneg {θ : ℝ} (hθ1 : θ ≤ 1) (e : ℕ → ℝ) (n : ℕ) :
    0 ≤ errorBudget θ e n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [errorBudget]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hθ1) ih) (by positivity)

open scoped BigOperators

theorem errorBudget_sum_identity (θ : ℝ) (e : ℕ → ℝ) (n : ℕ) :
    θ * ∑ k ∈ Finset.range n, errorBudget θ e (k + 1) + (1 - θ) * errorBudget θ e n =
      (1 / 2) * ∑ k ∈ Finset.range n, (e k) ^ 2 := by
  induction n with
  | zero => simp [errorBudget]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, errorBudget]
    nlinarith

theorem errorBudget_sum_le {θ : ℝ} (hθ1 : θ ≤ 1) (e : ℕ → ℝ) (n : ℕ) :
    θ * ∑ k ∈ Finset.range n, errorBudget θ e (k + 1) ≤
      (1 / 2) * ∑ k ∈ Finset.range n, (e k) ^ 2 := by
  have hi := errorBudget_sum_identity θ e n
  have hn := mul_nonneg (sub_nonneg.mpr hθ1) (errorBudget_nonneg hθ1 e n)
  linarith

end RandomizedFO2003.Accelerated
