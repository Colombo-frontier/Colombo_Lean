import FreshGradientMinimax.NormalInverse
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-! A concrete positive parameter for the path recurrence, and its exact
hyperbolic solutions. These formulas are later checked against the actual
finite incidence operator, including its boundary rows. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def pathTheta (μ β : ℝ) : ℝ := Real.arsinh (Real.sqrt ((1 + μ / (2 * β)) ^ 2 - 1))

theorem pathTheta_pos {μ β : ℝ} (hμ : 0 < μ) (hβ : 0 < β) : 0 < pathTheta μ β := by
  apply Real.arsinh_pos_iff.mpr
  apply Real.sqrt_pos.mpr
  have h : 0 < μ / (2 * β) := by positivity
  nlinarith

theorem pathTheta_cosh {μ β : ℝ} (hμ : 0 < μ) (hβ : 0 < β) :
    Real.cosh (pathTheta μ β) = 1 + μ / (2 * β) := by
  have h : 0 < μ / (2 * β) := by positivity
  have hp : 0 ≤ (1 + μ / (2 * β)) ^ 2 - 1 := by nlinarith
  rw [pathTheta, Real.cosh_arsinh, Real.sq_sqrt hp]
  rw [show 1 + ((1 + μ / (2 * β)) ^ 2 - 1) = (1 + μ / (2 * β)) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

theorem pathTheta_coefficient {μ β : ℝ} (hμ : 0 < μ) (hβ : 0 < β) :
    μ + 2 * β = 2 * β * Real.cosh (pathTheta μ β) := by
  rw [pathTheta_cosh hμ hβ]
  field_simp
  ring

theorem path_sinh_recurrence (θ t : ℝ) :
    Real.sinh (t - θ) + Real.sinh (t + θ) = 2 * Real.cosh θ * Real.sinh t := by
  rw [Real.sinh_sub, Real.sinh_add]
  ring

def pathGreenSequence (β θ : ℝ) (n k : ℕ) : ℝ :=
  Real.sinh (k * θ) / (β * Real.sinh ((n + 1) * θ))

@[simp]
theorem pathGreenSequence_zero (β θ : ℝ) (n : ℕ) : pathGreenSequence β θ n 0 = 0 := by
  simp [pathGreenSequence]

theorem pathGreenSequence_boundary {β θ : ℝ} (hβ : 0 < β) (hθ : 0 < θ) (n : ℕ) :
    β * pathGreenSequence β θ n (n + 1) = 1 := by
  have hs : Real.sinh ((n + 1) * θ) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (by positivity)).ne'
  simp only [pathGreenSequence, Nat.cast_add, Nat.cast_one]
  field_simp

theorem pathGreenSequence_recurrence {μ β θ : ℝ}
    (hc : μ + 2 * β = 2 * β * Real.cosh θ) (n k : ℕ) :
    (μ + 2 * β) * pathGreenSequence β θ n (k + 1) -
      β * pathGreenSequence β θ n k - β * pathGreenSequence β θ n (k + 2) = 0 := by
  have h := path_sinh_recurrence θ ((k + 1) * θ)
  rw [show ((k : ℝ) + 1) * θ - θ = k * θ by ring,
    show ((k : ℝ) + 1) * θ + θ = (k + 2) * θ by ring] at h
  have hm := congrArg (fun t : ℝ => β * t / (β * Real.sinh ((n + 1) * θ))) h
  simp only [pathGreenSequence, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, hc]
  calc
    _ = (β * (2 * Real.cosh θ * Real.sinh (((k : ℝ) + 1) * θ)) -
        β * (Real.sinh (k * θ) + Real.sinh (((k : ℝ) + 2) * θ))) /
          (β * Real.sinh (((n : ℝ) + 1) * θ)) := by ring
    _ = 0 := by rw [h]; simp

end FreshGradientMinimax
