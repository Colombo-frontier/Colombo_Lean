import Mathlib.Tactic

namespace RandomizedFO2003

open scoped BigOperators

variable {J : Type*} [Fintype J]

def weightedPair (ν r p : J → ℝ) : ℝ := ∑ j, ν j * r j * p j
def weightedEnergy (ν r : J → ℝ) : ℝ := ∑ j, ν j * r j ^ 2

/-- Deterministic norm comparison on the relative spectral-weight event. -/
theorem weighted_energy_stability (ν ω r : J → ℝ) (δ : ℝ)
    (hweight : ∀ j, |ω j - ν j| ≤ δ * ν j) :
    (1 - δ) * weightedEnergy ν r ≤ weightedEnergy ω r ∧
      weightedEnergy ω r ≤ (1 + δ) * weightedEnergy ν r := by
  constructor
  · simp only [weightedEnergy, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have h := (abs_le.mp (hweight j)).1
    have hmul := mul_le_mul_of_nonneg_right h (sq_nonneg (r j))
    nlinarith
  · simp only [weightedEnergy, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have h := (abs_le.mp (hweight j)).2
    have hmul := mul_le_mul_of_nonneg_right h (sq_nonneg (r j))
    nlinarith

/-- Perturbation of exact orthogonality. No random-vector claim is assumed here. -/
theorem weighted_orthogonality_stability (ν ω r p : J → ℝ) (δ : ℝ)
    (hweight : ∀ j, |ω j - ν j| ≤ δ * ν j)
    (horth : weightedPair ν r p = 0) :
    |weightedPair ω r p| ≤ δ * ∑ j, ν j * |r j| * |p j| := by
  have heq : weightedPair ω r p = ∑ j, (ω j - ν j) * r j * p j := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    change weightedPair ω r p = weightedPair ω r p - weightedPair ν r p
    rw [horth, sub_zero]
  rw [heq, Finset.mul_sum]
  calc
    |∑ j, (ω j - ν j) * r j * p j| ≤ ∑ j, |(ω j - ν j) * r j * p j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, δ * (ν j * |r j| * |p j|) := by
      apply Finset.sum_le_sum
      intro j _
      simp only [abs_mul]
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hweight j) (abs_nonneg (r j))) (abs_nonneg (p j))
      nlinarith

theorem weighted_cauchy_schwarz (ν r p : J → ℝ) (hν : ∀ j, 0 ≤ ν j) :
    (∑ j, ν j * |r j| * |p j|) ^ 2 ≤ weightedEnergy ν r * weightedEnergy ν p := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
    (fun j _ => mul_nonneg (hν j) (sq_nonneg (r j)))
    (fun j _ => mul_nonneg (hν j) (sq_nonneg (p j)))
  intro j _
  simp only [mul_pow, sq_abs]
  ring

/-- Squared form of the short-Krylov orthogonality estimate, in design weights. -/
theorem approximate_orthogonality_squared (ν ω r p : J → ℝ) (δ : ℝ)
    (hν : ∀ j, 0 ≤ ν j) (hδ : 0 ≤ δ)
    (hweight : ∀ j, |ω j - ν j| ≤ δ * ν j)
    (horth : weightedPair ν r p = 0) :
    weightedPair ω r p ^ 2 ≤ δ ^ 2 * (weightedEnergy ν r * weightedEnergy ν p) := by
  have h := weighted_orthogonality_stability ν ω r p δ hweight horth
  have hsum : 0 ≤ ∑ j, ν j * |r j| * |p j| :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (mul_nonneg (hν j) (abs_nonneg _)) (abs_nonneg _))
  have hsq := sq_le_sq₀ (abs_nonneg (weightedPair ω r p)) (mul_nonneg hδ hsum)
  have hb : weightedPair ω r p ^ 2 ≤ δ ^ 2 * (∑ j, ν j * |r j| * |p j|) ^ 2 := by
    simpa only [sq_abs, mul_pow] using hsq.mpr h
  exact hb.trans (mul_le_mul_of_nonneg_left (weighted_cauchy_schwarz ν r p hν) (sq_nonneg δ))

end RandomizedFO2003
