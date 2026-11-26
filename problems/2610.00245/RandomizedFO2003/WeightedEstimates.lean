import RandomizedFO2003.Spectral
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace RandomizedFO2003

open scoped BigOperators

variable {J : Type*} [Fintype J]

theorem weighted_energy_nonneg (ν r : J → ℝ) (hν : ∀ j, 0 ≤ ν j) :
    0 ≤ weightedEnergy ν r :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (hν j) (sq_nonneg _))

theorem weighted_pair_sq_le (ν r p : J → ℝ) (hν : ∀ j, 0 ≤ ν j) :
    weightedPair ν r p ^ 2 ≤ weightedEnergy ν r * weightedEnergy ν p := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
    (fun j _ => mul_nonneg (hν j) (sq_nonneg (r j)))
    (fun j _ => mul_nonneg (hν j) (sq_nonneg (p j)))
  intro j _
  ring

theorem weighted_pair_abs_le (ν r p : J → ℝ) (hν : ∀ j, 0 ≤ ν j) :
    |weightedPair ν r p| ≤ Real.sqrt (weightedEnergy ν r) *
      Real.sqrt (weightedEnergy ν p) := by
  have h := weighted_pair_sq_le ν r p hν
  have hr := Real.sq_sqrt (weighted_energy_nonneg ν r hν)
  have hp := Real.sq_sqrt (weighted_energy_nonneg ν p hν)
  have hprod : (Real.sqrt (weightedEnergy ν r) * Real.sqrt (weightedEnergy ν p)) ^ 2 =
      weightedEnergy ν r * weightedEnergy ν p := by rw [mul_pow, hr, hp]
  nlinarith [sq_abs (weightedPair ν r p),
    mul_nonneg (Real.sqrt_nonneg (weightedEnergy ν r)) (Real.sqrt_nonneg (weightedEnergy ν p))]

/-- Stability for a general pairing, including the inverse target, which need
not be orthogonal to the residual. -/
theorem weighted_pair_stability (ν ω r p : J → ℝ) (δ : ℝ)
    (hν : ∀ j, 0 ≤ ν j) (hδ : 0 ≤ δ)
    (hweight : ∀ j, |ω j - ν j| ≤ δ * ν j) :
    |weightedPair ω r p - weightedPair ν r p| ≤
      δ * (Real.sqrt (weightedEnergy ν r) * Real.sqrt (weightedEnergy ν p)) := by
  have heq : weightedPair ω r p - weightedPair ν r p =
      ∑ j, (ω j - ν j) * r j * p j := by
    simp [weightedPair, sub_mul, Finset.sum_sub_distrib]
  have hsum : 0 ≤ ∑ j, ν j * |r j| * |p j| :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (mul_nonneg (hν j) (abs_nonneg _)) (abs_nonneg _))
  have hcs : (∑ j, ν j * |r j| * |p j|) ≤
      Real.sqrt (weightedEnergy ν r) * Real.sqrt (weightedEnergy ν p) := by
    have h := weighted_cauchy_schwarz ν r p hν
    have hp : (Real.sqrt (weightedEnergy ν r) * Real.sqrt (weightedEnergy ν p)) ^ 2 =
        weightedEnergy ν r * weightedEnergy ν p := by
      rw [mul_pow, Real.sq_sqrt (weighted_energy_nonneg ν r hν),
        Real.sq_sqrt (weighted_energy_nonneg ν p hν)]
    nlinarith [mul_nonneg (Real.sqrt_nonneg (weightedEnergy ν r))
      (Real.sqrt_nonneg (weightedEnergy ν p))]
  calc
    _ = |∑ j, (ω j - ν j) * r j * p j| := congrArg abs heq
    _ ≤ ∑ j, |(ω j - ν j) * r j * p j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ δ * ∑ j, ν j * |r j| * |p j| := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      simp only [abs_mul]
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hweight j) (abs_nonneg (r j))) (abs_nonneg (p j))
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hcs hδ

/-- Converts exact design orthogonality into an estimate in the empirical
norms, with no division by a possibly zero polynomial norm. -/
theorem empirical_orthogonality_bound (ν ω r p : J → ℝ) (δ : ℝ)
    (hν : ∀ j, 0 ≤ ν j) (hω : ∀ j, 0 ≤ ω j)
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hweight : ∀ j, |ω j - ν j| ≤ δ * ν j)
    (horth : weightedPair ν r p = 0) :
    |weightedPair ω r p| ≤ 2 * δ *
      (Real.sqrt (weightedEnergy ω r) * Real.sqrt (weightedEnergy ω p)) := by
  have hr := (weighted_energy_stability ν ω r δ hweight).1
  have hp := (weighted_energy_stability ν ω p δ hweight).1
  have hr0 := weighted_energy_nonneg ν r hν
  have hp0 := weighted_energy_nonneg ν p hν
  have hrw0 := weighted_energy_nonneg ω r hω
  have hr' : weightedEnergy ν r ≤ 2 * weightedEnergy ω r := by nlinarith
  have hp' : weightedEnergy ν p ≤ 2 * weightedEnergy ω p := by nlinarith
  have hprod := mul_le_mul hr' hp' hp0 (by positivity : 0 ≤ 2 * weightedEnergy ω r)
  have hsqr : (Real.sqrt (weightedEnergy ω r) * Real.sqrt (weightedEnergy ω p)) ^ 2 =
      weightedEnergy ω r * weightedEnergy ω p := by
    rw [mul_pow, Real.sq_sqrt (weighted_energy_nonneg ω r hω),
      Real.sq_sqrt (weighted_energy_nonneg ω p hω)]
  have hs := approximate_orthogonality_squared ν ω r p δ hν hδ hweight horth
  have hb := mul_le_mul_of_nonneg_left hprod (sq_nonneg δ)
  have ht : 0 ≤ Real.sqrt (weightedEnergy ω r) * Real.sqrt (weightedEnergy ω p) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq : weightedPair ω r p ^ 2 ≤
      (2 * δ * (Real.sqrt (weightedEnergy ω r) * Real.sqrt (weightedEnergy ω p))) ^ 2 := by
    calc
      _ ≤ δ ^ 2 * (weightedEnergy ν r * weightedEnergy ν p) := hs
      _ ≤ δ ^ 2 * (2 * weightedEnergy ω r * (2 * weightedEnergy ω p)) := hb
      _ = _ := by rw [mul_pow, hsqr]; ring
  nlinarith [sq_abs (weightedPair ω r p), mul_nonneg (by positivity : 0 ≤ 2 * δ) ht]

end RandomizedFO2003
