import GradientHessian.Model

/-! Real arithmetic for optimizing the manuscript's parameter lower bound. -/

noncomputable section
namespace GradientHessian.ParameterOptimization

theorem three_halves_eq_mul_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  calc
    x ^ (3 / 2 : ℝ) = x ^ ((1 : ℝ) + 1 / 2) := by norm_num
    _ = x * Real.sqrt x := by
      rw [Real.rpow_add' hx (by norm_num), Real.rpow_one, Real.sqrt_eq_rpow]

theorem power_two_thirds_three_halves {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = x := by
  rw [← Real.rpow_mul hx]
  norm_num

theorem power_three_halves_two_thirds {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) = x := by
  rw [← Real.rpow_mul hx]
  norm_num

theorem sqrt_two_thirds {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (x ^ (2 / 3 : ℝ)) = x ^ (1 / 3 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num

theorem sqrt_min (x y : ℝ) :
    Real.sqrt (min x y) = min (Real.sqrt x) (Real.sqrt y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (Real.sqrt_le_sqrt h)]
  · rw [min_eq_right h, min_eq_right (Real.sqrt_le_sqrt h)]

/-- The rate is exactly `T` times the square root of the available size. -/
theorem lowerRate_eq (H d : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    Model.lowerRate H d T =
      T * Real.sqrt (min ((d : ℝ) ^ (2 / 3 : ℝ)) (T / ((H : ℝ) + 1))) := by
  rw [sqrt_min, mul_min_of_nonneg _ _ hT, sqrt_two_thirds (Nat.cast_nonneg d),
    Real.sqrt_div hT]
  unfold Model.lowerRate
  rw [three_halves_eq_mul_sqrt hT]
  congr 1
  ring

/-- The numerical dimension cost of a rounded size. -/
theorem dimension_power_bound {M ζ d : ℝ} (hM : 0 ≤ M) (hζ : 0 ≤ ζ)
    (hd : 0 ≤ d) (h : M ≤ ζ * d ^ (2 / 3 : ℝ)) :
    M ^ (3 / 2 : ℝ) ≤ ζ ^ (3 / 2 : ℝ) * d := by
  calc
    M ^ (3 / 2 : ℝ) ≤ (ζ * d ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow hM h (by norm_num)
    _ = ζ ^ (3 / 2 : ℝ) * d := by
      rw [Real.mul_rpow hζ (Real.rpow_nonneg hd _), power_two_thirds_three_halves hd]

/-- A quantitative loss estimate after rounding both integer parameters. -/
theorem rounded_rate_bound {E ζ M n T : ℝ} (H d : ℕ) (hE : 0 < E)
    (hζ : 0 ≤ ζ) (hM : 0 < M) (hT : 0 ≤ T)
    (hsize : ζ * min ((d : ℝ) ^ (2 / 3 : ℝ)) (T / ((H : ℝ) + 1)) / 4 ≤ M)
    (hn : T / (8 * E * M) ≤ n) :
    (Real.sqrt ζ / (16 * E)) * Model.lowerRate H d T ≤ n * M ^ (3 / 2 : ℝ) := by
  let K := min ((d : ℝ) ^ (2 / 3 : ℝ)) (T / ((H : ℝ) + 1))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hs := Real.sqrt_le_sqrt hsize
  have hs4 : Real.sqrt (ζ * K / 4) = Real.sqrt ζ * Real.sqrt K / 2 := by
    rw [Real.sqrt_div (mul_nonneg hζ hK), Real.sqrt_mul hζ]
    norm_num
  change Real.sqrt (ζ * K / 4) ≤ Real.sqrt M at hs
  rw [hs4] at hs
  have hn' : T ≤ n * (8 * E * M) := (div_le_iff₀ (by positivity)).mp hn
  have hs' := mul_le_mul_of_nonneg_left hs hT
  have hn'' := mul_le_mul_of_nonneg_right hn' (Real.sqrt_nonneg M)
  rw [lowerRate_eq H d hT, three_halves_eq_mul_sqrt hM.le]
  change Real.sqrt ζ / (16 * E) * (T * Real.sqrt K) ≤ n * (M * Real.sqrt M)
  calc
    Real.sqrt ζ / (16 * E) * (T * Real.sqrt K) =
        (T * (Real.sqrt ζ * Real.sqrt K)) / (16 * E) := by ring
    _ ≤ n * (M * Real.sqrt M) :=
      (div_le_iff₀ (by positivity)).mpr (by nlinarith [hs', hn''])

end GradientHessian.ParameterOptimization
