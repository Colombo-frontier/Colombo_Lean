import MinimaxAudit.HardInstance
import MinimaxAudit.Haar

/-! A concrete integer random hard dimension, with the exact cubic-logarithmic
upper bound. Neither the radius nor the smoothness enters this public choice. -/
namespace MinimaxAudit
noncomputable section

/-- Universal coefficient for a strict interior gate margin. -/
def randomDimensionCoefficient : ℝ := 1280 / (geometryEta * geometryKappa) ^ 2

def randomHardDimension (N : ℕ) : ℕ :=
  (N + 1) + Nat.ceil (randomDimensionCoefficient * (N + 1 : ℝ) ^ 3 * Real.log (N + 2 : ℝ)) + 1

theorem randomDimensionCoefficient_pos : 0 < randomDimensionCoefficient := by
  unfold randomDimensionCoefficient geometryEta geometryKappa
  positivity

theorem randomHardDimension_gt (N : ℕ) : N + 1 < randomHardDimension N := by
  unfold randomHardDimension
  omega

theorem randomHardDimension_sufficient (N : ℕ) :
    1280 * (N + 1 : ℝ) ^ 3 / (geometryEta * geometryKappa) ^ 2 * Real.log (N + 2 : ℝ) ≤
      ((randomHardDimension N - (N + 1) : ℕ) : ℝ) := by
  let a := randomDimensionCoefficient * (N + 1 : ℝ) ^ 3 * Real.log (N + 2 : ℝ)
  have hceil : a ≤ (Nat.ceil a : ℝ) := Nat.le_ceil a
  have hnat : Nat.ceil a ≤ randomHardDimension N - (N + 1) := by
    unfold randomHardDimension
    change Nat.ceil a ≤ (N + 1) + Nat.ceil a + 1 - (N + 1)
    omega
  have hcast : (Nat.ceil a : ℝ) ≤ ((randomHardDimension N - (N + 1) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have heq : 1280 * (N + 1 : ℝ) ^ 3 / (geometryEta * geometryKappa) ^ 2 *
      Real.log (N + 2 : ℝ) = a := by
    unfold a randomDimensionCoefficient
    ring
  rw [heq]
  exact hceil.trans hcast

/-- Rounding costs only a universal addition to the cubic-log coefficient. -/
theorem randomHardDimension_upper (N : ℕ) :
    (randomHardDimension N : ℝ) ≤
      (randomDimensionCoefficient + 8) * (N + 1 : ℝ) ^ 3 * Real.log (N + 2 : ℝ) := by
  let n : ℝ := N + 1
  have hn : 1 ≤ n := by dsimp [n]; have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hn0 : 0 ≤ n := by linarith
  have hbase : 2 ≤ n + 1 := by linarith
  have hinv : (1 : ℝ) / (n + 1) ≤ 1 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hbase
  have hlog : (1 : ℝ) / 2 ≤ Real.log (n + 1) := by
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < n + 1 by linarith)
    simp only [one_div] at hinv
    linarith
  have hn2 : (1 : ℝ) ≤ n ^ 2 := one_le_pow₀ hn
  have hn3 : n ≤ n ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hn2 hn0
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hlog (pow_nonneg hn0 3)
  have hround : n + 2 ≤ 8 * n ^ 3 * Real.log (n + 1) := by nlinarith
  let a := randomDimensionCoefficient * n ^ 3 * Real.log (n + 1)
  have ha : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (mul_nonneg randomDimensionCoefficient_pos.le (pow_nonneg hn0 3))
      (by linarith)
  have hc := Nat.ceil_lt_add_one ha
  have harg : (N + 2 : ℝ) = n + 1 := by dsimp [n]; ring
  have han : a = randomDimensionCoefficient * (N + 1 : ℝ) ^ 3 * Real.log (N + 2 : ℝ) := by
    change randomDimensionCoefficient * n ^ 3 * Real.log (n + 1) = _
    rw [harg]
  have hd : (randomHardDimension N : ℝ) = n + (Nat.ceil a : ℝ) + 1 := by
    simp only [randomHardDimension, Nat.cast_add, Nat.cast_one]
    rw [← han]
  rw [hd, harg]
  change n + (Nat.ceil a : ℝ) + 1 ≤
    (randomDimensionCoefficient + 8) * n ^ 3 * Real.log (n + 1)
  have haeq : a = randomDimensionCoefficient * n ^ 3 * Real.log (n + 1) := rfl
  linarith

/-- The manuscript's calibrated gate width corresponds to the strict Haar slab. -/
theorem hardGateWidth_strict_slab (N : ℕ) (R : ℝ) :
    Haar.strictSlabThreshold (N + 1) geometryEta geometryKappa R =
      hardGateWidth N R / (8 * Real.sqrt 2) := by
  unfold Haar.strictSlabThreshold hardGateWidth hardSeed
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The chosen finite dimension satisfies the exact random transcript theorem. -/
theorem randomHardDimension_source_sufficient (N : ℕ) {R : ℝ} (hR : 0 < R) :
    2 * R ^ 2 / (hardGateWidth N R / (8 * Real.sqrt 2)) ^ 2 *
      Real.log (8 * (((N + 1) * (N + 2) : ℕ) : ℝ)) ≤
      ((randomHardDimension N - (N + 1) : ℕ) : ℝ) := by
  have hn : (0 : ℝ) < N + 1 := by positivity
  have heta : 0 < geometryEta := by norm_num [geometryEta]
  have hk : 0 < geometryKappa := by norm_num [geometryKappa]
  rw [← hardGateWidth_strict_slab N R, Haar.strict_slab_dimension_factor hn heta hk hR]
  have hlog := Haar.paired_event_log_bound (n := (N + 1 : ℝ)) (by
    have := Nat.cast_nonneg (α := ℝ) N
    linarith)
  have hlog' : Real.log (8 * (((N + 1) * (N + 2) : ℕ) : ℝ)) ≤
      5 * Real.log (N + 2 : ℝ) := by
    convert hlog using 1 <;> push_cast <;> ring_nf
  calc
    _ ≤ (256 * (N + 1 : ℝ) ^ 3 / (geometryEta * geometryKappa) ^ 2) *
        (5 * Real.log (N + 2 : ℝ)) := mul_le_mul_of_nonneg_left hlog' (by positivity)
    _ = 1280 * (N + 1 : ℝ) ^ 3 / (geometryEta * geometryKappa) ^ 2 *
        Real.log (N + 2 : ℝ) := by ring
    _ ≤ _ := randomHardDimension_sufficient N

end
end MinimaxAudit
