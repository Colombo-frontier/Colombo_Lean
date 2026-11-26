import NCConcave16991.DenseWeakRowCost

/-! # The actual floor row cost has the required information budget -/

noncomputable section

namespace NCConcave16991.DenseWeakHiding

theorem rowCost_le_invSq (n : ℕ) (ρ : ℝ) :
    (rowCost n ρ : ℝ) ≤ (ρ⁻¹) ^ 2 / 4096 := by
  have hx : (0 : ℝ) ≤ (1 / 4096 : ℝ) * min (n : ℝ) ((ρ⁻¹) ^ 2) := by positivity
  exact (Nat.floor_le hx).trans (by nlinarith [min_le_right (n : ℝ) ((ρ⁻¹) ^ 2)])

theorem rowCost_bias_energy {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (rowCost n ((m : ℝ) / n) : ℝ) * (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 / 4096 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh := mul_le_mul_of_nonneg_right (rowCost_le_invSq n ((m : ℝ) / n)) (sq_nonneg (m : ℝ))
  have he : ((((m : ℝ) / n)⁻¹) ^ 2 / 4096) * (m : ℝ) ^ 2 = (n : ℝ) ^ 2 / 4096 := by
    field_simp [hnR.ne', hmR.ne']
  rwa [he] at hh

theorem information_coefficient_budget {n m r : ℝ} (hn : 0 < n) (hr : 0 ≤ r)
    (hrn : r ≤ n / 4096) (henergy : r * m ^ 2 ≤ n ^ 2 / 4096) :
    (32 / 63 : ℝ) * r * (m / (n - r)) ^ 2 ≤ 1 / 8000 := by
  have hd : 0 < n - r := by linarith
  have hscale : 0 ≤ (4095 / 4096 : ℝ) * n := by positivity
  have hden : ((4095 / 4096 : ℝ) * n) ^ 2 ≤ (n - r) ^ 2 :=
    pow_le_pow_left₀ hscale (by linarith) 2
  have he : (32 / 63 : ℝ) * r * (m / (n - r)) ^ 2 =
      ((32 / 63 : ℝ) * (r * m ^ 2)) / (n - r) ^ 2 := by rw [div_pow]; ring
  rw [he]
  apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
  have hnum := mul_le_mul_of_nonneg_left henergy (by norm_num : (0 : ℝ) ≤ 32 / 63)
  have hnum2 : (32 / 63 : ℝ) * (n ^ 2 / 4096) ≤
      (1 / 8000 : ℝ) * (((4095 / 4096 : ℝ) * n) ^ 2) := by
    nlinarith [sq_nonneg n]
  exact hnum.trans (hnum2.trans (mul_le_mul_of_nonneg_left hden (by norm_num)))

theorem parityGrid_information_budget {n : ℕ} (hn : 256 ≤ n) :
    let m := parityRoundedSqrt n
    let r := rowCost n ((m : ℝ) / n)
    (32 / 63 : ℝ) * (r : ℝ) * ((m : ℝ) / ((n : ℝ) - r)) ^ 2 ≤ 1 / 8000 := by
  dsimp only
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 256) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hmR : (0 : ℝ) < parityRoundedSqrt n :=
    (Real.sqrt_pos.mpr hnR).trans_le (parityRoundedSqrt_bounds n).1
  have hm0 : 0 < parityRoundedSqrt n := by exact_mod_cast hmR
  exact information_coefficient_budget hnR (Nat.cast_nonneg _)
    (parityGrid_rowCost_bounds hn).2 (rowCost_bias_energy hn0 hm0)

theorem parityGrid_rowCost_linear {n : ℕ} (hn : 65536 ≤ n) :
    (n : ℝ) / 32768 ≤ rowCost n ((parityRoundedSqrt n : ℝ) / n) ∧
      2 ≤ rowCost n ((parityRoundedSqrt n : ℝ) / n) := by
  have hn' : 256 ≤ n := by omega
  have hb := (parityGrid_rowCost_bounds hn').1
  have hnR : (65536 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · linarith
  · have hh : (2 : ℝ) ≤ rowCost n ((parityRoundedSqrt n : ℝ) / n) := by linarith
    exact_mod_cast hh

theorem parityGrid_row_information_interior {n : ℕ} (hn : 65536 ≤ n) :
    8 * (parityRoundedSqrt n : ℝ) +
      9 * (rowCost n ((parityRoundedSqrt n : ℝ) / n) : ℝ) ≤ (n : ℝ) := by
  have hnR : (65536 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : Real.sqrt (n : ℝ) ≤ (n : ℝ) / 256 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [mul_nonneg (show (0 : ℝ) ≤ n by positivity) (sub_nonneg.mpr hnR)]
  have hm := (parityRoundedSqrt_bounds n).2
  have hr := (parityGrid_rowCost_bounds (show 256 ≤ n by omega)).2
  linarith

end NCConcave16991.DenseWeakHiding
